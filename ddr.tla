------------------------------- MODULE ddr ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANT MV, DDR \* The set of major versions. MV = 2..4

(***************************************************************************
--fair algorithm ddr {
variable smState = [mv \in MV |-> "NULL"],
         ddrState = [mv \in MV |-> "NULL"]
         
define {
   isSliceManagementRunning(state) == state \in { "NEW", "EMR" }
   isTrackingDDRRunning(state) == state \in {"EMR"}
   isTrackingDDRExisting(state) == state \in {"NEW", "EMR"}
}

  fair process (SliceManagementGenerator=0) {
GSM: while (\E mv \in MV: smState[mv] = "NULL") {
       with (mv \in MV) {
         \* If there is an existing DDR job, do not start new slice managemnet job
         if (smState[mv] = "NULL" /\ ~isTrackingDDRExisting(ddrState[mv])) {
            smState[mv] := "NEW";
         }
       }
     }
  }

  fair process (MasterDDRJob=1) {
MDDR: while (\E mv \in MV: ddrState[mv] = "NULL") {
        with (mv \in MV) {
          if (ddrState[mv] = "NULL") {
              ddrState[mv] := "NEW";
          }
        }
      }
  }

  fair process (smp \in MV) {
SM: while (smState[self] /= "DONE") {
        either {
            await smState[self] = "NEW";
            smState[self] := "EMR";
        } or {
            await smState[self] = "EMR";
            smState[self] := "DONE";
        }
    }
  }

   fair process (ddr \in DDR)
   variables majorversion=self-1; {
TDDR: while (ddrState[majorversion] /= "DONE") {
          either {
             await ddrState[majorversion] = "NEW" /\ smState[majorversion] \notin {"NEW", "EMR"};
             ddrState[majorversion] := "EMR";
          } or {
             await ddrState[majorversion] = "EMR";
             ddrState[majorversion] := "DONE";
          }
      }
  }

}
 ***************************************************************************)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-ac4934b0f8337cab34a244aca27e59d3
VARIABLES smState, ddrState, pc

(* define statement *)
isSliceManagementRunning(state) == state \in { "NEW", "EMR" }
isTrackingDDRRunning(state) == state \in {"EMR"}
isTrackingDDRExisting(state) == state \in {"NEW", "EMR"}

VARIABLE majorversion

vars == << smState, ddrState, pc, majorversion >>

ProcSet == {0} \cup {1} \cup (MV) \cup (DDR)

Init == (* Global variables *)
        /\ smState = [mv \in MV |-> "NULL"]
        /\ ddrState = [mv \in MV |-> "NULL"]
        (* Process ddr *)
        /\ majorversion = [self \in DDR |-> self-1]
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "GSM"
                                        [] self = 1 -> "MDDR"
                                        [] self \in MV -> "SM"
                                        [] self \in DDR -> "TDDR"]

GSM == /\ pc[0] = "GSM"
       /\ IF \E mv \in MV: smState[mv] = "NULL"
             THEN /\ \E mv \in MV:
                       IF smState[mv] = "NULL" /\ ~isTrackingDDRExisting(ddrState[mv])
                          THEN /\ smState' = [smState EXCEPT ![mv] = "NEW"]
                          ELSE /\ TRUE
                               /\ UNCHANGED smState
                  /\ pc' = [pc EXCEPT ![0] = "GSM"]
             ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                  /\ UNCHANGED smState
       /\ UNCHANGED << ddrState, majorversion >>

SliceManagementGenerator == GSM

MDDR == /\ pc[1] = "MDDR"
        /\ IF \E mv \in MV: ddrState[mv] = "NULL"
              THEN /\ \E mv \in MV:
                        IF ddrState[mv] = "NULL"
                           THEN /\ ddrState' = [ddrState EXCEPT ![mv] = "NEW"]
                           ELSE /\ TRUE
                                /\ UNCHANGED ddrState
                   /\ pc' = [pc EXCEPT ![1] = "MDDR"]
              ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
                   /\ UNCHANGED ddrState
        /\ UNCHANGED << smState, majorversion >>

MasterDDRJob == MDDR

SM(self) == /\ pc[self] = "SM"
            /\ IF smState[self] /= "DONE"
                  THEN /\ \/ /\ smState[self] = "NEW"
                             /\ smState' = [smState EXCEPT ![self] = "EMR"]
                          \/ /\ smState[self] = "EMR"
                             /\ smState' = [smState EXCEPT ![self] = "DONE"]
                       /\ pc' = [pc EXCEPT ![self] = "SM"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED smState
            /\ UNCHANGED << ddrState, majorversion >>

smp(self) == SM(self)

TDDR(self) == /\ pc[self] = "TDDR"
              /\ IF ddrState[majorversion[self]] /= "DONE"
                    THEN /\ \/ /\ ddrState[majorversion[self]] = "NEW" /\ smState[majorversion[self]] \notin {"NEW", "EMR"}
                               /\ ddrState' = [ddrState EXCEPT ![majorversion[self]] = "EMR"]
                            \/ /\ ddrState[majorversion[self]] = "EMR"
                               /\ ddrState' = [ddrState EXCEPT ![majorversion[self]] = "DONE"]
                         /\ pc' = [pc EXCEPT ![self] = "TDDR"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED ddrState
              /\ UNCHANGED << smState, majorversion >>

ddr(self) == TDDR(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == SliceManagementGenerator \/ MasterDDRJob
           \/ (\E self \in MV: smp(self))
           \/ (\E self \in DDR: ddr(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ WF_vars(SliceManagementGenerator)
        /\ WF_vars(MasterDDRJob)
        /\ \A self \in MV : WF_vars(smp(self))
        /\ \A self \in DDR : WF_vars(ddr(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-8772925f775f065b6c6c213faae37a81

(***************************************************************************
Eventually the job are either not started or terminated
 ***************************************************************************)
Completed == <>(\A mv \in MV : smState[mv] \in {"DONE"} /\ ddrState[mv] \in {"DONE"})


(***************************************************************************
Invariant that slice management job and tracking job should be mutually exclusive
 ***************************************************************************)
Mutex == \A mv \in MV:
             CASE isSliceManagementRunning(smState[mv]) -> ~isTrackingDDRRunning(ddrState[mv])
               [] isTrackingDDRRunning(ddrState[mv]) -> ~isSliceManagementRunning(smState[mv])
               [] OTHER -> TRUE
                     

=============================================================================
\* Modification History
\* Last modified Sun Sep 27 01:26:38 PDT 2020 by yanson
\* Created Sat Sep 26 19:45:35 PDT 2020 by yanson
