------------------------------ MODULE rws_ddr ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANT MV \* The set of major versions. MV = 2..4

(***************************************************************************
--fair algorithm ddr {
variable smState = [mv \in MV |-> "NULL"],
         ddrState = [mv \in MV |-> "NULL"];

define {
   isSliceManagementRunning(state) == state \in { "NEW", "EMR" }
   isTrackingDDRRunning(state) == state \in {"EMR"}
   isTrackingDDRExisting(state) == state \in {"NEW", "EMR"}
}

  fair process (SliceManagementGenerator=0) {
GSM: with (mv \in MV) {
         \* If there is an existing DDR job, do not start new slice managemnet job
         if (smState[mv] = "NULL" /\ ~isTrackingDDRExisting(ddrState[mv])) {
            smState[mv] := "NEW";
         }
     }
  }

  fair process (MasterDDRJob=1) {
MDDR:  with (mv \in MV) {
          if (ddrState[mv] = "NULL") {
              ddrState[mv] := "NEW";
          }
      }
  }

  fair process (SliceManagementJob=2) {
SM:   with (mv \in MV) {
       if (smState[mv] \notin {"NULL", "DONE"}) {
            if (smState[mv] = "NEW") {
                smState[mv] := "EMR";
            } else if (smState[mv] = "EMR") {
                smState[mv] := "DONE";
            }
        };
     }
   }

   fair process (TrackingDDR=3) {
TDDR:  with (mv \in MV) {
         if (ddrState[mv] \notin {"NULL", "DONE"}) {
             if (ddrState[mv] = "NEW" /\ ~isSliceManagementRunning(smState[mv])) {
                 ddrState[mv] := "EMR";
             } else if (ddrState[mv] = "EMR") {
                ddrState[mv] := "DONE";
             }
         }
       }
  }

}
 ***************************************************************************)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-2a238c893982ebb1179e76f44c3b7c5b
VARIABLES smState, ddrState, pc

(* define statement *)
isSliceManagementRunning(state) == state \in { "NEW", "EMR" }
isTrackingDDRRunning(state) == state \in {"EMR"}
isTrackingDDRExisting(state) == state \in {"NEW", "EMR"}


vars == << smState, ddrState, pc >>

ProcSet == {0} \cup {1} \cup {2} \cup {3}

Init == (* Global variables *)
        /\ smState = [mv \in MV |-> "NULL"]
        /\ ddrState = [mv \in MV |-> "NULL"]
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "GSM"
                                        [] self = 1 -> "MDDR"
                                        [] self = 2 -> "SM"
                                        [] self = 3 -> "TDDR"]

GSM == /\ pc[0] = "GSM"
       /\ \E mv \in MV:
            IF smState[mv] = "NULL" /\ ~isTrackingDDRExisting(ddrState[mv])
               THEN /\ smState' = [smState EXCEPT ![mv] = "NEW"]
               ELSE /\ TRUE
                    /\ UNCHANGED smState
       /\ pc' = [pc EXCEPT ![0] = "Done"]
       /\ UNCHANGED ddrState

SliceManagementGenerator == GSM

MDDR == /\ pc[1] = "MDDR"
        /\ \E mv \in MV:
             IF ddrState[mv] = "NULL"
                THEN /\ ddrState' = [ddrState EXCEPT ![mv] = "NEW"]
                ELSE /\ TRUE
                     /\ UNCHANGED ddrState
        /\ pc' = [pc EXCEPT ![1] = "Done"]
        /\ UNCHANGED smState

MasterDDRJob == MDDR

SM == /\ pc[2] = "SM"
      /\ \E mv \in MV:
           IF smState[mv] \notin {"NULL", "DONE"}
              THEN /\ IF smState[mv] = "NEW"
                         THEN /\ smState' = [smState EXCEPT ![mv] = "EMR"]
                         ELSE /\ IF smState[mv] = "EMR"
                                    THEN /\ smState' = [smState EXCEPT ![mv] = "DONE"]
                                    ELSE /\ TRUE
                                         /\ UNCHANGED smState
              ELSE /\ TRUE
                   /\ UNCHANGED smState
      /\ pc' = [pc EXCEPT ![2] = "Done"]
      /\ UNCHANGED ddrState

SliceManagementJob == SM

TDDR == /\ pc[3] = "TDDR"
        /\ \E mv \in MV:
             IF ddrState[mv] \notin {"NULL", "DONE"}
                THEN /\ IF ddrState[mv] = "NEW" /\ ~isSliceManagementRunning(smState[mv])
                           THEN /\ ddrState' = [ddrState EXCEPT ![mv] = "EMR"]
                           ELSE /\ IF ddrState[mv] = "EMR"
                                      THEN /\ ddrState' = [ddrState EXCEPT ![mv] = "DONE"]
                                      ELSE /\ TRUE
                                           /\ UNCHANGED ddrState
                ELSE /\ TRUE
                     /\ UNCHANGED ddrState
        /\ pc' = [pc EXCEPT ![3] = "Done"]
        /\ UNCHANGED smState

TrackingDDR == TDDR

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == SliceManagementGenerator \/ MasterDDRJob \/ SliceManagementJob
           \/ TrackingDDR
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ WF_vars(SliceManagementGenerator)
        /\ WF_vars(MasterDDRJob)
        /\ WF_vars(SliceManagementJob)
        /\ WF_vars(TrackingDDR)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-ffc2812d6f1c7a918ee3c3c31fc87ab6

(***************************************************************************
Eventually the job are either not started or terminated
 ***************************************************************************)
Completed == <>(\A mv \in MV : smState[mv] \in {"NULL", "DONE"} /\ ddrState[mv] \in {"NULL", "DONE"})


(***************************************************************************
Invariant that slice management job and tracking job should be mutually exclusive
 ***************************************************************************)
Mutex == \A mv \in MV:
             CASE isSliceManagementRunning(smState[mv]) -> ~isTrackingDDRRunning(ddrState[mv])
               [] isTrackingDDRRunning(ddrState[mv]) -> ~isSliceManagementRunning(smState[mv])
               [] OTHER -> TRUE
                     

=============================================================================
\* Modification History
\* Last modified Sat Sep 26 22:37:46 PDT 2020 by yanson
\* Created Sat Sep 26 19:45:35 PDT 2020 by yanson
