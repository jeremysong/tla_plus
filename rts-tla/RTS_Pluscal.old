-------------- MODULE RTS_Pluscal --------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS NULL, PUBLISHING, FAILED, SUCCEEDED, MAX_VERSION

PublishProcess == {1, 2}
OtsHost == {10, 11, 12}
CustomerIds == {100, 101, 102, 103}

(* --algorithm Rts {
    variables
      memorydb = <<>>; \* A funtion mapping from customer ID to version 
      version = 0; \* Globally unique version ID
      batches = <<>>; \* A function mapping from version to status

    define {
        TypeOK == /\ DOMAIN memorydb \subseteq CustomerIds
                  /\ version >= 0
                  /\ \A v \in DOMAIN batches: batches[v] \in {PUBLISHING, FAILED, SUCCEEDED}
        
        EventuallyComplete == <>[](\A v \in DOMAIN batches: batches[v] \in {FAILED, SUCCEEDED})
    }

    fair process (Host \in OtsHost)
        variable v; {
        READ:
        while (TRUE) {
            with (id \in CustomerIds) {
                if (id \in DOMAIN memorydb) {
                    \* print(<<"Read data", self, id, memorydb>>);
                    v := memorydb[id];
                    assert id \in DOMAIN memorydb;
                    \* assert batches[v] # FAILED;
                }
            }
        }
    }

    fair process (Publisher \in PublishProcess)
        variable v = 0; {
        PUBLISH:
        while (version < MAX_VERSION) {
        INIT:
            v := version;
            version := version + 1;
            \* print(version);
            assert v \notin DOMAIN batches;
            batches := v :> PUBLISHING @@ batches;
        WRITE:
        with (ids \in (SUBSET(CustomerIds) \ {{}})) {
            memorydb := [id \in ids |-> v] @@ memorydb;
        };
        STATUS:
            with (status \in {FAILED, SUCCEEDED}) {
                batches := v :> status @@ batches;
                \* print(batches);
            }
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "cb9608d0" /\ chksum(tla) = "3bf92335")
\* Process variable v of process Host at line 25 col 18 changed to v_
CONSTANT defaultInitValue
VARIABLES memorydb, version, batches, pc

(* define statement *)
TypeOK == /\ DOMAIN memorydb \subseteq CustomerIds
          /\ version >= 0
          /\ \A v \in DOMAIN batches: batches[v] \in {PUBLISHING, FAILED, SUCCEEDED}

EventuallyComplete == <>[](\A v \in DOMAIN batches: batches[v] \in {FAILED, SUCCEEDED})

VARIABLES v_, v

vars == << memorydb, version, batches, pc, v_, v >>

ProcSet == (OtsHost) \cup (PublishProcess)

Init == (* Global variables *)
        /\ memorydb = <<>>
        /\ version = 0
        /\ batches = <<>>
        (* Process Host *)
        /\ v_ = [self \in OtsHost |-> defaultInitValue]
        (* Process Publisher *)
        /\ v = [self \in PublishProcess |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in OtsHost -> "READ"
                                        [] self \in PublishProcess -> "PUBLISH"]

READ(self) == /\ pc[self] = "READ"
              /\ \E id \in CustomerIds:
                   IF id \in DOMAIN memorydb
                      THEN /\ v_' = [v_ EXCEPT ![self] = memorydb[id]]
                           /\ Assert(id \in DOMAIN memorydb, 
                                     "Failure of assertion at line 32, column 21.")
                      ELSE /\ TRUE
                           /\ v_' = v_
              /\ pc' = [pc EXCEPT ![self] = "READ"]
              /\ UNCHANGED << memorydb, version, batches, v >>

Host(self) == READ(self)

PUBLISH(self) == /\ pc[self] = "PUBLISH"
                 /\ IF version < MAX_VERSION
                       THEN /\ pc' = [pc EXCEPT ![self] = "INIT"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << memorydb, version, batches, v_, v >>

INIT(self) == /\ pc[self] = "INIT"
              /\ v' = [v EXCEPT ![self] = version]
              /\ version' = version + 1
              /\ Assert(v'[self] \notin DOMAIN batches, 
                        "Failure of assertion at line 47, column 13.")
              /\ batches' = (v'[self] :> PUBLISHING @@ batches)
              /\ pc' = [pc EXCEPT ![self] = "WRITE"]
              /\ UNCHANGED << memorydb, v_ >>

WRITE(self) == /\ pc[self] = "WRITE"
               /\ \E ids \in (SUBSET(CustomerIds) \ {{}}):
                    memorydb' = [id \in ids |-> v[self]] @@ memorydb
               /\ pc' = [pc EXCEPT ![self] = "STATUS"]
               /\ UNCHANGED << version, batches, v_, v >>

STATUS(self) == /\ pc[self] = "STATUS"
                /\ \E status \in {FAILED, SUCCEEDED}:
                     batches' = (v[self] :> status @@ batches)
                /\ pc' = [pc EXCEPT ![self] = "PUBLISH"]
                /\ UNCHANGED << memorydb, version, v_, v >>

Publisher(self) == PUBLISH(self) \/ INIT(self) \/ WRITE(self)
                      \/ STATUS(self)

Next == (\E self \in OtsHost: Host(self))
           \/ (\E self \in PublishProcess: Publisher(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in OtsHost : WF_vars(Host(self))
        /\ \A self \in PublishProcess : WF_vars(Publisher(self))

\* END TRANSLATION 


=====================
