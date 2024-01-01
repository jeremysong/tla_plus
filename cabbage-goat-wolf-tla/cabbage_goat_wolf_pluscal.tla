---- MODULE cabbage_goat_wolf_pluscal ----
EXTENDS TLC, FiniteSets, Naturals

\* A farmer with a wolf, a goat, and a cabbage must cross a river by boat.
\* The boat can carry only the farmer and a single item.
\* If left unattended together, the wolf would eat the goat,
\* or the goat would eat the cabbage.
\* How can they cross the river without anything being eaten?

CONSTANTS CABBAGE, GOAT, WOLF, FARMER

Items == {CABBAGE, GOAT, WOLF}

(* --algorithm puzzel {
    variables
      bank_a = Items \union {FARMER};
      bank_b = {};

    define {
        TypeOK == /\ bank_a \intersect bank_b = {}
                  /\ bank_a \union bank_b = {CABBAGE, GOAT, WOLF, FARMER}
        
        \* If farmer is not at the bank, make sure all items are safe
        SafeBank(bank) == FARMER \notin bank => ({CABBAGE, GOAT} \notin SUBSET bank) /\ ({WOLF, GOAT} \notin SUBSET bank)
        Safe(a, b) == SafeBank(a) /\ SafeBank(b)
        
        \* Returns either 1 or 0 item for farmer to carry to the other bank
        SafeItem(a, b) == { item \in SUBSET (a \ {FARMER}):
            /\ SafeBank(a \ ({FARMER} \union item))
            /\ SafeBank(b \union {FARMER} \union item)
            /\ Cardinality(item) <= 1
        }

        AllSafe == Safe(bank_a, bank_b)
        NotSovled == (Items \union {FARMER}) # bank_b
    }

    fair process (p1 = "moveToB") {
        MOVE_TO_B:
        while(TRUE) {
            await FARMER \in bank_a;
            with (item \in SafeItem(bank_a, bank_b)) {
                print(<<"Moving from A to B", item, bank_a, bank_b>>);
                bank_b := bank_b \union {FARMER} \union item;
                bank_a := bank_a \ ({FARMER} \union item);
                print(<<"After Moving from A to B", item, bank_a, bank_b>>);
            }
        }
    }

    fair process (p2 = "moveToA") {
        MOVE_TO_A:
        while(TRUE) {
            await FARMER \in bank_b;
            with (item \in SafeItem(bank_b, bank_a)) {
                print(<<"Moving from B to A", item, bank_a, bank_b>>);
                bank_a := bank_a \union {FARMER} \union item;
                bank_b := bank_b \ ({FARMER} \union item);
                print(<<"After Moving from B to A", item, bank_a, bank_b>>);
            }
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "1ad6e5ea" /\ chksum(tla) = "17897e95")
VARIABLES bank_a, bank_b

(* define statement *)
TypeOK == /\ bank_a \intersect bank_b = {}
          /\ bank_a \union bank_b = {CABBAGE, GOAT, WOLF, FARMER}

SafeBank(bank) == FARMER \notin bank => ({CABBAGE, GOAT} \notin SUBSET bank) /\ ({WOLF, GOAT} \notin SUBSET bank)
Safe(a, b) == SafeBank(a) /\ SafeBank(b)

SafeItem(a, b) == { item \in SUBSET (a \ {FARMER}):
    /\ SafeBank(a \ ({FARMER} \union item))
    /\ SafeBank(b \union {FARMER} \union item)
    /\ Cardinality(item) <= 1
}

AllSafe == Safe(bank_a, bank_b)
NotSovled == (Items \union {FARMER}) # bank_b


vars == << bank_a, bank_b >>

ProcSet == {"moveToB"} \cup {"moveToA"}

Init == (* Global variables *)
        /\ bank_a = (Items \union {FARMER})
        /\ bank_b = {}

p1 == /\ FARMER \in bank_a
      /\ \E item \in SafeItem(bank_a, bank_b):
           /\ PrintT((<<"Picking item:", item>>))
           /\ PrintT((<<"Moving from A to B", item, bank_a, bank_b>>))
           /\ bank_b' = (bank_b \union {FARMER} \union item)
           /\ bank_a' = bank_a \ ({FARMER} \union item)
           /\ PrintT((<<"After Moving from A to B", item, bank_a', bank_b'>>))

p2 == /\ FARMER \in bank_b
      /\ \E item \in SafeItem(bank_b, bank_a):
           /\ PrintT((<<"Picking item:", item>>))
           /\ PrintT((<<"Moving from B to A", item, bank_a, bank_b>>))
           /\ bank_a' = (bank_a \union {FARMER} \union item)
           /\ bank_b' = bank_b \ ({FARMER} \union item)
           /\ PrintT((<<"After Moving from B to A", item, bank_a', bank_b'>>))

Next == p1 \/ p2

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(p1)
        /\ WF_vars(p2)

\* END TRANSLATION 

====
