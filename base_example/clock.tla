------------------------------ MODULE clock ------------------------------
VARIABLE clock                    \*declare clock variables
vars == << clock >>               \*declare variable list
Inv == clock \in {0, 1}           \*define invariant
Init == clock \in {0, 1}          \*initialization
Tick ==                           \*clock Tick
        IF clock = 0              \*If the value of clock is 0
           THEN clock' = 1        \*change the value of clock to 1
           ELSE clock' = 0        \* change the value of clock to 0
Spec ==                           \*Specification
        /\ Init                   \*Initialize, and /\is the logical and
        /\ [][Tick]_vars          \*Tick is always true or keeps variables unchanged
        /\ WF_vars(Tick)          \*prevent Tick from never executing
=============================================================================
\* Modification History
\* Last modified Tue Mar 28 09:57:31 KST 2023 by rnyeong._.jin
\* Created Tue Mar 21 09:43:09 KST 2023 by rnyeong._.jin
