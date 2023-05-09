--------------------------- MODULE election_algo ---------------------------

EXTENDS Naturals, Sequence, TLC

CONSTANTS N

Node == 1..N
pre_elec(n) == IF n > 1 THEN n - 1 ELSE N

ASSUME
 /\ N \in Nat \ {0}

(* --algorithm election_algo {
    variables 
        election = [self \in 1..N |-> ""];
        num_UID = [self \in 1..N |-> 0];
        max_UID = 0;
        start = TRUE;
    
    fair process (Send \in 1..N)
    variables
        election_produce = "",
        election_UID = 0,
        leader = FALSE,
        pre_elec
        {
            p1 : while(TRUE) 
                {
                    if (start == TRUE) 
                    {
                        election[self] := "election";
                        num_UID[self] := self;
                        start := FALSE;
                    }
                    else
                    {
                        await(election[self] = "" \/ elction[self] = "election"); 
                        if (election[pre_elec(self)] == "election" /\ elction[self] == "")
                        {
                            if (num_UID[pre_elec(self)] <= self)
                            {
                                num_UID[self] := self;
                                election[self] := "election";
                            }
                            else
                            {
                                num_UID[self] := num_UID[pre_elec(self)];
                                election[self] := "election";
                            }
                        }
                        else if (election[pre_elec(self)] == "election" /\ elction[self] == "election")
                        {
                            if (num_UID[pre_elec(self)] < self)
                            {
                                num_UID[self] := self;
                                election[self] := "elected";
                                max_UID := num_UID[self];
                            }
                            else
                            {
                                num_UID[self] := num_UID[pre_elec(self)];
                                election[self] := "elected";
                                max_UID := num_UID[self];
                            }
                        }
                        else if (election[pre_elec(self)] == "elected" /\ election[self] == "election")
                        {
                            if (self = max_UID)
                                leader := TRUE;
                            election[self] := "elected";
                        }
                    }
                }
        }
}
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "a1960156" /\ chksum(tla) = "634dea1a")
CONSTANT defaultInitValue
VARIABLES election, num_UID, max_UID, start, election_produce, election_UID, 
          leader, pre_elec

vars == << election, num_UID, max_UID, start, election_produce, election_UID, 
           leader, pre_elec >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ election = [self \in 1..N |-> ""]
        /\ num_UID = [self \in 1..N |-> 0]
        /\ max_UID = 0
        /\ start = TRUE
        (* Process Send *)
        /\ election_produce = [self \in 1..N |-> ""]
        /\ election_UID = [self \in 1..N |-> 0]
        /\ leader = [self \in 1..N |-> FALSE]
        /\ pre_elec = [self \in 1..N |-> defaultInitValue]

Send(self) == /\ IF start == TRUE
                    THEN /\ election' = [election EXCEPT ![self] = "election"]
                         /\ num_UID' = [num_UID EXCEPT ![self] = self]
                         /\ start' = FALSE
                         /\ UNCHANGED << max_UID, leader >>
                    ELSE /\ (election[self] = "" \/ elction[self] = "election")
                         /\ IF election[pre_elec[self](self)] == "election" /\ elction[self] == ""
                               THEN /\ IF num_UID[pre_elec[self](self)] <= self
                                          THEN /\ num_UID' = [num_UID EXCEPT ![self] = self]
                                               /\ election' = [election EXCEPT ![self] = "election"]
                                          ELSE /\ num_UID' = [num_UID EXCEPT ![self] = num_UID[pre_elec[self](self)]]
                                               /\ election' = [election EXCEPT ![self] = "election"]
                                    /\ UNCHANGED << max_UID, leader >>
                               ELSE /\ IF election[pre_elec[self](self)] == "election" /\ elction[self] == "election"
                                          THEN /\ IF num_UID[pre_elec[self](self)] < self
                                                     THEN /\ num_UID' = [num_UID EXCEPT ![self] = self]
                                                          /\ election' = [election EXCEPT ![self] = "elected"]
                                                          /\ max_UID' = num_UID'[self]
                                                     ELSE /\ num_UID' = [num_UID EXCEPT ![self] = num_UID[pre_elec[self](self)]]
                                                          /\ election' = [election EXCEPT ![self] = "elected"]
                                                          /\ max_UID' = num_UID'[self]
                                               /\ UNCHANGED leader
                                          ELSE /\ IF election[pre_elec[self](self)] == "elected" /\ election[self] == "election"
                                                     THEN /\ IF self = max_UID
                                                                THEN /\ leader' = [leader EXCEPT ![self] = TRUE]
                                                                ELSE /\ TRUE
                                                                     /\ UNCHANGED leader
                                                          /\ election' = [election EXCEPT ![self] = "elected"]
                                                     ELSE /\ TRUE
                                                          /\ UNCHANGED << election, 
                                                                          leader >>
                                               /\ UNCHANGED << num_UID, 
                                                               max_UID >>
                         /\ start' = start
              /\ UNCHANGED << election_produce, election_UID, pre_elec >>

Next == (\E self \in 1..N: Send(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..N : WF_vars(Send(self))

\* END TRANSLATION 



=============================================================================
\* Modification History
\* Last modified Tue Apr 11 15:46:01 KST 2023 by rnyeong._.jin
\* Created Sun Apr 09 23:33:46 KST 2023 by rnyeong._.jin
