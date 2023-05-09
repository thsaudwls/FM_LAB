------------------------------- MODULE Chang -------------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANTS N, Start_Node

pre_elec(n) == IF n > 1 THEN n - 1 ELSE N

ASSUME 
    /\ N \in Nat \{0}

(* --algorithm election{

    variables
        mail_elec = [self \in 1..N |-> ""];
        mail_UID = [self \in 1..N |-> 0];
        
    fair process (send \in 1..N)
    variables
        leader = 0;
        end_election = 0;
        recv_msg = "";
        recv_UID = 0;
        start = 1;
    {
        starts : while (TRUE)
        {
            if (start = 1 /\ Start_Node = self)
            {  
                mail_elec[self] := "election";
                mail_UID[self] := self;
                start := 0;
            }
            else 
            {
                await end_election = 0;
                if (recv_msg = "election" /\ recv_UID # self /\ end_election = 0)
                {
                    if (recv_UID > self)
                    {
                        mail_elec[self] := "election";
                        mail_UID[self] := recv_UID;                        
                    }
                    else
                    {
                        mail_elec[self] := "election";
                        mail_UID[self] := self;
                    }
                }
                else if (recv_msg = "election" /\ recv_UID = self /\ end_election = 0)
                {
                    mail_elec[self] := "elected";
                    mail_UID[self] := self;
                    leader := 1;
                    end_election = 1;
                }
                else
                {
                    if (recv_msg = "elected")
                    {
                        mail_elec[self] := "elected";
                        mail_UID[self] := recv_UID;
                        end_election := 1;
                    }
                }
            }
        }
    }
    
    fair process (recv \in 1..N)
    variables
    {
        startr : while (TRUE)
        {
            recv_msg := mail_elec[pre_elec(self)];
            recv_UID := mail_UID[pre_elec(self)];
        }
    }
}
*)

\* BEGIN TRANSLATION (chksum(pcal) \in STRING /\ chksum(tla) \in STRING)

VARIABLES mail_elec, mail_UID, leader, end_election, recv_msg, recv_UID, 
          start

vars == << mail_elec, mail_UID, leader, end_election, recv_msg, recv_UID, 
           start >>

ProcSet == (1..N) \cup (1..N)

Init == (* Global variables *)
        /\ mail_elec = [self \in 1..N |-> ""]
        /\ mail_UID = [self \in 1..N |-> 0]
        (* Process send *)
        /\ leader = [self \in 1..N |-> 0]
        /\ end_election = [self \in 1..N |-> 0]
        /\ recv_msg = [self \in 1..N |-> ""]
        /\ recv_UID = [self \in 1..N |-> 0]
        /\ start = [self \in 1..N |-> 1]

send(self) == /\ IF start[self] = 1 /\ Start_Node = self
                  THEN /\ mail_elec' = [mail_elec EXCEPT ![self] = "election"]
                       /\ mail_UID' = [mail_UID EXCEPT ![self] = self]
                       /\ start' = [start EXCEPT ![self] = 0]
                       /\ UNCHANGED << leader, end_election >>
                  ELSE /\ end_election[self] = 0
                       /\ IF recv_msg[self] = "election" /\ recv_UID[self] # self /\ end_election[self] = 0
                           THEN /\ IF recv_UID[self] > self
                                    THEN /\ mail_elec' = [mail_elec EXCEPT ![self] = "election"]
                                         /\ mail_UID' = [mail_UID EXCEPT ![self] = recv_UID[self]]
                                    ELSE /\ mail_elec' = [mail_elec EXCEPT ![self] = "election"]
                                         /\ mail_UID' = [mail_UID EXCEPT ![self] = self]
                                /\ UNCHANGED << leader, end_election >>
                           ELSE /\ IF recv_msg[self] = "election" /\ recv_UID[self] = self /\ end_election[self] = 0
                                    THEN /\ mail_elec' = [mail_elec EXCEPT ![self] = "elected"]
                                         /\ mail_UID' = [mail_UID EXCEPT ![self] = self]
                                         /\ leader' = [leader EXCEPT ![self] = 1]
                                         /\ UNCHANGED end_election
                                    ELSE /\ IF recv_msg[self] = "elected"
                                             THEN /\ mail_elec' = [mail_elec EXCEPT ![self] = "elected"]
                                                  /\ mail_UID' = [mail_UID EXCEPT ![self] = recv_UID[self]]
                                                  /\ end_election' = [end_election EXCEPT ![self] = 1]
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED << mail_elec, 
                                                                  mail_UID, 
                                                                  end_election >>
                                       /\ UNCHANGED leader
                      /\ start' = start
              /\ UNCHANGED << recv_msg, recv_UID >>

recv(self) == /\ recv_msg' = [recv_msg EXCEPT ![self] = mail_elec[pre_elec(self)]]
              /\ recv_UID' = [recv_UID EXCEPT ![self] = mail_UID[pre_elec(self)]]
              /\ UNCHANGED << mail_elec, mail_UID, leader, end_election, start >>

Next == (\E self \in 1..N: send(self))
           \/ (\E self \in 1..N: recv(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..N : WF_vars(send(self))
        /\ \A self \in 1..N : WF_vars(recv(self))

Correctness == \E n \in 1..N : leader[n] = 1 =>
                /\ \A m \in 1..N \ {n} :
                    /\ leader[m] = 0
                    /\ mail_UID[m] = mail_UID[n]
                    
Liveness == \E n \in 1..N : start[n] = 0 =>
                /\ <> \E p \in 1..N : leader[p] = 1


=============================================================================
\* Modification History
\* Last modified Fri Apr 28 14:53:44 KST 2023 by rnyeong._.jin
\* Created Tue Apr 11 21:41:32 KST 2023 by rnyeong._.jin
