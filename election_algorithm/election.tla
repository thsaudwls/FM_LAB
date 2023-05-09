------------------------------ MODULE election ------------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANTS N, Start_Node

pre_elec(n) == IF n > 1 THEN n - 1 ELSE N

ASSUME 
    /\ N \in Nat \{0}

(* --algorithm election{

    variables
        mailbox = [self \in 1..N |-> <<>>];
        
    fair process (send \in 1..N)
    variables
        leader = 0;
        end_election = 0;
        recv_msg = "",
        recv_UID = 0;
    {
        starts : while (TRUE)
        {
            if (Start_Node == self /\ end_election == 0)
            {
                await Len(mailbox[self]) < 2;      
                mailbox[self] := Append(@, "election");
                mailbox[self] := Append(mailbox[self], self);
            }
            else 
            {
                if (recv_msg == "election" /\ recv_UID # self /\ end_election == 0)
                {
                    if (recv_UID > self)
                    {
                        p3 :
                            mailbox[self] := Append(@, "election");
                        p4 :
                            mailbox[self] := Append(@, recv_UID);
                    }
                    else
                    {
                        p5 :
                            mailbox[self] := Append(@, "election");
                        p6 :
                            mailbox[self] := Append(@, self);
                    }
                }
                else if (recv_msg = "election" /\ recv_UID == self /\ end_election == 0)
                {
                    p7 :
                        mailbox[self] := Append(@, "elected");
                    p8 :
                        mailbox[self] := Append(@, self);
                    leader := 1;
                    print "leader = ";
                    print self;
                }
                else if (recv_msg = "elected")
                {
                    p9 :
                        mailbox[self] := Append(@, "elected");
                    p10 :
                        mailbox[self] := Append(@, recv_UID);
                }
                else
                {
                    end_election := 1;
                }
            }
        }
    }
    
    fair process (recv \in 1..N)
    variables
    {
        startr : while (TRUE)
        {
            await Len(mailbox[pre_elec(self)]) > 0;
            recv_msg := Head(mailbox[pre_elec(self)]);
            recv_UID := Head(mailbox[pre_elec(self)]);
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) \in STRING /\ chksum(tla) \in STRING)
VARIABLES mailbox, pc, leader, end_election, recv_msg, recv_UID

vars == << mailbox, pc, leader, end_election, recv_msg, recv_UID >>

ProcSet == (1..N) \cup (1..N)

Init == (* Global variables *)
        /\ mailbox = [self \in 1..N |-> <<>>]
        (* Process send *)
        /\ leader = [self \in 1..N |-> 0]
        /\ end_election = [self \in 1..N |-> 0]
        /\ recv_msg = [self \in 1..N |-> ""]
        /\ recv_UID = [self \in 1..N |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in 1..N -> "starts"
                                        [] self \in 1..N -> "startr"]

starts(self) == /\ pc[self] = "starts"
                /\ IF Start_Node == self /\ end_election[self] == 0
                      THEN /\ Len(mailbox[self]) < 2
                           /\ mailbox' = [mailbox EXCEPT ![self] = Append(@, "election")]
                           /\ pc' = [pc EXCEPT ![self] = "p2"]
                           /\ UNCHANGED end_election
                      ELSE /\ IF recv_msg[self] == "election" /\ recv_UID[self] # self /\ end_election[self] == 0
                                 THEN /\ IF recv_UID[self] > self
                                            THEN /\ pc' = [pc EXCEPT ![self] = "p3"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "p5"]
                                      /\ UNCHANGED end_election
                                 ELSE /\ IF recv_msg[self] = "election" /\ recv_UID[self] == self /\ end_election[self] == 0
                                            THEN /\ pc' = [pc EXCEPT ![self] = "p7"]
                                                 /\ UNCHANGED end_election
                                            ELSE /\ IF recv_msg[self] = "elected"
                                                       THEN /\ pc' = [pc EXCEPT ![self] = "p9"]
                                                            /\ UNCHANGED end_election
                                                       ELSE /\ end_election' = [end_election EXCEPT ![self] = 1]
                                                            /\ pc' = [pc EXCEPT ![self] = "starts"]
                           /\ UNCHANGED mailbox
                /\ UNCHANGED << leader, recv_msg, recv_UID >>

p2(self) == /\ pc[self] = "p2"
            /\ mailbox' = [mailbox EXCEPT ![self] = Append(mailbox[self], self)]
            /\ pc' = [pc EXCEPT ![self] = "starts"]
            /\ UNCHANGED << leader, end_election, recv_msg, recv_UID >>

p3(self) == /\ pc[self] = "p3"
            /\ mailbox' = [mailbox EXCEPT ![self] = Append(@, "election")]
            /\ pc' = [pc EXCEPT ![self] = "p4"]
            /\ UNCHANGED << leader, end_election, recv_msg, recv_UID >>

p4(self) == /\ pc[self] = "p4"
            /\ mailbox' = [mailbox EXCEPT ![self] = Append(@, recv_UID[self])]
            /\ pc' = [pc EXCEPT ![self] = "starts"]
            /\ UNCHANGED << leader, end_election, recv_msg, recv_UID >>

p5(self) == /\ pc[self] = "p5"
            /\ mailbox' = [mailbox EXCEPT ![self] = Append(@, "election")]
            /\ pc' = [pc EXCEPT ![self] = "p6"]
            /\ UNCHANGED << leader, end_election, recv_msg, recv_UID >>

p6(self) == /\ pc[self] = "p6"
            /\ mailbox' = [mailbox EXCEPT ![self] = Append(@, self)]
            /\ pc' = [pc EXCEPT ![self] = "starts"]
            /\ UNCHANGED << leader, end_election, recv_msg, recv_UID >>

p7(self) == /\ pc[self] = "p7"
            /\ mailbox' = [mailbox EXCEPT ![self] = Append(@, "elected")]
            /\ pc' = [pc EXCEPT ![self] = "p8"]
            /\ UNCHANGED << leader, end_election, recv_msg, recv_UID >>

p8(self) == /\ pc[self] = "p8"
            /\ mailbox' = [mailbox EXCEPT ![self] = Append(@, self)]
            /\ leader' = [leader EXCEPT ![self] = 1]
            /\ PrintT("leader = ")
            /\ PrintT(self)
            /\ pc' = [pc EXCEPT ![self] = "starts"]
            /\ UNCHANGED << end_election, recv_msg, recv_UID >>

p9(self) == /\ pc[self] = "p9"
            /\ mailbox' = [mailbox EXCEPT ![self] = Append(@, "elected")]
            /\ pc' = [pc EXCEPT ![self] = "p10"]
            /\ UNCHANGED << leader, end_election, recv_msg, recv_UID >>

p10(self) == /\ pc[self] = "p10"
             /\ mailbox' = [mailbox EXCEPT ![self] = Append(@, recv_UID[self])]
             /\ pc' = [pc EXCEPT ![self] = "starts"]
             /\ UNCHANGED << leader, end_election, recv_msg, recv_UID >>

send(self) == starts(self) \/ p2(self) \/ p3(self) \/ p4(self) \/ p5(self)
                 \/ p6(self) \/ p7(self) \/ p8(self) \/ p9(self)
                 \/ p10(self)

startr(self) == /\ pc[self] = "startr"
                /\ Len(mailbox[pre_elec(self)]) > 0
                /\ recv_msg' = [recv_msg EXCEPT ![self] = Head(mailbox[pre_elec(self)])]
                /\ recv_UID' = [recv_UID EXCEPT ![self] = Head(mailbox[pre_elec(self)])]
                /\ pc' = [pc EXCEPT ![self] = "startr"]
                /\ UNCHANGED << mailbox, leader, end_election >>

recv(self) == startr(self)

Next == (\E self \in 1..N: send(self))
           \/ (\E self \in 1..N: recv(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..N : WF_vars(send(self))
        /\ \A self \in 1..N : WF_vars(recv(self))

\* END TRANSLATION 


Correctness == \E n \in 1..N : leader[n] = 1 =>
                /\ \A m \in 1..N \ {n} :
                    /\ leader[m] = 0
                    /\ recv_UID[m] < recv_UID[n]
                    


=============================================================================
\* Modification History
\* Last modified Tue Apr 11 21:39:43 KST 2023 by rnyeong._.jin
\* Created Tue Apr 11 18:54:24 KST 2023 by rnyeong._.jin
