-------------------------------- MODULE FIFO --------------------------------

EXTENDS Integers, Sequences

CONSTANT Task

VARIABLE queue

Init == queue = <<>>

Enqueue(task) == 
            queue' = Append(queue, task)

Dequeue == 
            /\ queue # <<>>
            /\ queue' = Tail(queue)

Next == 
        \/ Enqueue(Task)
        \/ Dequeue

FIFOScheduler == 
                Init /\ [][Next]_queue

=============================================================================
\* Modification History
\* Last modified Tue Mar 28 12:31:15 KST 2023 by rnyeong._.jin
\* Created Tue Mar 28 12:08:25 KST 2023 by rnyeong._.jin
