------ MODULE aries ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Page

VARIABLES mem_page, mem_page_lsn, mem_rec_lsn,
    disk_page, disk_page_lsn,
    mem_log_start, mem_log_end, disk_log_start, disk_log_end,
    buffer

vars == <<mem_page, mem_page_lsn, mem_rec_lsn,
    disk_page, disk_page_lsn,
    mem_log_start, mem_log_end, disk_log_start, disk_log_end,
    buffer>>

mem_vars == <<mem_page, mem_page_lsn, mem_rec_lsn,
    mem_log_start, mem_log_end, buffer>>

disk_vars == <<disk_page, disk_page_lsn,
    disk_log_start, disk_log_end>>

max_buffer_len == 2
mem_log_size == 3

ARIESConstraint == mem_log_end <= 5

TypeOK ==
    /\ mem_page_lsn \in [Page -> Nat]
    /\ mem_page \in [Page -> Seq(Nat)]
    /\ mem_rec_lsn \in [Page -> Nat]
    /\ disk_page_lsn \in [Page -> Nat]
    /\ disk_page \in [Page -> Seq(Nat)]
    /\ mem_log_start \in Nat
    /\ mem_log_end \in Nat
    /\ disk_log_start \in Nat
    /\ disk_log_end \in Nat
    /\ buffer \in SUBSET Page

Terminated ==
    /\ UNCHANGED vars

Init ==
    /\ mem_page_lsn = [p \in Page |-> 0]
    /\ mem_page = [p \in Page |-> <<>>]
    /\ mem_rec_lsn = [p \in Page |-> 0]
    /\ disk_page_lsn = [p \in Page |-> 0]
    /\ disk_page = [p \in Page |-> <<>>]
    /\ mem_log_start = 1
    /\ mem_log_end = 0
    /\ disk_log_start = 1
    /\ disk_log_end = 0
    /\ buffer = {}


BufferLen == Cardinality(buffer)


FixPage(p) ==
    /\ ~(p \in buffer)
    /\ BufferLen < max_buffer_len
    /\ buffer' = buffer \union {p}
    /\ mem_page' = [mem_page EXCEPT ![p] = disk_page[p]]
    /\ mem_page_lsn' = [mem_page_lsn EXCEPT ![p] = disk_page_lsn[p]]
    /\ UNCHANGED mem_rec_lsn
    /\ UNCHANGED disk_vars
    /\ UNCHANGED <<mem_log_start, mem_log_end>>


Update(p) ==
    /\ p \in buffer
    /\ mem_log_end + 1 - mem_log_start < mem_log_size
    /\ mem_log_end' = mem_log_end + 1
    /\ mem_page_lsn' = [mem_page_lsn EXCEPT ![p] = mem_log_end']
    /\ mem_rec_lsn' = [mem_rec_lsn EXCEPT ![p] = mem_log_end']
    /\ mem_page' = [mem_page EXCEPT ![p] = Append(@, mem_log_end')]
    /\ UNCHANGED mem_log_start
    /\ UNCHANGED buffer
    /\ UNCHANGED disk_vars


SyncLog(index) ==
    /\ disk_log_end' = index
    /\ UNCHANGED mem_vars
    /\ UNCHANGED <<disk_log_start, disk_page, disk_page_lsn>>

TrimLogBuffer(index) ==
    /\ mem_log_start' = index
    /\ UNCHANGED <<buffer, mem_log_end, mem_page, mem_page_lsn, mem_rec_lsn>>
    /\ UNCHANGED disk_vars


Next ==
    \/ \E p \in Page:
        \/ FixPage(p)
        \/ Update(p)
    \/ \E index \in (disk_log_end + 1)..mem_log_end: SyncLog(index)
    \/ \E index \in (mem_log_start + 1)..(disk_log_end + 1): TrimLogBuffer(index)
    \/ Terminated


====