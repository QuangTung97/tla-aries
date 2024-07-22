------ MODULE aries ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Page

VARIABLES mem_page, mem_page_lsn, mem_rec_lsn, dirty,
    disk_page, disk_page_lsn,
    mem_log_start, mem_log_end, disk_log_start, disk_log_end,
    buffer, flush_page, flush_page_data, flush_page_lsn,
    recovering, log, fail_count

vars == <<mem_page, mem_page_lsn, mem_rec_lsn, dirty,
    disk_page, disk_page_lsn,
    mem_log_start, mem_log_end, disk_log_start, disk_log_end,
    buffer, flush_page, flush_page_data, flush_page_lsn,
    recovering, log, fail_count>>

mem_vars == <<mem_page, mem_page_lsn, mem_rec_lsn, dirty,
    mem_log_start, mem_log_end, buffer,
    flush_page, flush_page_data, flush_page_lsn,
    recovering>>

disk_vars == <<disk_page, disk_page_lsn,
    disk_log_start, disk_log_end>>

flush_vars == <<flush_page, flush_page_data, flush_page_lsn>>

max_buffer_len == 2
mem_log_size == 2
disk_log_size == 4
max_fail_count == 3
lsn_max == 6

null == "nil"

Terminated ==
    /\ disk_log_end >= lsn_max
    /\ fail_count >= max_fail_count
    /\ buffer = {}


TypeOK ==
    /\ mem_page_lsn \in [Page -> Nat]
    /\ mem_page \in [Page -> Seq(Nat)]
    /\ mem_rec_lsn \in [Page -> Nat]
    /\ dirty \in SUBSET Page
    /\ disk_page_lsn \in [Page -> Nat]
    /\ disk_page \in [Page -> Seq(Nat)]
    /\ mem_log_start \in Nat
    /\ mem_log_end \in Nat
    /\ disk_log_start \in Nat
    /\ disk_log_end \in Nat
    /\ buffer \in SUBSET Page
    /\ flush_page \in Page \union {null}
    /\ flush_page_data \in Seq(Nat)
    /\ flush_page_lsn \in Nat
    /\ recovering \in BOOLEAN
    /\ log \in Seq(Page)
    /\ fail_count \in Nat


InitMem ==
    /\ recovering = TRUE
    /\ mem_page_lsn = [p \in Page |-> 0]
    /\ mem_page = [p \in Page |-> <<>>]
    /\ mem_rec_lsn = [p \in Page |-> 0]
    /\ dirty = {}
    /\ mem_log_start = 1
    /\ mem_log_end = 0
    /\ buffer = {}
    /\ flush_page = null
    /\ flush_page_data = <<>>
    /\ flush_page_lsn = 0
    /\ fail_count = 0


Init ==
    /\ InitMem
    /\ disk_page_lsn = [p \in Page |-> 0]
    /\ disk_page = [p \in Page |-> <<>>]
    /\ disk_log_start = 1
    /\ disk_log_end = 0
    /\ log = <<>>


BufferLen == Cardinality(buffer)


FixPage(p) ==
    /\ ~(p \in buffer)
    /\ BufferLen < max_buffer_len
    /\ buffer' = buffer \union {p}
    /\ mem_page' = [mem_page EXCEPT ![p] = disk_page[p]]
    /\ mem_page_lsn' = [mem_page_lsn EXCEPT ![p] = disk_page_lsn[p]]
    /\ UNCHANGED mem_rec_lsn
    /\ UNCHANGED dirty
    /\ UNCHANGED flush_vars
    /\ UNCHANGED disk_vars
    /\ UNCHANGED recovering
    /\ UNCHANGED log
    /\ UNCHANGED fail_count
    /\ UNCHANGED <<mem_log_start, mem_log_end>>


EvictPage(p) ==
    /\ p \in buffer
    /\ ~(p \in dirty)
    /\ buffer' = buffer \ {p}
    /\ UNCHANGED dirty
    /\ UNCHANGED disk_vars
    /\ UNCHANGED flush_vars
    /\ UNCHANGED log
    /\ UNCHANGED <<mem_log_start, mem_log_end>>
    /\ UNCHANGED <<mem_page, mem_page_lsn, mem_rec_lsn>>
    /\ UNCHANGED recovering
    /\ UNCHANGED fail_count


MemLogAvail == mem_log_end + 1 - mem_log_start < mem_log_size


SetPage(p, lsn) ==
    /\ mem_page' = [mem_page EXCEPT ![p] = Append(@, lsn)]
    /\ mem_page_lsn' = [mem_page_lsn EXCEPT ![p] = lsn]
    /\ IF p \in dirty
        THEN
            /\ UNCHANGED dirty
            /\ UNCHANGED mem_rec_lsn
        ELSE
            /\ mem_rec_lsn' = [mem_rec_lsn EXCEPT ![p] = lsn]
            /\ dirty' = dirty \union {p}


DoRecover ==
    /\ recovering
    /\ mem_log_end < disk_log_end
    /\ MemLogAvail
    /\ mem_log_end' = mem_log_end + 1
    /\ LET p == log[mem_log_end'] IN
        /\ p \in buffer
        /\ IF mem_log_end' > mem_page_lsn[p]
            THEN SetPage(p, mem_log_end')
            ELSE UNCHANGED <<mem_page, mem_page_lsn, mem_rec_lsn, dirty>>
    /\ UNCHANGED <<buffer, mem_log_start>>
    /\ UNCHANGED recovering
    /\ UNCHANGED flush_vars
    /\ UNCHANGED log
    /\ UNCHANGED disk_vars
    /\ UNCHANGED fail_count


ReadyToFinish ==
    /\ recovering
    /\ mem_log_end = disk_log_end


RecoverFinish ==
    /\ ReadyToFinish
    /\ recovering' = FALSE
    /\ UNCHANGED disk_vars
    /\ UNCHANGED <<buffer, dirty>>
    /\ UNCHANGED flush_vars
    /\ UNCHANGED log
    /\ UNCHANGED fail_count
    /\ UNCHANGED <<mem_log_start, mem_log_end>>
    /\ UNCHANGED <<mem_page, mem_page_lsn, mem_rec_lsn>>


Update(p) ==
    /\ ~recovering
    /\ mem_log_end < lsn_max
    /\ (mem_log_end + 1 - disk_log_start) < disk_log_size
    /\ p \in buffer
    /\ MemLogAvail
    /\ log' = Append(log, p)
    /\ mem_log_end' = mem_log_end + 1
    /\ SetPage(p, mem_log_end')
    /\ UNCHANGED mem_log_start
    /\ UNCHANGED flush_vars
    /\ UNCHANGED buffer
    /\ UNCHANGED recovering
    /\ UNCHANGED fail_count
    /\ UNCHANGED disk_vars


SyncLog(index) ==
    /\ index - disk_log_start + 1 <= disk_log_size
    /\ disk_log_end' = index
    /\ UNCHANGED mem_vars
    /\ UNCHANGED <<disk_log_start, disk_page, disk_page_lsn>>
    /\ UNCHANGED log
    /\ UNCHANGED fail_count


TrimLogBuffer(index) ==
    /\ mem_log_start' = index
    /\ UNCHANGED <<mem_log_end, mem_page, mem_page_lsn, mem_rec_lsn>>
    /\ UNCHANGED <<buffer, dirty>>
    /\ UNCHANGED flush_vars
    /\ UNCHANGED disk_vars
    /\ UNCHANGED recovering
    /\ UNCHANGED fail_count
    /\ UNCHANGED log


PrepareFlush(p) ==
    /\ p \in buffer
    /\ p \in dirty
    /\ flush_page = null
    /\ flush_page' = p
    /\ flush_page_data' = mem_page[p]
    /\ flush_page_lsn' = mem_page_lsn[p]
    /\ UNCHANGED <<mem_log_start, mem_log_end>>
    /\ UNCHANGED buffer
    /\ UNCHANGED dirty
    /\ UNCHANGED <<mem_page, mem_page_lsn, mem_rec_lsn>>
    /\ UNCHANGED disk_vars
    /\ UNCHANGED log
    /\ UNCHANGED recovering
    /\ UNCHANGED fail_count


FlushPage ==
    LET p == flush_page IN
        /\ p /= null
        /\ flush_page_lsn <= disk_log_end
        /\ disk_page' = [disk_page EXCEPT ![p] = flush_page_data]
        /\ disk_page_lsn' = [disk_page_lsn EXCEPT ![p] = flush_page_lsn]
        /\ flush_page' = null
        /\ flush_page_data' = <<>>
        /\ flush_page_lsn' = 0
        /\ mem_rec_lsn' = [mem_rec_lsn EXCEPT ![p] = flush_page_lsn + 1]
        /\ IF mem_page_lsn[p] = flush_page_lsn
            THEN dirty' = dirty \ {p}
            ELSE UNCHANGED dirty
        /\ UNCHANGED buffer
        /\ UNCHANGED <<mem_log_start, mem_log_end>>
        /\ UNCHANGED <<mem_page, mem_page_lsn>>
        /\ UNCHANGED <<disk_log_start, disk_log_end>>
        /\ UNCHANGED log
        /\ UNCHANGED recovering
        /\ UNCHANGED fail_count


SystemFail ==
    /\ fail_count < max_fail_count
    /\ fail_count' = fail_count + 1
    /\ recovering' = TRUE
    /\ mem_page_lsn' = [p \in Page |-> 0]
    /\ mem_page' = [p \in Page |-> <<>>]
    /\ mem_rec_lsn' = [p \in Page |-> 0]
    /\ dirty' = {}
    /\ mem_log_start' = disk_log_start
    /\ mem_log_end' = disk_log_start - 1
    /\ buffer' = {}
    /\ flush_page' = null
    /\ flush_page_data' = <<>>
    /\ flush_page_lsn' = 0
    /\ log' = SubSeq(log, 1, disk_log_end) \* trim log
    /\ UNCHANGED disk_vars


Checkpoint ==
    \E lsn \in (disk_log_start + 1)..(disk_log_end + 1):
        /\ ~recovering
        /\ \A p \in dirty: mem_rec_lsn[p] >= lsn
        /\ disk_log_start' = lsn
        /\ UNCHANGED mem_vars
        /\ UNCHANGED disk_log_end
        /\ UNCHANGED <<disk_page, disk_page_lsn>>
        /\ UNCHANGED fail_count
        /\ UNCHANGED log


Next ==
    \/ DoRecover
    \/ RecoverFinish
    \/ \E p \in Page:
        \/ FixPage(p)
        \/ Update(p)
        \/ PrepareFlush(p)
        \/ EvictPage(p)
    \/ \E index \in (disk_log_end + 1)..mem_log_end: SyncLog(index)
    \/ \E index \in (mem_log_start + 1)..(disk_log_end + 1): TrimLogBuffer(index)
    \/ FlushPage
    \/ SystemFail
    \/ Checkpoint


InSeq(e, s) ==
    /\ \E index \in DOMAIN s: s[index] = e


ExistEntry(index, p) ==
    /\ IF p \in buffer
        THEN InSeq(index, mem_page[p])
        ELSE InSeq(index, disk_page[p])


PageOpSet(p) == {mem_page[p][index]: index \in DOMAIN mem_page[p]}

NoDuplicate(p) == Cardinality(PageOpSet(p)) = Len(mem_page[p])


DataConsistent ==
    /\ \A p \in buffer: NoDuplicate(p)
    /\ \A p \in buffer:
        /\ \A index \in DOMAIN mem_page[p]:
            mem_page[p][index] <= Len(log)
    /\ \A index \in DOMAIN log:
        /\ \E p \in Page: \* Exists unique page p
            /\ ExistEntry(index, p)
            /\ \A p1 \in Page: ExistEntry(index, p1) => p1 = p


Consistency ==
    /\ ~recovering => DataConsistent
    /\ mem_log_end - mem_log_start + 1 <= mem_log_size
    /\ Cardinality(buffer) <= max_buffer_len
    /\ (mem_log_end < disk_log_start) => dirty = {}
    /\ dirty \subseteq buffer


Perms == Permutations(Page)

====