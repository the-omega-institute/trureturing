# Concurrent native cut acquisition with rereading workspace

## 1. Source, complete row and evidence boundary

This volume is mathematical reference input. Its constructions and proofs are
ordinary mathematical arguments, not new Lean certification. The source-specific
contribution is acquisition without an auxiliary tree or transcript, with a
uniform workspace bound and an explicit family separating workspace from Read
traffic. Native leaf certification, endpoint obstructions and post-acquisition
recovery retain their existing suppliers.

**Definition 1.1 (source and history).** Use exactly [CNA, Definitions 1.1–1.4][CNA].
The source is any finite nonempty ordered full tree, with

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\quad \rho\alpha=\beta,
\quad \rho\beta=\langle\beta,\alpha\rangle,
\quad \rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
$$

One atomic `Read(p)` accepts an entire materialized finite $L/R$ word and
returns alpha, beta, branch or absent. Every finite address is legal.
An independent internal writer may apply genuine global $\rho$ to this same
register between observer events, including during local computation.
There are no other source changes, resets, rerootings, locks, snapshots,
subtree-equality ports, source-walk handles, size queries, epochs or schedule
notifications. The observer's fixed program and initialization are independent
of the unknown source. The public cut is its only variable input.

Observer progress means that every pending local step or Read eventually
occurs after finitely many intervening events. Finite interference means a
finite total number of writer updates during the pending call, without a
known bound or a known last-update event. Safety below holds on every legal
history on which the procedure returns; termination additionally requires
finite interference and observer progress.

**Definition 1.2 (row).** The public $P$ is any finite prefix-free address set,
including the empty cut and the root cut. Put $O=P\cap\operatorname{Pos}(u)$.
Reuse [NAR, Definition 1.2][NAR] and [ACPD] `literalRecord`: $C_P(u)$ is the
literal ordered exterior with the entire subtree at each reached $p\in O$
replaced by an address-marked hole, and

$$
R_P(u)=(C_P(u),\pi_P(u)),\qquad
p\sim_{\pi_P(u)}q\ \Longleftrightarrow\ u|_p=u|_q.
\tag{CWS.1}
$$

Different classes assert disequality. Every unreached cut address has a
concrete blocking strict-prefix leaf in the exterior; these guards are part
of the literal output, not just absence flags. Prefix freeness ensures that
such a blocking leaf is not hidden behind another cut hole.
For $P=\varnothing$ the output intrinsically contains the whole tree. For
$P=\{\varepsilon\}$ it is the constant root hole and singleton partition.
The output is an actual readable retained object.

**Mathematical citation 1.3 (reused native certificate).** [CNA, Theorem 2.2
and §4][CNA], using [NDP] `original_present_transport`, supplies two facts:
present addresses and branches persist; two equal leaf replies at one address
enclose zero global updates. A left-only search from the root obtains such
a leaf without knowing height. Branch and absent replies do not certify a
quiet interval. This volume applies that existing guard to a different
computation; it does not recreate the full-tree acquisition theorem.

**Definition 1.4 (safety endpoints).** Invocation, validation and Return are
separate events. Our validation event is the last guard Read. Validation
safety asserts $R=R_P(U_v)$ there and implies existence of an instantaneous
in-call version with row $R$. It asserts neither the invocation row nor the
row at the separate Return event. The endpoint obstructions and special-cut
exceptions are [CNA, §7][CNA]; no new endpoint guarantee is implicit below.

## 2. A finite program using paths and a private row

**Definition 2.1 (charged sequential storage).** Fix a finite program with a
constant number of named, extensible sequence regions and a constant number
of scalar registers. Each sequence cell has an alphabet of sixteen symbols,
hence four bits. A region supports reading and writing a cell, appending one
cell and retracting its last cell. A head is a binary encoded offset, counted
as mutable state even when the region is immutable. Scalar integers are
variable-length binary strings; arithmetic is performed by finite bit steps.
No unbounded integer, program counter, pointer or region length is one bit.

Regions have fixed names; there are no per-node heap pointers. Used capacity,
lengths, head offsets and the finite control are billed. Extension is by one
cell at the end, not by making a second copy of a growing tree. Retraction
and clearing take paid local steps. This is an abstract finite-sequence
storage model, not a claim about a language runtime's allocator, garbage
collector, secure deletion or physical memory bandwidth. A realization with
extra allocation tables, unreclaimed capacity, address translation or copies
must add them to its account.

The immutable cut tape encodes its addresses in lexicographic order, each
terminated by `/`, followed by `!`. Its length is

$$
K=1+\sum_{p\in P}(|p|+1),\qquad M=|P|.
\tag{CWS.2}
$$

It occupies $4K$ bits in this encoding, even when most cut addresses are
absent. No cut trie or bound on source height is installed. Input validity
and prefix freeness are the stated public promise; scanning the tape is paid.
Code and its fixed literal alphabet occupy a source-independent constant
$I_{\rm code}$ bits. There is no source-specific immutable address dictionary.

**Definition 2.2 (row encoding and ownership).** Write the exterior in prefix
order, using single tokens `B`, `a`, `b` for branch and the two leaves.
A hole is `H`, its literal address letters, then `;`. Branch has arity two;
leaves and holes have arity zero, so explicit closing brackets are unnecessary
and the entire ordered bracketing is recoverable. Terminate the exterior by
`|`. Append the upper-triangular equality bits for the holes in exterior
order, then `$`. The diagonal is true and symmetry is implicit. All off-diagonal
false bits are stored. Thus the complete partition is present, without an
additional class-label array. Class ordinals can be recovered by scanning
these bits. Holes occur in lexicographic order because $P$ is prefix-free.

If $c$ is the exterior token length and $r$ its hole count, the row occupies

$$
s=c+\binom r2+2\quad\hbox{cells},\qquad O_{\rm ret}=4s\quad\hbox{bits}.
\tag{CWS.3}
$$

A private candidate region $B$ is readable by the observer and rollbackable.
Only exterior tokens and final pair-result bits are ever appended to it;
no stack, temporary node value, counter, guard or transcript is stored there.
Scans may read its already written hole fields. Before acceptance this is
charged private candidate allocation, not published output and not a free
output channel. On success its ownership changes to retained output without
copying its payload. A rejected candidate is cleared and retracted before
another attempt. A candidate formed during interference need not be a valid
partition and is never published on that basis.

**Definition 2.3 (stackless next address).** `after(x)` removes trailing `R`
letters. If nothing remains, it returns a distinguished `DONE`. Otherwise
it replaces the last `L` by `R`. The empty address and `DONE` are different.
After finishing a subtree at $x$, this is the next pending right subtree in
a left-first preorder traversal. Descending through a branch appends `L`.
These two operations use the address itself as continuation information;
they store neither ancestor records nor sibling subtrees.

**Definition 2.4 (rereading acquisition, RA).** The following is an executable
finite-string specification. `Read` is the sole source operation. `put` appends
tokens, `clear` overwrites and retracts a region, and `release` removes a local
record after clearing it. Scans and sequence operations expand to finite cell
steps under Definition 2.1. `cut_member` compares a path to successive cut
words in place, with indices and an equality flag; it never copies the cut
or materializes an absent long cut address. `hole(B,i)` scans only the exterior
prefix, counts `H` markers and copies the address of its $i$th hole. It skips
other hole addresses in place. It neither constructs a hole list nor parses
a tree into memory.

```text
after(x):
    while x ends in R: remove its last letter
    if x is empty: return DONE
    replace its last L by R
    return x

same(p,q):
    z := empty
    repeat:
        materialize p followed by z in the operand region
        a := Read(operand)
        materialize q followed by z in the operand region
        b := Read(operand)
        if a != b: release z,a,b; return false
        if a == branch: append L to z
        else if a == alpha or a == beta:
            z := after(z)
            if z == DONE: release z,a,b; return true
        else: reject the purported port history

RA(P):
    repeat:
        g := empty
        repeat:
            ell := Read(materialize(g))
            if ell == branch: append L to g
            else if ell == alpha or ell == beta: break
            else: reject the purported port history
        B := empty; x := empty; r := 0
        repeat:
            if cut_member(x,P):
                put(B,H,x,semicolon); r := r+1
                x := after(x)
            else:
                a := Read(materialize(x))
                if a == branch: put(B,B_token); append L to x
                else if a == alpha or a == beta:
                    put(B,the corresponding leaf token); x := after(x)
                else: reject the purported port history
            if x == DONE: break
        put(B,exterior_end)
        for i := 0,...,r-1:
            for j := i+1,...,r-1:
                p := hole(B,i); q := hole(B,j)
                bit := same(p,q); put(B,bit); release p,q,bit
        put(B,row_end)
        v := Read(materialize(g))
        if v == ell:
            clear/release every local region and scalar except B
            transfer the canonical readable B object; Return
        clear/release B and every local region and scalar
```

The impossible `absent` cases specify rejection of an invalid purported
history, not an additional retry on a legal source. Scalars `i,j,r` and scans
use binary registers. Loop bounds are computed from the actual candidate,
not from the source or a bound on interference. RA keeps no attempt count,
Read count, history or timestamp. A separate root-cut shortcut is available
from [CNA, Proposition 4.3][CNA], but all bounds here concern this same RA
program, including its guard search on the root cut.

## 3. Termination and exactness of the new computation

**Lemma 3.1 (presence and finite moving traversals).** On every legal RA
history, guard search, exterior traversal and `same` issue only present-address
Reads. In each exterior traversal an address is processed at most once. In
each pair comparison a relative address $z$ is processed at most once.
On a history with at most finitely many updates, each such operation finishes
after finitely many observer actions.

Proof. The root exists. A descent is made only after its parent replied
branch; the branch and both children persist. Each pending right sibling
selected by `after` has an earlier branch ancestor. Stopping at a cut hole
does not descend into it. A hole is present when emitted: it is either root
or a child reached through those branch replies. It remains present when
used in any later comparison.

For `same`, initially both bases are present. Descent at a relative $z$
requires branch replies on both sides; both parents and both pairs of
children then persist. Pending right siblings use the same invariant. Even
an update between the two replies cannot create an absent query. Unequal
replies terminate that comparison immediately. Equal leaves skip both
subtrees; they never reopen a skipped subtree if it later grows.

The `after` operation is the ordinary next-subtree operation on finite words.
Each step either enters a fresh left descendant or moves past a completed
subtree; no address is revisited within one traversal. For a pair, apply the
same argument to relative words. Let $V$ be the finite final iterate after
all the history's updates. Persistence puts every visited address inside
$\operatorname{Pos}(V)$. The guard follows distinct prefixes there; exterior
visits are distinct there; a comparison's visited words inject into each of
the two finite descendant sets of $V$. All are therefore finite. Scans of
the finite cut and candidate and all local sequence operations are finite.
Observer progress completes these actions. This reasoning uses $V$ only in
the proof and does not tell the observer when updates stop. $\square$

**Lemma 3.2 (stationary computation of the full row).** If the source is
constant throughout RA's exterior and comparison phases, the candidate is
exactly the encoding of $R_P(u)$ for that source.

Proof. Induct over its finite exterior preorder. At a cut position, presence
and prefix freeness authorize precisely the marked hole and stop descent.
Else the literal constructor is read; a branch schedules both children and
a leaf schedules none. `after` exhausts exactly this grammar, so no literal
child, blocking guard or reached hole is omitted. This is the `cutExterior`
object of [ACPD], not a point-reply vector.

For each pair of actual hidden subtrees, `same` compares constructors in
common preorder. A mismatch witnesses unequal trees. If constructors agree,
a leaf has no children and a branch schedules both children; exhaustion
therefore proves equality by structural induction. Conversely identical
finite trees cause no mismatch and exhaust together. Every unordered pair
is compared and its result appended, including disequalities. Consequently
the matrix is the exact equivalence relation, without relying on transitivity
of possibly mixed replies. The encoding recovers `literalRecord`, and [ACPD]
`canonicalRow_record_iff` supplies its equivalence with canonical row information.
Neither a hidden-subtree equality port nor an acquired full tree was used.
$\square$

**Theorem 3.3 (all-source validation safety).** For every finite nonempty
source, every finite prefix-free cut and every legal history on which RA
Returns, its readable output equals $R_P(U_v)$ at its final guard Read $v$.
No complete auxiliary tree or transcript is retained at any phase.

Proof. The saved $(g,\ell)$ is an authentic leaf observation. Acceptance
rereads exactly this whole address and obtains exactly this leaf label.
The supplied native guard theorem implies zero updates between these two
Reads. All candidate construction, both replies of every comparison, all
local scans and the validation lie in that interval. Lemma 3.2 gives the
entire literal exterior and partition of $U_v$. Ownership transfer preserves
those bytes. The list of live records in Definition 2.4 contains only paths,
scalars, constant-size replies and the row candidate. In particular no hidden
subtree value is saved. For an empty cut the candidate itself necessarily
contains the source tree, which is permitted output, not an auxiliary copy.
The safety proof does not require finite interference outside this successful
interval. $\square$

**Theorem 3.4 (unknown finite interference).** On every observer-progressing
history with a finite total of $b$ writer updates while the call is pending,
RA Returns after finitely many observer actions. At most $b$ attempts fail
validation and at most $b+1$ attempts are made.

Proof. If a pending history with finitely many updates were infinite,
Lemma 3.1 would still make every attempt finite, using its final finite
source. Each failed validation encloses at least one update between its
saved leaf and its validation: with none, the reply would agree. These
intervals belong to successive nonoverlapping attempts, so distinct failures
charge distinct updates. Thus there are at most $b$ failures, and the next
finite attempt succeeds. Clearing and Return preparation are finite as well.
Updates before a guard leaf, between attempts or after successful validation
consume budget without creating extra failures. The program receives none
of $b$, the final source, its size or its height. $\square$

## 4. One resource account for success and failure

**Definition 4.1 (proof parameters and measured traffic).** For a completed
call let $V=\rho^b u$, $N=|\operatorname{Pos}(V)|$, and
$H=\max_{p\in\operatorname{Pos}(V)}|p|$. Here $b$ includes any updates after
validation and before Return. For a pending finite-interference history use
its final iterate in the same way. All three are proof parameters, not
public promises or retained data. The actual maximum depth over *all*
submitted query operands is

$$
D_{\rm read}=\max(\{0\}\cup\{|a|:\operatorname{Read}(a)
                 \text{ is issued by RA}\}).
\tag{CWS.4}
$$

For attempt $j$, let $d_j=|g_j|$, $E_j$ be its ordered exterior Read addresses,
$r_j$ its candidate hole count, and $Z_{j,pq}$ the relative words visited by
`same(p,q)`. These are analytical traces; RA does not retain them. Then the
exact raw Read count and exact delivered-address letter count are

$$
\begin{aligned}
T_j&=d_j+2+|E_j|+2\sum_{p<q}|Z_{j,pq}|,\\
A_j&=\frac{d_j(d_j+1)}2+d_j+\sum_{a\in E_j}|a|
 +\sum_{p<q}\sum_{z\in Z_{j,pq}}(|p|+|q|+2|z|).
\end{aligned}
\tag{CWS.5}
$$

The first guard search Reads depths $0,\ldots,d_j$; validation adds one
Read of length $d_j$. Both sides of a final mismatching comparison count.
Thus $T=\sum_jT_j$, $A=\sum_jA_j$ and the actual operand peak is
$Q_{\rm peak}=D_{\rm read}$ letters, even when a first leaf is shallow.
A delimiter cell and the operand length field are additional storage, not
additional address letters. In particular an empty root operand has length
zero and still needs a port state.

**Theorem 4.2 (traffic and candidate bounds).** Write $m_* =\max(1,M-1)$ and
$F=N+K+\binom M2+2$. For successes and failures of the same RA program,

$$
\begin{aligned}
J&\le b+1,\qquad d_j\le D_{\rm read}\le H,\\
T_j&\le H+2+m_*N,\\
T&\le(b+1)(H+2+m_*N),\qquad A\le HT,\\
\text{candidate cells in attempt }j&\le F.
\end{aligned}
\tag{CWS.6}
$$

Proof. Let $O_j$ be the holes actually emitted on this attempt. They are
present in $V$ and prefix-free, whether or not the candidate is ultimately
correct. Let $n_p$ be the number of positions below $p$ in $V$.
Each comparison visits at most $\min(n_p,n_q)$ relative words, so

$$
2\sum_{p<q}|Z_{j,pq}|
 \le \sum_{p<q}(n_p+n_q)=(r_j-1)\sum_{p\in O_j}n_p
\quad(r_j\ge2).
$$

The exterior Read positions and these descendant sets are disjoint subsets
of $\operatorname{Pos}(V)$. For $r_j\ge2$ their weighted sum is at most
$\max(1,r_j-1)N$; for $r_j=0,1$ no comparisons occur and exterior Reads
are at most $N$. Add the guard and validation. All operands are present
addresses of $V$, yielding $D_{\rm read}\le H$ and $A\le HT$.
An exterior contributes at most $N$ node tokens plus at most $K$ additional
hole-address/delimiter tokens. Its upper triangle has at most $\binom M2$
bits and there are two framing tokens. This also bounds rejected candidates
that are inconsistent with every instantaneous source. $\square$

**Definition 4.3 (nonoverlapping physical accounts).** At any observer step
partition its live storage as follows. The peak of a sum need not equal the
sum of peaks.

| Region | Bill and status |
| --- | --- |
| Immutable cut and code | $4K+I_{\rm code}$ bits; no source-dependent installation. |
| Candidate/output payload | $4|B|$ bits, including its one current payload only; $B$ is private until validation, then becomes the output. |
| Operand payload | $4(|a|+1)$ bits for the complete flat query and delimiter; a dedicated mutable region, separate from paths and candidate. |
| Auxiliary paths and pending replies | Guard $g$, exterior cursor $x$, two hole bases $p,q$, comparison cursor $z$, constant-size temporary sequence copies and replies. |
| Mutable control and indices | Every sequence length, scan position, cut position, pair index, hole counter, operand head, output write head and allocation extent; finite control plus binary encodings. |
| Retained certificate/history | Zero in the row-only variant; no Read or retry archive. |

Lengths and heads are in the control account only, not charged again as
payload. A fixed number of sequence copies suffices to implement the displayed
concatenations; all are at most a constant times $H+1$ cells. In-place path
operations also give such a realization. The returned object's length and
canonical framing depend on its bytes and belong to its retained representation;
any extra machine header is charged explicitly. The mathematical encoding
uses its end token, so a separately retained length is unnecessary.

**Theorem 4.4 (workspace bound without a snapshot).** In the storage model of
Definition 2.1, RA has peak auxiliary mutable storage, excluding candidate
and dedicated operand payloads but including all their heads and control,

$$
W_{\rm aux}=O\bigl(H+1+\log_2(F+K+H+2)\bigr)
           =O\bigl(H+1+\log_2(K+2)\bigr)\quad\hbox{bits}.
\tag{CWS.7}
$$

The same bound includes all failed attempts. The dedicated operand payload
has at most $4(H+1)$ bits. Total observer-plus-port storage is at most

$$
I_{\rm code}+4K+4F+O(H+1+\log_2(K+2))
\quad\hbox{bits},
\tag{CWS.8}
$$

including the candidate. The actual retained output is $4s$ bits, not the
worst-case bound $4F$. On Return the row-only handoff has no source-dependent
auxiliary state beyond that row.

Proof. Only a constant number of path words is live, each of length at most
$H$: long absent words on the cut tape are compared in place and never copied.
The explicit comparisons materialize their whole operands; those are billed
separately. All scalar registers index the input, paths or candidate, or count
at most $M$ holes/pairs. Their values are bounded by a polynomial in
$F+K+H+2$, and a fixed number of binary registers therefore uses logarithmic
width. There is no recursion stack or per-node pointer collection. Tapes grow
by the stated single-cell operations and failed regions are cleared and
retracted, so live peaks do not accumulate with the number of attempts.

Since a binary tree of height $H$ has $N\le2^{H+1}-1$ and $M\le K$,
$\log(F+K+H+2)=O(H+1+\log(K+2))$. Adding the disjoint payload accounts
proves (CWS.8). Multiplication by the constant four converts sequence cells
to bits; registers were already in bits. No mixed cell/bit sum is used.

For row-only handoff, reset every guard, cursor, reply latch, index and
control register to a source-independent state; clear and retract all
nonoutput regions, including failure residue and operand capacity. Use a
fixed output region identity and a canonical extent depending only on its
row bytes. Do not expose earlier allocation extents, pointer identities,
freelists or elapsed-work counters. This finite cleanup is paid computation.
If a host instead preserves those fields, its handoff is richer and the
last assertion does not apply. $\square$

**Proposition 4.5 (local work and source hardware are not free).** There is a
finite bit implementation of the same RA program. One deliberately loose
bound on its local cell/bit work per attempt, including clearing, is

$$
O\left(\left[(T_j+1)(H+1)+N(K+H+1)+(M+1)^2(F+H+1)+F\right]
          [1+\log_2(F+K+H+2)]^2\right).
\tag{CWS.9}
$$

Proof. Materializing each operand, editing paths and emitting hole addresses
cost at most $O(H+1)$ operations per relevant visit. Exterior membership scans
cost $O(K+H+1)$ per processed position, including holes; there are at most
$N$ such positions. Each of at most $M^2$ pair preparations scans a finite
exterior of length at most $F$ and copies at most two length-$H$ bases.
The matrix and cleanup use at most $O(F)$ writes. Binary index updates,
comparisons and bounded arithmetic have polynomial bit cost in their
logarithmic widths; the displayed square is a sufficient elementary bound.
The sums over attempts and final cleanup give the call's local work; the
program need not maintain the sum. $\square$

At physical time $t$, total system storage is the observer account above
plus the actual source-register storage, source-port engine state and writer
workspace. Their internal layout is not specified by the atomic Read/rho
contract and is not assigned zero cost. A literal source encoding alone
occupies $\Theta(|\operatorname{Pos}(U_t)|)$ finite-alphabet cells; a different
source encoding needs its own realization argument. The complete address
payload is already counted once on the observer/source boundary. Copies made
inside a particular port implementation must be added, not hidden under
atomicity. The small-workspace theorem concerns acquisition storage, not the
entire physical machine including its source.

## 5. A constant-boundary family with small workspace and large traffic

**Definition 5.1 (family).** Let $t_h$ be the complete tree of height $h\ge0$
with alpha leaves, and put $u_h=\langle t_h,t_h\rangle$, $P=\{L,R\}$.
Its source has

$$
N_h=2^{h+2}-1,\qquad H_h=h+1,\qquad
A_h=\sum_{a\in\operatorname{Pos}(u_h)}|a|=h2^{h+2}+2.
\tag{CWS.10}
$$

These are finite geometric sums, not source advice. The exterior encoding
has seven cells, the single partition bit is equality, and two framing cells
give $s=10$. Thus its retained row occupies forty bits in the chosen alphabet.

**Theorem 5.2 (RA separation on the same all-finite program).** On a quiescent
call for $(u_h,P)$, RA uses one attempt, retains the ten-cell row, and has

$$
\begin{aligned}
T&=2^{h+2}+h+2,\\
A&=h2^{h+2}+2+\frac{(h+1)(h+4)}2,\\
Q_{\rm peak}&=h+1,\qquad
W_{\rm aux}+W_{\rm operand}=\Theta(h+1)\ \hbox{bits}.
\end{aligned}
\tag{CWS.11}
$$

The private candidate is also at most ten cells. More generally, with $b$
unknown finite writer updates, every candidate still has at most ten cells,
the accepted row is still the equality row, and the acquisition workspace is
$O(h+b+1)$ bits, with at most $b$ failures. These statements concern RA,
not a separate stationary or height-informed algorithm.

Proof. Guard depth is $h+1$. Exterior traversal reads only the root and emits
two holes. The only comparison visits each of the $2^{h+1}-1$ positions in
each hidden tree, with no mismatch. Its body therefore reads every position
of $u_h$ once. Guard search and validation add $h+3$ Reads and
$(h+1)(h+4)/2$ address letters. Apply (CWS.5) and (CWS.10).
The guard and deepest operand have $h+1$ cells; all other paths, the fixed
cut, constant candidate and logarithmic indices give the matching upper
bound. This is a lower bound for the stated RA representation only.

Under updates, the source is always a root pair of identical iterates of
$t_h$. The exterior and reached holes never change. A comparison may
temporarily report a mismatch, but its ten-cell candidate fails validation
if it crossed an update. Successful comparisons are of identical trees.
Each $\rho$ increases height by at most one, hence $H\le h+1+b$; use
Theorems 3.4 and 4.4. There is no bound $b$ in the code. $\square$

**Theorem 5.3 (traffic lower bound, allowing rereads and paid immutable
operands).** Every deterministic observer that returns exact complete rows
for all finite sources on quiescent progressing calls, with the same
source-independent code, initialization and public cut $\{L,R\}$, must,
on its quiescent run at $u_h$, query each of its $2^{h+1}$ leaf addresses.
Consequently

$$
T\ge2^{h+1},\qquad A\ge(h+1)2^{h+1},\qquad Q_{\rm peak}\ge h+1.
\tag{CWS.12}
$$

Proof. Fix any one leaf occurrence and change only its label to beta.
Exactly one of the two hidden trees changes, so the correct partition bit
changes from equality to disequality. Every other address has the same reply:
proper ancestors remain branches, other nodes are unchanged, and strict
extensions of the changed leaf are absent in both trees. Therefore only a
Read at that exact leaf address distinguishes the two sources. If the run
on $u_h$ omits it, induction over the deterministic local steps and replies
gives the same terminating run and output on the neighbor, a contradiction.
Apply this separately to every leaf of $u_h$. These are distinct addresses
of length $h+1$, giving all three bounds.

The argument allows arbitrary local recomputation, repeated Reads, arbitrary
finite immutable code/literal installation and readable output. It needs
only identical initial observer data for the two sources and absence of any
extra source port. It bounds traffic and materialized operand size, not
online writable width for arbitrary representations. A paid immutable
operand may have small mutable selection state. The immutable-tail example
in [SLD, §8][SLD] explicitly prevents inferring a universal mutable-space
lower bound merely from length. $\square$

Thus RA is optimal in Read and address-traffic order on this quiescent family:
$T=\Theta(2^h)$ and $A=\Theta((h+1)2^h)$, while its observer storage is
$\Theta(h+1)$ bits and its retained boundary is constant. Full hidden-tree
retention would require exponentially many literal cells. The all-source
upper bound still permits linear-height workspace on very unbalanced trees;
it is not a logarithmic-size bound on every tree.

**Counterexample 5.4 (guard depth is not operand peak).** Take
$w_h=\langle\alpha,t_h\rangle$, $h\ge1$, and $P=\varnothing$.
RA's guard is $L$ of depth one, but its exterior traversal submits right
subtree addresses of depth $h+1$. Consequently $d=1$ and
$Q_{\rm peak}=h+1$. Here the output legitimately is the complete literal
source; this does not authorize a second snapshot. It also shows why a
bound defined only from first-leaf depths cannot measure all query operands.

## 6. Retention, relative time and memory consumers

**Proposition 6.1 (row-only handoff).** With the explicit cleanup and access
restriction of Theorem 4.4, later observation receives only the public cut,
the row and source-independent code/control. It receives no validation guard,
comparison paths, Read count, attempt count, transcript, timestamp or
allocation residue. Finitely many authentic chronological calls on one
same-root pure-$\rho$ register therefore supply exactly the row-value inputs
of [CNA, Definitions 8.1–8.2 and Theorem 8.3][CNA].

Proof. Each accepted call gives a row at its named actual validation event.
Counting intervening genuine updates supplies semantic epoch witnesses,
not an extra input. Cleanup leaves exactly the declared row encoding and
public data. The existing overlap criterion and its necessity now apply
with their original quantifiers. Every finite chronological row family
allowed there is still attainable: choose its finite source and pause the
writer during each finite RA call, inserting the required finite bursts
between calls. Acquisition therefore excludes none of its collision inputs.
$\square$

This uses the existing row-only connected-overlap criterion; it is not a new
relative-time theorem. If a certificate, full tree, transcript, retry counter,
source-dependent pointer or guard is retained, the input changes and the
row-only necessity cannot be imported. [CNA, §8][CNA] gives the richer-tree
counterexample using [DOR] `right_clock_iterate` and its private `clock_step`:
retained trees can recover lags even when root rows are constant.

A success is certified operationally by the authentic guard observations,
but RA retains no independently replayable proof certificate. Retaining a
transcript for later checking requires separate storage and changes the
handoff. Literal output does not authenticate the register, common root,
writer law or designated origin. Fixed-cut intermediate-row recovery from
endpoint rows and authenticated lag remains exactly [CNA, Proposition 8.5][CNA]
and its native birth-provenance supplier; no such lag is silently supplied
when the row-only overlap hypotheses fail. Event placement and physical
duration are not recovered by these mathematical update counts.

## 7. Provenance, correspondence and remaining questions

**Mathematical citation 7.1 (repository correspondence).** Repository sources
are taken at revision `96eefd8005c580da62498f9fd559760f0b30b603`; CNA is the
committed supplier introduced by `49bdebade254ee007be4e4321d8a73731624f685`.

| Supplier | Exact reuse and limitation |
| --- | --- |
| [ACPD] `cutExterior`, `actualPartition`, `literalRecord`, `canonicalRow_record_iff`; private `eraseClasses_literal` | Exact exterior/partition information, including false pairs. Does not execute concurrent acquisition. |
| [NFSP] `sourceControl`, `native_source_producer`; private `traverse`, `production_reads`, `stationary` | Existing stationary full-tree and chronology supplier; its control retains subtrees. RA does not treat it as a workspace-efficient implementation. |
| [NWRS] `stationary_whole_fiber_service` | Stationary source, old row and consistent-history hypotheses remain required. No concurrent equality port follows. |
| [NDP] `original_present_transport`; [CNA, §§2–5][CNA] | Persistence, leaf validation, full-tree acquisition and finite-interference method are existing inputs. RA's cut-only candidate and streaming comparison are the different consumer. |
| [CILB] `successful_run_read_lower_bound`, private `leaf_alternative`, `separating_read` | Existing native parity leaf-perturbation argument. Its target and serial execution differ; Theorem 5.3 supplies the actual complete-row pair and quantifiers. |
| [SLD, Definitions 1.3 and 8.1, Proposition 8.4][SLD] | Charge control, receivers, heads and physical immutable letters separately. Its bounded literal installation is not advice for an unknown-height RA source. |
| [CNA, §8][CNA], [NAR, §12][NAR], [DOR] | Exact post-acquisition row-only versus richer-memory boundary, with their authentic-history assumptions. |

**Mathematical citation 7.2 (primary sources).** Herlihy and Wing,
*Linearizability: A Correctness Condition for Concurrent Objects*, ACM TOPLAS
12(3), 463–492 (1990), [original paper, §2.2][HW], DOI
[10.1145/78969.78972](https://doi.org/10.1145/78969.78972), define linearizable
histories through an equivalent legal sequential history respecting
nonoverlapping operation order. RA's validation Read gives a particular
in-call linearization point for the row. This is a safety correspondence,
not a wait-free guarantee or equality at the separate Return endpoint.

Turing, *On Computable Numbers, with an Application to the Entscheidungsproblem*,
Proceedings of the London Mathematical Society, series 2, 42, 230–265
(1936–1937), [original paper, §§1–2][TURING], describes tape symbols, finite
control and the scanned square; a complete configuration includes the
scanned-square position. This motivates explicitly charging moving heads and
mutable control. It does not supply a lower bound for this native row problem
or turn a binary address description into a physically materialized word.

These are `literature-attested` background in the stated scopes. The RA
construction, its moving-traversal proof, candidate and bit-space account,
and the same-program family/traffic comparison are `repo-derived` results.
They combine the cited native suppliers with the explicit proofs above.
No worldwide originality, exhaustive literature classification, independent
review or new kernel verification is asserted.

**Definition 7.3 (unresolved frontier).** The uniform upper construction
settles avoidability of an auxiliary full-tree snapshot and supplies the
small-boundary/small-workspace family under the original all-finite,
unknown-finite-interference contract. A sharp universal Pareto frontier among
mutable workspace, installed immutable storage, candidate/output size, Read
traffic and retained certificates remains open. In particular, the traffic
lower bound does not settle minimum mutable width in models with paid
immutable operand regions or alternative traversal encodings. The explicit
matrix is a complete partition representation, not a minimum-size partition
encoding; canonical classes could reduce its quadratic output, but need their
own same-program resource proof.

The next relational question is which additional *small retained relations*,
short of full trees, suffice to join disconnected row-overlap components and
recover their relative epochs, with an acquisition-and-retention bill under
the same native ports. This keeps the original spatial-cut, internal-time,
boundary and memory recovery objective: final boundary sufficiency and the
resources needed to acquire it are distinct. Exact certificate minimality,
authentication of source and origin, all-fair progress with infinitely many
updates, physical realization and a globally minimal relational structure
remain separate unresolved obligations. No broad-goal completion follows.

[CNA]: RECURSIVE_RELATIONAL_OBSERVATION_CONCURRENT_NATIVE_CUT_ACQUISITION.md
[NAR]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY.md
[SLD]: RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_LITERAL_DELIVERY.md
[ACPD]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.lean
[NFSP]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean
[NWRS]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowService.lean
[NDP]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[DOR]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.lean
[CILB]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/CombLiteralInstallationBounds.lean
[HW]: https://cs.brown.edu/~mph/HerlihyW90/p463-herlihy.pdf
[TURING]: https://www.cs.virginia.edu/~robins/Turing_Paper_1936.pdf

## 追加锚（本行以下为增补区）

## 8. Protected RA records and paid concurrent routing

**Definition 8.1 (designated actions and protected state).** Expand the
finite sequence operations of Definition 2.4 into the finite cell and
binary-register steps of Definition 2.1. Call these local steps, the
original Reads and the separate Return the *designated* observer actions.
A Read includes its immediate receipt into the designated response field;
subsequent decoding and copying are local steps. This convention does not
make a multi-cell computation atomic. Invocation initializes the same RA
state, independently of the source, from the public cut alone.

Write $c$ for this entire RA state. Its protected fields include the cut
and its scan position; the saved leaf address and label $(g,\ell)$; the
candidate bytes, framing, ownership and extent; the exterior cursor; both
hole bases and the relative comparison cursor; the materialized pending
operand; all pending designated replies; all sequence lengths, heads,
pair indices and temporary flags; and the instruction continuation,
including the validation, cleanup and Return stages. Protection means
preservation of the values decoded as $c$, not an extra retained copy of
these records. If the records are separately stored, their bytes are
preserved. If they share a representation with a router, the representation
must supply a fixed decoding of exactly these fields throughout routing.

A routing extension has an additional finite record $w$ at each event,
possibly of unbounded extent across different calls. It can insert paid
local service steps and paid native root Reads between designated actions.
A routing root Read has its actual reply from the same current source,
but cannot replace a designated reply or alter any decoded field of $c$.
The empty address does not identify an event as routing: RA itself makes
designated root Reads. Event designation is part of the action
specification, not a retained event log.

**Assumption 8.2 (local routing interface).** The following are local
obligations of the extension on every reachable configuration.

1. Every writer update is the original atomic $U\leftarrow\rho U$ on
   the same register. It leaves $c,w$ unchanged. Every service step
   leaves $U,c$ unchanged. A service Read consumes its actual raw reply,
   including replies changed by intervening writer updates.
2. At a ready configuration the next designated action is the action
   selected by $c$. A designated local step has exactly its RA effect.
   A designated Read submits the whole operand selected by $c$, and its
   actual reply has exactly the RA receipt effect. Return exposes exactly
   the accepted candidate. These one-action requirements apply also to
   retry, clearing, operand delivery and output preparation; a substituted
   storage interface must realize them and charge its own work.
3. Before each next designated action there is at most one routing
   episode, with a finite natural measure $\nu(c,w)$. Within that episode
   every pending service action is enabled, every one of its possible
   actual responses strictly decreases $\nu$, and writer updates leave
   $\nu$ unchanged. A nonready episode has a pending service action.
   Readiness ends the episode and enables the designated action;
   no fresh episode can postpone that same action. Entry and exit local
   work are included among these actions or among the designated steps.
4. All newly used mutable fields, response latches, operand delivery,
   selection/control state and immutable installation are included in
   the storage and service account. The decoder and measure in the proof
   do not provide an extra source observation, uncharged controller,
   retained certificate or knowledge of a final source.

There is no common bound on $\nu$, source height, candidate length or
number of attempts. The measure need not be stored. Item 3 requires
progress for every actual response and update interleaving; an
existential finite path, a source-preserving hold loop or an equation
defining a possibly infinite continuation is insufficient. Observer
progress here applies to the next pending service or designated action
in the sense of Definition 1.1.

**Lemma 8.3 (actual native history projection).** Under items 1–2 of
Assumption 8.2, delete only service events from any finite extended RA
history. Retain every writer event, including those occurring inside
routing episodes, and every designated action with its address and actual
reply. The result is a legal RA history prefix from the same invocation
source and cut. At each retained event its source and decoded RA state
agree with those in the extended history. In particular the designated
validation has the same actual response and source in both histories.

Proof. Induct on the extended prefix, starting with its identical $u,P,c$.
A service local step changes neither $U$ nor $c$. A service root Read
also changes neither, regardless of its authentic reply, so either event
can be deleted. A writer update changes both compared sources from the
same $U$ to the same $\rho U$ and preserves their RA states. It is retained,
rather than commuted past a designated event. At a designated local step
the identical decoded state selects the same transition and successor.
At a designated Read it selects the same entire address; equal sources
then give the same actual constructor or absence reply, and the receipt
rule gives the same next $c$. The same reasoning applies to Return and
its candidate bytes. These cases exhaust the events.

The original writer may place an update between any two RA actions.
Consequently the additional placements exposed by deletion are legal:
no lock or quiet interval is manufactured by the projection. Each finite
extended prefix yields a finite original prefix, even if its last events
belong to an unfinished routing episode. The induction establishes the
correspondence from local rules; it does not assume a matched complete
run or prescribe replies from a separately chosen source. $\square$

**Mathematical citation 8.4 (scope of the projection argument).** Hiding
the service events and checking one-step correspondence is standard
untimed simulation reasoning: Lynch and Vaandrager, *Forward and Backward
Simulations, Part I: Untimed Systems*, Information and Computation 121(2),
214–233 (1995), [§3.2 and Theorem 3.10][CWS-LV], give soundness of forward
simulations for trace inclusion. This is literature-attested
intermediate machinery. Lemma 8.3 checks its native obligations with
independent writer events and actual designated replies. Trace inclusion
alone neither preserves progress nor makes the extra physical Reads
disappear from the bill. The finite-service argument below supplies the
needed progress condition for this RA application. No timed, probabilistic
or adversary-policy equivalence is asserted: a projected history is a
legal history, not a claim that the same scheduling policy would generate
it after service events became invisible.

## 9. The all-finite RA application and its same-history account

**Theorem 9.1 (validation and finite-interference termination with
routing).** Extend the original all-finite RA program by an interface
satisfying Assumption 8.2. For every finite source, every finite prefix-free
cut, and every legal independent-writer interleaving on which this
extension Returns, the returned row is $R_P(U_v)$ at its actual
designated final validation Read $v$. On every observer-progressing
history with an unknown finite total of $b$ writer updates during the
pending call, it Returns after finitely many observer actions, with at
most $b$ failed validations and at most $b+1$ attempts. Neither the program
nor the router is given $b$, a height bound or a last-update indication.

Proof. On a completed history Lemma 8.3 gives an actual RA execution
with identical guard address, saved leaf label, candidate and validation
reply. Theorem 3.3 therefore applies. More explicitly, the successful
saved leaf and its equal validation reply are authentic observations on
the same source. The native leaf certificate of citation 1.3 excludes
every update between them, including updates scheduled while routing.
The candidate's exterior and comparisons thus have the stationary source
required by Lemma 3.2. Later routing cannot change the accepted bytes.

For progress, fix one pending designated action. Its routing episode
starts with some finite value of $\nu$. Each service action occurs after
finitely many intervening events by observer progress and strictly
decreases that natural number. Writer updates cannot replenish it.
Consequently the episode has finitely many service actions and ends;
the ready designated action then occurs by the same progress premise.
This argument holds without a bound on the intervening updates.

If a pending extended call with finite interference were infinite, this
argument would make its projected RA observer progressing: no pending
designated action could be postponed forever inside routing. All its
writer updates are retained, so their total remains $b$. Theorem 3.4
forces a finite successful RA execution, its cleanup and its Return,
contradicting the purported infinite pending extension. Equivalently,
the final finite source bounds the moving traversals by Lemma 3.1,
and every failed guard interval contains a distinct writer update.
The disjoint failure intervals give the same $b$ and $b+1$ bounds.
The finitely many routing episodes preceding the resulting finite set
of designated actions each terminate, including any episode after
validation and before Return. $\square$

**Mathematical citation 9.2 (endpoint scope).** The designated validation
point in Theorem 9.1 remains an in-call point, distinct from invocation
and Return. [CNA, Theorem 7.1][CNA] supplies the invocation-row and
separate Return-row obstructions for nonroot cuts in the source-blind
read-only comparison class. Its indistinguishable histories still apply
to the routed observer: place the entry update before all observer
actions, or the final update after its last Read, including all routing
Reads, but before the separate Return. The root cut retains its
constant-row exception from Definition 1.2. Finite-service progress
removes routing divergence; Theorem 9.1 makes no liveness assertion
under infinitely many writer updates.

**Proposition 9.3 (separate event costs on one actual history).** For a
completed extended RA call, let $T_0,A_0,Q_0$ be the Read count, delivered
address-letter count and operand peak of its projection in Lemma 8.3.
Let $D$ be the number of added routing root Reads, and $L_{\rm svc}$ the
number of added local service steps. Then

$$
T_{\rm ext}=T_0+D,\qquad
A_{\rm ext}=A_0,\qquad
Q_{\rm ext}=Q_0,\qquad
U_{\rm obs,ext}=U_{\rm obs,0}=0,\qquad
U_{\rm writer,ext}=U_{\rm writer,0}=b.
\tag{CWS.13}
$$

The projected designated local-step sequence is also unchanged;
$L_{\rm svc}$ is a separate additional count. With $V=\rho^b u$, its
$N,H$ and $m_*=\max(1,|P|-1)$ as in §4, this gives

$$
T_0\le(b+1)(H+2+m_*N),\qquad A_0\le HT_0.
\tag{CWS.14}
$$

These are same-history relations, not a comparison with RA under a
different writer schedule.

Proof. The extended observer events partition into the retained
designated actions and the added service actions. Every added Read
has operand $\varepsilon$, of length zero; every designated address
and reply is preserved by Lemma 8.3. RA has at least a root guard Read,
so adjoining further zero-length operands cannot increase its operand
peak. Neither observer performs an Update, and every writer update
survives deletion exactly once. Apply Theorem 4.2 to this projected
history, using its identical final source, including updates after
validation. This proves both displays. $\square$

**Definition 9.4 (additional resource coordinates).** Equation (CWS.13)
prices address letters only. Each of its $D$ root Reads still requires
instruction selection, a port invocation, a response and a control
transition. Its empty literal still requires the declared operand/port
state. Service local steps, router installation, mutable word, response
latches, selection machinery, delivery and handoff cleanup are separately
paid. In a disjoint storage realization the instantaneous storage is
the sum of the §4 account and these added regions; shared regions
require an explicit nonoverlapping allocation and decoder. Peak storage
is the maximum of this instantaneous sum. Theorem 4.4 bounds the
protected RA representation, not an arbitrary added router.

A finite value of $D$ or $\nu$ supplies no physical duration, bandwidth,
energy or zero-cost hardware claim. If a cleanup protocol itself calls
the source, its root Reads join $D$ and its nonroot Reads require their
own address bill; (CWS.13) applies as written only to root-only additions.
A retained transcript or certificate requires its own storage and changes
the row-only handoff.

## 10. Actual concurrent transfers of the complete two-bank table

**Definition 10.1 (finite-table specialization).** Fix a supplied total
$k$-bit Table from [TwoBankInstalledWord][CWS-TBI]. Its controls are
$z\subseteq\operatorname{Fin}(k)$, its instructions are fixed literal
Reads, genuine observer Updates or fixed Boolean halts, and its
successor is $\delta(z,r)$. Read flags are the four raw replies;
the sole Update flag is the acknowledgement $\star$. Halt has no
typed response. This table is fixed independently of the source.

Use its actual Word, installed, ready and physical constructions.
Write $\operatorname{ready}(d,z)$ for bank A active in phase 000 when
$d=0$, and bank B active in phase 010 when $d=1$; the inactive bank and
all five flags are zero. At each native observer event execute the
instruction of installed on the current $U$ and follow its response
row. The independent writer can apply $\rho$ between any such events.
It changes no installed word. Root Reads are genuine operations with
their actual current-source responses, not silent local instructions.

**Theorem 10.2 (response-uniform transfer despite writer updates).**
Begin in $\operatorname{ready}(d,z)$ with a nonhalting instruction.
Let $r$ be its actual typed response and put $t=\delta(z,r)$.
After its immediate flag-setting response, the actual installed
controller reaches $\operatorname{ready}(1-d,t)$ in exactly

$$
m_d(z,r)=|z|+|t|+
\begin{cases}
4,&d=0,\\
6,&d=1
\end{cases}
\tag{CWS.15}
$$

additional root Reads, under observer progress and arbitrary legal
independent-writer interleavings. Every one of these root Reads follows
the installed successor for its own actual response. They cause no
source update, but all interleaved writer updates remain in the history.
The designated original operation and its response agree with the
concurrent finite-table execution obtained by deleting these routing
Reads and retaining every writer event.

Proof. The installed ready row has exactly the original instruction.
Its actual response sets the corresponding single flag, with the old
active bank unchanged. This statement covers a Read at its actual
source and an Update followed by its constant acknowledgement; an
Update changes the source once before routing.

For $d=0$, the flagged phase-000 rows keep $z,r$ fixed and fill bank B
towards $t$. The inactive bank initially is empty. Each installed
toward step flips the least differing bit and reduces
$|B\mathbin{\triangle}t|$ by one, giving exactly $|t|$ root Reads.
One more advances to phase 001. Then $|z|$ root Reads erase bank A,
one enters phase 011, one clears the flag, and one enters phase 010.
The resulting word is $\operatorname{ready}(1,t)$.
For $d=1$ the corresponding fill and erase phases are 010, 110 and
111. After clearing the flag, three phase changes, through 101 and
100 to 000, finish the transfer. This gives $|t|+|z|+6$.

These are precisely the paths counted by typed_transfer, whose
Routing edges satisfy the stronger row equality
$\operatorname{installed}(w)=\operatorname{root}(w')$:
the installed instruction is a root Read and its successor is $w'$
for every raw response. Thus the counted path is forced, not merely
one selectable finite route. Writer updates preserve the word, the
old-bank/flag selector during filling and the target bank during
erasure. Induction along these edges therefore gives the same next
word for every actual root reply, even when consecutive root replies
differ. The remaining number of edges is a finite episode measure
unchanged by writers and decreased by every routing Read. Observer
progress completes all its edges.

There is also an explicit decoding during the transfer. In a flagged
filling phase 000 decode $\delta(A,r)$, and in phases 001 and 011
decode B. In a flagged filling phase 010 decode $\delta(B,r)$,
and in phases 110, 111, 101 and 100 decode A. In the ready phases
decode the active bank. At a fill-to-erase change the filled bank
equals the target; erasure never touches that bank. Clearing the flag
does not change this decoding. Thus every routing edge preserves the
decoded successor $t$, including the part where the old bank is being
destroyed. The decoding is a mathematical function of the installed
word, not another stored bank or retained raw response. Together with
the finite edge measure it supplies the protected-control and
all-response progress clauses of Assumption 8.2 for this table.

At the next ready row the control is exactly the original successor
$t$. Induct over transfers and writer events: deleting routing Reads
preserves the source; retaining a writer event applies the same $\rho$;
and a ready instruction reads the same source at the same retained
position or performs the same single observer Update. This proves the
claimed actual-response correspondence.

The source state's semantic exponent is the total of both kinds of
genuine updates. In particular, a writer update during routing is not
absorbed into a source-preserving observer step. The serial supplier
native_transfer counts the same observer operations in its own
Execution relation; that relation has no independent-writer event.
The response-uniform row argument above is the additional concurrent
application, rather than an invocation of that serial relation on a
history it does not represent. $\square$

**Corollary 10.3 (concurrent finite-table costs and scope).** Consider
a finite actual history segment from a ready entry to a ready exit,
consisting of $n$ completed nonhalting transfers and their interleaved
writer events. Write $z_i,r_i,d_i$ for their controls, actual typed
responses and directions. If $R_0,U_0,A_0$ count the
designated table's Reads, observer Updates and address letters, then

$$
\begin{aligned}
n&=R_0+U_0,&
D&=\sum_{i=1}^n m_{d_i}(z_i,r_i)\le(2k+6)n,\\
R_{\rm ext}&=R_0+D,&
U_{\rm obs,ext}&=U_0,&
A_{\rm ext}&=A_0,\\
R_{\rm ext}+U_{\rm obs,ext}&\le(2k+7)n,&
U_{\rm writer,ext}&=U_{\rm writer,0}.
\end{aligned}
\tag{CWS.16}
$$

The logical word has $2k+8$ bits, its zero-interleaved physical width
is $4k+15$, and the full installed set has exactly $2^{2k+8}$ words.
Each actual nonhalting observer response in these transfers changes
exactly one physical bit. All installed typed rows, including
unsupported words, hold or change one bit and preserve the no-$11$
condition. The complete installed set includes unsupported flag and
phase patterns; its hold completion supplies no termination claim
from those patterns.

Proof. Sum (CWS.15), using $|z_i|,|\delta(z_i,r_i)|\le k$.
A transfer includes one original primitive in addition to its $m_{d_i}$
root Reads. Writers are a disjoint event class and are retained.
The literal statements follow because all added operands are empty.
The flag setting, each fill or erase, and each Gray phase change flip
one logical bit. Zero interleaving carries this to one physical bit.
The width, full installed count and global hold/one-bit property are
exactly the physical, installedWords, physical_rows and
installed_halt structural conclusions of [CWS-TBI], and the count
in [SLHC, Construction 11.6, (SLHC.11.9)–(SLHC.11.11)][CWS-SLHC].
No installation cost is derived merely by counting words: the fixed
instructions, expanded literals and response-choice rows also require
their declared representation and service.

By Theorem 10.2, if the concurrent designated table terminates on
every observer-progressing history with finite total writer interference,
the installed table also terminates on every such history: deletion
preserves the update total, and finite routing preserves progress.
The same argument applies to another stated history class only if
that class is preserved by deleting service events. This is conditional
inheritance, not termination of an arbitrary total table or preservation
of a scheduling policy. The serial
installed_halt remaining-call rank assumes its fixed serial observation
and terminating run. Under a concurrent writer, equal current
$(U,w)$ can have different future update schedules; the argument here
does not assign a deterministic total remaining-call rank to them.
Only the current routing episode has the response-uniform finite
measure just proved. $\square$

**Proposition 10.4 (the finite table does not supply all-finite RA).**
A single fixed Table with the opcodes in Definition 10.1, and no
additional operand or storage service, cannot realize the designated
Reads of RA on every finite source. Theorems 10.2–10.3 discharge the
finite-table routing obligation; they do not construct an encoding of
RA's extensible records or its row output.

Proof. There are only $2^k$ table controls, hence finitely many literal
Read operands. Let $D$ be their maximum length, including zero if the
menu is empty. The installed construction adds only the root operand.
Run RA quiescently on a complete tree of height $D+1$, with any fixed
valid cut. Its unshortened guard search in Definition 2.4 Reads
$\varepsilon,L,\ldots,L^{D+1}$. The last operand belongs to neither
the original finite menu nor the added root Reads. Exact designated
action matching is therefore impossible for this table.

RA additionally has candidate growth, paths, local cell work and a
readable row, whereas the supplied table has fixed literal operations
and Boolean halts. A finite subroutine table can be used inside a
larger RA realization only with a separately supplied faithful
storage, operand, continuation and output interface satisfying
Assumption 8.2 and its full resource account. Neither a hypothetical
height bound nor a different bounded-source task is substituted into
Theorem 9.1. $\square$

## 11. Routing residue and the row-only handoff

**Definition 11.1 (accessible handoff).** Fix the public cut and the
source-independent installed code. Let $H$ be everything in the
observer that a later row consumer can access after Return, including
readable banks, direction/phase, flags, response latches, operand and
allocation metadata, pointers and service state. Row-only handoff
requires a fixed function $h$ such that

$$
H=h(P,R)
\tag{CWS.17}
$$

on every admitted returned history, with the declared row itself
readable in $H$. Access excluded from $H$ is not a free resource:
its storage remains charged while physically retained. Subsequent
native observation of the live source, if allowed, is a new acquisition
interface and is not part of this passive row-value handoff.

**Proposition 11.2 (conditions for importing the original handoff).**
After a routing extension of RA, Proposition 6.1's row-only interface
is available if the original §4 cleanup is completed and either of the
following additional conditions is satisfied: all remaining accessible
routing fields are canonically reset to functions of $P,R$ by paid
finite cleanup; or every residual field not so determined is excluded
from later access. This includes ready-bank direction and phase even
when both banks' unused parts and all flags are already zero.
Any routing during cleanup must itself satisfy Assumption 8.2 and
must not reopen access to cleared data.

Proof. Original cleanup leaves only the declared row, public cut and
source-independent control. The extra condition makes every additional
accessible field a function of those same data, or removes it from
the accessible interface. Taking their product gives (CWS.17).
Finite cleanup under observer progress completes without changing
the accepted bytes; writer updates during it remain genuine updates
after validation. Thus the validation endpoints and the row-value
inputs required in Proposition 6.1 retain their meanings.

For finitely many chronological calls, the overlap implications of
[CNA, Theorem 8.3][CNA] apply to these authentic row values. Its
attainability argument is also retained: pause the writer during each
call and its finite routing/cleanup, and insert the prescribed finite
update bursts between calls. No row-only collision family is lost.
The source itself, source-port internals and writer workspace remain
separate charged components and are not secretly handed over.

If reset is required, existence and cost of the reset operations are
an additional interface obligation. The two-bank table at a halt does
not automatically execute them. Merely projecting away a field in a
proof leaves any accessible physical value present. $\square$

**Proposition 11.3 (native equal-output separation by ready direction).**
There is a complete total three-bit table, with source-independent
entry, on which two quiescent native sources give the same fixed
Boolean output and the same root-cut row, but leave different ready
directions under the actual two-bank construction. Hence zero flags
and an erased inactive bank do not suffice for row-only handoff.

Proof. Name the eight three-bit controls
$s,l,a_\varepsilon,b_\varepsilon,a_L,b_L,h,e$, respectively, by the
codes $000,001,010,011,100,101,110,111$. Let $s$ Read the root and
send $\alpha,\beta,\mathsf{branch},\mathsf{absent}$ respectively to
$a_\varepsilon,b_\varepsilon,l,e$. Let $l$ Read $L$, sending
$\alpha,\beta$ to $a_L,b_L$ and the other Read replies to $e$.
For $p\in\{\varepsilon,L\}$, let $a_p$ and $b_p$ Read $p$:
their matching leaf reply goes to $h$ and every other Read reply
goes to $s$. Let $h$ halt with Boolean zero and $e$ halt with Boolean
one. Assign every unused acknowledgement successor and every
halt-state successor to $e$. This defines the complete total table;
those assignments do not create typed responses at halt.

Start in $\operatorname{ready}(0,s)$. On $u=\alpha$, the designated
control path is
$s\to a_\varepsilon\to h$, with exactly two Reads. On
$u'=\langle\alpha,\alpha\rangle$, it is
$s\to l\to a_L\to h$, with exactly three Reads. These are also the
guard-search and validation Read sequences of RA for the root cut
on these two stationary sources; the intervening root-hole candidate
is constant. No encoding of arbitrary RA configurations is assumed.

Theorem 10.2 forces one ready-direction toggle per designated
nonhalt instruction, independently of all routing replies. The
terminal words are therefore respectively
$\operatorname{ready}(0,h)$ and $\operatorname{ready}(1,h)$.
Their phase bits are 000 and 010, so they are distinct even though
the halt control code is the same, all flag bits are zero and both
inactive banks are empty. Zero interleaving preserves this difference.
Both original instructions at the terminal words halt with Boolean
zero. Moreover $R_{\{\varepsilon\}}(u)=
R_{\{\varepsilon\}}(u')$ by Definition 1.2. If the declared output
is this row, supply a paid output service that, on these histories,
emits the four fixed cells H, semicolon, exterior-end and row-end
of Definition 2.2 while leaving the ready word accessible. Its row
payload occupies sixteen bits; the four cell writes and its output
control are additional costs. It needs no source query.

A later observer of the phase distinguishes these executions, while
their declared output and public cut do not. Thus no function in
(CWS.17) can include that phase for both histories. This is a
specified native finite-table witness, not an assertion about the
parity of an unspecified finite encoding of all-finite RA. $\square$

## 12. Mathematical correspondence and remaining interface obligations

**Mathematical citation 12.1 (suppliers and application boundaries).**
The finite-stuttering proof method in citation 8.4 is
literature-attested; it is used as an intermediate argument, not
as a new standalone general simulation theorem. [SLD, Proposition 4.5][SLD]
already represents a macro successor by the old node and a typed flag,
then carries out a paid local continuation. Its literal-delivery
setting does not introduce the independent writer of Definition 1.1.
[SLHC, Construction 11.6][CWS-SLHC] and [CWS-TBI] supply the exact
two-bank rows, typed transfer paths, physical encoding and serial
native counts. [SLHC, §13][CWS-SLHC] uses that construction for a
particular bounded-update parity table; its Theorem 13.3's separation
windows and address lower bounds retain that task's parameters.
[FIB IV, §§51–52][CWS-FIB-IV] instead assumes a complete finite
controller and selection/response services preserving its original
call trace; those services do not supply the paid root-Read chronology
or RA's unbounded operand interface.

The repo-derived application here is the combination with this
volume's protected leaf guard, cut-only candidate and all-finite
moving traversals: every concurrent writer event survives, designated
responses match, finite routing cannot obstruct finite-interference
RA termination, and the native address/event and retention statements
follow on that same history. The finite-table case obtains its
universal local routing progress from the actual installed rows;
it does not assume a complete concurrent simulation. Proposition 11.3
supplies a native equal-row pair with explicitly calculated retained
routing state. These scopes make no worldwide originality claim.

**Definition 12.2 (unresolved realization boundary).** An all-finite
physical realization still requires a faithful extensible
storage/operand/output interface, finite response-uniform routing
service with its installation and work bills, and either paid
canonical cleanup or the stated access exclusion. A complete finite
table supplies its own routing lemma but none of those unbounded
interfaces. Authentication, separately retained certificates, physical
duration, all-infinite-interference liveness and a universal optimal
resource frontier retain their independent obligations. The
validation-Read endpoint and same-history counts do not settle them.

[CWS-TBI]: ../../../D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.lean
[CWS-SLHC]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT_CONTINUATION.md
[CWS-FIB-IV]: FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_IV.md
[CWS-LV]: https://groups.csail.mit.edu/tds/papers/Lynch/IC95.pdf

## 追加锚（本行以下为增补区）
