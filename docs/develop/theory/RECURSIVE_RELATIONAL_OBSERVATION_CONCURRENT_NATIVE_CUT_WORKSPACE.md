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
