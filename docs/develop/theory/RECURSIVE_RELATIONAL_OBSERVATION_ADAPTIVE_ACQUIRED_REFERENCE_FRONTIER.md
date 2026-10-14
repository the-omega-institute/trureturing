# Adaptive acquired references and the retention frontier

## 1. Native histories, acquired data and the research boundary

This volume is ordinary mathematical theory, not Lean certification. Its
claims are `repo-derived` unless a literature or repository supplier is
explicitly identified. Source reading supplies correspondence, not a new
kernel check. The broad question is how a small relational description
can support spatial cuts, internal time, boundaries and memory, and under
what conditions these descriptions recover one another. The result here
concerns an acquired spatial anchor and the cost of losing it. It does
not settle the general mutual-recovery question.

The locator convention is `generic-v1`. After integration, existing
bytes are preserved; extensions and corrections belong after the final
append anchor. This reference source does not carry machine status.

**Definition 1.1 (source and events).** Let $\mathcal T$ be all finite
nonempty ordered full trees on leaves $\alpha,\beta$. The writer's only
operation on its one register is the homomorphic substitution

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
\tag{AAR.1}
$$

An atomic $\operatorname{Read}(p)$ takes the entire materialized literal
$p\in\{L,R\}^*$ and returns alpha, beta, branch or absent. The empty
literal addresses the root. A strict continuation past a leaf is absent.
The writer can update between arbitrary observer events, including
individual local computation steps, operand construction and Return.
There is no reset, source replacement, rerooting, free navigation,
subtree-equality port, snapshot, clock, source-size input or observation
of the scheduler. There is no protected entry.

One deterministic finite program starts source-blind and uses only
declared public input, its actually acquired replies and its own paid
state. Its storage may grow finitely on each finite execution; finite
program does not mean a fixed finite configuration space. Safety means
correctness on every legal history on which it returns. Liveness means
termination whenever the pending call has finitely many writer updates
in total, with no known bound, and every pending observer operation
eventually executes. A returned record refers to its specified actual
validation Read, not the later Return event.

**Definition 1.2 (complete rows).** For any finite public prefix-free
cut $P$, including the empty and root cuts, set
$O=P\cap\operatorname{Pos}(u)$. The complete row is

$$
R_P(u)=(C_P(u),\pi_P(u)),\qquad
p\sim_{\pi_P(u)}q\ \Longleftrightarrow\ u|_p=u|_q\quad(p,q\in O).
\tag{AAR.2}
$$

The exterior is the literal ordered tree with the subtrees at $O$
replaced by holes carrying their entire addresses. It retains concrete
blocking leaves for unreached cut words. The partition includes every
equality and disequality of reached holes. This is the supplied
`literalRecord` and `canonicalRow_record_iff` of [ACPD]. In particular a
root cut has one hole and its singleton partition, independently of the
source. A vector of selected constructor replies is not a complete row.

**Definition 1.3 (validation and accessible interfaces).** A capture at
$v$ is an actual observation on the same root/register that supplies
its claimed data. Between two designated captures $v\le w$ the genuine
history premise is $U_w=\rho^k U_v$, where $k$ is the number of actual
updates between those events. The premise supplies neither $k$ nor an
identified original tree. A passive decoder receives exactly the
ordered data declared in its theorem and has no fresh hidden-source
access. A later acquisition service, when present, is a different paid
phase, whose actual native queries are specified.

Every source-bearing distinction accessible across a handoff belongs
to its retained state: descriptors, scalars, rows, calibration, prior
outputs, reply latches, control, query or retry histories, pointers,
region identities, capacities, allocation metadata and readable length
fields. A strict scalar-only interface requires all other accessible
state to be a fixed function of the scalar and declared public inputs.
Merely erasing an address variable does not establish that interface.
Positive constructions use fixed output-region identities, canonical
extents determined by the output bytes, and paid clearing and retraction
of all other regions and controls. If a host retains other accessible
information, the scalar-only lower bound is not being applied to it.
Physically retained but inaccessible storage is still a storage cost.

Clock agreement does not authenticate a history. No theorem below
recovers physical duration, the placement of unobserved events or an
external origin before the first validation.

**Definition 1.4 (separate resources).** For actual submitted words
$p_1,\ldots,p_T$, count

$$
T,\qquad A=\sum_{i=1}^T|p_i|,\qquad
Q=\max(\{0\}\cup\{|p_i|:1\le i\le T\})
\tag{AAR.3}
$$

as query count, total literal letters and maximum operand length.
Separately count writable auxiliary state, the complete operand buffer,
candidate/output payload, immutable code and installed literals, local
bit/cell work, and the entire inter-call retained interface. An installed
word still costs its bytes and every submission of its full literal.
A binary integer costs its bit length, not one unbounded cell. Source
storage and writer/port implementation costs are additional coordinates.
The port does not conceal a free observer buffer.

For row costs use [CWS]'s explicit finite-sequence implementation: each
cell in its sixteen-symbol alphabet costs four bits; a row of $c$
exterior cells and $r$ holes has $s=c+\binom r2+2$ cells, including
framing and the complete upper-triangular partition. An accepted private
candidate becomes output by ownership transfer. No second payload copy
is required.

## 2. Suppliers and the local relation that is already sufficient

**Mathematical citation 2.1 (exact reuse).** [CNA, Theorem 2.2] supplies
the following facts under Definition 1.1: a present address persists;
a branch persists; its subtree undergoes exactly the global iterates;
and equal leaf replies at one address enclose no update. A leaf alpha
becomes beta and then branch; a leaf beta becomes branch immediately.
Neither label can return at the same address after an update.
[NDP]'s `original_present_transport` is the formal present-subtree
supplier. The off-flipped-leaf conjunct of [READ]'s `source_foundation`
states that changing one leaf label changes no other native reply,
including replies at strict extensions of that leaf.

[CWS, Definition 2.4 and Theorems 3.3–4.4] supplies the row body: a
stackless literal exterior traversal, then complete pairwise hidden
subtree comparison by actual rereads, and validation by a saved leaf.
Moving failed bodies are finite under finite interference. The body
does not require its guard to be leftmost; left descent in RA is one
way to obtain a leaf before that body. Its proof uses leaf equality
to validate the entire intervening body.

[CAB, §§2–5] already supplies fixed left/right clock acquisition,
finite-interference right-search repair, complete-row calibration and
complementary-cut recovery. [IDC, §6] supplies stationary right-ray
search and its contract limits. These are available results, not
missing bridges here. [NAR, §§10–12] supplies agreed references,
absence-safe advancing coordinates and exact integration of acquired
overlap relations. [NLC, Lemma 3.1] supplies minimum leaf depth in an
atomic iterate. Their recurrences, subtraction and generic integration
are used as ingredients, not claimed as independent new content.

**Definition 2.2 (weights and atomic descendants).** Write
$e(\alpha)=0$, $e(\beta)=1$,
$s(p)=\#_L(p)+2\#_R(p)$ and $T_n=\rho^n\alpha$.
The supplied right clock is

$$
c(\alpha)=0,\quad c(\beta)=1,\quad
c(\langle x,y\rangle)=2+c(y),\quad
c(\rho^k u)=c(u)+k.
\tag{AAR.4}
$$

For finite $q$, let $a(u,q)$ be its longest reached prefix and use
the [NAR, Definition 11.2] variant

$$
J^c_q(u)=s(a(u,q))+c(u|_{a(u,q)}),\qquad
J^c_q(\rho^k u)=J^c_q(u)+k.
\tag{AAR.5}
$$

This is not the intrinsic inverse-depth coordinate $J^\nu$. The
longest-prefix rule handles absent addresses using a concrete blocking
leaf. On a reached leaf $a$ of label $e$, $J^c_a(u)=s(a)+e$.

**Proposition 2.3 (historical leaf-cylinder calibration).** Suppose an
actual Read at $v$ acquires leaf $(a,e)$ and a later actual Read at $w$
acquires leaf $(b,f)$ with $b=ar$. On any authentic history of
Definition 1.3,

$$
k=s(r)+f-e=s(b)-s(a)+f-e.
\tag{AAR.6}
$$

This allows any acquired descendant leaf, including a ray different
from $aR^\infty$. It does not require simultaneous observation of two
references, a global boundary profile or the future descriptor $b$
to have been known at $v$.

Proof. Present-subtree transport gives $U_w|_a=T_{k+e}$. Every terminal
word $r$ of $T_n$ satisfies $s(r)+e(T_n|_r)=n$. This follows directly
from (AAR.5) applied to a ray through that terminal: at alpha every
finite reference has coordinate zero, so after $n$ updates it has
coordinate $n$. Equivalently the two children of an expanded beta
have equal weighted leaf score. Substitute $n=k+e$. At $v$ every
finite extension of $a$ had the same absence-safe coordinate $s(a)+e$;
the old leaf is the actually acquired common calibration for its
whole cylinder. No value elsewhere in the tree enters the argument.
$\square$

**Construction 2.4 (cheap continued use).** Keep the acquired literal
$a$ and bit $e$. At a later call, submit $a,aR,aR^2,\ldots$ until an
actual leaf is returned; extend only after a branch reply. Designate
that leaf Read as $w$. Present-subtree and branch persistence exclude
absence. Under finite interference the final finite subtree at $a$
has finite right depth, so the search terminates. On every return
(AAR.6) gives the exact lag, regardless of updates during earlier
search or later local work.

To attach a complete row for any cut $P$, retain this newly observed
leaf as guard, execute exactly the CWS row body, and reread that same
literal. Accept only the same leaf label. Otherwise discard the row
candidate and restart the search from the still retained old anchor
$a$. The final guard Read is the joint validation. Its equality makes
the body stationary and preserves the new leaf value throughout the
body; (AAR.6) applies at that final Read. This is a fresh proof of the
modified entry/guard composition using the CWS body contract, not an
application of CWS's routing theorem to a changed protected state.

**Definition 2.5 (continued decoder inputs and rebasing).** The passive
decoder receives the literal old record $(a,e)$, literal new record
$(b,f)$, their order, the genuine history promise, and any explicitly
requested complete rows and public cuts. It computes (AAR.6), with
no source access. Additional retained outputs and controls must be
charged under Definition 1.3, whether or not this formula uses them.
Keeping $(a,e)$ supports later references anywhere inside that old
cylinder. Replacing it by $(b,f)$ narrows the supported cylinder to
$[b]$; retaining also the acquired accumulated count $K$ gives the
next absolute-from-first count

$$
K+s(c)-s(b)+g-f\qquad(c\succeq b).
\tag{AAR.7}
$$

Discarding $K$ changes the retained origin to the capture at $b$.
This baseline has no global-minimum certification requirement. It
can start with any leaf already paid for by CNA, CWS or CAB.

## 3. Which acquired anchors stay shortest?

**Definition 3.1 (phase-sensitive terminal score).** For $u\in\mathcal T$
let $F(u)$ be its finite leaf-address set and put

$$
\mu(u)=\min_{p\in F(u)}|p|,\qquad
m(u)=\min_{p\in F(u)}\bigl(2|p|+e(u|_p)\bigr).
\tag{AAR.8}
$$

The associated recurrence is $m(\alpha)=0$, $m(\beta)=1$ and
$m(\langle x,y\rangle)=2+\min(m(x),m(y))$.
A certified minimizing anchor is an actually acquired leaf $(a,e)$
with $2|a|+e=m(U_v)$ at its designated validation. Certification means
the program's all-source correctness property, not a free certificate
port or an independently authenticating output string.

**Lemma 3.2 (consumed phase and orbit identities).** For every finite
$u$ and $k\ge0$,

$$
m(\rho^k u)=m(u)+k,\qquad
\mu(\rho^k u)=\left\lfloor\frac{m(u)+k}{2}\right\rfloor.
\tag{AAR.9}
$$

For a leaf $(a,e)$ of $u$, the shortest leaf inside its future
descendant cylinder has absolute length

$$
|a|+\left\lfloor\frac{k+e}{2}\right\rfloor
=\left\lfloor\frac{2|a|+e+k}{2}\right\rfloor.
\tag{AAR.10}
$$

Proof. Structural induction in the displayed recurrence gives a
one-step increment: alpha changes from zero to one; beta from one
to $2+\min(1,0)=2$; pairing commutes with the same increment of
both children. Iteration gives the first formula. Taking the floor
of each leaf score divided by two gives its depth, and finite minima
commute with that monotone floor. Transport gives the subtree $T_{k+e}$
at $a$; apply the supplied [NLC] formula
$\mu(T_n)=\lfloor n/2\rfloor$. These elementary identities serve the
selection and retention theorems below. $\square$

**Proposition 3.3 (exact permanent shortest-cylinder criterion).** For
every finite $u$ and actual leaf $(a,e)$, the following are equivalent:

1. $2|a|+e=m(u)$.
2. At every $k\ge0$ the descendants of $a$ include a globally shortest
   leaf of $\rho^k u$.
3. That shortest-depth equality holds at both $k=0$ and $k=1$.

Proof. Set $x=2|a|+e$ and $y=m(u)$, so $x\ge y$. By (AAR.9)–(AAR.10)
the equality at $k$ is $\lfloor(x+k)/2\rfloor=\lfloor(y+k)/2\rfloor$.
Equality of $x,y$ implies all of them. Conversely
$\lfloor z/2\rfloor+\lfloor(z+1)/2\rfloor=z$ for every natural $z$;
the two equalities in item 3 therefore imply $x=y$. $\square$

**Counterexample 3.4 (shortest now is insufficient).** In
$u=\langle\beta,\alpha\rangle$ both leaves have length one. Choosing
$L$ is initially shortest. After one update its shortest descendant
has length two, while $R$ remains a leaf of length one. The minimizing
phase chooses $R$. For any initially shortest leaf, its score is at
most $m(u)+1$, so its future shortest descendant is at most one letter
longer than the global minimum. This additive-one statement does not
give the exact permanent property.

**Definition 3.5 (a distinct boundary objective).** The weighted minimum
$M(u)=\min_{p\in F(u)}(s(p)+e(u|_p))$ differs from $m(u)$.
In $u=\langle\langle\alpha,\beta\rangle,\beta\rangle$, the unique
weighted minimizer is $LL$ with score two, but the shortest leaf is
$R$, with phase-sensitive score three. Thus minimizing the canonical
boundary-density coordinate and minimizing literal terminal length are
different objectives. No second minimum-acquisition algorithm is needed
for the present continuation theorem.

## 4. Concurrent acquisition of the shortest anchor

**Construction 4.1 (monotone level scan).** Start at $h=0$. Generate
all words of length $h$ in lexicographic order, $L$ before $R$, one
materialized word at a time. Keep no whole level or query transcript.
For each reply do the following:

- Alpha: accept that word with label zero at this Read.
- Beta: replace the saved beta address by this address.
- Branch: continue.

If the level finishes without alpha and no beta was seen, increase
$h$ by one. If some beta was seen, reread the **chronologically latest**
saved beta address. On beta accept it with label one at this reread.
On branch increase $h$ by one. Clear the saved address at each new
level. Alpha or absent at this beta reread, or absent in a level scan,
is an invalid purported port history; it cannot arise under (AAR.1).
All increases, enumeration, saving and acceptance use finite paid local
steps. The program receives no bound on $h$ or on the updates.

**Theorem 4.2 (all-source concurrent minimum certification).** For every
finite source, Construction 4.1 safely returns a genuine minimizing
anchor $(a,e)$ at its designated Read $v$:

$$
2|a|+e=m(U_v).
\tag{AAR.11}
$$

It terminates under unknown finite total interference and observer
progress. The number of failed beta rereads is at most the number
of actual updates during the call. No quiet interval for the entire
scan is assumed.

Proof. At the start of level $h$ every shorter address is currently
branch. This is vacuous at zero. These branch facts persist, so every
length-$h$ word is present throughout the level. An alpha reply is
a leaf of score $2h$, and no smaller score is possible because all
shorter words remain branch. Acceptance there is correct.

If there was no alpha, each tested word was branch or beta. Thereafter
it cannot become alpha. When no beta occurred, all words of this
level are branch, justifying the next level. Otherwise let $g$ be
the latest beta observation. If its reread is beta, no word at this
level is alpha and $g$ is still beta. All shorter words are branch;
the minimum is exactly $2h+1$.

If the reread is branch, at least one update followed the latest beta
observation. That update followed every earlier beta observation in
this level too. It made all those positions branch; they and all
already observed branches persist. Hence every word of length $h$
is now branch, justifying advancement. This also proves that the
impossible replies named in Construction 4.1 never occur. The
validation claims concern the actual accepting Read; subsequent local
computation and writer updates do not change its recorded value.

For finite interference let $V$ be the final source and $D=\mu(V)$.
All branch facts used by the scan hold in $V$. It cannot advance
from level $D$ because $V$ has a leaf there. There are only finitely
many generated words at each of the at most $D+1$ visited levels.
Observer progress completes all those Reads and their finite local
work, and it must accept. Each failed beta reread encloses an update
between the latest beta and its reread. These intervals are disjoint
in chronological order; one update cannot be charged twice.
$\square$

**Counterexample 4.3 (an earlier beta is not a substitute).** Begin with
$\langle\beta,\alpha\rangle$. Read root branch, then $L$ beta. Perform
one global update. Read $R$ beta in
$\langle\langle\beta,\alpha\rangle,\beta\rangle$. Rereading the
earlier $L$ gives branch although $R$ is still a leaf. An invalid
advance to level two can accept $LR$ alpha, of score four, when the
true minimum is three. Rereading the latest beta $R$ instead accepts
the correct score. This is a legal one-register history.

**Theorem 4.4 (complete-row consumer).** Replace the guard search in
Construction 2.4's row variant by Construction 4.1. After its
successful anchor Read, keep the chosen guard fields unchanged, run the
unchanged CWS body, and reread that guard. On equality return

$$
\bigl(R_P(U_v),a,e,z\bigr),\qquad z=2|a|+e=m(U_v)
\tag{AAR.12}
$$

at the final guard validation $v$. On disagreement discard the entire
candidate and restart the level scan at zero. Optional output modes
retain only the scalar and row, or only the anchor and row; the mode
is a declared public input. For every finite source and every finite
prefix-free $P$ this is safe and has finite-interference liveness.

Proof. Theorem 4.2 gives a minimum certificate at the first guard
Read. Equal leaf validation excludes every update from that Read
through the row body and final validation. Thus both the minimum
and complete row hold at $v$. The CWS traversal and comparisons
preserve reached holes, concrete blocking leaves and every partition
bit under this stationary interval. They are finite even in failed
attempts under finite interference. A failed final validation
encloses an update; its interval starts after every failed-beta
interval in that scan and ends before the next attempt starts.
All such intervals are disjoint, so there are at most $b$ outer
failures when $b$ updates occur. After the last update a finite
attempt succeeds. Cleanup and Return are finite paid operations;
they do not relocate the validation. $\square$

No CWS §§8–12 routing extension is invoked to change its protected
decoded guard or control. If additional routing is introduced, it
must preserve this new algorithm's actual state and separately
satisfy that supplier's operation and cleanup obligations. The
protected-entry scheduling variant in CNA is not used.

## 5. Every attempt, descriptor and retained bit is charged

**Proposition 5.1 (scan resource bounds).** For one completed scan let
$b$ include updates through Return, $V=\rho^b u$, and $D=\mu(V)$.
These are analysis parameters, not inputs. Put

$$
B_D=2^{D+1}+D.
\tag{AAR.13}
$$

The scan satisfies

$$
T\le B_D,\qquad Q\le D,\qquad A\le DB_D.
\tag{AAR.14}
$$

More precisely, if $E_h$ is the actually scanned initial segment
of the length-$h$ lexicographic level and $I$ is the set of levels
at which a beta reread was made, then

$$
T=\sum_h|E_h|+|I|,\qquad
A=\sum_h h|E_h|+\sum_{h\in I}h.
\tag{AAR.15}
$$

All failed beta rereads occur in these sums. Auxiliary writable
state is $O(D+1)$ bits, excluding a separate $4(D+1)$-bit operand
region and the returned payload. The common code has constant size
independent of the source. A literal anchor uses $D_v$ letters, its
one label bit and self-delimiting length/framing, where $D_v=|a|$;
the scalar alone uses $O(\log(m(U_v)+2))$ bits with framing.

Proof. Each level is scanned at most once and reread at most once,
and no visited level exceeds $D$. Hence
$\sum_{h=0}^D2^h+(D+1)=B_D$. Each operand has length at most $D$.
Keep the current $h$-bit word, a saved beta word, binary length/head
registers, one reply and finite control. Lexicographic increment
uses the current word itself; it installs no exponential word table.
The output scalar is computed from a paid length and label. All
copies, operand construction and clearing can be implemented with
$O((T+1)(D+1)[1+\log(D+2)]^2)$ local bit/cell operations, a loose
bound which also charges arithmetic and framing. $\square$

**Proposition 5.2 (joint row and minimum costs).** In Theorem 4.4 let
$N=|\operatorname{Pos}(V)|$, $H=\operatorname{height}(V)$,
$M_P=|P|$,

$$
K_P=1+\sum_{p\in P}(|p|+1),\quad
q_P=\max(1,M_P-1),\quad
F=N+K_P+\binom{M_P}{2}+2.
\tag{AAR.16}
$$

There are at most $b+1$ outer attempts, and the entire call obeys

$$
\begin{aligned}
T&\le(b+1)(B_D+q_PN+1),\\
A&\le(b+1)(DB_D+Hq_PN+D),\qquad Q\le H.
\end{aligned}
\tag{AAR.17}
$$

For the exact account let $S_j$ be each scan's actual word list,
$W_j$ its CWS body's actual word list, and $g_j$ its final guard.
Including all failures,

$$
\begin{aligned}
T&=\sum_j(|S_j|+|W_j|+1),\\
A&=\sum_j\left(\sum_{p\in S_j}|p|+\sum_{p\in W_j}|p|+|g_j|\right).
\end{aligned}
\tag{AAR.18}
$$

The operand maximum is the maximum over those same literal lists.
The candidate row has at most $4F$ bits; an anchor candidate has
$O(D+1)$ bits and a scalar candidate $O(\log(D+2))$ bits. The
dedicated operand payload has at most $4(H+1)$ bits. Auxiliary
writable state is $O(H+1+\log(K_P+2))$ bits, excluding those payloads
but including all heads, control and allocation extents. Immutable
installation is $I_{\rm code}+4K_P+O(1)$ bits. Final retained row
storage is its actual $4s$ bits, plus the chosen supplement and
framing, not the worst-case $4F$.

Proof. Every scan in any attempt is bounded by the same final $D$.
The CWS body uses at most $q_PN$ Reads at present addresses of $V$,
each of length at most $H$; its candidate bound is $F$. Add the
separate final validation, of length at most $D$, and sum all outer
attempts. Scan failures are already in $B_D$; the outer failure
count is not a second uncharged retry allowance. Workspace follows
by retaining a constant number of paths and binary indices and
clearing failed candidates before retry. Apply [CWS, Proposition
4.5]'s local-work bound to each body and add Proposition 5.1's scan
work and finite output cleanup. This counts local work without
identifying it with query count or assuming unit-cost integers.
$\square$

**Proposition 5.3 (retained-anchor continuation costs).** For
Construction 2.4 without a row, let $v_0$ be the old anchor capture,
let $K_f$ count all updates from $v_0$ through this call's Return,
and put $r_f=\lfloor(K_f+e)/2\rfloor$. The entire moving search obeys

$$
T\le r_f+1,\quad
Q\le |a|+r_f,\quad
A\le(r_f+1)|a|+\frac{r_f(r_f+1)}2.
\tag{AAR.19}
$$

On a quiescent later call with lag $k$, these are equalities with
$r_f$ replaced by $r=\lfloor(k+e)/2\rfloor$. With a row body and
$b$ updates during the call, there are at most $b+1$ attempts; on
each attempt add $q_PN+1$ Reads and at most $Hq_PN+|a|+r_f$ letters
to (AAR.19), with $N,H$ from the final tree. The last summand charges
the extra guard validation. The row can require operands longer
than the shortest clock operand.

Proof. Every branch encountered on the right suffix persists in
the final subtree $T_{K_f+e}$. Its rightmost leaf depth equals
$\lfloor(K_f+e)/2\rfloor$ by (AAR.4) and the supplied right-reply
intervals. Consecutive suffix lengths are $0,1,\ldots,r$ on a
stationary call; sum their lengths after the literal prefix $a$.
For the row variant use the disjoint failed validation intervals
from Construction 2.4. Workspace consists of the retained prefix,
current suffix/path, binary counters and a separate materialized
operand, in addition to the CWS body and row candidate when present.
An optional output of only the scalar lag still pays those transient
regions and the retained old anchor. $\square$

## 6. Exact continuation interfaces and the native operand frontier

**Theorem 6.1 (certified anchors attain the continuation operand minimum).**
Fix any authentic first capture $v_0$, source $t=U_{v_0}$ and
retained state produced before any future lag is known. A later
deterministic acquisition service must recover the exact lag for
every finite burst of updates before its invocation. It has no new
source-bearing input other than its own native Reads. Arbitrary
earlier information about $t$, arbitrary finite source-independent
code and installed literals, arbitrary adaptive finite address
queries and local computation are allowed and charged.

The later designated capture must occur inside that later call.
On a quiescent later call at $u=\rho^k t$, every such correct
terminating service must have

$$
Q\ge\mu(u).
\tag{AAR.20}
$$

If its earlier retained record is a certified minimizing leaf
$(a,e)$ of $t$, Construction 2.4 without a row attains equality on
every such $k$, using its genuine acquired relation (AAR.6).
Its safety and finite-interference liveness do not require the
later call to be quiescent; quiescence specifies the comparison
on which this exact cost optimum is asserted.

Proof. If every operand on the call at $u$ had length less than
$\mu(u)$, every reply would be branch. Consider the identical
first capture and retained state, with one additional actual
update before the later invocation, giving $\rho u$. Branch
persistence makes every one of those replies branch there too.
Deterministic transcript induction makes all local state, selected
words, outputs, chosen validation event and termination coincide.
The later writer is paused in both histories, so the required lags
are $k$ and $k+1$, a contradiction. The extra update occurs on the
same register after the common prefix; there is no changed original
source or free new row in this proof. The bound includes arbitrarily
rich retained knowledge of that prefix. If $\mu(u)=0$ the length
bound is zero; absence of any Read would still give the same
contradiction for exact lag recovery.

For attainment, Proposition 5.3 gives
$Q=|a|+\lfloor(k+e)/2\rfloor$. The certified condition and
Proposition 3.3 identify this with $\mu(\rho^k t)$. The program
actually acquires its terminal literal and bit, and (AAR.6)
recovers $k$. $\square$

This is a one-coordinate optimum for later acquisition, after the
earlier certification and retention have been paid. It is not an
optimum for total lifetime queries, all-attempt work, complete rows,
immutable installation or mutable space. If a current row or clock
is supplied for free to the later service, the no-new-source-input
hypothesis is false. A long mandatory operand alone is not a
universal mutable-space lower bound.

**Proposition 6.2 (scalar continuation with genuine reference changes).**
At each capture independently run Construction 4.1 or Theorem 4.4
and export the certified scalar $z_i=m(U_{v_i})$. Under authentic
same-root pure continuation, the passive decoder with precisely
these scalars, their order, and any declared complete rows returns,
for $i\le j$,

$$
k_{ij}=z_j-z_i.
\tag{AAR.21}
$$

The selected minimizing leaves may lie in different incomparable
cylinders. If the acquired descriptors are retained as well, the
same identity reads

$$
k_{ij}=J^c_{a_j}(U_{v_j})-J^c_{a_i}(U_{v_i})
       +\#_L(a_j)-\#_L(a_i).
\tag{AAR.22}
$$

Proof. Use (AAR.9) on the genuine history. At a certified leaf,
$2|a|+e=J^c_a+\#_L(a)$. Substitution gives the second formula.
The crucial premise is actual global minimum certification at
both captures; the correction from address letters does not make
an arbitrary chosen short leaf a common normalization. All search
and failed-attempt costs remain those of §5. $\square$

**Proposition 6.3 (external-cylinder calibration).** For arbitrary finite
references $p,q$, a genuinely acquired common-version offset
$\Delta=J^c_q(U_x)-J^c_p(U_x)$ together with the acquired old and new
readings, all on the same authentic pure history, suffices for

$$
k=J^c_q(U_w)-J^c_p(U_v)-\Delta.
\tag{AAR.23}
$$

The coordinate law makes $\Delta$ invariant on the pure orbit.
This is the supplied calibration/integration mechanism, not a new
acquisition theorem. If $q$ is chosen causally, its descriptor must
first be computed from paid data. Evaluating both references under
one saved equal-leaf guard, with restart on failure, is a legal
fallback: finite native traversals acquire the reached subtree or
blocking leaf needed by (AAR.5), followed by local evaluation.
All traversals, descriptor construction, calibration storage, row
work and failed attempts are charged. Whole-tree evaluation is an
available supplier fallback, not the new result of this volume.
No future menu is assumed; CAB's public-menu theorem applies only
when that menu is explicitly present.

For an explicit all-attempt account of this fallback, include the
selection phase's actual query list, then for every attempt its
guard-search list, both reference-evaluation lists, optional row-body
list and final validation literal. The length and sum of literal
lengths of their concatenation are exactly $T,A$; their maximum
length is $Q$. All failed lists count. Two fixed-descriptor evaluations
can use successive present prefixes toward each descriptor followed
by right descent, stopping early at a blocking leaf. For a final tree
of height $H$, each evaluation uses at most $H+1$ Reads, each of
length at most $H$: every visited branch persists and each path grows
by one letter. With a supplied left guard search and no row, one
attempt thus uses at most $3H+4$ Reads. Matching the final leaf makes
both values common-version; failed guard intervals are disjoint, so
after selection at most $b+1$ attempts are needed for $b$ further
updates. Selection's own traffic is added, never bounded by this
calibration-only count. Retain the paid descriptors, their encoded
offset and whichever origin reading the decoder consumes; writable
paths, operands, candidates, output framing and installation remain
separate under Definition 1.4.

## 7. Certification price and the exponential cost of losing location

**Definition 7.1 (native witness family).** Let $B_d^\alpha$ and
$B_d^\beta$ be the perfect height-$d$ trees with the indicated
uniform leaf label. For $q\in\{L,R\}^d$ let $V_{d,q}$ be
$B_d^\beta$ with the single leaf at $q$ relabelled alpha. These
are mathematical alternative sources, not allowed edits during
one source's history. Their scores are

$$
m(B_d^\alpha)=m(V_{d,q})=2d,\qquad
m(B_d^\beta)=2d+1,\qquad
\rho B_d^\alpha=B_d^\beta.
\tag{AAR.24}
$$

**Theorem 7.2 (all-literal certification lower bound).** Any deterministic
source-blind program correct for acquiring $m(u)$ on all finite
quiescent sources must, on $B_d^\beta$, query every one of its
$2^d$ exact leaf literals. The same conclusion holds if its output
is a certified minimizing anchor. Thus, already on a legal
zero-update subcase of the concurrent task,

$$
T\ge2^d,\qquad A\ge d2^d,\qquad Q\ge d.
\tag{AAR.25}
$$

No restriction to level scans, ray-only queries or short operands
is imposed on competitors.

Proof. If exact leaf $q$ is unqueried, flip it to obtain $V_{d,q}$.
The supplied off-flipped-leaf identity says every submitted native
reply is unchanged. Proper ancestors are branch in both trees;
strict descendants of the flipped leaf are absent in both; every
other address is unchanged. By induction the entire deterministic
execution, including query selection, control, allocation and
Return, is identical, whereas (AAR.24) changes the required scalar.
A correct anchor determines that scalar by $2|a|+e$, so it cannot
evade the contradiction. Each exact leaf is mandatory, proving
all three bounds. $\square$

The $2^d$ beta leaf replies also form a sufficient stationary
information certificate: they force the literal tree to equal
$B_d^\beta$ by [READ]'s leaf-determination conjunct. Its certificate
coordinates are exactly $(2^d,d2^d,d)$. This does not give an unknown
observer the depth or certificate for free. Construction 4.1 is
uniform and on this source uses $T=2^{d+1}$ and
$A=(d-1)2^{d+1}+2+d$, with $Q=d$. It pays for discovering and
certifying the level; the extra last Read is its beta validation.

**Theorem 7.3 (scalar-only retention forces exponential fresh acquisition).**
Suppose the first producer, correct on all finite sources, exports
only $z=m(U_{v_0})$ and optionally the constant complete root-cut
row. Its entire accessible inter-call state is a fixed encoding
of these values and common public controls. The later deterministic
service, using arbitrary native literals and local computation,
must obtain enough data for a passive decoder to recover exact
lag on every authentic continuation. It need not explicitly
reacquire $m$, choose a minimum leaf or follow any particular
search algorithm.

There is a lawful history with first source $B_d^\alpha$, one
update between the two captures and quiescent later acquisition,
on which that later service must query all $2^d$ length-$d$ words.
Consequently its fresh costs satisfy (AAR.25). By contrast, an
actually retained first leaf $(a,0)$ permits a correct all-source
continuation service that on this same one-update history uses
one Read of length $d$ and no global recertification.

Proof. Call the displayed history $H_*$. After its first capture
and Return, make one genuine update, so its current source is
$B_d^\beta$. For every $q$ also consider a history $H_q$ starting
from the fixed original source $V_{d,q}$, with zero updates
between captures. Pause each writer during its acquisition calls.
Each history uses only its own unchanged register and (AAR.1).
There is no transition from one alternative source to another.

All first scalars are exactly $2d$. All first root-cut rows have
the same addressed root hole and singleton partition. The strict
handoff condition makes the later entry states identical, even
if the producers' now inaccessible old traces were different.
The later source on $H_q$ differs from the later source on $H_*$
only at exact leaf $q$. If the later run on $H_*$ omits $q$,
the all-address identity used in Theorem 7.2 makes its full later
trace and returned data identical on $H_q$. Any passive decoder
therefore gets the same complete input. Its required answers,
however, are one and zero. Thus every $q$ is mandatory. Later
root-cut rows are again identical complete rows; adding them does
not invalidate the proof. No history name, source label, retained
capacity or producer output may silently distinguish these
histories under the stated interface.

For the positive contrast, actually acquire any alpha leaf $a$
in the first $B_d^\alpha$ capture and keep its descriptor and
bit. Construction 2.4 begins its later search with Read$(a)$.
On $H_*$ that reply is beta, so it returns one from (AAR.6) with
$r=\varepsilon$. On any other authentic continuation it either
returns the correct leaf-based lag or continues below a branch;
the baseline's all-source safety and finite-interference liveness
apply. Acquisition, the retained literal and any representation
of it are paid; only fresh later query count has fallen from
at least $2^d$ to one. $\square$

There is also an explicit inexpensive first acquisition for this
positive interface. Use the supplied CNA/CWS left guard search,
which works on every finite source without $d$ as an input. On the
quiescent $B_d^\alpha$ it reads exactly
$\varepsilon,L,\ldots,L^d$, acquiring $(L^d,0)$ with
$T=d+1$, $A=d(d+1)/2$ and $Q=d$. Together with the later one-Read
continuation, the two calls use $T=d+2$ and $A=d(d+3)/2$.
The first search under interference is bounded by its final left
depth, just as in the supplied guard construction. No global minimum
certificate is requested by this local-anchor interface. Its retained
literal, framing, search buffers and expanded operands still cost
storage; the scalar-only interface has the different retained payload.

If an earlier empty-cut row, acquired full tree, anchor output or
location-bearing capacity survives, this is a richer interface
and the scalar-only premise is false. A compressible anchor can
use a shorter description than a flat literal, but the description
must be acquired, included in retained information and expanded
into a complete paid operand. This theorem does not establish
an exact bit optimum over arbitrary descriptor encodings. Its
exponential lower bound holds even when $d$ is given publicly:
the unknown information is the source relation, not the numerical
depth.

## 8. Source-sensitive comparison and a failed free switch

**Proposition 8.1 (a paid adaptive anchor avoids a deep fixed ray).** Fix
any finite preagreed word $w$. For arbitrary
$h\ge\max(1,|w|)$ construct $u_h$ by placing $B_h^\beta$ in the
root child traversed by the ray $wR^\infty$, and alpha in the
other child. Let $P=\{L,R\}$. The one uniform program of
Theorem 4.4, with no $w$ or $h$ input, has on these quiescent
sources

$$
(T,A,Q)=
\begin{cases}
(6,4,1),&\text{alpha is the left child},\\
(7,5,1),&\text{alpha is the right child}.
\end{cases}
\tag{AAR.26}
$$

It returns the complete two-hole disequality row and an actually
acquired minimizing anchor of length one. Every all-source
correct program required to acquire the fixed value $J^c_w(u_h)$,
even with arbitrary off-ray queries and the same complete-row
target, must submit an operand of length $h+1$ on $u_h$.

Proof. With shallow alpha left the scan reads root and $L$; with
shallow alpha right it reads root, $L$, $R$. In both cases it
accepts alpha. The CWS body reads root and compares $L$ with $R$,
ending at their leaf/branch mismatch; final validation rereads
the chosen shallow leaf. These literal lists give (AAR.26) and
the entire row: two reached addressed holes and their disequality.

The terminal leaf $p$ on the fixed ray is at depth $h+1$, beyond
the finite prefix $w$. Flipping its beta label to alpha changes
$J^c_w$ by one and no other native reply. The deep child remains
a branch in both sources, so the complete two-hole row is unchanged.
Theorem 7.2's deterministic induction forces Read$(p)$ on the
original source for this exact fixed-coordinate target.
$\square$

This extends the supplied CAB asymmetric comparison to an
actually selected anchor and its continued-use consumer. It
does not prove that every fixed reference is inferior: an
already agreed shallow reference avoids selection cost, and
different orientations favor different fixed choices. On
$B_d^\beta$, the fixed right clock alone takes $O(\log(d+2))$
Reads with the CAB/IDC right search, whereas globally certifying
$m$ needs at least $2^d$ Reads. Its scalar value there is also
$2d+1$. Equal output values on a family are not equal
all-source acquisition tasks. The cost vectors remain
incomparable in general.

**Counterexample 8.2 (complete rows do not calibrate a free outside switch).**
Use first cut $P=\{R\}$ and later cut $Q=\{L\}$. The two authentic
histories are

$$
\begin{array}{c|c|c|c}
 &U_{v_0}&k&U_{v_1}\\ \hline
H_0&\langle\alpha,\beta\rangle&0&\langle\alpha,\beta\rangle\\
H_1&\langle\alpha,\alpha\rangle&1&\langle\beta,\beta\rangle.
\end{array}
\tag{AAR.27}
$$

Both first rows are $\langle\alpha,\square_R\rangle$ with one
reached hole and its singleton partition. Both later rows are
$\langle\square_L,\beta\rangle$, again with the identical complete
singleton partition. The first acquired leaf record is $(L,0)$
in both histories and the later outside record is $(R,1)$ in
both. Thus all those decoder inputs agree but the lags differ.
There are no blocked holes or unverified disequalities to repair.

These are operationally realizable full-state comparisons. A
first producer can Read$(L)$ as guard, run the CWS body for $P$
and validate $L$; a second can do the same with guard $R$ and
cut $Q$. Both guards are present leaves in both alternatives.
On a nonleaf or absent proposed guard reply, the producer can invoke
the supplied all-source RA fallback; that branch is unused on these
witnesses.
The complete chronological query/reply lists coincide across
the alternatives at each call: the first body reads root and
$L$, the second root and $R$, and there is no pair of holes
requiring comparison. With identical code, controls and public
input, local states, outputs, capacities and cleanup coincide
as well. Insert the one update only between calls in $H_1$.
No scheduler event or identity is exposed. These legal traces
show why arbitrary outside replacement lacks the relation
provided by (AAR.6), (AAR.21) or (AAR.23). In $H_0$ the later
beta is not a certified phase-sensitive minimizer; the
minimum-certified scalar theorem is therefore not contradicted.

## 9. Boundary meaning, correspondence and unresolved recovery

**Proposition 9.1 (a local boundary relation, not a global profile).** Let
$\varphi=(1+\sqrt5)/2$. [NAR, Proposition 12.8] uses the canonical
locally constant density $f_u$ on infinite binary rays, scale
$W(u)$ and weighted cylinder mass $\varphi^{-s(p)}$ to give

$$
W(u)f_u(qR^\infty)=\varphi^{J^c_q(u)}.
\tag{AAR.28}
$$

At an acquired leaf $(a,e)$ this relation has the constant value
$\varphi^{s(a)+e}$ throughout $[a]$. Proposition 2.3 transports
that locally acquired calibration through the growing native
subtree. It supplies neither point access to an unknown global
density nor a free selection of its cheapest cylinder. The
phase-sensitive objective satisfies $m=J^c_a+\#_L(a)$ only
at a certified minimizing leaf, retaining the distinction
between letter length and the boundary weight.

Proof. The supplied canonical-density formula is constant on
every original leaf cylinder and has precisely that value after
multiplication by $W$. Formula (AAR.5) advances the common local
coordinate under the genuine history. The last equality is
$2|a|=s(a)+\#_L(a)$ applied to the certified score. $\square$

Even a retained local calibration and its scalar do not recover
arbitrary geometry. For example
$\langle\alpha,\beta\rangle$ and
$\langle\alpha,\langle\beta,\beta\rangle\rangle$ have the same
$m=2$, the same minimizing anchor $(L,0)$ and the same complete
root-cut row, but different hidden finite trees. CAB's
complementary-row reconstruction requires its own acquired
calibration and complementary exterior hypotheses. Exact time
recovery alone does not supply them.

**Mathematical citation 9.2 (Lean-source correspondence).** The following
are statement-level suppliers; no new compilation or formal
status is claimed for this volume.

| Source | Exact use and nontransfer boundary |
| --- | --- |
| [READ], `readout`, `leaves`, `flip`, `source_foundation` | Actual arbitrary literal port; off-leaf reply equality and leaf determination. Its native `paid` counts distinct addresses; (AAR.3) counts every invocation. Lower bounds use mandatory distinct queries and hence also bound invocations. Its unrelated positive-image decision target is not imported. |
| [NDP], `original_present_transport` | At an acquired present $a$, set the initial subtree to its observed alpha/beta leaf and iterate the same homomorphism. It supplies no free subtree Read and says nothing about an originally absent base. |
| [DOR], `right_clock_iterate`, `right_clock_readout`, including the existing private `clock_step` | Right-clock advancement and exact reply intervals, with alpha represented by `true`, beta by `false`, $L$ by address `false` and $R$ by `true`. Its later epoch-supplied original-read decoder is not used. |
| [ACPD], `literalRecord`, `canonicalRow_record_iff` | Full literal exterior, reached holes and equality/disequality partition. No hidden equality port follows from the semantic row definition. |
| [NLC], Lemma 3.1; [NAR], §§10–12 | Atomic shortest depth, agreed references, absence-safe $J^c$, calibrated overlaps and canonical boundary interpretation. Coordinate recurrences and graph integration are consumed facts. |
| [CNA], §§2–5; [CWS], §§2–4, 8–12; [CAB], §§2–5, 8 | Native leaf validation, finite moving bodies, full costs and complete accessible-state cleanup; fixed-clock and menu calibrations retain their own state and input contracts. No protected entry or free modification of protected routing state is inferred. |
| [IDC], §§6–7 | Stationary exponential/binary search and its operation-relative limits. Concurrent use needs CAB's finite failure exit, not just the stationary interval invariant. |

The substantive package is the monotone latest-beta minimum
acquisition, its paid all-cut consumer, the retained-anchor
continuation operand optimum and the scalar-only same-history
reacquisition obstruction. The native substitutions, guard
method, leaf-flip argument, minimum arithmetic and scalar
subtraction belong to the suppliers or elementary deductions.
The stationary sequence window model in [FIBSEQ, §§44–54] has no native
tree/register writer interface; none of its query prices is
used here by identifying a word position with a tree address.

**Mathematical citation 9.3 (primary literature and operation correspondence).**

| Primary source | Verified scope and correspondence |
| --- | --- |
| Grossman, Komargodski and Naor, *Instance Complexity and Unlabeled Certificates in the Decision Tree Model*, ITCS 2020, DOI [10.4230/LIPIcs.ITCS.2020.56][GKN], primary proceedings abstract and reference list | Distinguishes per-input algorithm performance from a competitor's correct certificate and studies barriers to instance optimality. In Theorem 7.2 the $2^d$ leaf labels are individual native query bits: every other literal is insensitive to a label flip. This actual operation correspondence, proved above, gives the native certificate bound. No theorem about instance optimality is imported from the abstract, and no free certificate is supplied to our program. |
| Golovin and Krause, *Adaptive Submodularity: Theory and Applications in Active Learning and Stochastic Optimization*, JAIR 42 (2011), 427–486, [arXiv:1003.3967v5][GK], §§2–3, Definitions 2–3 | Uses a finite ground set with a fixed realization and a known prior; marginal benefit is conditional expectation under the posterior, and adaptive submodularity is its diminishing-return property. Our repeated literal replies may change under a writer and there is no source prior. Adaptive greedy approximation bounds therefore do not follow. The level scan instead exploits branch persistence and the chronological last beta. |
| Rovelli, *Partial observables*, Physical Review D 65, 124013, [arXiv:gr-qc/0110035v3][ROV], §II | Separates quantities with measurement procedures from relational predictions; its pendulum example also separates a relation from inversion in either direction. Here the actual leaf Reads are the procedures and (AAR.6) is a conditional exact relation. No Hamiltonian, physical time parameter, gauge equivalence or measurement apparatus correspondence is established, so no physical clock theorem is imported. |

Höhn and Vanrietvelde, *How to switch between relational quantum
clocks*, New Journal of Physics 22 (2020), 123048,
[arXiv:1810.04153v3][HV], introduction and §2, link reduced
descriptions through a clock-choice-neutral constrained theory.
Their parametrized-particle constraint is $C_H=p_t+p^2\approx0$;
their clock-change maps need not be globally valid. This
`literature-attested` comparison motivates checking the domain of
a reference change, as the retained cylinder and acquired offsets
do here. The native tree has neither that phase space nor quantum
reduction maps; these results supply no literal acquisition,
retention price or physical interpretation of $k$.

These are `literature-attested` methods and boundaries, not a
worldwide novelty claim. The proofs of the new native statements
are given in this volume. In particular a common numerical
coordinate does not make source certification a standard binary
search problem, and a relational-clock interpretation does not
pay for acquiring its reference.

**Open problem 9.4 (the general bridge remains open).** Determine the
all-source Pareto frontier over acquired reference choice,
arbitrary future cuts, total all-attempt queries and letters,
maximum operand length, writable workspace, immutable
installation and all accessible retained encodings. The exact
arbitrary-descriptor memory frontier is not established here.
Nor is an optimum dependence on interference or on adaptively
chosen outside-cylinder calibration. A predeclared finite
public menu is a separately specified CAB/NAR variation, not
information available to these programs by default.

The strongest proved continuation comparison is conditional
and precise: keep a genuinely acquired local leaf for cheap
continued use; pay global phase-sensitive certification when
the exact future terminal-operand optimum is wanted; if only
the minimum scalar survives, some lawful later histories
force exponentially many fresh native queries. Neither this
finite package nor clock agreement closes the broad recovery
of all spatial, temporal, boundary and memory descriptions.

[READ]: ../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean
[NDP]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[DOR]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.lean
[ACPD]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.lean
[NLC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_DEPTH_CONTACT.md
[NAR]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY.md
[CNA]: RECURSIVE_RELATIONAL_OBSERVATION_CONCURRENT_NATIVE_CUT_ACQUISITION.md
[CWS]: RECURSIVE_RELATIONAL_OBSERVATION_CONCURRENT_NATIVE_CUT_WORKSPACE.md
[CAB]: RECURSIVE_RELATIONAL_OBSERVATION_CONCURRENT_ACQUIRED_CLOCK_BRIDGES.md
[IDC]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_INTRINSIC_DEPTH_CALIBRATION.md
[FIBSEQ]: FIB_LEGAL_EDGE_LOAD_VISIBLE_TAIL_PHASE_RIGIDITY_AND_WINDOW_LIMITS.md
[GKN]: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2020.56
[GK]: https://arxiv.org/html/1003.3967v5
[ROV]: https://arxiv.org/html/gr-qc/0110035v3
[HV]: https://arxiv.org/html/1810.04153v3

## 追加锚（本行以下为增补区）
