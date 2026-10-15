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

## 10. Arbitrary retained information and the exact quiescent lag price

**Definition 10.1 (acquired source and bounded retained information).**
Fix integers $z,b\ge0$. The sources remain the finite nonempty ordered
full trees generated by $\alpha$, $\beta$ and $\langle x,y\rangle$, with

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
$$

For a leaf label write $e(\alpha)=0$, $e(\beta)=1$, and retain the
phase-sensitive minimum of Definition 3.1:

$$
m(t)=\min_{p\in F(t)}\bigl(2|p|+e(t|_p)\bigr),
\qquad \mathcal T_z=\{t\in\mathcal T:m(t)=z\}.
\tag{AAR.29}
$$

The actual first tree $t$ has been fully acquired before handoff. The
handoff retains $z=m(t)$ and an arbitrary effective encoding $E(t)$
whose image on $\mathcal T_z$ has at most $2^b$ values. The encoder may
use the entire acquired tree; it need not encode an address or a leaf.
The public program and public parameters are source-independent. Every
other accessible source-dependent distinction has been erased: the
entire later entry state, including control, capacities, framing and
allocation metadata, is a deterministic function of $(z,b,E(t))$ and
the common public data. Deterministic consequences of these inputs are
allowed but provide no additional retained distinction.

At the later invocation the same register contains $u=\rho^k t$ for an
unknown integer $k\ge0$. The call is quiescent. Its sole source port is
an actual $\operatorname{Read}(p)$ of a fully materialized absolute
literal $p\in\{L,R\}^*$, returning alpha, beta, branch or absent as in
Definition 1.1. Repeated queries, arbitrary literal lengths, adaptivity
and finite local computation are allowed. One deterministic effective
service, with the chosen encoder, must terminate and return the exact
$k$ for every finite $t$ and every $k\ge0$. Its designated later capture
must be an actual Read inside the call. The restriction $k\in\{0,1\}$ will
be used only to measure performance, never as input or as a restriction
on correctness.

**Definition 10.2 (one joint performance slice).** For a fixed admissible
encoder and service, let $w_1,\ldots,w_n$ be the literals actually
submitted on $(t,k)$, counting each invocation, including repetitions.
Set

$$
\begin{aligned}
T(t,k)&=n,\\
A(t,k)&=\sum_{i=1}^n|w_i|,\\
\Lambda(t,k)&=\max\bigl(\{0\}\cup\{|w_i|:1\le i\le n\}\bigr).
\end{aligned}
$$

All three suprema below belong to that same encoder and that same
service:

$$
(q,a,\ell)=
\left(
\sup_{\substack{t\in\mathcal T_z\\k\in\{0,1\}}}T(t,k),\quad
\sup_{\substack{t\in\mathcal T_z\\k\in\{0,1\}}}A(t,k),\quad
\sup_{\substack{t\in\mathcal T_z\\k\in\{0,1\}}}\Lambda(t,k)
\right).
\tag{AAR.30}
$$

These suprema may be infinite. They are not separately optimized over
different services. Write uniquely

$$
\begin{gathered}
z=2d+e,\qquad e\in\{0,1\},\qquad
r=d+e=\left\lceil\frac z2\right\rceil,\\
N=2^d,\qquad C=2^b,\qquad
M=\left\lceil\frac NC\right\rceil=2^{\max(d-b,0)}.
\end{gathered}
\tag{AAR.31}
$$

Here $e$ is the parity of $z$; on a minimizing leaf it agrees with the
label function in (AAR.29). These parameters and this section's budget
letters have their local meanings, independently of the earlier
per-execution notation (AAR.3).

**Theorem 10.3 (one finite source forces all three prices).** For every
encoder and service of Definition 10.1 there is one finite
$t_*\in\mathcal T_z$ such that the actual quiescent run at
$\rho^e(t_*)$ submits at least $M$ literals of length at least $r$.
Consequently, on this one history in the performance slice,

$$
T(t_*,e)\ge M,\qquad
A(t_*,e)\ge rM,\qquad
\Lambda(t_*,e)\ge r.
\tag{AAR.32}
$$

Proof. Let $S=E(\mathcal T_z)$, so $|S|\le C$. For each $s\in S$
consider the formal deterministic execution from entry data $(z,b,s)$
in which every submitted Read receives branch. This is only a formal
reply path. It is not presumed to describe a real tree, to terminate,
or to satisfy the service's correctness contract. In particular it
may stop, loop in local computation, make infinitely many short
submissions, or submit words of unbounded length.

Call a submission long if its length is at least $r$. From each formal
path collect its first $M-1$ long submissions, or all its long
submissions if it has fewer. Denote the resulting finite lists by
$W_s$. Multiplicities are retained when counting submissions; repeated
words can only reduce the number of distinct prefixes covered. Since
$r\ge d$, every collected word has a length-$d$ prefix, and

$$
\left|\bigcup_{s\in S}
 \{\operatorname{pref}_d(w):w\in W_s\}\right|
\le C(M-1)<N.
\tag{AAR.33}
$$

Choose a length-$d$ word $p_*$ outside this union. Define

$$
D=\max\left(\{0\}\cup
 \{|w|:s\in S,\ w\in W_s\}\right),\qquad H=D+1.
\tag{AAR.34}
$$

The zero in this maximum covers the empty collection. Every collected
submission is a finite literal, and only finitely many are collected,
so $D$ and $H$ are finite even when a formal path later uses unbounded
lengths. No effective procedure for recognizing the end of a looping
formal path is needed: the lower bound is an existence argument from
its finitely many selected words.

Construct one tree $t_*$ with a complete depth-$d$ skeleton. In slot
$p_*$ put alpha when $e=0$ and beta when $e=1$. In every other
length-$d$ slot put a perfect height-$H$ all-alpha tree. The distinguished
leaf has score $2d+e=z$; every filler leaf has score $2(d+H)>z$ because
$H\ge1$. Thus $t_*$ is finite, full and nonempty, and $m(t_*)=z$.
This is a single common construction against all retained values. Only
now set

$$
s_*=E(t_*).
$$

Consider $u_* = \rho^e(t_*)$. Every collected word, for every $s\in S$,
returns branch on $u_*$. Indeed it misses $p_*$ at depth $d$ and enters
a filler with suffix length at most $D-d<H$. Such a position is a
branch before substitution, and remains a branch after substitution.
Every word shorter than $r$ also returns branch on $u_*$. If $e=0$,
it stops strictly inside the depth-$d$ skeleton. If $e=1$, it either
stops there or has length $d$: the distinguished beta has become a
branch, and all filler roots are branches. These arguments cover
arbitrary absolute literals, not just a traversal's next child or a
fixed ray.

Until the $M$th long submission, the actual run from $(z,b,s_*)$ on
$u_*$ therefore agrees, step by step, with its formal all-branch path.
Every prior long submission is in $W_{s_*}$, and every intervening
short submission has the branch reply just established. Determinism
also identifies all intervening local computation and control.

This actual run cannot halt before the $M$th long submission. If it
did, use the same original $t_*$, the same acquired data and the same
handoff, but insert one more update before the later invocation.
The current register is then $\rho^{e+1}(t_*)$. Every branch observed
in the alleged terminating transcript persists, so the complete
transcript and output are identical in the two quiescent histories.
The required outputs are $e$ and $e+1$, a contradiction. When $e=1$
the second history has lag two; it need not belong to the performance
slice because correctness was required for every lag.

Nor can the actual run continue forever without that submission:
$t_*$ is an actual finite source and the service is required to
terminate on it. This excludes infinite local delay and infinitely
many short or repeated submissions just as it excludes any other
nonterminating continuation. Hence the $M$th long call is made. Its
reply need not be branch and its word need not have been collected;
its submission already supplies the last required cost. The preceding
$M-1$ long calls and this call give (AAR.32) simultaneously.

When $M=1$ the collection is empty, $D=0$ and $H=1$; the argument
forces the first long call without requiring a nonempty padding
maximum. When $d=0$, $N=M=1$, the distinguished word is the empty word
and there are no filler slots. For $z=0$, $t_*=\alpha$ and $r=0$, so
every call, including a root Read of length zero, is long. For $z=1$,
$t_*=\beta$ and $r=1$; at lag one the root is branch, and the proof
forces a nonempty operand. No case chooses a different source for
each code or replaces the actual source during a run. $\square$

**Construction 10.4 (uniform prefix retention and complete block readout).**
From the fully acquired $t$, compute $z=m(t)$ and choose the
lexicographically first minimizing leaf $p_0$, with $L$ before $R$.
Equation $2|p_0|+e(t|_{p_0})=2d+e$ forces $|p_0|=d$ and its label to
be alpha for $e=0$, beta for $e=1$. Put $j=\min(b,d)$ and retain only
the first $j$ letters of $p_0$ as $E(t)$. Their length is public from
$(z,b)$, and there are at most $2^j\le2^b$ possible values. Erase all
other source-dependent state except the retained scalar $z$.

At the later call generate, in public lexicographic order, the block

$$
B=\{p\in\{L,R\}^d:\operatorname{pref}_j(p)=E(t)\},
\qquad |B|=2^{d-j}=M.
\tag{AAR.35}
$$

Every depth-$d$ address is present in $t$: a leaf at any depth less
than $d$ would have score at most $2d-1<z$. For such addresses the
minimum recurrence gives

$$
m(t)=2d+\min_{|p|=d}m(t|_p).
$$

Hence $m(t|_p)\ge e$ for every $p\in B$, while $p_0\in B$ has
$m(t|_{p_0})=e$. In particular

$$
\min_{p\in B}m(t|_p)=e.
$$

The right clock from (AAR.4) is the score $2h+f$ of a subtree's
rightmost leaf, so $c(v)\ge m(v)$ for every finite $v$. At $p_0$ both
are $e$. Applying present-subtree transport [NDP] and
[DOR]'s `right_clock_iterate` therefore gives, for every $k\ge0$,

$$
\begin{aligned}
(\rho^k t)|_p&=\rho^k(t|_p) &&(p\in B),\\
\min_{p\in B}c((\rho^k t)|_p)
 &=\min_{p\in B}\bigl(c(t|_p)+k\bigr)=e+k.
\end{aligned}
\tag{AAR.36}
$$

Thus no equality between the two minima for arbitrary subtrees is
being assumed; equality here is supplied by the acquired minimizing
leaf in this particular block.

For each $p\in B$, submit exactly one fully materialized literal
$pR^e$: use $\operatorname{Read}(p)$ when $e=0$, and
$\operatorname{Read}(pR)$ when $e=1$. Finish the entire batch before
returning. The supplied `right_clock_readout` of [DOR], applied at
this originally present $p$, says for every suffix length $v\ge0$:

$$
\operatorname{Read}(pR^v)=
\begin{cases}
\mathrm{absent},&c(u|_p)<2v,\\
\mathrm{alpha},&c(u|_p)=2v,\\
\mathrm{beta},&c(u|_p)=2v+1,\\
\mathrm{branch},&c(u|_p)\ge2v+2,
\end{cases}
\qquad u=\rho^k t.
\tag{AAR.37}
$$

For $e=0$, use the following decision after the complete $p$ batch:

- If any reply is alpha, return zero.
- If none is alpha but some reply is beta, return one.
- Otherwise apply Construction 4.1 and Theorem 4.2 to the current
  tree to acquire a certified minimum $m(u)$, and return $m(u)-z$.

Indeed no $p$ is absent, and (AAR.36) has minimum clock $k$.
The first two reply cases are exactly $k=0$ and $k=1$; all replies
are branch exactly when $k\ge2$.

For $e=1$, use the following decision after the complete $pR$ batch:

- If any reply is absent, return zero.
- If none is absent but some reply is alpha, return one.
- If none is absent or alpha but some reply is beta, return two.
- Otherwise use the same finite minimum certification and return
  $m(u)-z$.

Here the minimum clock is $1+k$. With $v=1$, (AAR.37) makes these
four cases exactly $k=0$, $k=1$, $k=2$ and $k\ge3$. In particular,
an alpha at one slot alone does not justify returning one: at lag
zero another slot can still be absent. For example, with $d=1$,
$b=0$ and $t=\langle\langle\alpha,\alpha\rangle,\beta\rangle$,
we have $m(t)=3$; the $LR$ query returns alpha and the $RR$ query
returns absent. The whole-batch priority of absent gives the correct
zero. A few reply-occurrence flags suffice; no original tree or
unretained minimizing address is supplied to the later service.

The fallback uses the existing all-source finite minimum procedure,
not a new clock-acquisition primitive. It terminates on the finite
quiescent $u$, and Lemma 3.2 gives $m(u)-z=k$. Each batch is finite,
all of its words are generated effectively, and the fallback is
finite whenever it is used. Thus this one encoder and service are
uniformly effective in $z,b$ and correct for every finite source and
every unknown lag. For a direct batch return designate its final
Read as the capture; for a fallback return use that supplier's
accepting Read. Quiescence makes the returned lag valid at the
chosen actual event, without any extra validation call.

On every run in the slice $k\in\{0,1\}$ the fallback is unused.
The service makes exactly $M$ Reads, each of full literal length
$d+e=r$. Therefore its joint suprema are exactly

$$
(q,a,\ell)=(M,rM,r).
\tag{AAR.38}
$$

The block need not be retained as an installed table: its words can
be enumerated from the retained prefix and public lengths. This
observation supplies effectiveness, not a free buffer or a workspace
optimum. First acquisition, encoding, clearing, prefix storage,
operand materialization, enumeration, arithmetic, local work and
fallback costs outside the slice retain their separate charges.

**Theorem 10.5 (singleton joint Pareto minimum).** In the contract of
Definitions 10.1–10.2, the attainable joint supremum triples have the
coordinatewise least element

$$
\left(
2^{\max(\lfloor z/2\rfloor-b,0)},\quad
\left\lceil\frac z2\right\rceil
 2^{\max(\lfloor z/2\rfloor-b,0)},\quad
\left\lceil\frac z2\right\rceil
\right)=(M,rM,r).
\tag{AAR.39}
$$

Their Pareto-minimal set is the singleton consisting of this triple.
For each admissible pair of encoder and service, all three lower
coordinates are witnessed together by one finite source and one
performance-slice history.

Proof. Theorem 10.3 gives $(q,a,\ell)\ge(M,rM,r)$ coordinatewise,
with the stronger common-history witness. Construction 10.4 attains
all three equalities with the same encoder and service. Thus the
attained triple weakly dominates every other attainable triple, and
any different triple is strictly worse in at least one coordinate.
This determines the Pareto minimum without classifying which other
exact supremum triples are attainable. $\square$

**Corollary 10.6 (upper budgets, small scalars and one fresh Read).**
For nonnegative budgets $Q,A,L$, there is an admissible encoder and
service satisfying $q\le Q$, $a\le A$, $\ell\le L$ if and only if

$$
Q\ge M,\qquad A\ge rM,\qquad L\ge r.
\tag{AAR.40}
$$

For $z=0$ the optimum is $(1,0,0)$; for $z=1$ it is $(1,1,1)$.
Exactly one fresh Read suffices uniformly on the performance slice
if and only if $b\ge d=\lfloor z/2\rfloor$, while correctness still
ranges over all $k\ge0$.

Proof. Necessity follows from the common-source lower bound;
sufficiency uses the attaining triple (AAR.38) within the stated
upper budgets. When $z=0$, $d=e=r=0$ and $M=1$: the block consists
of the empty word and its root Read distinguishes alpha from beta.
When $z=1$, $d=0$, $e=r=1$ and $M=1$: the single literal $R$ is
absent on beta and alpha on $\rho\beta$. More generally $M=1$ is
equivalent to $b\ge d$. Zero Reads cannot recover an unknown lag,
even with a completely known first tree; Theorem 10.3 includes this
case and the contract also requires an actual later capture. The
one-Read statement concerns the slice, not all unknown lags at the
same query budget. $\square$

**Mathematical citation 10.7 (suppliers and remaining boundaries).**
The new result is `repo-derived`: its common finite padding and its
complete-block native readout concern arbitrary effective retained
information after actual acquisition. The proof uses the clock law
AAR3.2, finite minimum certification AAR4.1–4.2, and the native
present-subtree and right-clock suppliers [NDP] and [DOR]. The operand
obstruction AAR6.1 is consistent with the attained value: at lag
$e$, AAR3.2 gives

$$
\mu(\rho^e t)=\left\lfloor\frac{z+e}{2}\right\rfloor=r.
$$

Theorem 10.3 strengthens that one-operand requirement to $M$ long
invocations on one source. It does not obtain a joint witness by
combining coordinate bounds from different sources.

AAR7.3 retains only the scalar and proves a particular exponential
fresh-acquisition obstruction. The present result allows any
$2^b$-valued effective retention on $\mathcal T_z$ and determines the
joint optimum for both parity classes under the present performance
slice. Static [WORD4.2](RECURSIVE_RELATIONAL_OBSERVATION_WORD_RETENTION_AND_GEOMETRIC_REACCESS.md#4-固定编码器的准确调用与加权价格)
concerns a fixed encoder on a promised family of unchanged trees and
allows inference of the last unqueried candidate. Its $|B_s|-1$
price, including zero for a singleton fiber, is not the lag price
here. Even when the original tree is known, the two continuations
$\rho^e t$ and $\rho^{e+1}t$ still require different answers. The
common-source construction explicitly preserves this distinction.

For primary-literature context, Andrew Chi-Chih Yao, *Should Tables
Be Sorted?*, Journal of the ACM 28(3), 615–628 (1981),
[DOI:10.1145/322261.322274](https://doi.org/10.1145/322261.322274),
provides the preprocessing/query viewpoint. Here the acquired
instance supplies the retained advice $E(t)$; it is not advice chosen
from the later unknown $k$. A bound on the number of retained states
is not a bound on total storage, preprocessing work or a table's
probe complexity. Robert D. Nowak, *The Geometry of Generalized
Binary Search*, IEEE Transactions on Information Theory 57(12),
7893–7906 (2011),
[arXiv:0910.4397v5](https://arxiv.org/abs/0910.4397v5),
[DOI:10.1109/TIT.2011.2169298](https://doi.org/10.1109/TIT.2011.2169298),
relates query efficiency to available hypothesis-splitting geometry.
The native port here accepts complete absolute words; it supplies
neither arbitrary subset queries nor an address-dictionary index
interface. These are contextual correspondences only. No literature
theorem supplies a step of the proof of (AAR.39).

Quiescence and the chosen two-lag performance slice are essential
parts of this frontier's scope. No interference price or optimum
for other resource coordinates is asserted. Acquisition and all
non-query costs remain outside the three optimized coordinates,
and no claim is made that every triple dominated by this minimum
is an attainable exact supremum triple. This restricted result
leaves AAR9.4 and the broad mutual recovery of spatial, temporal,
boundary and memory descriptions open, with their existing source
and operation boundaries intact.

## 追加锚（本行以下为增补区）

## 11. Finite ray memory and exact literal reply recovery

This section asks which finitely many acquired boundary coordinates
retain enough distinctions to predict a declared menu of literal reply
values. The menu can contain nested addresses. Its output is a vector
of values at one specified version, not a complete cut row and not a
list of observation events. The finite source restriction below makes
an exact necessity statement possible, while the sufficient decoding
rule works on every finite native tree.

**Definition 11.1 (finite initial family and complete retained input).**
Use the actual trees, substitution, four-valued literal port and resource
convention of Definitions 1.1–1.4. Give leaves height zero and give a
branch height one plus the maximum child height. Fix public $D\ge1$ and

$$
\begin{aligned}
\mathcal F_D
 &=\{\langle\alpha,v\rangle:\operatorname{height}
          (\langle\alpha,v\rangle)\le D+1\},\\
A_D&=\{p\in\{L,R\}^*:1\le |p|\le D,
                          \ p\text{ starts with }R\},\qquad P\subseteq A_D.
\end{aligned}
\tag{AAR.41}
$$

The set $P$ is a finite public menu, possibly empty; its words, if any,
are nonempty. No prefix-free assumption is imposed on it. The known
phase-sensitive source minimum is $m(t)=2$ for every $t\in\mathcal F_D$:
the actual leaf $L$ is alpha, and every other leaf has depth at least
one. This is $m$ from Definition 3.1, not the weighted minimum from
Definition 3.5.

Let $\Omega=\{L,R\}^{\mathbb N}$, let $[b]$ denote the rays beginning
with $b$, and let $Q$ be a finite public set of distinct eventually-right
rays. Write each $\omega\in Q$ by a fixed finite descriptor
$q_\omega$ with $\omega=q_\omega R^\infty$. Different descriptors of
the same ray do not count as different samples. For any finite tree $u$,
there is one actual leaf $a$ on $\omega$; set

$$
 h_u(\omega)=s(a)+e(u|_a),\qquad
 s(a)=\#_L(a)+2\#_R(a),\qquad e(\alpha)=0,\quad e(\beta)=1,
 \qquad Z_Q(u)=(h_u(\omega))_{\omega\in Q}.
\tag{AAR.42}
$$

The ordered table $Z_Q(t)$ has been truthfully acquired at a first
capture $v$, with $t=U_v\in\mathcal F_D$. After handoff the entire
accessible source-dependent retained state is exactly this table, or a
fixed lossless encoding of it. All other accessible state is a fixed
function of the table and public $D,P,Q$. This includes outputs,
control, buffers, lengths, capacities, allocation identities, logs and
pointers as in Definition 1.3; an extra source-bearing distinction
changes the interface. The table centered by the known constant two,
$Z_Q(t)-2\mathbf1$, is an equivalent encoding, not extra memory.

The passive consumer receives an exact nonnegative update count $k$
for a specified authentic continuation $U_w=\rho^k t$ on the same root
and register. The requested value is

$$
 V_P(U_w)=\bigl(\operatorname{readout}(p,U_w)\bigr)_{p\in P}.
\tag{AAR.43}
$$

This consumer gets no fresh Read, source name, hidden subtree, global
boundary object, clock or history log. The genuine-history premise
authenticates the meaning of the supplied count; the table does not
authenticate that premise. Acquisition of an unknown count is a separate
paid operation in Proposition 11.8 below. Public menus and descriptors
are source-independent but their installation and use still cost bytes.

**Lemma 11.2 (the supplied advancing boundary coordinate).** For every
finite $u$, every eventually-right $\omega=qR^\infty$ and every $k\ge0$,

$$
 h_u(\omega)=J^c_q(u),\qquad
 h_{\rho^k u}(\omega)=h_u(\omega)+k,\qquad
 \varphi^{h_u(\omega)}=W(u)f_u(\omega).
\tag{AAR.44}
$$

Here $J^c$ is the absence-safe right-clock coordinate, and $f_u$ is the
canonical locally constant density, not an arbitrary almost-everywhere
representative. These are precisely [NAR, Theorem 11.3 and Proposition
12.8] and §9, with their existing boundary and scale suppliers.

Proof of the parameter correspondence. If navigation toward $q$ stops
at a blocking leaf $a$, the longest-reached-prefix rule gives
$J^c_q(u)=s(a)+e(u|_a)$. Otherwise the leaf on the ray is $qR^r$, and
the right-clock recurrence gives $c(u|_q)=2r+e(u|_{qR^r})$.
Both cases give (AAR.42), including a descriptor ending at a leaf or
strictly beyond one. The supplied advancement and canonical-density
identities now have exactly the displayed parameters. Thus a descriptor
never has to be reached for its table entry to make sense. This reuse
does not supply a boundary point-evaluation port. $\square$

**Lemma 11.3 (the left-child obstruction and its precise test).** Fix
any finite native tree $u$ and any nonempty address $p$. Choose any
ray $\omega\in[pR]$ and put $x=h_u(\omega)$ and $s=s(p)$.
If $p=aL$, also choose any $\eta\in[aR]$ and put $y=h_u(\eta)$.
The exact literal reply is

$$
\operatorname{readout}(p,u)=
\begin{cases}
\mathrm{absent},&x<s,\\
\mathrm{absent},&x=s,\ p=aL,\ y=s,\\
\alpha,&x=s,\ p\text{ ends with }R,\\
\alpha,&x=s,\ p=aL,\ y>s,\\
\beta,&x=s+1,\\
\mathrm{branch},&x\ge s+2.
\end{cases}
\tag{AAR.45}
$$

The listed cases exhaust all attained inputs. In particular sampling
inside $[p]$ without the additional right step is not the stated test.

Proof. If $p$ is a leaf, its whole cylinder has score $s$ for alpha
and $s+1$ for beta. If $p$ is a branch, a ray in $[pR]$ reaches a leaf
strictly below its right child, or at that child. Its score is at least
$s+2$, regardless of all other branches or labels.

If $p$ is absent, its unique blocking leaf $b$ is a strict prefix of
$p$ and of $\omega$. Write $p=br$ with $r\ne\varepsilon$ and let its
label bit be $e_b$. Then

$$
 x=s(b)+e_b,\qquad s(p)-x=s(r)-e_b\ge0.
\tag{AAR.46}
$$

Equality holds exactly when $r=L$ and $e_b=1$, since every letter has
positive weight and only the one-letter word $L$ has weight one.
Thus the sole absent case with $x=s(p)$ is a beta at the parent $a$
of a left child $p=aL$. Every ray in $[aR]$ then has the same score
$s(a)+1=s(p)$. In contrast, if $p=aL$ is an actual alpha, $a$ is a
branch and every ray in $[aR]$ has score at least
$s(a)+2=s(p)+1$. This proves the additional test and all cases in
(AAR.45). It also shows that the answer is independent of which rays
in the required cylinders were selected. $\square$

**Theorem 11.4 (necessary and sufficient finite sampling geometry).**
Under Definition 11.1, the following are equivalent:

1. There is one total computable decoder $\mathsf D_{P,Q}$ such that
   for every $t\in\mathcal F_D$ and every $k\in\mathbb N$,
   $\mathsf D_{P,Q}(Z_Q(t),k)=V_P(\rho^k t)$.
2. There is a single-valued decoder with that property, without an
   effectiveness requirement.
3. The public rays satisfy

$$
\begin{aligned}
&Q\cap[pR]\ne\varnothing &&\text{for every }p\in P,\\
&Q\cap[aR]\ne\varnothing &&\text{for every }aL\in P.
\end{aligned}
\tag{AAR.47}
$$

The necessity is for uniform correctness at all counts, including zero;
it is not a claim that these samples are necessary at every fixed late
epoch. The source height bound applies at the first capture, not to
its future iterates.

Proof of sufficiency. Select one public ray in each required cylinder,
using the fixed order of $Q$. Compute $x=Z_Q(t)_\omega+k$ and, when
needed, $y=Z_Q(t)_\eta+k$. Lemma 11.2 identifies these with the
coordinates of the actual current tree $\rho^k t$. Apply Lemma 11.3
for each target. The arithmetic and public selections are finite.
Define arbitrary default outputs on malformed inputs to make the
decoder total. Its correctness is asserted on the promised inputs.
The argument works for every finite initial tree; $\mathcal F_D$
is needed below to witness necessity within the specified family.

Proof of necessity. Define an actual one-hole path context recursively
by

$$
 C_\varepsilon[z]=z,\qquad
 C_{Lb}[z]=\langle C_b[z],\alpha\rangle,\qquad
 C_{Rb}[z]=\langle\alpha,C_b[z]\rangle.
\tag{AAR.48}
$$

For a nonempty word $b$ beginning with $R$, consider

$$
 u_b=C_b[\beta],\qquad
 v_b=C_b[\langle\alpha,\alpha\rangle].
\tag{AAR.49}
$$

These are concrete finite sources with the same off-path leaves and
initial left child alpha. Their heights are $|b|$ and $|b|+1$.
Their entire ray profiles agree outside $[bR]$. Indeed rays outside
$[b]$ encounter an unchanged leaf; on $[bL]$ both profiles equal
$s(b)+1$; on $[bR]$ their values are respectively $s(b)+1$ and
$s(b)+2$. This is an exact description of the differing set, not
just an equality of chosen summary numbers.

If the first condition in (AAR.47) fails for $p$, put $b=p$.
Both sources belong to $\mathcal F_D$, their whole retained tables
agree, and at count zero their replies at $p$ are beta and branch.
If the second condition fails for $p=aL$, put $b=a$. Since $p$
begins with $R$, $a$ is nonempty and begins with $R$. Both heights
are at most $|p|\le D$, so both sources again belong to
$\mathcal F_D$. Their retained tables agree but their replies at
$p$ are absent and alpha. In both cases their known minimum is two,
all public data and the supplied count zero coincide, and the complete
accessible entry state coincides by Definition 11.1. Each is a valid
constant initial history. A single-valued decoder cannot give both
answers. Their translated tables also agree at every common future
count, although the zero-count difference already proves failure of
the required uniform task. This proves both necessary conditions.
Computability implies single-valuedness, completing the equivalence.
$\square$

**Example 11.5 (two distinct failures in small native sources).** The
following collisions instantiate both missing distinctions. Every
entry refers to an actual finite tree and its whole indicated table.

| Target and sampled ray | Two sources | Common sampled score | Different target replies at zero |
| --- | --- | --- | --- |
| $p=R$, $Q=\{RLR^\infty\}$ | $\langle\alpha,\beta\rangle$, $\langle\alpha,\langle\alpha,\alpha\rangle\rangle$ | $3$ | beta, branch |
| $p=RL$, $Q=\{RLR^\infty\}$ | the same two sources | $3$ | absent, alpha |

The first row uses $D=1$ and misses $[RR]$. The second uses $D=2$:
its ray does hit $[RLR]$, but it misses the required parent-right
cylinder $[RR]$. Thus a test retaining only the first line of
(AAR.47) is false even when the sampled ray lies strictly inside
the target's right cylinder. Adding $R^\infty$ supplies the second
row's missing distinction: the two scores there are three and four.

**Corollary 11.6 (attained minimum number of rays).** Define the finite
set of required words and its prefix-maximal members by

$$
\begin{aligned}
 B(P)&=\{pR:p\in P\}\cup\{aR:aL\in P\},\\
 B_{\max}(P)&=\{b\in B(P):\nexists c\in B(P)
                                      \text{ with }b\prec c\}.
\end{aligned}
\tag{AAR.50}
$$

Among all fixed public eventually-right sampling sets that solve
Theorem 11.4, the exact minimum cardinality is $|B_{\max}(P)|$.
It is attained by $Q=\{bR^\infty:b\in B_{\max}(P)\}$.
For the full depth menu $P=A_D$, this minimum is $2^{D-1}$.
For an empty menu it is zero.

Proof. Two binary cylinders either are disjoint or one contains the
other. Distinct prefix-maximal words in (AAR.50) are incomparable,
so one ray cannot hit two of their cylinders. Theorem 11.4 therefore
requires at least their number. Every required word is a prefix of
some prefix-maximal member, by finiteness. One ray through each of
those members hits every required cylinder, proving attainment.
For $P=A_D$, every required word begins with $R$, ends with $R$ and
has length at most $D+1$. Every one of length at most $D$ has its
strict extension $bR$ in $B(P)$. The maximal words are consequently
exactly the length-$(D+1)$ words beginning and ending with $R$,
of which there are $2^{D-1}$. The empty case is vacuous. $\square$

This optimum counts distinct retained ray coordinates under the fixed
sampling interface. It is not a lower bound on the number of arbitrary
encoded registers, retained bits, native queries, installed literal
bytes or peak workspace. Shared prefixes can save acquisition queries;
coordinates can be encoded jointly; a single ray can have several
finite descriptors. None of those changes the cylinder count proved
here.

**Proposition 11.7 (translation, restriction and the task-relative boundary).**
For a table $z$, put $\tau_k z=z+k\mathbf1$, and let $d_{P,Q}$ be the
rule (AAR.45) on current table values. On all attained inputs satisfying
(AAR.47),

$$
\begin{aligned}
\mathsf D_{P,Q}(Z_Q(t),k)&=d_{P,Q}(\tau_k Z_Q(t)),\\
d_{P,Q}(\tau_h\tau_k Z_Q(t))&=V_P(\rho^{k+h}t),\\
\tau_h\tau_k z&=\tau_{h+k}z.
\end{aligned}
\tag{AAR.51}
$$

If $P'\subseteq P$ and $Q'\subseteq Q$ still satisfies (AAR.47) for
$P'$, then, with the ordinary coordinate restrictions,

$$
 \operatorname{res}_{P'}d_{P,Q}(\tau_k Z_Q(t))
 =d_{P',Q'}\bigl(\tau_k\operatorname{res}_{Q'} Z_Q(t)\bigr).
\tag{AAR.52}
$$

Proof. Equation (AAR.44) gives $Z_Q(\rho^k t)=\tau_k Z_Q(t)$;
addition of actual update counts composes the same-source continuation.
Lemma 11.3 identifies both sides of (AAR.52) with the same actual
replies. Coordinate restriction commutes with adding $k$. These facts
prove the statements, including independence of the public witness-ray
choices. A rebased table is associated with its actual capture; a future
increment must be counted from that capture. Discarding the old count
discards its old time origin. $\square$

The compatibility does not put a well-defined update operation on every
selected-reply vector alone. For example, at $P=\{RL\}$ the sources
$\langle\alpha,\alpha\rangle$ and $\langle\alpha,\beta\rangle$
both give absent initially. After one update their replies at $RL$
are respectively absent and beta. The sufficient table retains a
distinction that this selected-reply vector discards. Nor does one
recovered vector recover its table or the count. For $t\in\mathcal F_D$
and $k\ge2D$, §3 gives
$\mu(\rho^k t)=1+\lfloor k/2\rfloor>D$; hence every target in $A_D$
is branch at every such count. All those different epochs give the
same selected replies. The table-to-reply recovery is task-relative,
not an equivalence of all spatial, temporal and memory descriptions.

**Proposition 11.8 (actual acquisition and an unknown-lag consumer).**
A finite ray table can be acquired by native literal Reads on a
stationary first source in $\mathcal F_D$. A valid equal-alpha guard at
$L$ can certify the common version. Subsequently, the same acquired
initial alpha at $L$ permits a paid native service to acquire an unknown
lag $k_w$ and then compute $V_P(U_w)$ under (AAR.47), even with finite
interference in that later service.

Proof and costs. To acquire one table entry, submit successive complete
prefixes of its public ray from the root until a leaf reply is actually
obtained. Use its actual address and label in (AAR.42). There is no
infinite operand or navigation port. On a stationary first tree of
height at most $D+1$, this takes at most $D+2$ Reads per ray, each
operand of length at most $D+1$. Read $L$ as alpha before the table
body and reread $L$ as alpha afterwards. The supplied leaf-rigidity
law excludes every update between these two observations. The final
Read is a joint validation of the acquired entries and the initial
anchor. Without prefix sharing, the successful stationary procedure
has the explicit bounds

$$
 T\le |Q|(D+2)+2,\qquad
 A\le |Q|\frac{(D+1)(D+2)}2+2,\qquad Q_{\mathrm{operand}}\le D+1.
\tag{AAR.53}
$$

All submitted literals, local work, table storage, guards and failed
attempts are charged separately as in §5. Export entries in public order
into fixed regions with canonical extents determined by the encoded
table. Clear and retract the acquired leaf descriptors, reply latches,
operand buffers, temporary counters and nonpublic control state before
handoff. This realizes the complete interface of Definition 11.1 only
when the host exposes no additional acquisition transcript or allocation
distinction; inaccessible residual storage still has its storage cost.
The conditional procedure
does not guarantee capturing an $\mathcal F_D$ version after an
unprotected writer has already changed its left alpha. Failure of a
guard supplies no table with the stated initial-family premise.

For the later service submit $L,LR,LR^2,\ldots$, extending only after
a branch reply, until an actual leaf with label bit $f$ is acquired at
$LR^j$. Let that event be $w$. Present-subtree transport gives
$U_w|_L=T_{k_w}$, because the validated initial subtree at $L$ was
alpha. Proposition 2.3, or the exact right-clock readout supplier,
therefore gives

$$
 k_w=2j+f.
\tag{AAR.54}
$$

Branch persistence excludes absence along this expanding search.
After finitely many updates the final finite tree has finite right
depth, so under the fairness convention the search reaches a leaf.
Earlier search steps and local calculations may have been interleaved
with updates. The formula concerns their actual terminal leaf Read,
not invocation or Return. Its query list has exactly $j+1$ Reads,
total literal length $(j+1)(j+2)/2$ and maximum length $j+1$.
For a quiescent lag $k$, $j=\lfloor k/2\rfloor$; none of these prices
is uniformly bounded over unknown lags.

Use this acquired $k_w$ in Theorem 11.4 with the original retained
table. It computes the menu values of the one actual version $U_w$,
even if the source advances during computation. Formula (AAR.54)
reuses the already acquired local calibration of §2; the new consumer
is the finite spatial-reply decoder, not a new clock-subtraction law.
The family promise and the first actual guard make $L$ a legitimate
known reference; a mere promise $m(t)=2$ on arbitrary sources would
not identify that address. $\square$

Computing a value in (AAR.43) creates no $\operatorname{Read}(p)$ event
at $w$. A later submission of $p$ is a new paid event and may occur on
a different version. If the task requires actual observations of the
menu at one common version, it must acquire and validate that separate
body, for example by an unchanged acquired leaf guard with charged
retries. Theorems about paid transcripts or complete rows cannot count
these predictions as acquired replies. Likewise, without a supplied
count or a new source observation, even a fully known initial tree
cannot distinguish a later quiescent lag zero from lag one: the entire
passive input before that observation is identical.

**Counterexample 11.9 (same sufficient memory, different hidden equality).**
Set

$$
\begin{aligned}
 X&=\langle\alpha,\alpha\rangle,&
 Y&=\langle\beta,\alpha\rangle,\\
 t&=\langle\alpha,\langle X,X\rangle\rangle,&
 t'&=\langle\alpha,\langle Y,X\rangle\rangle,\\
 D&=2,&P&=\{RL,RR\},\qquad
 Q=\{RLR^\infty,RRR^\infty\}.
\end{aligned}
\tag{AAR.55}
$$

Both sources lie in $\mathcal F_2$ and have $m=2$. The rays hit
$[RLR]$, $[RRR]$ and the left target's required $[RR]$, so (AAR.47)
holds. Both initial tables, in the displayed order, are $(5,6)$:
the relevant leaves are the alpha at $RLR$ and the alpha at $RRR$.
Both selected replies are branch at every update count. Nevertheless
the complete $P$ rows have different partitions at every common count.

Proof. At count zero both row exteriors are exactly
$\langle\alpha,\langle\square_{RL},\square_{RR}\rangle\rangle$.
In $t$ the hidden values are equal, while in $t'$ they are $Y$ and
$X$ and hence unequal. At count $k$, present-subtree transport gives
equal hidden values $\rho^k X,\rho^k X$ in the first source and
$\rho^k Y,\rho^k X$ in the second. Their left children are
$T_{k+1}$ and $T_k$; the supplied right clock gives their distinct
values $k+1$ and $k$. The hidden values therefore remain unequal.
The common exterior now has the same concrete $T_k$ at $L$ and the
same two holes. The table values in both sources are $(5+k,6+k)$
by (AAR.44). Even the paid calibration in Proposition 11.8 has the
same left subtree on both histories, so adding that acquired count
does not resolve the hidden equality. Thus neither the complete row
nor the full source is a function of these inputs. $\square$

Full-menu reply recovery also need not recover the source. In (AAR.55)
add $R$ to $P$; the same two rays attain Corollary 11.6's optimum for
$A_2$, yet the sources and partitions still differ. This obstruction
concerns finite sampled coordinates, not the full boundary-plus-scale
representation of Boundary Geometry Continuation IV, Theorem 113.5.
That already established injective representation has a richer input.

**Proposition 11.10 (finite initial storage and the count boundary).**
For fixed $D,P,Q$, every initial entry on $\mathcal F_D$ belongs to
$\{1,\ldots,2D+3\}$. Therefore the number $N_Q$ of attained initial
tables is finite and at most $(2D+3)^{|Q|}$, and lossless table storage
admits a fixed-width binary code of
$\lceil\log_2 N_Q\rceil$ bits. This is an attainable finite-family
bound for storing this table, not an arbitrary-encoder optimum for
the selected-reply task.

Proof. Every original leaf has depth between one and $D+1$;
$1\le s(a)+e\le2(D+1)+1$. There are finitely many trees in
$\mathcal F_D$, which can be generated by finite recursion on their
height, and the ray entries are computable on each. Enumerate the
distinct tables to obtain the stated code. A lossless fixed-width
encoding of $N_Q$ different tables requires at least that many code
values, giving the width for this particular lossless-storage task.
No claim that the reply consumer distinguishes all these tables is
needed or made. $\square$

For nonempty $Q$, the exact rebased tables
$\tau_k Z_Q(t)$ are pairwise distinct as $k$ grows. Retaining them
losslessly for $0\le k\le K$, even for one fixed initial tree,
requires at least $K+1$ code values. An exact materialized binary
count likewise grows with its value. If the count is supplied anew
as public task input, its acquisition, transmission and working
representation are separate from the bounded initial table; it is
not a free bounded cell. This does not impose an unbounded-storage
lower bound on every reply-only service: after $2D$ updates all
selected replies are branch, so a service concerned only with these
values can deliberately forget further increments. Exact unbounded
time recovery and saturated reply prediction are different tasks.

**Mathematical citation 11.11 (suppliers, literature and scope).** The
native additions here are the exact right-cylinder sampling criterion,
its left-child beta-versus-absence obstruction, the finite native
collision contexts and the attained laminar-cylinder ray count. Their
proofs are ordinary `repo-derived` mathematics. The following suppliers
fix their parameter meanings and their nontransfer boundaries.

| Supplier | Correspondence and limit |
| --- | --- |
| [NAR], §§11–12, especially (NAR.11.3), (NAR.11.6) and Proposition 12.8 | $h_u(qR^\infty)=J^c_q(u)$ with the actual blocking-leaf convention; canonical density interpretation and unit advancement are reused. Finite sampling geometry and (AAR.45) are the additional recovery interface. |
| §§2–3, 6, 9–10 of this volume | Local leaf calibration, $m$ advancement, native operand costs, complete retained-state accounting and arbitrary-encoding distinctions. The count supplied to Theorem 11.4 differs from §10's unknown-lag input; Corollary 11.6 is not §10's all-encoder frontier. |
| [READ], `readout`, `source_foundation` | The actual four replies use alpha = `true`, beta = `false`, left address bit = `false`, right = `true`. The general leaf-determination and off-leaf facts do not prove the new beta-to-branch profile collision; (AAR.49) checks that collision directly. |
| [DOR], `rightClock`, `right_clock_iterate`, `right_clock_readout` | The right-spine phase and the intervals for actual right-spine replies supply (AAR.54). An arbitrary ray in $[pR]$ need not be the right spine at $p$, and an absent left child has the extra case proved in Lemma 11.3. The epoch-supplied original-read service is a different consumer. |
| [NDP], `original_present_transport`, `original_prefix_locality` | Same-source evolution at a reached leaf and finite-depth response dependence. Originally absent positions are handled by (AAR.46), not by assuming they have a transported subtree. |
| [ACPD], `cutExterior`, `actualPartition`, `literalRecord`, `canonicalRow_record_iff` | The counterexample compares entire literal exteriors and the hidden equality partition. Selected constructor replies do not provide that partition. |
| [Native Cross-Epoch Relations, §6](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CROSS_EPOCH_RELATIONS.md#6-exactly-which-relative-times-the-input-determines) | Its consistent complete-record support tests and common-source constraints concern richer input. An acquired count used here is not inferred from an unacquired cross-row equality or from graph connectivity. |
| [Boundary Geometry Continuation IV, §113](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_IV.md#113-the-original-tree-boundary-kernel-acquired-scale-and-initial-cut-rows) | Full canonical measure plus scale is already injective. (AAR.44) samples its logarithmic scaled density; the finite samples do not supply its full value, scale or acquisition for free. |

The elementary same-input/different-output argument is a zero-error
separation principle. Related primary literature is
[Charpenay, Le Treust and Roumy, *Optimal Zero-Error Coding for Computing
under Pairwise Shared Side Information*, arXiv:2211.03649v2,
Definitions II.1 and IV.5, Theorem IV.8](https://arxiv.org/html/2211.03649v2).
Their characteristic graph joins sources separated by a compatible
query, and their full-support result groups vectors of task responses.
Those are useful correspondences to a declared recovery target. Their
rate theorem uses i.i.d. blocks, a distribution and expected prefix-code
length; none is a hypothesis here. No asymptotic coding theorem supplies
the geometric cylinders, the actual sources (AAR.49), or a sharp
arbitrary-encoder bit price for this task. The finite-cylinder count
uses the elementary laminar prefix structure, with its proof above.
Neither it nor the reuse of boundary coordinates claims worldwide
originality, new Lean verification or a physical spacetime law.

**Open problem 11.12 (remaining recovery obligations).** The criterion
settles a fixed public ray table and a finite literal-value menu on
$\mathcal F_D$, uniformly over supplied authentic counts. It does not
settle the all-source optimum over arbitrary retained encodings,
source-dependent ray selection with charged selection information,
unknown future menus, complete-row acquisition costs, or the recovery
of all hidden equality and full source structure. Exact clock and
boundary relations still require genuine acquisition and a common
history. The general programme of mutually recovering spatial,
temporal, boundary and memory descriptions remains open.

## 追加锚（本行以下为增补区）
## 12. The native spatial quotient for arbitrary retained prediction codes

**Definition 12.1 (known menu, complete export and supplied count).**
Fix $D\ge1$, the actual initial family $\mathcal F_D$ and a public
$P\subseteq A_D$ from Definition 11.1. Write

$$
 S=R^{-1}P:=\{q:Rq\in P\},\qquad
 \mathcal H_P(t)(k)=V_P(\rho^k t),\qquad
 H_P=\max\bigl(\{0\}\cup\{s(p):p\in P\}\bigr).
\tag{AAR.56}
$$

Here $R^{-1}$ removes the first letter; it is not an inverse source
operation. In particular $S$ may contain the empty word, although $P$
never does. The requested output is the vector of four-valued replies,
including absent, at the supplied count $k$. Repeated requests at the
same count have the same required value. Nested addresses are allowed.

An encoder may use a genuinely acquired initial tree $t$, or genuinely
acquired sufficient data about it, before exporting an effective code
$E(t)$ with finite attained alphabet. It exports before $k$ is supplied.
The entire accessible source dependence at handoff is this code: every
other accessible field is a fixed function of it and public $D,P$.
Definition 1.3 applies to selectors, sample identities, operands,
pointers, allocation distinctions, latches, transcripts, prior outputs
and control as well as to explicitly named registers. Acquisition,
local work, code installation, temporary storage, clearing and export
have their separate costs from Definition 1.4. A semantic function of
the initial tree is not a free source-aware table.

The later decoder receives only $E(t)$, public $D,P$, and an authentic
$k\ge0$ identifying the same-root, same-register continuation
$\rho^k t$. It has no new Read or clock. Correctness is uniform over
all $t\in\mathcal F_D$ and all such $k$. The optimum below counts
attained retained code values, or their fixed-width binary names. It
does not minimize the resources of obtaining or using those names.

This is the arbitrary-encoder component of Open problem 11.12 for its
specified initial family, declared menu and supplied counts. The
fixed-public-ray optimization of Theorem 11.4 and Corollary 11.6 keeps
its original interface. Unknown menus, acquisition of unknown lags,
complete rows, hidden equality, full-source recovery and physical time
remain different targets.

**Definition 12.2 (a finite spatial statistic).** For a finite tree $u$
and an address $q$, define two integers $b_q(u),c_q(u)$ by inspecting
only the initial path toward $q$:

$$
 (b_q,c_q)(u)=
 \begin{cases}
 (0,0),&q\text{ is a branch of }u,\\
 (2,1),&q\text{ is an alpha leaf of }u,\\
 (1,0),&q\text{ is a beta leaf of }u,\\
 (s(r)+2-e(u|_a),\ \mathbf1_{r\text{ ends with }R}),
   &q=ar\text{ is absent, }a\text{ its blocking leaf},\ r\ne\varepsilon.
 \end{cases}
\tag{AAR.57}
$$

The root is always present, so the last case never applies to the empty
address. Set

$$
 \Sigma_P(t)=\bigl((b_p(t),c_p(t))\bigr)_{p\in P}.
\tag{AAR.58}
$$

The statistic records neither the identity of a blocking leaf nor its
whole subtree. It retains its weighted distance only to the extent
needed by the selected address, together with the alpha-stage flag.
Its coordinates share one actual initial tree; their possible values
are not postulated to be independently attainable.

**Theorem 12.3 (spatial classification and the sharp finite horizon).**
For every finite $u$, address $q$ and $k\ge0$, let $(b,c)=(b_q,c_q)(u)$.
Then

$$
 \operatorname{readout}(q,\rho^k u)=
 \begin{cases}
 \mathrm{branch},&k\ge b,\\
 \beta,&b\ge1,\ k=b-1,\\
 \alpha,&c=1,\ k=b-2,\\
 \mathrm{absent},&\text{otherwise}.
 \end{cases}
\tag{AAR.59}
$$

On attained inputs $c=1$ implies $b\ge2$, so the alpha case has a
nonnegative count and is disjoint from the preceding cases. Consequently,
for $t,t'\in\mathcal F_D$,

$$
 \Sigma_P(t)=\Sigma_P(t')
 \quad\Longleftrightarrow\quad
 \mathcal H_P(t)=\mathcal H_P(t')
 \quad\Longleftrightarrow\quad
 \forall\,0\le k<H_P,\ V_P(\rho^k t)=V_P(\rho^k t').
\tag{AAR.60}
$$

Every target is branch for $k\ge H_P$, and $H_P\le2D$. For nonempty
$P$, $H_P$ is the least uniform all-branch count on this family. Empty
$P$ has one statistic and one trajectory, with $H_P=0$.

Proof. Reuse the guarded atomic reply law of
[Sparse Literal History Transport, Theorem 6.2 and (SLH.6.1)](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md#6-原纪元右射线前缀的准确联合取得),
also stated as the actual query table in
[Acquired Orbit Resource Frontier, Definition 8.2](RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_ORBIT_RESOURCE_FRONTIER.md#8-stationary-interval-reading-with-a-zero-origin).
For $T_n=\rho^n\alpha$ and nonempty $r$, an $R$-ending word gives
absent for $n<s(r)$, alpha at $s(r)$, beta at $s(r)+1$ and branch
thereafter. An $L$-ending word is absent also at $n=s(r)$, gives beta
at $s(r)+1$, and is branch thereafter. The last-edge reachability
guard is essential; an $L$-ending word does not acquire an alpha stage
merely because the formal residual index is zero. At the root the
three cases are alpha, beta and branch at indices $0,1,\ge2$.

An originally present branch stays branch. At an original leaf, the
supplied present-subtree transport gives $T_k$ or $T_{k+1}$ at that
address. If $q=ar$ is initially absent, transport applies at its
actually present blocking leaf $a$, giving $T_{k+e(u|_a)}$ there.
Applying the guarded law to the nonempty suffix $r$ proves (AAR.59)
and all four cases of (AAR.57). No subtree is transported from an
originally absent address.

The first count with branch reply is exactly $b$. The trajectory has
an alpha reply exactly when $c=1$, then only at $b-2$. Thus the whole
trajectory recovers both numbers, and (AAR.59) reconstructs it from
them. Taking the joint vector proves both directions of the first
equivalence in (AAR.60).

For an arbitrary finite $u$ the same formula gives
$b_q(u)\le s(q)+2$. In $t=\langle\alpha,v\rangle$, every target is
$Rq$, and its trajectory is the trajectory at $q$ in $v$ by
homomorphism. Hence

$$
 b_{Rq}(t)=b_q(v)\le s(q)+2=s(Rq).
\tag{AAR.61}
$$

This proves the uniform horizon, including all future counts beyond
the finite initial height bound. For $t_0=\langle\alpha,\alpha\rangle$
one has $b_{Rq}(t_0)=s(q)+2$ for every $q$, including $q=\varepsilon$.
Choose a target of maximum weight. Its reply at $H_P-1$ is beta, so
no smaller uniform all-branch count works. This source belongs to
every $\mathcal F_D$ in question. Since the tail from $H_P$ is fixed,
agreement below $H_P$ is exactly agreement at all counts. Repetitions
of a count add no distinction; repeating actual observations would
still incur their own costs. $\square$

**Theorem 12.4 (explicit factor of the canonical boundary data).**
For $p\in P$, put

$$
 x_p=h_t(pR^\infty)=J^c_p(t),\qquad
 y_p=h_t(aR^\infty)=J^c_a(t)\quad\text{when }p=aL.
\tag{AAR.62}
$$

The ray $pR^\infty$ lies in $[pR]$, including when $p$ itself ends
in $R$; $aR^\infty$ lies in the required parent-right cylinder.
On the actual attained boundary/readout data, the following function
is exactly (AAR.58):

$$
 \begin{aligned}
 b_p&=\max(0,s(p)+2-x_p),\\
 c_p&=\begin{cases}
 \mathbf1_{b_p\ge2},&p\text{ ends with }R,\\
 \mathbf1_{b_p\ge2\ \mathrm{and}\ y_p>x_p},&p=aL.
 \end{cases}
 \end{aligned}
\tag{AAR.63}
$$

Any public witness rays in the respective cylinders of Lemma 11.3
may replace the rays in (AAR.62); (AAR.63) still gives the same
statistic. For the displayed rays, the function can also be applied
to the canonical boundary-plus-scale representation by substituting

$$
 x_p=\log_\varphi\bigl(W(t)f_t(pR^\infty)\bigr),\qquad
 y_p=\log_\varphi\bigl(W(t)f_t(aR^\infty)\bigr).
\tag{AAR.64}
$$

Its attained image is in bijection with the selected complete future
trajectory image, with the maps given by (AAR.59) and recovery of
$(b_p,c_p)$ from the first branch and the presence of an alpha stage.
These are mutually inverse on those images, not recovery of the full
boundary representation from the task statistic.

Proof. By Lemmas 11.2–11.3, a reply is branch precisely when
$x_p+k\ge s(p)+2$, giving the first line of (AAR.63). For an
$R$-ending word, alpha occurs precisely at
$k=s(p)-x_p\ge0$, equivalent to $b_p\ge2$. For $p=aL$ the same
candidate time is alpha precisely when
$y_p+k>s(p)$, or $y_p>x_p$. This proves the second line as well. Lemma 11.3 gives the same
argument for any allowed witness rays, proving the claimed independence
of those choices. The exceptional equality case is concrete: a beta leaf at $a$ gives
$x_p=y_p=s(p)$, hence $(b_p,c_p)=(2,0)$ and an initially absent $p$.
An actual alpha at $p$ instead has $x_p=s(p)<y_p$, giving $(2,1)$.
Thus the alpha/absent ambiguity is preserved rather than discarded.
In fact, on this $L$-ending attained domain, $c_p=1$ can only mean
an alpha at count zero.

Equation (AAR.64) is exactly the canonical-density identity of
[NAR, Proposition 12.8], with $q=p$ and $q=a$. The density is its
canonical locally constant representative. Arbitrary almost-everywhere
representatives do not support this point evaluation. The logarithms
here return integer exponents on attained data; this semantic identity
neither grants an unacquired measure oracle nor claims an effective
point-evaluation algorithm for arbitrary real-number presentations.
The finite acquired $J^c$ values implement (AAR.63) without that extra
interface. Theorem 12.3 supplies the two inverse maps on attained
images. A finite prefix through $H_P$ already suffices to compute
both: take the first branch in that prefix and test for an alpha before
it. $\square$

**Definition 12.5 (menu geometry and a finite code grammar).** For a
finite set $S$ of words, possibly containing $\varepsilon$, define

$$
 \begin{aligned}
 S_L&=\{q:Lq\in S\},& S_R&=\{q:Rq\in S\},\\
 \delta(S)&=\begin{cases}
 1,&S\ne\varnothing\text{ and every }q\in S
                      \text{ starts with }L\text{ and has }|q|\ge2,\\
 0,&\text{otherwise}.
 \end{cases}
 \end{aligned}
\tag{AAR.65}
$$

Define the positive integer $n(S)$ recursively by

$$
 n(\varnothing)=1,\qquad
 n(S)=n(S_L)n(S_R)+2-\delta(S)\quad(S\ne\varnothing).
\tag{AAR.66}
$$

This recursion uses only the finite prefix tree of the public menu.
It is not a recursion over all possible sources. For nonempty $S$,
put $J=n(S_L)n(S_R)$. The codes $0,\ldots,J-1$ are ordered branch
pairs $i\,n(S_R)+j$. Code $J$ is alpha. Code $J+1$ is beta only
when $\delta(S)=0$. When $\delta(S)=1$ the beta source uses the
branch code whose left entry is the alpha code for $S_L$ and whose
right entry is the sole empty-menu code. Thus beta is identified with
one particular branch code, not given an additional name.

More explicitly, define $e_S(u)$ by

$$
 \begin{aligned}
 e_\varnothing(u)&=0,\\
 e_S(\langle u_L,u_R\rangle)
    &=e_{S_L}(u_L)n(S_R)+e_{S_R}(u_R),\\
 e_S(\alpha)&=J,\\
 e_S(\beta)&=\begin{cases}
 J+1,&\delta(S)=0,\\
 e_{S_L}(\alpha)n(S_R)+e_{S_R}(\alpha),&\delta(S)=1.
 \end{cases}
 \end{aligned}
\tag{AAR.67}
$$

The last three lines apply when $S\ne\varnothing$. In the overlap
case $S_R=\varnothing$, while $S_L$ is nonempty and does not contain
$\varepsilon$. A canonical representative $r_S(i)$ is defined by
reversing the branch-pair numbering, using $\alpha$ for the alpha
code, $\beta$ for the separate beta code when present, and $\alpha$
for the empty-menu code. All these are finite native trees.

**Theorem 12.6 (exact joint count, joint realization and minimum alphabet).**
For the entire source family and every public menu of Definition 12.1,
the minimum attained alphabet size of a sufficient arbitrary retained
code is

$$
 \boxed{\quad N(P,D)=n(R^{-1}P).\quad}
\tag{AAR.68}
$$

The quantity is independent of a larger admissible $D$ for the same
fixed menu. The code
$E_P(\langle\alpha,v\rangle)=e_{R^{-1}P}(v)$ attains it effectively.
Every one of its labels has a representative in $\mathcal F_D$, and
different labels require different replies at some common count below
$H_P$. For any finite effective $E$ on $\mathcal F_D$, the exact
sufficiency criterion is

$$
 E(t)=E(t')\ \Longrightarrow\ \Sigma_P(t)=\Sigma_P(t')
 \qquad(t,t'\in\mathcal F_D).
\tag{AAR.69}
$$

In particular the optimum fixed-width binary naming cost is
$\lceil\log_2 n(R^{-1}P)\rceil$, zero for the empty menu. No total
storage, computation or acquisition optimum is asserted.

Proof of the spatial count. For a general finite $S$, consider replies
at its words on every iterate of an arbitrary finite initial subtree.
Induction on the maximum word length proves that (AAR.67) identifies
exactly equal such trajectories, has all $n(S)$ labels attained, and
has representatives of height at most
$1+\max\{|q|:q\in S\}$ when $S$ is nonempty. The empty-menu case
has one label, represented by a height-zero alpha.

For a branch source, a root query, if selected, is constantly branch.
The other queries split exactly into the left and right suffix menus.
Homomorphism evolves both children with the same supplied count.
By the induction hypothesis, two branch sources therefore agree
exactly when their two child codes agree. Conversely, every ordered
pair of child codes is attained in the single actual tree obtained
by pairing their representatives. Thus the branch sector has exactly
$J=n(S_L)n(S_R)$ classes. This product is justified by a common
native realization, not by multiplying separate coordinate optima.

It remains to classify the two leaf sources and their possible overlap
with that branch sector. For any address $q$, Theorem 12.3 gives the
first branch times $s(q)+2$ on alpha and $s(q)+1$ on beta, including
the root. These differ, so the two leaves have different trajectories
whenever $S$ is nonempty. Alpha cannot agree with any branch source:
a root query distinguishes them immediately; for a nonempty query
$q=dr$, any initial branch has first branch time at most $s(r)+2$,
by its child and (AAR.57), strictly less than alpha's $s(q)+2$.

Beta also cannot agree with a branch if $\varepsilon\in S$, by the
initial root reply, or if $L\in S$, since beta gives absent there
initially and a branch has a present left child. If a selected word is
$Rr$, beta's first branch time is $s(r)+3$, whereas a branch source's
is at most $s(r)+2$. These observations exclude overlap whenever
$\delta(S)=0$.

If $\delta(S)=1$, every selected word is $Lr$ with $r\ne\varepsilon$.
Reuse $T_{k+1}=\langle T_k,T_{k-1}\rangle$ for $k\ge1$. On the beta
source, the reply at $Lr$ at count $k\ge1$ is the reply at $r$ in
$T_k$. It is the same reply on the branch
$\langle\alpha,\alpha\rangle$. At count zero both replies are
absent, since $r$ is nonempty. Thus beta agrees with that actual
branch at every selected word and count. The branch classes are
already distinct by their child codes, so this is precisely one
already counted class. It is the branch code specified in (AAR.67).
There are no other leaf/branch overlaps. Adding the leaf classes
therefore gives exactly $J+2-\delta(S)$.

The representatives are constructed at this same induction step:
use alpha, use beta only when it has a separate code, and pair every
ordered pair of child representatives. For maximum menu length $d$,
nonempty child menus have maximum length at most $d-1$, so their
representatives have height at most $d$; empty children use alpha.
Pairing has height at most $d+1$. This also covers $d=0$, when the
only nonempty menu is $\{\varepsilon\}$ and the branch representative
has height one. This proves attainment and the height assertion
along with both directions of the classification. In particular
$e_S(r_S(i))=i$ for every code.

Now put $S=R^{-1}P$. For nonempty $P$, its maximum suffix length is
at most $D-1$. Every representative $r_S(i)$ has height at most $D$,
so $\langle\alpha,r_S(i)\rangle\in\mathcal F_D$. Homomorphism
identifies the trajectories at $P$ in this paired source with those
at $S$ in its right subtree. The classification and Theorem 12.3
therefore identify exactly the same fibers for $E_P$, $\Sigma_P$ and
$\mathcal H_P$. Their attained images are mutually recoverable:
a code gives its representative and hence its statistic, while a
statistic gives the unique representative code with that statistic.
The finite grammar computes this inverse without enumerating all
initial sources. Each pair of distinct representatives is separated
before $H_P$. Both can be truthfully captured as stationary initial
sources and then undergo that very same number of actual substitutions;
the lower bound never switches source during a run.

Proof of sufficiency and optimality. The general factor principle is
already supplied by
[`target_family_minimal_quotient`](../../../D5/S3/ConceptDynamics/SufficiencyQuotient/TargetFamilyMinimalQuotient.lean):
take source $X=\mathcal F_D$, index $(p,k)\in P\times\mathbb N$, and
target $t\mapsto\operatorname{readout}(p,\rho^k t)$. Sufficiency
forces the kernel of $E$ to refine the joint-target kernel. The native
classification above identifies this latter kernel spatially, so it
is exactly (AAR.69). It forces different code values on all the
$n(S)$ representatives. This is the generic minimum-target argument
with the newly calculated native image, not a new general quotient
principle.

Conversely, (AAR.69) makes the target constant on each attained
$E$-fiber. Since $\mathcal F_D$ is a finite effectively generable
family and $E$ is effective with finite labels, these factors can be
made total computable: compute its finite attained code list and
assign the common statistic to each label, with a fixed default on
malformed inputs. This existence argument for arbitrary $E$ is not
the count construction. The optimal $E_P$ already has (AAR.67):
decode its index to $r_S(i)$, form its spatial statistic, and evaluate
(AAR.59). It does not enumerate all sources. Empty $P$ uses the
constant zero code and returns the empty vector. Finally a fixed-width
$b$-bit region has at most $2^b$ names, and the consecutive integer
codes have exactly the size in (AAR.68). This proves the binary-width
claim. $\square$

**Theorem 12.7 (literal, nested and disjoint consumers).** The recurrence
has the following attained values, for every admissible $D$:

| Public menu $P$ | Minimum labels | Canonical right-subtree representatives or count |
| --- | ---: | --- |
| $\varnothing$ | $1$ | $\alpha$ |
| $\{R\}$ | $3$ | $\alpha,\beta,\langle\alpha,\alpha\rangle$ |
| $\{RL\}$ | $5$ | $\alpha,\beta,\langle z,\alpha\rangle$ with $z\in\{\alpha,\beta,\langle\alpha,\alpha\rangle\}$ |
| $\{RR\}$ | $5$ | $\alpha,\beta,\langle\alpha,z\rangle$ with the same three $z$ |
| $\{RL,RR\}$ | $11$ | two leaves and all nine pairs of those three $z$ |
| $\{R,RL\}$ | $5$ | the five representatives for $\{RL\}$ |
| $\{RLL,RLR\}$ | $12$ | $\alpha$ and $\langle z,\alpha\rangle$ for all eleven representatives of $\{RL,RR\}$ |
| $\{RLL,RLR,RR\}$ | $35$ | two leaves and $11\cdot3$ branch combinations |

Every listed right subtree is used in the initial source
$\langle\alpha,v\rangle$, not supplied as a hidden decoder operand.
For a singleton $P=\{Rq\}$, let $m=|q|$ and let $\lambda(q)$ be
the number of $L$ letters among the first $m-1$ letters of $q$, zero
when $m\le1$. Then the general singleton value is

$$
 N(\{Rq\},D)=2m+3-\lambda(q).
\tag{AAR.70}
$$

Proof. For $S=\{\varepsilon\}$, both child menus are empty and
$\delta=0$, giving three codes. For $S=\{L\}$ or $\{R\}$ one child
has those three codes and the other has one, giving five. For
$S=\{L,R\}$ both have three, giving eleven. Adding $\varepsilon$
to $\{L\}$ does not add child constraints or alter its zero overlap
indicator, so the nested menu still has five. This equality is about
complete future replies; a single current reply at $RL$ would not
recover the same information.

For $S=\{LL,LR\}$ the left suffix menu is $\{L,R\}$, the right
one is empty, and $\delta=1$, giving $11+2-1=12$. In particular the
initial right subtrees $\beta$ and $\langle\alpha,\alpha\rangle$
are distinct but agree at both selected addresses at every count,
by the overlap argument of Theorem 12.6. They are represented by
one of the eleven branch combinations, not counted twice. At the
shallower address $RL$ these same initial sources instead have
$(b,c)=(2,0)$ and $(2,1)$: absent and alpha at zero, followed by
beta and then branch in both. This verifies that the flag cannot be
removed from the general spatial statistic.

For $S=\{LL,LR,R\}$ both suffix menus are nonempty, with counts
eleven and three; a right-starting target forces $\delta=0$, giving
thirty-five. More generally, whenever both $S_L,S_R$ are nonempty,
there are $n(S_L)n(S_R)$ jointly attained branch combinations and
two further leaf classes. This explains why disjoint selected
addresses do not justify multiplying their separate whole-source
optima: for $\{RL,RR\}$ that multiplication would give $25$, whereas
the actual common-source count is $11$.

For the singleton formula, start at the terminal suffix menu
$\{\varepsilon\}$ with value three and ascend its $m$ edges. Each
step adds two, except that an $L$ edge with a nonempty remaining
suffix has $\delta=1$ and adds only one. These are exactly the
$\lambda(q)$ edges in (AAR.70). The representative construction of
Theorem 12.6 supplies all claimed distinctions with the required
height bounds. Thus $D=1$ has only the empty menu and $\{R\}$,
with values one and three, respectively. $\square$

**Theorem 12.8 (strict compression of a valid public ray table).**
For $P=\{R\}$ the single ray $R^\infty$ satisfies Theorem 11.4.
On $\mathcal F_D$ its attained raw scores are exactly

$$
 \{2,3,\ldots,2D+3\},\qquad N_{\{R^\infty\}}=2D+2.
\tag{AAR.71}
$$

Their prediction classes are exactly the three cells
$\{2\},\{3\},\{4,\ldots,2D+3\}$. They can be retained as three
names, although losslessly retaining the whole ray score requires
$2D+2$ names.

Proof. The score is $2+c(v)$ for $t=\langle\alpha,v\rangle$.
If the rightmost leaf of $v$ has depth $d\le D$ and label bit $e$,
then $c(v)=2d+e$. Every $d\in\{0,\ldots,D\}$ and $e\in\{0,1\}$
is attained by a right comb of depth $d$ with alpha side leaves and
that terminal label. These are actual height-bounded right subtrees,
so the scores are exactly the consecutive integers in (AAR.71).
Equation (AAR.63) at $p=R$ reads $b=\max(0,4-x)$: score two
means an initial alpha, three a beta, and every larger score a
branch. These give three different trajectories, proving the stated
compression. At $D=1$ the raw count is already four while the task
count is three, although both happen to have two-bit fixed-width
names. A smaller label alphabet need not even lower the rounded
binary width in every instance. $\square$

Corollary 11.6 minimizes the number of fixed public ray coordinates,
not their attained joint alphabet. Equations (AAR.66)–(AAR.68)
minimize an arbitrary complete retained alphabet for the declared
prediction task. A ray chosen using the source has its identity in
that alphabet unless it is already a function of the exported label.
Its actual operand and acquisition still have their own prices. Thus
(AAR.71) neither invalidates the ray theorem nor provides a free
source-dependent sampling procedure.

**Theorem 12.9 (paid acquisition and complete handoff).** Suppose a
stationary initial $\mathcal F_D$ source is available for capture.
For nonempty $P$ there is a native literal acquisition followed by
export of exactly the code in Theorem 12.6. A sufficient full-tree
acquisition has the explicit successful-capture bounds

$$
 T\le2^{D+1}+1,\qquad
 A\le D\,2^{D+1}+3,\qquad Q\le D+1.
\tag{AAR.72}
$$

Alternatively one may acquire a sufficient fixed public ray table by
Proposition 11.8 and then compress it by Theorems 12.4 and 12.6,
with that proposition's acquisition bounds. These are sufficient
constructions, not claims of minimal acquisition cost.

Proof. Read $L$ as alpha, then traverse the right subtree using full
literal addresses from the root. Read each visited node once and
visit both children precisely when the reply is branch. A branch
reply at depth $D+1$, an unexpected absence, or an unsuccessful
alpha guard rejects the capture. Finally reread $L$ as alpha. The
existing equal-leaf rigidity supplier excludes every update between
the two successful guards. The acquired right subtree is therefore
one actual $v$ and the complete initial source is
$\langle\alpha,v\rangle$ at the final guard. No snapshot or subtree
port was used. The traversal has at most $2^{D+1}-1$ right-subtree
nodes plus the two guards. At relative depth $j$ in that subtree it
submits at most $2^j$ words of length $j+1$. Hence its total literal
length is bounded by

$$
 2+\sum_{j=0}^D(j+1)2^j=D\,2^{D+1}+3,
$$

proving (AAR.72). Acquisition buffers, the temporary tree, traversal
state, local work and any failed attempt remain separately charged.
This conditional capture does not promise an $\mathcal F_D$ version
after an unprotected writer has already changed the initial left
alpha. A failed guard supplies no source with the required premise.

Compute (AAR.67) from this genuinely acquired tree. Use a fixed
output-region identity with the public fixed width
$\lceil\log_2 n(S)\rceil$, and clear or retract all other accessible
source dependence before handoff. In particular discard the temporary
tree, descriptors, selectors, reply latches, buffers, traversal and
retry states, old outputs and distinguishing allocation metadata.
The construction realizes Definition 12.1 when the host supports
this complete export; an accessible surviving distinction enlarges
the retained state. Inaccessible physical remnants still incur their
storage cost. For the ray-table alternative, (AAR.63) computes the
statistic; its unique code is found by the finite representative
grammar of Definition 12.5, since Theorem 12.6 identifies exactly its
fibers. Public codebooks, their construction and lookup work are not
free resources. Empty $P$ needs only the constant code and empty
output, so the task requires no source acquisition.

After export, every supplied count is interpreted relative to that
validated capture and its authentic continuation, even if the source
advanced during encoding. The decoder may replace $k$ by
$\min(k,H_P)$ for this task alone. Acquisition, authentication,
transmission and representation of the supplied count are separate
inputs and costs; the code does not provide them. The predicted
values create no observation events at their addresses. A service
requiring actual common-version receipts must acquire and validate
those separately. $\square$

**Mathematical citation 12.10 (reuse, attribution and recovery limits).**
The substantive native assertions are (AAR.57)–(AAR.60), the concrete
boundary factor (AAR.63), the unique leaf/branch overlap (AAR.65),
and its exact joint count with height-bounded representatives. They
are ordinary `repo-derived` deductions. Generic behavioral equivalence
and minimum sufficient coding are reused; no new kernel verification
or worldwide originality is claimed.

The source correspondences are as follows. [NAR, §§11–12], especially
its Proposition 12.8, supplies absence-safe $J^c$, unit advancement
and the canonical density; it does not count this task's fibers.
[READ] fixes the four replies and literal addresses, and [NDP]'s
`original_present_transport` and `original_prefix_locality` supply
same-source transport and finite-depth dependence. [DOR]'s
`right_clock_iterate` and `right_clock_readout` fix the right-ray
parameter meanings. The guarded atomic table, including its
$L$-ending absence case, is reused from SLH Theorem 6.2 and AOF
Definition 8.2. SLH §§6.2–6.3 optimize paid original right-prefix
acquisition from a certified later version; AOF §§8–9 optimize calls
and peak literal length for an unknown atomic age in a supplied
interval. Neither objective is the retained-alphabet objective here.

The static target-family supplier in Theorem 12.6 applies directly
because $(p,k)$ is an index, requiring no endomap on $\mathcal F_D$.
The existing
[`canonical_minimal_realization`](../../../D5/S3/ObserverMemory/Realization/CanonicalMinimalRealization.lean)
and
[`predictive_memory_minimal_quotient`](../../../D5/S3/ObserverMemory/RefinementClosure/PredictiveMemoryMinimalQuotient.lean)
require an actual endomap and exact update/readout factorization.
They can be interpreted on all finite native trees with update $\rho$
and output $V_P$, before restricting initial captures. The original
family $\mathcal F_D$ is not $\rho$-invariant: its initial left alpha
already becomes beta after one update. Likewise the finite-carrier
premise of
[`finite_future_maximal_congruence`](../../../D5/S3/Observer/Separation/FiniteFutureCongruence.lean)
cannot be supplied by pretending that $\rho:\mathcal F_D\to\mathcal F_D$.
The native horizon in Theorem 12.3 instead directly proves which
finite prefix determines the trajectory. Saturation concerns selected
replies, not a bound on future-tree height or recovery of an unknown
count. The horizon also makes the set of all suffixes of attained
trajectories finite and shift-closed: each trajectory has at most
$H_P+1$ different suffixes, and shifting a suffix produces another
one. That is a lawful carrier for the finite congruence supplier,
without regarding $\mathcal F_D$ as a source endomap carrier.

The bounded primary-literature correspondences are these:

| Primary statement | Object, assumption and objective correspondence |
| --- | --- |
| [Rabin and Scott, *Finite Automata and Their Decision Problems*, Theorem 2 and Corollary 2.1](https://www.cse.chalmers.se/~coquand/AUTOMATA/rs.pdf) | Equality under all continuation tests gives the least-state accepting automaton; the authors attribute this relation and corollary to Nerode. Continuation tests correspond here to supplied substitution counts and selected reply coordinates. Their tape languages and binary acceptance are not the native tree family, four-valued reply function or spatial recurrence (AAR.66). |
| [Angluin, *Learning Regular Sets from Queries and Counterexamples*, §2.1 and Theorem 1](https://people.eecs.berkeley.edu/~dawnsong/teaching/s10/papers/angluin87.pdf) | Rows of a closed, consistent observation table represent candidate states and columns distinguishing experiments; a consistent inequivalent acceptor must have more states. Here a finite horizon yields complete distinguishing data for a specified native task. No membership/equivalence teacher is supplied, and no learning-time bound or acquisition algorithm is imported from that theorem. |
| [Charpenay, Le Treust and Roumy, *Optimal Zero-Error Coding for Computing under Pairwise Shared Side Information*, Definitions II.1 and IV.5, Theorem IV.8](https://arxiv.org/html/2211.03649v2) | With source $t$, side input $k$ and task $V_P(\rho^k t)$, different response vectors induce the analogous characteristic-graph separation. One can restrict side inputs to the finite horizon here. Their full-support response-vector grouping is background; their i.i.d. distribution, expected prefix-code length and asymptotic rate objective are not the finite worst-case number of retained names. Their theorem does not give the native overlap or height-bounded joint realizations. |

Thus the minimum-target principle alone would leave the native question
unanswered: it names a quotient without supplying (AAR.57), deciding
its leaf/branch identifications, or constructing all of its joint
classes. The additional spatial analysis supplies those missing facts.
Its recoverability is exactly between the task statistic, its minimal
names, and the selected complete future trajectory on their attained
images. The canonical boundary and the acquired initial tree map to
that statistic; they need not be recoverable from it. The twelve-class
example already merges distinct trees, and Counterexample 11.9 retains its
hidden-equality obstruction. Counts after saturation are also merged
by the reply output. The rest of Open problem 11.12 and the broader
space, time, boundary and memory programme have not been identified
with this supplied-count prediction problem.

## 追加锚（本行以下为增补区）

## 13. Exact native acquisition of one declared future literal

**Definition 13.1 (source-blind stationary acquisition).** Fix public
$D\ge1$ and $p\in A_D$, and write $n=|p|$. The initial source ranges over
exactly Definition 11.1's family

$$
 \mathcal F_D=\{\langle\alpha,v\rangle:\operatorname{height}(v)\le D\},
 \qquad p\text{ starts with }R,\qquad 1\le n\le D.
\tag{AAR.73}
$$

Its shape and all nonpublic labels are unknown. During acquisition the
one initial register is promised stationary. An encoder $\mathsf A$ is
a deterministic effective procedure, with the same source-blind initial
state on every member of this family. Public $D,p$ and the family promise
are allowed. Its only source operation is an actual
$\operatorname{Read}_t(w)$ for an arbitrary finite original-root word
$w\in\{L,R\}^*$. All four replies have their meanings in Definition 1.1.
There is no restriction to prefixes of $p$, no query-depth restriction,
and no subtree, age, navigation, reset, source-identity or pre-acquired
boundary input. No $\rho$ operation occurs during acquisition.

The encoder must terminate for every $t\in\mathcal F_D$. Its complete
accessible source dependence at handoff is $E_{\mathsf A}(t)$, including
any surviving selector, operand, latch, buffer, transcript, control,
length or allocation distinction. A single effective passive decoder
must satisfy

$$
 \mathsf D(E_{\mathsf A}(t),D,p,k)
       =\operatorname{readout}(p,\rho^k t)
 \quad(t\in\mathcal F_D,\ k\in\mathbb N).
\tag{AAR.74}
$$

Here $k$ is supplied authentically for the same root, register and initial
version. It is supplied after acquisition and is not inferred by the
code. The decoder makes no fresh source Read. The code need not identify
the source, retain a lossless ray table, or use the minimum alphabet of
§12. It must serve every supplied count, not just the current reply.

Let $T_{\mathsf A}(t)$ count actual initial Reads, including constant,
repeated and absent calls. Let $A_{\mathsf A}(t)$ and $Q_{\mathsf A}(t)$
be their total submitted letters and peak word length, as in
Definition 1.4. Put

$$
 C_D(p)=\min_{\mathsf A}\max_{t\in\mathcal F_D}T_{\mathsf A}(t),
 \qquad
 Q_D(p)=\min_{\mathsf A}\max_{t\in\mathcal F_D}Q_{\mathsf A}(t),
\tag{AAR.75}
$$

where both minima range over all encoders satisfying this contract.
These are separate objectives. Installation, local computation, working
and retained memory, clearing, authentication and the representation of
$k$ are separate resource coordinates. In particular, a public promise
of stationarity is not a paid validation protocol. This contract concerns
one address declared before acquisition. It supplies neither a later
unknown menu nor an unknown lag.

**Definition 13.2 (an acquired path descriptor and its predictive factor).**
Let $p_i$ be the length-$i$ prefix of $p$, with $p_0=\varepsilon$.
Write $\lambda_0=\alpha$, $\lambda_1=\beta$ and retain the weight $s$
of (AAR.42). There are two kinds of path descriptor:

- $B$: the address $p$ is initially branch;
- $(j,e)$: the first leaf on the path toward $p$ is at $p_j$, with
  actual label $\lambda_e$, where $1\le j\le n$ and $e\in\{0,1\}$.

The root is known branch, so there is no candidate at index zero.
Denote this mathematical descriptor by $\partial_p(t)$. Its existence
is a property of $t$, not an acquisition operation. For a descriptor
actually obtained from Reads, define

$$
 \Gamma_p(B)=(0,0),\qquad
 \Gamma_p(j,e)=
 \begin{cases}
 (2-e,1-e),&j=n,\\
 (s(r)+2-e,\mathbf1_{r\text{ ends with }R}),&p=p_jr,\ j<n.
 \end{cases}
\tag{AAR.76}
$$

**Proposition 13.3 (passive decoding and the distinction acquisition must
resolve).** On the whole family (AAR.73),
$\Gamma_p(\partial_p(t))=(b_p(t),c_p(t))$ from Definition 12.2.
Consequently the effective decoder (AAR.59), applied to this pair and
supplied $k$, satisfies (AAR.74). Different descriptors may have the same
predictive factor; for each fixed leaf position, however, its two labels
have different factors and different future trajectories.

Proof. An initially present branch persists. At a reached leaf $p_j$,
same-source present-subtree transport supplies $T_{k+e}=\rho^{k+e}\alpha$.
At $j=n$ the root replies of this tree give the first case of (AAR.76).
At $j<n$ the guarded atomic law of SLH §§35–38 applies to the nonempty
suffix $r$. Its first branch count is $s(r)+2-e$; an alpha stage occurs
exactly when the last letter is $R$. This is precisely (AAR.57)–(AAR.59).
It does not transport a subtree from an absent address, and for a
left-ending suffix it does not convert absence at a formal residual
index zero into alpha.

For $j=n$ the two initial replies are already different. For $j<n$ put
$d=s(r)$. At the common count $k=d+1$, the source with label alpha at
$p_j$ gives beta at $p$, while the source with label beta gives branch.
Thus the label matters even when the target was absent on both sources.
The collision between different positions is real: for $p=RLL$,
$t=\langle\alpha,\beta\rangle$ has descriptor $(1,1)$, whereas
$t'=\langle\alpha,\langle\alpha,\alpha\rangle\rangle$ has descriptor
$(2,0)$. Both give $(b,c)=(3,0)$ and the trajectory
absent, absent, beta, branch, branch, $\ldots$. Both sources are actual
members of every admissible $\mathcal F_D$ for this $p$. $\square$

The arbitrary-code minimum is already supplied by Theorems 12.6–12.7.
For $p=Rq$, it has $2n+1-\lambda(q)$ values, where $\lambda(q)$ counts
left letters before the last letter of $q$. It is not necessary to
reconstruct that quotient to acquire a sufficient code. The descriptor
has $2n+1$ possible values and may over-refine it. After acquisition one
may instead retain (AAR.76), or its minimum name from §12, with local
encoding and complete clearing separately charged. Theorem 12.4 gives
its factorization through sufficient acquired boundary coordinates.
It does not supply those coordinates without Reads.

**Theorem 13.4 (an attaining native acquisition).** There is a single
source-blind encoder for each public $D,p$ satisfying (AAR.74) with

$$
 T\le h(n):=\lceil\log_2(n+1)\rceil,\qquad
 A\le n h(n),\qquad Q\le n.
\tag{AAR.77}
$$

It uses only actual literal Reads of prefixes of $p$ and terminates on
every source in the full family, independently of its off-path shape.
There is no separate initial target probe in this construction.

Proof. Search the ordered candidate leaf positions $[1,n]$. At a
nonempty remaining interval $[a,b]$, take
$i=\lfloor(a+b)/2\rfloor$ and submit the whole word $p_i$.
A label reply acquires $(i,e)$ and terminates. A branch reply excludes
all leaf positions at or below $i$ and keeps $[i+1,b]$. An absent reply
keeps $[a,i-1]$. Branch at $p_n$ terminates with $B$; equivalently,
exhaustion of all leaf candidates leaves only $B$.

To check the last rule, regard $B$ as an additional possible position
$n+1$, always above the searched keys. Its prefix replies are all
branch. An absent reply discards this possibility. On an actual source,
a finite leaf index is never removed except by acquiring it. Therefore
an empty interval on an actual run can only leave $B$. Every unacquired
leaf candidate is a position in one interval. A nonterminal comparison
leaves at most $\lfloor m/2\rfloor$ of the previous $m$ candidates.
The ordinary successful-search bound is consequently

$$
 H(0)=0,\qquad H(m)\le1+H(\lfloor m/2\rfloor),\qquad
 H(m)\le\lfloor\log_2m\rfloor+1
       =\lceil\log_2(m+1)\rceil\quad(m\ge1).
\tag{AAR.78}
$$

The one possible unsuccessful search is for $B$ beyond all keys; its
path also obeys this height bound. Each query is a real finite literal
of length at most $n$, giving the other bounds. The actual source stays
fixed throughout, so all comparisons refer to its one boundary. No
queried prefix is repeated. Leaf acquisition or branch certification,
followed by Proposition 13.3, proves correctness for all future counts.

One complete export is a fixed public encoding of $B$ and $(j,e)$ in
$\lceil\log_2(2n+1)\rceil$ bits. Use a fixed output region and clear or
retract all other accessible source-dependent state, including query
control, operands, latches, histories and allocation distinctions.
This is the complete-interface convention of Definitions 1.3 and 12.1;
its storage, work and clearing costs are additional. Alternatively the
whole finite acquisition record can be included in $E$, with its actual
retention cost. Neither choice treats an accessible selector as free.
The resulting decoder uses only this genuinely acquired code, public
$p,D$, and the supplied count. $\square$

The capacity calculation is the ordinary ordered successful search
already used in CNA Theorem 17.1. Its use here starts directly on the
$n$ possible leaf positions below the known root. SLH Theorem 36.1's
initial target probe remains a valid construction for its stated
interface; that extra probe is not intrinsic to Definition 13.1.

**Lemma 13.5 (bounded-family actual-label necessity).** Every correct
encoder of Definition 13.1 must, on each source whose descriptor is
$(j,e)$, actually read $p_j$ before terminating. If $p$ is branch, its
terminal record must contain either $(p,\mathrm{branch})$ or a nonabsent
reply at a strict descendant of $p$.

Proof. In the leaf case change only that actual leaf label, obtaining
$t'$. It is still in $\mathcal F_D$: the left alpha, shape and height
are unchanged, and $p_j$ starts with $R$. The replies of $t,t'$ are
identical at every finite address except $p_j$. Their ancestors are the
same branches, every strict descendant of that leaf is absent on both,
and all other subtrees are identical. If the run on $t$ omitted $p_j$,
determinism from the common initial state would give the identical
queries, replies, local decisions, stopping time and complete retained
state on $t'$. Proposition 13.3 gives different future replies at one
common authentic count. One passive decoder on this identical input
cannot be correct for both.

For the branch case, suppose neither stated observation occurred.
Replace the entire subtree at $p$ by alpha. This reduces height and
preserves the prescribed initial left child, hence is still allowed.
The query at $p$ never occurred; every queried strict descendant was
absent and remains absent; every query elsewhere has the same reply.
The identical-run argument now contradicts branch versus alpha at
count zero. Both modifications compare two complete stationary
executions; neither changes the source within an execution. These are
the SLH Lemma 43.2 evidence arguments, with their required closure under
leaf relabeling and subtree pruning checked inside (AAR.73). $\square$

In particular, equal desired codes for two boundary positions do not
waive label acquisition. In Proposition 13.3's collision the first
source must be read at $R$ and the second at $RL$: flipping either
actual leaf changes that source's future. Equality of compressed
outputs allows erasure after acquisition, not a source-dependent
initial choice of which information to ignore.

**Definition 13.6 (a bounded native witness family).** For a finite word
$a$ and a tree $u$, let $C_a[u]$ be the tree obtained by placing $u$ at
$a$, making every strict ancestor of $a$ a branch, and placing alpha at
each sibling not on this path. In particular $C_\varepsilon[u]=u$.
Define the actual trees

$$
 t_{j,e}=C_{p_j}[\lambda_e]\quad(1\le j\le n,\ e\in\{0,1\}),
 \qquad t_* = C_p[\langle\alpha,\alpha\rangle],\qquad
 \mathcal K_p=\{t_{j,e}\}\cup\{t_*\}.
\tag{AAR.79}
$$

Because $p$ starts with $R$, every one has initial left child alpha.
The right-subtree heights are $j-1$ and $n$, respectively. Thus
$\mathcal K_p\subseteq\mathcal F_D$ for every $D\ge n$, without
padding above a submitted query. Their descriptors are exactly all
$2n+1$ possibilities of Definition 13.2, all simultaneously realized
in this same public family.

**Lemma 13.7 (classification of every literal on the witness family).**
For $1\le i\le n$, the prefix query $p_i$ has the following replies:

| Source condition | Reply at $p_i$ |
| --- | --- |
| $j<i$ | absent |
| $j=i$ | $\lambda_e$ |
| $j>i$, or source $t_*$ | branch |

All other finite words are exhausted by these cases:

1. The empty word gives branch, $L$ gives alpha, and a strict extension
   of $L$ gives absent on every witness.
2. A word first diverging from $p$ at position $i$, $2\le i\le n$,
   has the form $p_{i-1}\overline{p[i]}z$, where the bar exchanges $L,R$.
   For $z=\varepsilon$ its reply is alpha when $j\ge i$ or on $t_*$,
   and absent when $j<i$. For nonempty $z$ its reply is always absent.
3. A strict extension $pz$ gives alpha exactly when its source is $t_*$
   and $|z|=1$. In every other case it gives absent.

Consequently a word can distinguish the two labels of at most one
pair $\{t_{j,0},t_{j,1}\}$: it does so exactly when it equals $p_j$.
After discarding that possible pair, all other intact pairs receive at
most two different replies, each reply common to both labels of its
pair. The statement includes arbitrarily deep, off-path, empty and
repeated words.

Proof. Before $p_j$ the constructed path consists of branches; at it
there is the stated leaf, and below it all positions are absent. At a
first divergence the sibling exists exactly when its parent was before
the terminal leaf, namely $j\ge i$, and that sibling is alpha. Its own
strict descendants are absent. The terminal witness instead continues
the path through $p$ and has just two alpha children there. These facts
give the table and the three cases by literal navigation in the actual
trees. Every word is a prefix, first diverges, or strictly extends $p$;
the initial left branch and the root account for the remaining cases.
No property of an imagined comparison oracle is used. $\square$

**Theorem 13.8 (exact all-native-address Read price).** For every admissible
$D,p$,

$$
 \boxed{C_D(p)=\lceil\log_2(|p|+1)\rceil.}
\tag{AAR.80}
$$

The lower bound holds against every deterministic adaptive encoder of
Definition 13.1, with arbitrary finite word queries and arbitrary
complete retained codes, including codes that merge boundary positions.
It does not require the source shape to be known.

Proof. Theorem 13.4 gives attainment on the entire family. For the lower
bound restrict any proposed encoder to the $2n$ leaf witnesses in
(AAR.79), keeping its real queries and control. At a common truthful
transcript call a pair intact if both $t_{j,0}$ and $t_{j,1}$ remain
consistent and $p_j$ has not been queried. Lemma 13.5 forbids termination
while even one intact pair remains. Both sources of such a pair produce
the same complete acquired state so far and require different future
answers at a common count.

With at most $h$ Reads remaining, at most $2^h-1$ intact pairs can be
handled. This is induction on $h$, applied to any subset of the pairs
consistent with a common transcript. At $h=0$ there can be no pair. At
the next query, Lemma 13.7 allows at most one pair to be hit at its
actual leaf. Every other pair remains intact and belongs wholly to one
of at most two reply groups. Each group must be solvable in $h-1$
Reads, so their total size is at most $2(2^{h-1}-1)$. Adding the possible
hit pair gives $2^h-1$. A query with a constant reply, or one that does
not hit a candidate, cannot increase this capacity.

This induction is about actual source-consistent executions. At each
node the candidate trees are fixed members of the initial family and
realize the entire preceding transcript together, not separately chosen
answers. A selected nonempty branch retains those actual witnesses.
An early halt fails on a retained pair. Infinite local computation at a
reachable node fails termination on a retained actual source. Otherwise
the next Read or halt is common by determinism. Thus adaptivity, local
work and arbitrary growing state introduce no extra source input.
Since $\mathcal F_D$ is finite and every run terminates, each admissible
encoder has a finite worst Read count. Applying the capacity induction
at its common initial state yields $n\le2^h-1$, or
$h\ge\lceil\log_2(n+1)\rceil$.

In particular, the proof never assumes distinct future codes for all
$n$ leaf positions. It uses the separate indispensable label pair at
each position. The four replies supply two successful label outcomes
at a hit and at most two continuations for the other pairs; treating
them as four arbitrary equally powerful branches loses this constraint.
CNA's successful-search capacity is reused, but its unbounded-padding
realization is replaced by Lemma 13.7's fixed bounded witnesses.
$\square$

**Corollary 13.9 (exact peak and nonadaptive prices).** Under the same
contract,

$$
 \boxed{Q_D(p)=|p|,}\qquad
 \boxed{C_D^{\mathrm{nonadaptive}}(p)=|p|.}
\tag{AAR.81}
$$

One common strategy attains both the call minimum (AAR.80) and the peak
minimum. Nonadaptive here means a fixed source-independent ordered list
of literal queries, optionally stopped when the acquired information
already suffices; it does not allow reply-dependent address selection.

Proof. The two actual sources $t_{n,0},t_{n,1}$ have different replies
only at the literal $p$ and require different answers at $k=0$. Both
executions must therefore eventually query that literal, of length $n$.
This proves the peak bound even for strategies allowed arbitrarily many
other queries. Theorem 13.4 attains it and the call optimum together.

A fixed query list must contain every $p_j$, by the corresponding pair
$t_{j,0},t_{j,1}$. Early stopping cannot remove this requirement on the
run with that leaf. Consider the $p_j$ whose first occurrence in the
list is latest; its leaf sources require at least $n$ calls. Conversely,
query $p_1,\ldots,p_n$ in order, stopping at a leaf, or returning $B$
after branch at $p_n$. This acquires the descriptor in at most $n$ actual
Reads, with worst total letters $n(n+1)/2$ and peak $n$. $\square$

**Proposition 13.10 (endpoints, guards and collisions).** The same
acquisition result applies to left-ending, right-ending and mixed
addresses, with the following concrete distinctions.

| Public target | Calls from (AAR.80) | Actual semantic check |
| --- | ---: | --- |
| $R$, including $D=1$ | $1$ | $R$ itself gives alpha, beta or branch; these are the three complete future behaviors. |
| $RL$ | $2$ | $\langle\alpha,\beta\rangle$ gives absent at zero, while $\langle\alpha,\langle\alpha,\alpha\rangle\rangle$ gives alpha; both then give beta and branch. |
| $RR$ | $2$ | From $\langle\alpha,\alpha\rangle$ the replies are absent, absent, alpha, beta, then branch; the right-ending suffix has an alpha stage. |
| $RLL$ | $2$ | The distinct blockers in Proposition 13.3 have the same complete future; their respective labels must still be acquired. |
| $RLR$ | $2$ | Those same sources have factor $(4,1)$, hence absent, absent, alpha, beta, then branch on this mixed path. |
| $RLLL$ | $3$ | Four mandatory leaf positions exceed the two-call capacity $2^2-1$, although the predictive quotient merges some of their descriptors. |

Proof. The call values substitute the displayed lengths into Theorem
13.8. The replies follow from (AAR.76) and the guarded table (AAR.59).
For $RLR$, the two descriptors are $(1,1)$ and $(2,0)$; their suffix
weights are three and two, giving the same $(4,1)$. In the $D=1$ case,
$v$ may be either leaf or any height-one branch; a single $R$ Read
covers all of them, not only three representative sources. For every
row with length $n$, (AAR.79) fits $D=n$ and hence every larger $D$.
The upper algorithm never inspects off-path shape. Therefore arbitrary
extra height slack does not alter either optimum. Along an absent
target's nested prefixes there is exactly one first leaf, not several
independent blockers; the comparison invariant searches that one
actual boundary. $\square$

## 14. Resource normalization and its pointwise boundary

**Theorem 14.1 (projection-based normalization of worst resources).**
Define the mathematical projection

$$
 \pi_p(t)=
 \begin{cases}
 t_{j,e},&\partial_p(t)=(j,e),\\
 t_*,&\partial_p(t)=B.
 \end{cases}
\tag{AAR.82}
$$

For every encoder $\mathsf A$ in Definition 13.1 there is a prefix-only
encoder $\mathsf B$, correct on the same full family, such that for each
$t\in\mathcal F_D$ and each $c\in\{T,A,Q\}$,

$$
 c_{\mathsf B}(t)\le c_{\mathsf A}(\pi_p(t)),\qquad
 \max_{t\in\mathcal F_D}c_{\mathsf B}(t)
       \le\max_{t\in\mathcal F_D}c_{\mathsf A}(t).
\tag{AAR.83}
$$

It may be chosen as an ordered successful-search tree on the $n$ leaf
positions, with termination on either label at a hit and one additional
all-branch outcome beyond the last key. These inequalities concern the
three stated query resources, not local simulation work, installed code
or memory. They do not assert $c_{\mathsf B}(t)\le c_{\mathsf A}(t)$
for each unprojected source.

Proof. The projection belongs to the same family and preserves the
entire target trajectory by Proposition 13.3. Simulate the deterministic
run of $\mathsf A$ on this one projected source, obtaining its necessary
responses from actual prefix Reads on $t$. It is unnecessary to acquire
the whole projection first. The all-word classification supplies each
simulation step:

- For $w=p_i$, actually query $p_i$ on $t$; its reply equals the
  projected reply.
- For the immediate divergent sibling $w=p_{i-1}\overline{p[i]}$,
  $2\le i\le n$, query $p_{i-1}$. Its branch reply means the simulated
  sibling reply is alpha; every other reply means absent. The query
  length is $i-1$, one less than the simulated length $i$.
- For $w=pL$ or $pR$, query $p$. Branch means the simulated reply is
  alpha; every other reply means absent. Again the real word is shorter.
- Every remaining case in Lemma 13.7 is a known constant on the
  projected family and requires no actual query.

Each real query is on the unchanged actual $t$. Its reply either is the
projected reply or determines it by the stated map. Induction over the
simulated execution therefore preserves exactly the run of
$\mathsf A(\pi_p(t))$, including its control choices and termination.
Each simulated Read costs at most one real Read and no more letters or
peak length. Repeated known replies can be supplied from the already
acquired local state; this describes a different strategy, not a refund
of the original encoder's repeated calls. If a real prefix query hits a
leaf, the simulator may immediately retain its descriptor and stop; if
it obtains branch at $p$, it may stop with $B$. Such early termination
can only decrease the three coordinates. If neither occurs, the finite
correct simulated run must eventually supply sufficient evidence by
Lemma 13.5. The correctness of its final code also follows directly
from trajectory preservation. This proves the sourcewise inequality
with $\pi_p(t)$, and membership of the projection proves the worst-case
inequalities.

After early termination at every actual hit, the only continuing prefix
replies are absent and branch. They leave respectively a lower and an
upper interval of still possible leaf positions. Queries outside that
interval have a known nonterminal reply and can be omitted. Every
remaining leaf position must occur as a query node on its path, by
Lemma 13.5. Removing these known queries therefore leaves an ordered
binary search tree containing exactly the keys $1,\ldots,n$. An empty
upper interval may terminate with $B$ only on the rightmost path; other
empty continuations are unattained. The descriptor determines every
prefix reply, so the same tree is correct on all original sources, not
just on the representatives. Its whole resource bounds follow from
the preceding simulation and pruning. $\square$

This normalization is sufficient for worst-case resource comparisons.
The direct witness proof of Theorem 13.8 needs only Lemma 13.7 and label
necessity; it does not depend on a universal simulation of off-path
replies on the unprojected source.

**Proposition 14.2 (no same-source pointwise prefix dominator).** For
$D=4,p=RLLL$, there is a globally correct native encoder and a nine-source
subfamily realizing every descriptor, on each of which it terminates
within two Reads. No globally correct prefix-only encoder has Read
count at most that encoder's count on every actual source.

Proof. Use the eight witnesses $t_{j,e}$ of (AAR.79), modifying only the
subtree at $RR$ when that address is present, and use the terminal
branch witness. Choose the $RR$ subtree by the following table; all
other off-path siblings remain alpha.

| Descriptor | Subtree at $RR$ | First reply at $RR$ | Second literal |
| --- | --- | --- | --- |
| $(1,e)$, $e=0,1$ | absent | absent | $R$ |
| $(2,e)$, $e=0,1$ | alpha | alpha | $RL$ |
| $(3,e)$, $e=0,1$ | beta | beta | $RLL$ |
| $(4,e)$, $e=0,1$ | $\langle\alpha,\alpha\rangle$ | branch | $RLLL$ |
| $B$ | $\langle\alpha,\alpha\rangle$ | branch | $RLLL$ |

These are nine concrete trees. In the first row $R$ itself is the leaf,
so $RR$ is absent without any replacement. In all other rows $R$ is
branch and $RR$ is an off-path sibling subtree. Their right-subtree
heights are at most four, including the branch at $p$ in the last row.
Thus the whole family has the same allowed root and height promise.
The second query returns the true first-leaf label, or branch at $p$,
so the table defines a two-call success on every one of these trees.

For a globally correct extension, make these same two queries on every
$t\in\mathcal F_4$, with the second chosen from the actual first reply.
Return only if the second reply is a leaf on the path or branch at $p$;
otherwise run the prefix acquisition of Theorem 13.4. All returns are
justified by actual evidence, and the fallback is finite on every
source. This is one common program, without a source name or a promise
restricting its inputs to the nine witnesses.

A prefix-only pointwise dominator would use at most two Reads on all
nine. On prefixes these sources realize exactly the same replies as
all the descriptors in $\mathcal K_p$; the off-path replacements cannot
be seen. A two-call prefix tree would therefore have to hit all four
possible leaf positions, each with its two possible labels. Its capacity
is at most three by the proof of Theorem 13.8, a contradiction. Hence
off-path correlations can improve selected actual runs. Theorem 14.1
compares them with projected runs, which discard these correlations,
and does not claim this false pointwise dominance. $\square$

**Proposition 14.3 (a whole-strategy call/letter tradeoff).** For every
admissible length-six target, the smallest worst total submitted letters
among all native encoders using at most three Reads is exactly $14$.
There is also an encoder with worst resource vector

$$
 (\max T,\max A,\max Q)=(4,12,6),
\tag{AAR.84}
$$

whereas a three-call encoder attains $(3,14,6)$. These are complete
strategies for the full source family. In particular, the call and peak
optima do not specify a total-resource optimum.

Proof. By Theorem 14.1, any three-call encoder has a prefix search tree
with no larger worst letter total and height at most three. If its root
key is $i$, the two remaining subtrees have height at most two and thus
at most three keys each. With six keys, $i$ must be $3$ or $4$.
If $i=3$, the right subtree on $4,5,6$ must have root $5$ and children
$4,6$. Its key-six run submits lengths $3,5,6$, totaling $14$.
If $i=4$, the subtree on $5,6$ queries both on one attained run,
totaling $4+5+6=15$. Therefore every such whole native strategy has
worst letter total at least $14$, including competitors that use
nonprefix or deeper words.

For attainment at three calls, choose root key $3$, with lower subtree
root $1$ and its upper child $2$, and upper subtree root $5$ with
children $4,6$. For four calls, choose root $5$, lower subtree root $3$
with lower subtree $1$ followed upward by $2$ and upper child $4$,
and upper child $6$ at the root. At a key $i$, submit $p_i$; terminate
on either leaf label, descend left on absent and right on branch, and
terminate with $B$ after branch at key $6$. The actual runs are:

| First-leaf position, or terminal branch | Three-call strategy: submitted lengths | Four-call strategy: submitted lengths |
| --- | --- | --- |
| $1$ | $3,1$ | $5,3,1$ |
| $2$ | $3,1,2$ | $5,3,1,2$ |
| $3$ | $3$ | $5,3$ |
| $4$ | $3,5,4$ | $5,3,4$ |
| $5$ | $3,5$ | $5$ |
| $6$ or $B$ | $3,5,6$ | $5,6$ |

The first strategy has maximal sum $14$ and maximal call count three.
The second has maximal sum $12$ on position four and maximal call
count four on position two. Both have peak six. Every row has actual
witnesses in (AAR.79), and every source has one of these descriptors,
so these maxima are exact for the full strategies. The maxima need
not occur on the same source. This proves the stated tradeoff without
asserting a complete Pareto frontier or minimizing installation,
workspace, arithmetic, clearing or physical latency. $\square$

## 15. Acquired boundary meaning, suppliers and recovery limits

**Proposition 15.1 (comparison with paid ray and full-source capture).**
For the single target of Definition 13.1, the exact initial call and
peak prices are (AAR.80)–(AAR.81). The sufficient acquisition bounds in
Proposition 11.8 and Theorem 12.9 retain their stated contracts:

| Acquired object and contract | Sufficient initial Reads | Peak submitted length |
| --- | ---: | ---: |
| Single-target code, promised stationary source, Theorem 13.4 | $h(n)$ | $n$ |
| Fixed public ray table with the two equal-alpha guards of Proposition 11.8 | $|Q|(D+2)+2$ | $D+1$ |
| Full initial right subtree with the two guards of Theorem 12.9 | $2^{D+1}+1$ | $D+1$ |

For a single right-ending target Corollary 11.6 requires one ray; for a
left-ending target it requires two. This is a count of retained ray
coordinates under that interface, not a Read-count lower bound.

Proof. The first line is already attained. The other two lines are the
respective supplied bounds, with their guards included. For a
right-ending target the required set $B(\{p\})$ is just $\{pR\}$.
For $p=aL$ it is $\{pR,aR\}$, whose two cylinders are disjoint;
Corollary 11.6 gives two. The ray construction finds actual leaves by
successive prefixes and acquires their scores. The full-source
construction visits the actual right-subtree nodes. They obtain richer
objects than the task requires and have their separate capture
validation costs. Neither is silently reinterpreted as an optimal
single-target code acquisition.

If one additionally wants the equal-alpha capture test for the prefix
scheme, an actual $L$ Read before its body and another after it can be
used. Conditional on both returning alpha, the supplied rigidity law
excludes intervening updates and validates the one source. A successful
such attempt uses at most $h(n)+2$ Reads and $nh(n)+2$ letters, with peak
$n$. Failed attempts and retries remain paid, and this conditional
statement promises neither a bounded number of retries nor continued
membership of a source in $\mathcal F_D$ after it has advanced. The two
extra guard calls belong to this added capture contract, not to the
promised-stationarity minimum of Definition 13.1. $\square$

**Mathematical citation 15.2 (exact supplier correspondence and the native
gap).** The following are the sources and limits of the argument.

| Published supplier | Exact use and nontransfer boundary |
| --- | --- |
| This volume, Definition 11.1, Proposition 11.8 and Open problem 11.12 | The root/height family is identical. The fixed-ray capture bounds are sufficient acquisition bounds, not the arbitrary-code call optimum. The declared single target and supplied count specialize the recovery task without changing its source domain. |
| This volume, Theorems 12.3–12.7 and 12.9 | Reuse the exact predictive factor, its guarded future decoder, its boundary factorization and the arbitrary-code minimum. The sufficient full-source capture is not minimized there. The acquisition proof is not a new generic behavior quotient or a repeat of its joint code count. |
| [Sparse Literal History Transport, §§35–38 and 43](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md#35-达到切点上的任意地址未来任务) | Reuse the first-leaf future semantics, all-count passive decoding and actual-label evidence argument. Theorem 36.1 starts with a target probe; Theorem 37.2 gives a general four-way logarithmic lower bound and leaves exact minimax open. Lemma 43.2 and Theorem 43.5 concern evidence and terminal-record range. Lemma 13.5 checks the needed source modifications inside the bounded family; terminal-record cardinality alone does not give (AAR.80). |
| [Concurrent Native Cut Acquisition, §§17–19](RECURSIVE_RELATIONAL_OBSERVATION_CONCURRENT_NATIVE_CUT_ACQUISITION.md#17-executing-an-ordered-cover-within-its-budget) | Reuse ordinary successful-search capacity $2^h-1$ and actual acquisition of the equality label. Its protected invocation-row recovery and later capture differ from this passive future-value task. Lemma 18.1 pads beyond all submitted addresses; those sources need not lie in $\mathcal F_D$. The bounded witness classification (AAR.79) is needed before the same capacity applies here. The comb formula in Corollary 19.2 alone does not discharge that obligation. |
| [Literal Query Frontier, §§3–5](RECURSIVE_RELATIONAL_OBSERVATION_LITERAL_QUERY_FRONTIER.md#5-the-peak-projection-and-shortest-pair-separators), and [Acquired Orbit Resource Frontier, §§4–6](RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_ORBIT_RESOURCE_FRONTIER.md#6-a-signed-guard-sensitive-family-of-entire-rows) | Finite decision trees, same-history resource vectors and shortest-pair separators are existing methods. Their acquired entries, hidden clock slots or atomic orbit rows have different feasible query partitions. Their generic finite minimization is not a structural solution of (AAR.75); the new input is the native bounded all-word classification and its safe projection. |
| [Atomic Generation Acquisition, §12](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md) | Its adaptive and fixed passive threshold prices have the same numerical forms in (AA.40)–(AA.41). The objects are phase/tail candidates with an actual root archive and a different passive test interface. The constant-composition presentation of its replies does not identify the whole source family or unrestricted literal tests in (AAR.73). Numerical agreement is not an operation-preserving reduction. |
| [NativeDepthPatterns](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean), `original_present_transport`, `original_prefix_locality` | The first declaration transports only a present subtree, here the actual first leaf. The second gives finite-depth dependence of future replies. Neither is a native acquisition lower bound or permission to use an unobserved boundary. The ordinary argument supplies the necessary bounded witnesses and their actual replies. |
| [NativeLiteralPathConstraints](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeLiteralPathConstraints.lean), `compile_exact`, and [NativeIndependentExecution](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.lean), `native_history_correspondence`, `effective_native_correspondence` | These supply exact literal constraints and same-source execution correspondences, including absence and all four continuations. A run's source, control and chronology are joint inputs. They do not prove a Read optimum, and no new compilation or kernel-verification claim is attached to their source correspondence here. |

The focused ordinary addition is the bounded all-native-address lower
bound matched by acquisition, its exact peak price, and the valid
resource normalization with its pointwise obstruction. These are
`repo-derived` results. The capacity recurrence and decision-tree
principles are reused. Their value for the recovery programme is to
price obtaining an initial sufficient spatial distinction, not merely
to name that distinction once available.

**Mathematical citation 15.3 (primary search literature and correspondence
limits).** Three relevant primary sources place the search methods at
their proper scope.

[Robert D. Nowak, *The Geometry of Generalized Binary Search*,
§§I–II, Definition 1 and Lemma 1](https://arxiv.org/html/0910.4397v5)
uses a finite class of distinct binary-valued hypotheses on a query
space, with one fixed unknown hypothesis. Its noiseless decision-tree
view and query-space partition by response vectors correspond to a
stationary source and its literal reply functions. Its geometric and
coherence assumptions support near-optimal logarithmic bounds for a
greedy splitting procedure. Here tests have four replies, the target
is a future-behavior class rather than source identification, and no
such coherence hypothesis is imposed. Neither the binary information
bound nor its noisy-query results yield the exact constant in (AAR.80).
The native proof identifies why the two label replies terminate a hit
rather than supplying four arbitrary continuing subdivisions.

[Ferdinando Cicalese, Eduardo Laber and Aline Medeiros Saettler,
*Diagnosis determination: decision trees optimizing simultaneously
worst and expected testing cost*, §1's DFEP definition and decision-tree
costs, §2's different-class pairs](https://proceedings.mlr.press/v32/cicalese14.pdf)
provide a closer class-identification model. The correspondences are
$S=\mathcal F_D$, classes equal to the trajectories at the declared $p$,
and tests $w\mapsto\operatorname{readout}(w,t)$ with four outcomes.
For a finite test presentation one can keep words through depth $D+1$;
all deeper words are constant absent on initial sources and provide no
class distinction. These finite tests separate distinct trees. Unit
test costs give the Read objective; after removing the public constant
root test, costs $|w|$ give the separate letter objective with positive
costs. The paper also supplies a distribution and optimizes expected
cost, and its algorithm gives logarithmic approximation guarantees.
No distribution is supplied here and the objective is an exact worst
count. Its general framework explains why objects in one target class
may be merged, but does not provide the bounded native pair geometry
or its exact acquisition cost. In particular it does not identify the
minimum retained alphabet with the optimal test depth.

[R. Bruno, R. De Prisco, A. De Santis and U. Vaccaro,
*Bounds and Algorithms for Alphabetic Codes and Binary Search Trees*,
§§I–II](https://arxiv.org/html/2407.16443v1)
distinguish binary-result alphabetic searches from ternary comparisons
in binary search trees. Their internal nodes represent successful
searches at ordered keys, and external leaves represent gaps; the
objective uses probabilities of successful and unsuccessful searches
to minimize average cost. Our prefix test has the corresponding
less/equal/greater geometry, with equality further returning its
necessary alpha/beta label and only the final above-all-keys gap
attained. This is the ordinary search-tree structure used in
(AAR.78). No probability distribution, entropy-rate claim or
average-cost bound is transferred. Submitted word lengths are the
actual costs of native operands; Proposition 14.3 proves its particular
worst-cost tradeoff directly.

These inspected correspondences establish methodological reuse and
its limits. They do not assert worldwide originality, a new general
search capacity theorem, or an efficient algorithm for optimizing all
other resource coordinates.

**Proposition 15.4 (what is mutually recoverable, and what remains a
different task).** The genuinely acquired statistic
$\Gamma_p(\partial_p(t))$ and the complete supplied-count trajectory
at $p$ determine one another on their attained images. A sufficient
acquired boundary table or the acquired full source determines this
statistic. The converse implications to a full source, a full boundary,
an unknown lag or actual observation receipts do not follow.

Proof. The mutual recovery is Theorems 12.3–12.4: the first branch
count and alpha-stage flag recover the statistic, and (AAR.59) gives
all replies. Proposition 13.3 exhibits different actual source trees
with the same trajectory. Counterexample 11.9 gives the separate
hidden-equality obstruction even with sufficient boundary samples.
Every target here is branch by the supplied bound $s(p)\le2D$, so its
reply cannot recover how far the authentic count has advanced beyond
saturation. Before a new count or source observation is supplied, a
passive program has identical input at two different later lags.
Finally, calculating (AAR.74) performs no $\operatorname{Read}(p)$
event on that later version. An actual receipt requires a separately
paid observation; a common-version collection requires its own
capture justification. $\square$

Thus space enters as an actually probed original-root boundary,
memory as a sufficient retained factor of that boundary, and time as
the separately supplied count acting through the guarded decoder.
The exact cost here is for acquiring the first factor on the precise
stationary family. Multiple declared targets can share queries and
joint source constraints; an unknown later menu changes which
information must survive; an unknown count requires a new acquisition
problem; complete rows retain equality information absent from a
literal reply. Their general acquisition optima, the full resource
frontier, and the broader mutual-recovery programme are not settled
by the single-target price. All results in §§13–15 are ordinary
mathematical arguments, with no new kernel certification or physical
time law.

## 追加锚（本行以下为增补区）
## 16. Exact joint acquisition from the native menu prefix geometry

**Definition 16.1 (one declared joint prediction task).** Retain the
source-blind stationary acquisition contract of Definition 13.1, replacing
its singleton $p$ by an arbitrary public finite $P\subseteq A_D$. Thus
$D\ge1$, every $p\in P$ is nonempty, starts with $R$ and has $|p|\le D$,
and the unknown actual source is

$$
 t=\langle\alpha,v\rangle\in\mathcal F_D,
 \qquad \operatorname{height}(v)\le D.
\tag{AAR.85}
$$

The empty menu, nested targets and prefix-free targets are all allowed.
The same deterministic program and source-blind initialization are used
on every source. The only source operation during acquisition is an
actual four-reply Read at any finite original-root word. There is no
update, free navigation, subtree oracle, age oracle or source identifier.
The source is promised stationary throughout this phase. Every submitted
Read counts, including absent, repeated, constant and off-menu calls.

The encoder terminates on every actual source and exports its complete
accessible source dependence $E(t)$ before the authentic count $k$ is
supplied. A passive decoder, with no new Read, must satisfy

$$
 \mathsf D(E(t),D,P,k)=
 \bigl(\operatorname{readout}(p,\rho^k t)\bigr)_{p\in P}
 \quad(t\in\mathcal F_D, k\ge0).
\tag{AAR.86}
$$

The complete-state convention includes operands, buffers, control,
selectors, histories, lengths and allocation distinctions. The target
is exactly this vector for every supplied count, rather than full-source
identity or later undeclared menus. Define

$$
 \mathcal C_D(P)=\min_{\mathsf A}\max_{t\in\mathcal F_D}
       T_{\mathsf A}(t),\qquad
 S=R^{-1}P,\qquad K=\operatorname{Pref}(S).
\tag{AAR.87}
$$

The minimum ranges over all such native encoders and their passive
decoders. Put $\operatorname{Pref}(\varnothing)=\varnothing$; otherwise
include the empty suffix $\varepsilon$ and every prefix of every word
in $S$. The root of nonempty $K$ represents the original address $R$,
which is known present but whose constructor and label are unknown.
Its greatest suffix depth is at most $D-1$.

Write

$$
 B_K(t)=\bigl(\operatorname{readout}(Rq,t)\bigr)_{q\in K}
       =\bigl(\operatorname{readout}(q,v)\bigr)_{q\in K}.
\tag{AAR.88}
$$

This is a mathematical boundary table, not an initially supplied
observation. It retains every relevant branch, labelled stopping leaf
and absent position. Theorem 12.3 gives its factor to $\Sigma_P$, and
Theorem 12.6 gives the existing minimum retained code $e_S(v)$ and its
alphabet $n(S)$. Neither alphabet size nor terminal-record range is the
Read objective (AAR.87). Local computation, transient and retained
memory, operand lengths, installation, clearing, authentication and
validation of the stationarity promise are separate resources.

**Theorem 16.2 (the terminal evidence obligation on the bounded family).**
For every correct encoder in Definition 16.1, its actual terminal
address-reply transcript determines $B_K(t)$ among sources in
$\mathcal F_D$. For each $p\in P$ it must contain the following evidence:

1. If the initial path toward $p$ meets a leaf $a\preceq p$, including
   a leaf at $p$, it contains an actual Read of $a$ with that leaf's
   alpha or beta label.
2. If $p$ is initially branch, it contains the branch reply at $p$ or
   a nonabsent reply at a strict descendant of $p$.

Conversely, a truthful transcript with these witnesses determines the
whole table (AAR.88), and hence the joint prediction task. The complete
export may subsequently forget some distinctions of this table.

Proof. Reuse the evidence criterion of SLH Lemma 43.2 and its
terminating-record consequence in SLH Theorem 43.3, with the bounded
competitors checked as in Lemma 13.5. A blocking leaf $a$ lies in the
$R$ cone. Flipping only its label preserves the ordered shape, its
height and the fixed outer left alpha. Every literal reply except the
one at $a$ stays unchanged. If $a=p$, the requested reply differs
already at count zero. If $p=ar$ with $r\ne\varepsilon$, the first
branch count in (AAR.57) differs by one. Thus some common supplied
count distinguishes the two requested trajectories. Omitting $a$
would replay the identical terminal transcript and complete export on
this other member of $\mathcal F_D$, contradicting (AAR.86).

If the branch witness is missing, replace the subtree at $p$ by alpha.
No Read at $p$ occurred, and all queried strict descendants were absent;
they stay absent. Queries outside its cone stay unchanged. This
competitor lowers height and preserves the outer left alpha, so it is
also in $\mathcal F_D$. Deterministic replay again gives the same
termination and export, but the target replies at count zero differ.
Neither comparison changes a source within an execution.

A labelled leaf certifies all its strict ancestors as branches and all
its strict descendants as absent. A nonabsent descendant certifies all
its strict ancestors as branches. Applying these facts to every target
covers every vertex of $K$, because each is on a path to a target.
They prove the converse and the determination of (AAR.88). Its
predictive factor then uses the existing guarded decoder (AAR.59).
The leaf flip is indispensable even when two different boundary tables
have equal predictive factors. $\square$

**Theorem 16.3 (bounded canonical completions and every-word classification).**
For nonempty $K$ there is a projection $\pi_K$ on initial right subtrees
that preserves every reply on $K$. It keeps a reached leaf and its label;
at a reached branch it keeps children whose addresses belong to $K$
and replaces every other child subtree by alpha. In particular an
initial branch at a terminal vertex of $K$ becomes
$\langle\alpha,\alpha\rangle$. Put
$\widehat t=\langle\alpha,\pi_K(v)\rangle$. Then

$$
 \operatorname{height}(\pi_K(v))\le\operatorname{height}(v),
 \qquad
 \operatorname{height}(\pi_K(v))\le1+\max_{q\in K}|q|\le D,
 \qquad B_K(\widehat t)=B_K(t).
\tag{AAR.89}
$$

Every finite original-root word has the following reply on this
projected actual family:

| Original-root word | Reply on $\widehat t$ |
| --- | --- |
| $\varepsilon$ | branch |
| $L$ | alpha |
| A strict extension of $L$ | absent |
| $Rq$, $q\in K$ | The preserved actual reply at $Rq$ on $t$ |
| $Rad$, where $a\in K$, $d\in\{L,R\}$ and $ad\notin K$ | alpha if $a$ is branch in $v$; absent otherwise |
| $Rad z$ with that same first exit and $z\ne\varepsilon$ | absent |

Moreover all permitted boundaries on $K$ have simultaneous native
realizations within the height bound. More precisely, let $I\subseteq K$
be any downward-closed set in the prefix order, and put

$$
 \partial_K I=\{x\in K\setminus I:
                    \text{every strict ancestor of }x\text{ belongs to }I\}.
\tag{AAR.90}
$$

Assign an independent alpha or beta label to each member of
$\partial_K I$. There is a canonical right subtree whose replies on
$K$ are branch on $I$, the assigned labels on $\partial_K I$, and
absent everywhere else. Its height is at most
$1+\max_{q\in K}|q|$, so its paired source is in $\mathcal F_D$.
Here downward-closed does not mean principal or directed.

Proof. Replacing a child subtree by alpha does not increase height.
All kept branch vertices are in $K$; their added alpha children are
at depth at most $\max|q|+1$. At a leaf the construction stops, so
positions initially absent in $K$ remain absent. This proves (AAR.89).
For a suffix outside $K$, its longest prefix in $K$ is unique. Its
first edge leaving $K$ reaches the added alpha exactly when that
prefix is a branch. If the prefix is a leaf or absent, this child is
absent. Any further edge is absent in either case. These alternatives
exhaust arbitrary depths, rather than only words below the menu bound.

For the realization statement, start at the known-present root. Make
exactly the reached vertices in $I$ branches, stop with the prescribed
label at each reached vertex outside $I$, and fill every child leaving
$K$ by alpha. Downward closure makes this consistent: a vertex of $I$
cannot lie below a stopping leaf. Its relevant stopping leaves are
exactly (AAR.90); all other nonbranch vertices of $K$ are absent. The
same depth bound applies. In particular terminal branches are feasible
because the allowed menus leave one additional level in $v$. No
completion pads beyond $D$. $\square$

**Theorem 16.4 (all-word reduction with its exact source correspondence).**
The optimum (AAR.87) equals the minimum worst Read count for determining
$B_K$ using only actual menu-prefix queries $Rq$, $q\in K$, on the same
full family. For every all-word encoder $\mathsf A$ there is such a
boundary-acquiring encoder $\mathsf A^\circ$ satisfying

$$
 T_{\mathsf A^\circ}(t)\le T_{\mathsf A}(\widehat t),\qquad
 \max_{t\in\mathcal F_D}T_{\mathsf A^\circ}(t)
       \le\max_{t\in\mathcal F_D}T_{\mathsf A}(t).
\tag{AAR.91}
$$

This is a projected-source comparison of worst budgets, rather than
$T_{\mathsf A^\circ}(t)\le T_{\mathsf A}(t)$ on the identical source.

Proof. For empty $P$, return the empty vector with zero Reads. Otherwise
simulate $\mathsf A$ on $\widehat t$, keeping the actual register $t$
unchanged. A simulated query $Rq$ with $q\in K$ is supplied by the
actual Read of $Rq$ on $t$. A first-exit query $Rad$ is supplied by
at most one actual Read of $Ra$, mapped to alpha on branch and to
absent on all other replies. Fixed outer replies and strict extensions
of an exit require no source call. Replies already acquired on this
stationary source may be reused by this new strategy. Each Read that
is actually submitted still counts; no original repeated or absent
call is retrospectively free.

The classification in Theorem 16.3 makes the simulated transcript
truthful on the one actual source $\widehat t\in\mathcal F_D$.
Induction through the deterministic control therefore simulates its
finite terminating execution, including any finite local work. At
termination, Theorem 16.2 makes that transcript determine
$B_K(\widehat t)$. This determination is effective: a simulated labelled
Read at a vertex of $K$ used its actual reply; an immediate-exit alpha
certifies its parent branch by the actual prefix reply. The fixed or
absent cases supply no invented presence. Scan those witnesses to
recover the boundary. Equation (AAR.89) makes it $B_K(t)$, and at
most one actual call was used per simulated call. This proves (AAR.91).

Conversely, a boundary strategy queries the identical original source,
and its acquired table supplies (AAR.86) through Theorems 12.3 and
12.6. The two inequalities of optimal worst counts follow. Every
arbitrary adaptive finite-word competitor is included in the forward
simulation; no shape promise was imposed on its actual input.

The reply correspondence is concretely different from preserving the
original transcript. With $P=\{R\}$, $D=1$ and
$t=\langle\alpha,\langle\beta,\alpha\rangle\rangle$, Read$(RL)$ is
beta on $t$ and alpha on $\widehat t$. Proposition 14.2 already gives
a stronger singleton obstruction to universal identical-source
pointwise prefix domination. The present joint theorem makes only the
comparison (AAR.91). $\square$

**Definition 16.5 (unresolved rooted obligations and terminal caps).**
A rooted obligation tree $T$ is a finite nonempty prefix tree with at
most two children per vertex, retaining its original addresses through
an embedding into $K$. Its root is known present. An internal vertex
may be a stopping alpha/beta leaf or a branch. A terminal vertex may
be open, allowing alpha, beta or branch, or capped, allowing only
alpha or beta if reached. A cap never asserts that its vertex is
present: an earlier stopping leaf can make it absent. Relevant leaf
labels not yet acquired are unrestricted. The task is to determine
all replies on $T$.

For $x\in T$, let $A_T(x)$ be the inclusive root-to-$x$ path and
$\operatorname{Desc}_T(x)$ its inclusive descendant cone. Let
$\mathscr F_T(x)$ be the rooted connected components of
$T\setminus A_T(x)$. For nonroot $x$ with parent $p$, put

$$
 T_x^- = T\setminus\operatorname{Desc}_T^+(p),
 \qquad
 \operatorname{Desc}_T^+(p)=\operatorname{Desc}_T(p)\setminus\{p\}.
\tag{AAR.92}
$$

This retains $p$ and deletes all its strict descendants in both child
directions. Operationally the new terminal $p$ is capped. A forest of
obligations consists of disjoint components attached below already
certified branch paths, together with the fixed acquired replies
outside them. It keeps each component's original-root embedding and
its current terminal marks. Relabelling an embedding as a relative
root for a numerical calculation grants no navigation operation.

**Theorem 16.6 (exact closure of the native residual states).** Starting
with $K$ whose terminals are open, every informative prefix Read leaves
an obligation forest of Definition 16.5. If it queries $x$ in one
component $T$, its conditional families are exactly these:

| Actual reply | Unresolved obligations in that component |
| --- | --- |
| branch | All components $\mathscr F_T(x)$, with inherited terminal marks |
| alpha or beta | Only components hanging off the strict ancestor path of $x$; its label is acquired and its entire cone is resolved |
| absent, $x$ nonroot | $T_x^-$ with parent$(x)$ capped, and inherited marks outside the deleted cone |

Root absence is impossible. An internal $x$ has a feasible branch
reply. At an open terminal all three nonabsent replies are feasible;
at a capped terminal only the two label replies are feasible. For
every nonroot $x$, absence is feasible. Every allowed combination of
residual component boundaries, including all unread labels and caps,
is realizable in one original stationary source of $\mathcal F_D$.

Proof. Branch at $x$ certifies the entire path $A_T(x)$ as branches.
Every remaining component root is a child of one of those certified
branches, so it is present. No further relation is imposed between
its independent child cones. A leaf at $x$ instead certifies only its
strict ancestors as branches, fixes its own actual label and makes
all strict descendants absent. Removing its cone as well as the
ancestor path leaves the stated side components.

The full-binary source law gives, for any nonroot address in a
known-present component,

$$
 x\text{ is absent}\quad\Longleftrightarrow\quad
       \operatorname{parent}(x)\text{ is not a branch}.
\tag{AAR.93}
$$

The parent may be a leaf or may itself be absent. Either alternative
makes every strict descendant of that parent absent, including the
sibling direction of $x$. Conversely this condition makes $x$ absent.
If the parent is reached it must now be a leaf, which is precisely the
cap in (AAR.92). An earlier leaf is still allowed. Deleting only $x$'s
cone would leave a false sibling freedom; declaring its parent present
would discard actual sources. Descendant targets are not abandoned:
their future replies will be computed from the actual labelled blocker
when the remaining boundary is acquired.

These implications are sufficient, not only necessary. To realize an
allowed residual boundary, fill each component by Theorem 16.3's
canonical construction, forbidding a branch at a reached cap. Glue
these subtrees below the fixed certified branch paths; preserve acquired
labels and fill omitted children by alpha. After an absent reply,
expanding the deleted cone is unnecessary: if its new cap is reached,
put its chosen leaf label there, and otherwise its earlier leaf already
makes that cone absent. This gives exactly the original conditional
boundaries for every row of the table.

All branch vertices used in this construction belong to the original
$K$. Added children lie at most one level farther, so the right-subtree
height is at most $\max\operatorname{depth}(K)+1\le D$. Combining
components uses the maximum of their embedded depths, not a sum of
heights. Thus all their choices coexist on one native source. Terminal
marks persist until resolved or removed; an absent step only adds a
terminal mark after deleting that parent's children. Hence there is no
hidden internal cap. By induction this describes the exact family after
any informative adaptive prefix transcript. Queries at already resolved
vertices have known replies and can be omitted by a new strategy; their
calls in a competing strategy remain charged. $\square$

**Theorem 16.7 (component addition against arbitrary adaptive interleaving).**
For a forest of the independently realizable components in Theorem
16.6, its minimum worst prefix-Read count is the sum of the individual
component minima. This holds for every deterministic strategy that
interleaves components based on the whole acquired transcript.

Proof. Sequentially solve the components to attain the sum. For the
lower bound, a remaining query concerns at most one component; a query
outside them has a known reply. Their compatible boundaries form a
Cartesian product by Theorem 16.6, with already acquired labels fixed.
For each component keep its nonempty set $Z_i$ of still compatible
boundaries. As a proof device, let $d_i(Z_i)$ be its minimum worst
remaining number of local vertex queries to determine that boundary.
It is finite, since reading every vertex suffices, and is zero exactly
when the boundary is already determined. This conditional complexity
is used only for the adversary argument, rather than as the structural
characterization to be computed below.

At any query to component $i$, at least one nonempty truthful reply
cell $Z_i'$ has

$$
 d_i(Z_i')\ge d_i(Z_i)-1.
\tag{AAR.94}
$$

Otherwise this query followed by optimal local continuations would
improve $d_i(Z_i)$. Choose such a reply and keep that cell. Other
components' sets do not change. Thus $\sum_i d_i(Z_i)$ decreases
by at most one per actual Read, regardless of adaptive interleaving,
and a correct halt requires every component boundary to be determined.
At least its initial sum of queries is necessary.

Throughout this argument the product of retained completion sets is
nonempty. If the strategy halted too early, its terminal record would
leave an unresolved component. If it continued past the asserted
budget, choose one surviving boundary in each component and glue them
as in Theorem 16.6: that single initial source realizes the entire
preceding adaptive transcript. There is no change of source during
this execution and no combination of separately attainable marginal
optima. Finite termination on every completion excludes an infinite
source-consistent run. The inequality and attainment prove the claim.
$\square$

**Theorem 16.8 (the exact menu-prefix recurrence and native optimum).**
Define $c(\varnothing)=0$, and for a nonempty rooted obligation shape
$T$ define

$$
 \begin{aligned}
 f_T(x)&=\sum_{U\in\mathscr F_T(x)}c(U),\\
 a_T(x)&=\begin{cases}
          0,&x=\operatorname{root}(T),\\
          c(T_x^-),&x\ne\operatorname{root}(T),
         \end{cases}\\
 c(T)&=1+\min_{x\in T}\max\{f_T(x),a_T(x)\}.
 \end{aligned}
\tag{AAR.95}
$$

Every recursive tree has fewer vertices, so this is a finite recurrence
on path deletion, parent truncation and rooted components of the public
menu geometry. For every allowed $D,P$,

$$
 \boxed{\mathcal C_D(P)=c\bigl(\operatorname{Pref}(R^{-1}P)\bigr).}
\tag{AAR.96}
$$

The number is unchanged by any assignment of open/capped terminal marks
for a component of that same shape. An attaining source-blind encoder
uses only original-root words $Rq$, $q\in K$, and may subsequently
export the existing minimum $n(S)$-label prediction code. No enumeration
of $\mathcal F_D$, whole decision trees or behavioral classes is part
of (AAR.95).

Proof. Induct simultaneously on the number of vertices for every
assignment of terminal marks. A one-vertex component needs one Read:
it is known present, but its two possible labels must be distinguished.
An open terminal also allows branch; one Read resolves it as well.
Thus both terminal types have the same value one.

For a larger component, consider the first informative vertex query
$x$. Its branch continuation has value $f_T(x)$ by Theorems 16.6–16.7
and the inductive hypothesis. If $x$ is internal this reply is feasible.
Its leaf continuations have just the strict-ancestor side components;
the branch forest contains those components and, additionally, the
child components of $x$. Their nonnegative costs show that a leaf
continuation costs no more. If $x$ is terminal, there are no such child
components, so every feasible positive reply has exactly $f_T(x)$.
This includes a capped terminal, where branch is impossible but the
two actual label replies give that same continuation cost.

For nonroot $x$, absence is feasible, for example with a leaf at the
component root. Its conditional task is exactly $T_x^-$ with the new
cap. By the inductive hypothesis it has cost $a_T(x)$, independent of
all inherited terminal marks. Root absence is impossible and contributes
no extra alternative. Thus the true worst continuation for this first
query is exactly $\max\{f_T(x),a_T(x)\}$, for every mark assignment.
Every cell used for this lower bound has the bounded common-source
realizations proved in Theorem 16.6. Any first query therefore requires
at least the displayed leading one plus this maximum. A previously
resolved query only spends a Read without changing the task. Taking
the minimum over informative first queries proves the lower recurrence
against every prefix strategy, including arbitrary interleaving later.
It also proves that marks do not change its numerical value.

To attain it, use fixed public tie-breaking to choose a minimizing
$x$, and actually submit its embedded word $Rq$. On branch, solve
$\mathscr F_T(x)$. On a label, save that actual label and solve only
the side components left by its strict ancestors. On absent, retain
the parent cap and solve $T_x^-$. Sequentially solving the resulting
components attains their sum. Each step removes at least one unresolved
vertex. A positive query is removed with its ancestor path; an absent
query is removed with its parent's strict-descendant cone. Hence no
actual query is repeated, all calls including absence are charged, and
the procedure terminates on every original source with cost at most
$c(K)$. Its actual witnesses reconstruct the entire boundary, including
labels of caps that are reached and absence of caps blocked earlier.

Theorem 16.4 identifies this prefix-boundary minimum with the original
all-word prediction minimum, proving (AAR.96). Compute $\Sigma_P$
or $e_S$ from that acquired boundary and use (AAR.59) at the authentic
supplied $k$. For computing $e_S$, the constructor and relevant child
codes needed by (AAR.67) are all in $K$; an empty child menu has its
fixed zero code. The acquired table or complete finite transcript
already suffices as an export. If only the minimum code is retained,
use the complete handoff convention of Definition 12.1 to clear every
other accessible source-dependent distinction. Such local encoding,
storage and clearing add no Read, but have their separate costs.
The code count and decoder are reused from §12, rather than obtained
anew from this recurrence. $\square$

**Theorem 16.9 (geometry, redundancy and admissible height slack).** The
Read value in (AAR.96) depends only on the rooted prefix-tree shape,
including unary-chain lengths. It is unchanged by exchanging left and
right child directions, by increasing an admissible $D$, or by adding
a target that is an ancestor of an existing target. Left/right exchanges
and added ancestor targets can change the retained-alphabet count
$n(S)$; increasing an admissible $D$ leaves both counts unchanged by
Theorem 12.6. In particular,

$$
 \mathcal C_D(\varnothing)=0,\qquad
 \mathcal C_D(\{p\})=\lceil\log_2(|p|+1)\rceil,
 \qquad
 1\le c(K)\le|K|\quad(K\ne\varnothing).
\tag{AAR.97}
$$

The singleton formula is exactly the already published Theorem 13.8,
not an additional single-address acquisition result.

Proof. The three operations in (AAR.95) use rooted adjacency and
ancestor order, with no left/right weight or target markings. Adding
an already included prefix changes no vertex of $K$. The canonical
realizations fit every $D\ge\max_{p\in P}|p|$; the attaining queries
inspect no extra height slack. This proves the invariances. The empty
menu has constant output. For a singleton the obligation shape is a
path with $|p|$ vertices, and equality with Definition 13.1's optimum
allows direct reuse of Theorem 13.8. The lower positive bound follows
from the two root-leaf sources with different requested trajectories.
Reading all vertices of $K$ proves the upper bound.

A nonabsent descendant certifies each strict ancestor branch; requesting
such an already certified ancestor again adds no boundary information.
After reading a labelled leaf, its strict descendants are already known
absent and need no further initial probe. After absence at $x$, all
strict descendants of its parent are already absent, but the actual
blocking leaf and its label still require acquisition. These are
conditional redundancies on an actual acquired transcript. Removing
nonmaximal targets does not remove their addresses as potential probes:
a blocking leaf at one of those ancestors must itself be read by
Theorem 16.2. Nor do the worst-budget invariances deny source-specific
usefulness of off-menu probes, as Proposition 14.2 demonstrates.
$\square$

**Theorem 16.10 (shared acquisition and equal-width/depth obstructions).**
For every indicated admissible $D$, the following exact costs hold:

| Declared menu | Minimum Reads | Minimum admissible $D$ |
| --- | ---: | ---: |
| $\varnothing$ | $0$ | $1$ |
| $\{R\}$ | $1$ | $1$ |
| $\{RL,RR\}$ | $2$ | $2$ |
| $\{RLL\}$ or $\{R,RLL\}$ | $2$ | $3$ |
| $\{RLL,RLR\}$ | $3$ | $3$ |
| $\{RLL,RRR\}$ | $4$ | $3$ |

Thus a joint menu can cost strictly less than the sum of its singleton
optima. Menu size, antichain width and maximum target depth alone do
not determine the price.

Proof. The empty, root and singleton entries reuse (AAR.97); adding
$R$ does not change the singleton's prefix tree. For $\{RL,RR\}$,
Read $RL$. If absent, Read $R$: it is a leaf and its actual label
resolves both trajectories. If nonabsent, $R$ is branch and Read $RR$
resolves the other component. This uses at most two actual Reads.
For a matching lower bound take the four simultaneous native sources

$$
 t_{x,y}=\langle\alpha,\langle x,y\rangle\rangle,
 \qquad x,y\in\{\alpha,\beta\}.
\tag{AAR.98}
$$

All lie in $\mathcal F_2$. Every literal is either constant or reads
one of the two independent leaf labels. The requested count-zero
vector determines both, so one Read cannot suffice. Each singleton
has price two by Theorem 13.8, but the joint price is two rather than
four. The same acquired reply may certify their common branch and
supply one requested label; it is one event shared by the tasks.

For $\{RLL,RLR\}$, first Read $RL$. Absence is resolved by one $R$
Read, a leaf resolves both targets directly, and branch is followed
by the two child Reads. The maximum is three. Its relative trie is
$\{\varepsilon,L,LL,LR\}$. In (AAR.95) first querying the root has
positive continuation two, querying $L$ has worst continuation two, and
querying either terminal child has worst continuation two. For the
last case the positive forest has one vertex of cost one, while its
negative truncation is the two-vertex path of cost two. Thus the
minimum is three, giving the matching all-word bound by (AAR.96).

For $\{RLL,RRR\}$ the relative trie is
$\{\varepsilon,L,LL,R,RR\}$. Querying its root has positive
continuation four; querying $L$ or $R$ has positive continuation
three and negative continuation one; querying $LL$ or $RR$ has
positive continuation two and negative continuation three. The
latter truncated shape is $\{\varepsilon,L,R,RR\}$. Its root
query has continuation three; querying $L$ leaves the two-vertex
$R$ path of cost two; querying $R$ has positive continuation two
and negative continuation one; querying $RR$ has positive
continuation one and negative continuation two, the latter being
the two-child root $\{\varepsilon,L,R\}$ of cost two. Its exact
value is therefore three. Consequently (AAR.95)
gives four for the five-vertex trie.

There is also a direct native lower correspondence for that price.
Restrict to the 16 sources

$$
 t=\langle\alpha,\langle x,y\rangle\rangle,
 \quad
 \begin{aligned}
 x&\in\{\alpha,\beta,\langle\alpha,\alpha\rangle,
                            \langle\beta,\alpha\rangle\},\\
 y&\in\{\alpha,\beta,\langle\alpha,\alpha\rangle,
                            \langle\alpha,\beta\rangle\}.
 \end{aligned}
\tag{AAR.99}
$$

Their right-subtree height is at most two, so they lie in $\mathcal F_3$.
In the left component the selected child is $L$: a root Read merges
its two branch completions, a child Read merges the two root leaves,
and every other literal is constant or supplies no finer partition.
Its two leaf labels and selected child reply require two Reads in
the worst case. In the right component the selected child is $R$,
with the symmetric two-Read obstruction. Any original-root literal
concerns at most one component, or is a fixed outer reply. Theorem
16.7's product argument gives four against arbitrary interleaving
on one of these actual sources, with both local hard histories
simultaneously realizable. This is a common-source lower bound,
not the sum of initial singleton bounds.

Both three-letter menus have two incomparable targets and width two,
but costs three and four. They therefore falsify any formula using
only those summaries. The shared and split possibilities are realized
by actual trees, including the independent factors in (AAR.99);
the difference is their prefix overlap, rather than an imagined
combination of separately optimal probes. $\square$

**Theorem 16.11 (acquired boundary versus retained joint prediction).**
For $D\ge3$ and $P=\{RLL,RLR\}$, the actual sources

$$
 t_0=\langle\alpha,\beta\rangle,
 \qquad
 t_1=\langle\alpha,\langle\alpha,\alpha\rangle\rangle
\tag{AAR.100}
$$

have different menu-prefix boundaries and identical joint future
trajectories. A correct full-family acquisition must read $R$ on
$t_0$ and $RL$ on $t_1$, even though a minimum retained prediction
code merges them. Adding the ancestor target $R$ to
$P_0=\{RLL\}$ changes its minimum retained alphabet from six to
seven without changing its two-Read acquisition price. Moreover
$\{RLL\}$ and $\{RRR\}$ have the same acquisition shape and price,
but retained alphabets of six and seven, respectively.

Proof. The two sources in (AAR.100) have the joint statistic

$$
 \Sigma_{\{RLL,RLR\}}(t_0)
   =\Sigma_{\{RLL,RLR\}}(t_1)=((3,0),(4,1)).
\tag{AAR.101}
$$

This is the two-target instance of the already published collisions
in Propositions 13.3 and 13.10, using (AAR.57). The $RLL$ trajectory
has no alpha stage; its replies are absent, absent, beta, then branch.
The $RLR$ trajectory is absent, absent, alpha, beta, then branch.
The common left-ending absence guard is essential to the first equality.
The boundaries differ at $R$ and $RL$. Flipping the beta at $R$ in
$t_0$, or the alpha at $RL$ in $t_1$, changes a requested trajectory
while preserving every other initial literal reply. Both flips remain
in the same height-bounded family. Theorem 16.2 forces the stated
actual Reads. Their shared collision is one joint boundary choice,
rather than independent choices made per target.

For $P_0$, the suffix menu is $\{LL\}$. Formula (AAR.66) gives six;
for $\{R,RLL\}$ its suffix menu is $\{\varepsilon,LL\}$ and gives
seven, since the selected root removes the beta/branch collision.
The relative prefix tree is the same three-vertex path, so Theorem
16.9 leaves its acquisition price at two. For $\{RRR\}$ the suffix
menu $\{RR\}$ gives seven by the same existing count recurrence;
its path shape is unchanged. These are applications of §12's retained
code result, not new alphabet formulas.

Thus, on attained data, the recoveries are

$$
 \text{actual terminal transcript}\ \longrightarrow\ B_K(t)
 \ \longrightarrow\ \Sigma_P(t)
 \ \longleftrightarrow\ e_S(v)
 \ \longleftrightarrow\ \mathcal H_P(t).
\tag{AAR.102}
$$

The reverse of the first boundary-to-statistic arrow fails in
(AAR.100). The last two arrows are the attained-image bijections
already proved in Theorems 12.3 and 12.6. Correct acquisition can
therefore require a finer spatial boundary than the memory eventually
needed to serve the exact declared menu. $\square$

**Mathematical citation 16.12 (existing suppliers and their exact ports).**
The structural addition (AAR.95)–(AAR.96) uses the following prior
results with their source, operation and target conditions retained.

| Supplier | Reused content and remaining interface |
| --- | --- |
| This volume, §§11–12 | Finite initial family, sufficient acquired boundary coordinates, guarded supplied-count decoder, joint spatial statistic and minimum retained alphabet. The full-source capture in Theorem 12.9 is sufficient but is not a minimum initial Read theorem. The present addition prices actual acquisition of its sufficient input. |
| This volume, §§13–15 | Exact singleton Read price, height-safe leaf/branch evidence and projected-source normalization with its pointwise obstruction. They are direct suppliers for (AAR.97), the bounded evidence transfer and the singleton checks; their exact single-address results are not proved again. Multiple hanging components and parent caps require Theorems 16.6–16.8. |
| [SLH §§35–43](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md#35-达到切点上的任意地址未来任务), especially Definition 40.3 and Lemma 43.2 | Future-code semantics, joint-query objective, shared boundary collisions and indispensable actual leaf evidence. Theorem 16.2 checks the latter's competitors inside $\mathcal F_D$. Theorem 43.5 minimizes terminal-record range, rather than maximum record length. No record-count argument substitutes for (AAR.96). |
| [CNA §§14–21](RECURSIVE_RELATIONAL_OBSERVATION_CONCURRENT_NATIVE_CUT_ACQUISITION.md#14-protected-entry-and-the-public-cut-geometry) | Ancestor-path coverage, successful ordered search and independently realized native completions. Its Release permits later paid full-tree acquisition and origin calibration. That continuation port differs from (AAR.86)'s passive decoder. Its deep-padding lower witnesses must not be assumed height-bounded. |
| [LQF §§2–5](RECURSIVE_RELATIONAL_OBSERVATION_LITERAL_QUERY_FRONTIER.md#2-all-legal-words-their-reply-cells-and-their-literal-lengths) and [AOF §§8–9](RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_ORBIT_RESOURCE_FRONTIER.md#8-stationary-interval-reading-with-a-zero-origin) | All-word reply classification and actual response-map simulation are existing methods. Their acquired atomic-slot histories or age intervals are different source families. LQF's identical-history pointwise domination is stronger than (AAR.91) and is not transferred. Theorem 16.3 supplies the bounded arbitrary-tree classification needed here. |
| [ActualTreeReadoutAcquisition](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean), `readout`, `flip`, `source_foundation`; [NativeDepthPatterns](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean), `original_present_transport`, `original_prefix_locality` | Native four replies, leaf relabelling and transport of originally present subtrees. The source module's `paid` counts distinct addresses for its separate task; (AAR.87) instead charges every actual call. Present-subtree transport does not transport from an absent address or supply an unacquired boundary. |
| [NativeSerialMachine](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.lean), `operational_replay`, `reached_prefix_replay`; [NativeIndependentExecution](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.lean), `native_history_correspondence` | Source-free control and same-source literal histories are native interfaces. The ordinary replay used here allows growing finite workspace. [ActualObserverPrefixRigidity](../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverPrefixRigidity.lean), `actualPrefix_replay`, has its stated finite-carrier observer premise and is not silently enlarged to prove the new minimax theorem. |
| [TargetFamilyMinimalQuotient](../../../D5/S3/ConceptDynamics/SufficiencyQuotient/TargetFamilyMinimalQuotient.lean), `target_family_minimal_quotient` | General minimal sufficient target factor, already applied in Theorem 12.6. It supplies no query-partition geometry or acquisition cost. |

A concrete failed transfer of CNA's cover functional is visible in
Theorem 16.10's split trie
$T=\{\varepsilon,L,LL,R,RR\}$. This is the internal skeleton of a
complete cut. Its ordered cover $LL,RR$ has new-ancestor counts
$(3,2)$, hence cover budget

$$
 \max\{1+\lceil\log_2 3\rceil,
          2+\lceil\log_2 2\rceil\}=3.
\tag{AAR.103}
$$

Its native joint passive-prediction acquisition needs four Reads by
(AAR.99). Finding one authentic leaf permits CNA's later calibration,
but does not resolve the other independent prediction component
without further Reads. This exposes the target/continuation mismatch,
rather than contradicting the cover theorem. The geometric joint
recurrence and its bounded interfaces are `repo-derived` ordinary
results; successful-search capacity, generic target factors and finite
decision-game reasoning are reused methods.

**Mathematical citation 16.13 (primary search models and failure boundaries).**
[Cicalese, Laber and Saettler, *Decision Trees for Function Evaluation:
Simultaneous Optimization of Worst and Expected Cost*, §1's DFEP
model and decision-tree costs](https://arxiv.org/pdf/1309.2796v2)
define finite objects, target classes, complete multiway tests, a prior
and positive test costs. Here objects are actual bounded sources,
classes are joint futures, and tests are literal four-reply words with
unit Read costs. Words through right-subtree depth $D$ already
separate initial sources; deeper words are constant absent. After
projection, the prefix boundary is the finite object tested. The
paper's class-determination model explains why output need not identify
the source. Its approximation and distributional conclusions do not
supply the exact native recurrence or the stronger compulsory evidence
that distinguishes acquisition from retained classification. No prior
or expected-cost conclusion is imposed here.

[Bose, Cardinal, Iacono, Koumoutsos and Langerman, *Competitive Online
Search Trees on Trees*, §1.1 and §1.3.2](https://arxiv.org/html/1908.00848v1)
use a vertex query that finds one hidden vertex or identifies the
connected component containing it. On an unresolved chain this gives
the familiar shallower/hit/deeper geometry. In the joint task a branch
reply instead leaves several components, all of which must be solved,
and absence prunes at the queried vertex's parent. Their one-target
component oracle, online rotations and pointer-move costs do not give
(AAR.95), whose positive continuation is a sum rather than the cost
of one chosen component. A constant-factor oracle simulation would
also be insufficient for an exact unit-Read correspondence.

[Zhu et al., *Budget Constrained Interactive Search for Multiple
Targets*, §3.2's target independence and question definition](https://arxiv.org/html/2012.01945v3)
provide a rooted-tree boundary-search comparison: their hidden target
set is an antichain, and a Boolean question asks whether a supplied
vertex reaches any target. Their budgeted objective chooses vertices
close to those targets. Our relevant labelled leaves form an antichain,
but a native Read distinguishes a local branch, two leaf labels and
absence; it is not a descendant-existence oracle. Further, (AAR.86)
requires exact predictions for every authentic count, rather than
budgeted closeness. Those operation and objective differences prevent
transferring its search optimizer.

[Eisel, McMullen and Muth, *An efficient search strategy for hidden
ideals in pointed partially ordered sets*, §1.1 and Definition 2.2](https://arxiv.org/pdf/2505.07604v1)
permit membership queries with a cap on positive answers, and define
an ideal to be empty or a principal downward set. Their directed-lower-set
convention is different from (AAR.90)'s arbitrary downward-closed
branch set. For the actual right subtree
$\langle\langle\alpha,\alpha\rangle,\langle\alpha,\alpha\rangle\rangle$
and the full relative depth-two menu, that branch set is
$\{\varepsilon,L,R\}$, with two incomparable maximal vertices, so it
is not principal. The source lies in $\mathcal F_3$. Their hidden-ideal
recurrence therefore does not characterize this branching labelled
boundary, even before comparing its binary membership test with the
four-reply native port. No cap on positive replies is assumed here.

[van der Linden, de Weerdt and Demirović, *Necessary and Sufficient
Conditions for Optimal Decision Trees using Dynamic Programming*,
§§4.2–4.3, Definition 4.2, Proposition 4.3 and Theorem 4.6](https://arxiv.org/pdf/2305.19706v4)
identify sufficient current states and a principle of optimality as
the ingredients of a dynamic-programming decomposition. Their
feature-learning formulation presumes a chosen binarization and its
own objectives and constraints. Here Theorem 16.6 proves the concrete
native sufficient-state property, including absent guards, caps and
bounded completions; Theorem 16.7 proves addition for simultaneously
realizable components. These bridges cannot be supplied merely by
writing a generic minimax decision-tree formula. Neither their
scalability results nor a polynomial evaluation bound are claimed for
(AAR.95).

These primary correspondences concern class determination, ordered
and tree search, discovering a rooted boundary, poset search and
constrained decision trees. They establish the stated reuse and its
limits, rather than worldwide originality or an exhaustive absence
claim for other literature.

**Theorem 16.14 (the recovery interface and its remaining resource boundary).**
Under Definition 16.1, (AAR.95) prices acquiring the native spatial
boundary sufficient for the fixed joint future task. After that
acquisition the retained predictive factor and the supplied-count
trajectory determine one another on their attained images, as in
(AAR.102). Neither this factor nor the attained Read minimum entails
recovery of the whole source, the full boundary representation, an
unknown lag, hidden equality or authentic later observation receipts.

Proof. The acquisition equality is Theorem 16.8, and the predictive
bijections are the reused Theorems 12.3–12.6. The strict loss of a
boundary distinction in (AAR.100) excludes a general inverse back to
$B_K$. The projection also discards arbitrary off-menu subtree
content while preserving every requested trajectory. Counterexample
11.9 supplies the separate same-future, different-hidden-equality
obstruction within this bounded family. Every menu
reply is branch after the public horizon $H_P\le2D$, so the predicted
vector cannot identify an unknown count beyond saturation. Computing
a later reply creates no Read event on that later version; obtaining
an authentic observation or a common-version collection has its own
paid interface, as in Proposition 15.4. Empty $P$ has constant output
regardless of source or count.

The recurrence is finite and effective, but no polynomial optimizer,
minimum transient workspace, address-traffic optimum, joint optimum
over all resource coordinates or physical spacetime recovery follows
from its Read equality. Stationarity and count authentication are
hypotheses, not acquired certificates. The one extra available height
level and independent leaf labels are used by the native realizations
and evidence argument; an exact-height promise, restricted labels,
nonstationary source, deeper menu, later unknown menu or unknown count
requires its own acquisition analysis. All statements here are
ordinary mathematical arguments. They carry no new kernel
certification and do not settle the full mutual-recovery programme.
$\square$

## 追加锚（本行以下为增补区）
