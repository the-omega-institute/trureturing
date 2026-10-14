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
