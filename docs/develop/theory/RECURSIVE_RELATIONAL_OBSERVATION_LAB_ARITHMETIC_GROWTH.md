# Recursive relational observation: exact LAB arithmetic growth and current records

> Append-only reference input for `generic-v1`. Incorporated text remains
> fixed; further results and corrections belong after the final empty append
> anchor. The proofs concern the declared ideal process, without Lean
> certification or a physical realization claim.

## 1. Source, task and correspondence

This continuation of [Atomic Generation Acquisition][AA], abbreviated AA,
uses its actual local-growth source, initialization and owned installation.
It determines the least successful growth needed for every exact weighted
increment, then installs a derived arithmetic service on that same source.
The arithmetic record identities are reused from [Arithmetic Refinement
Memory][ARM], abbreviated ARM. The source-specific optimization and its
actuator application are `repo-derived` ordinary mathematical deductions;
they are not new Lean certification or a claim of worldwide originality.

**Definition 1.1 (actual starting cuts).** Fix one installation satisfying
AA Assumption 20.1: a known allocated alpha root, its actual binding,
exclusive current source rights, retained ancestral tapes and their rights,
finite work storage, allocation, field and bit operations, local
acknowledgement and real return. Consider every attained quiescent cut of
this installation, including every attained history ending at the same
current term. The source is the very finite ordered term

$$
t::=\alpha\mid\beta\mid\langle t,t\rangle
$$

represented by AA Definition 17.3's oriented support. A logical beta leaf
has a material unary marker; that marker is not another logical leaf.
The reachable domain $\mathcal D$ is exactly AA Theorem 17.2's terms with
no alpha leaf at an $L$-ending logical address. The only source edits are

$$
P_p:\alpha\longmapsto\beta,\qquad
S_p:\beta\longmapsto\langle\beta,\alpha\rangle
\tag{LAG.1}
$$

at a current logical leaf of the indicated type. No graft, reset, copying,
rerooting, substituted software source or extra growth primitive is added.
This is LAB, not Native's simultaneous global substitution $\rho$.

Let $a(t),b(t)$ count logical alpha and beta leaves and retain the original
[Fibonacci Atomic Relation Generation](FIBONACCI_ATOMIC_RELATION_GENERATION.md)
(FARG) interpretation

$$
C(t)=q(t)=2a(t)+3b(t).
\tag{LAG.2}
$$

The actual source is not an arbitrary positive integer. Scalar notation
below describes a target for its quantity, not a supplied integer register.
All existence and completion assertions require the sufficient finite
material of AA20.1. An observable quota, exhaustion, interruption,
revocation or competing writer is outside that installation contract.

**Definition 1.2 (exact successful-event work).** For $t\in\mathcal D$ and
an integer $\Delta\ge0$, let $L_t(\Delta)$ be the least number of successful
$P/S$ events in a finite original legal continuation from that very $t$
ending at a source $u$ with $q(u)=q(t)+\Delta$. If no such continuation
exists, set $L_t(\Delta)=\infty$. The endpoint is otherwise unrestricted
in $\mathcal D$. Reads, navigation, refusals, tape and arithmetic
maintenance, printing, acknowledgement, return and waiting are separately
charged; none is a successful growth event.

A uniform lift of $A_c:C\mapsto C+c$ or $M_m:C\mapsto mC$ means one
installed finite algorithm terminating on every admitted actual starting
cut and declared finite positive parameter, using only (LAG.1) for source
changes and paid authorized observation/control. Its storage and duration
may grow with the actual source and parameter. The quantification includes
all histories and valid attached tapes at that source.

## 2. Exact weighted-target spectrum

**Lemma 2.1 (quantity image and a persistent beta target).** Every
$t\in\mathcal D\setminus\{\alpha\}$ has $b(t)\ge1$, and

$$
q[\mathcal D]=\{2,3\}\ \cup\ \{n\in\mathbb Z:n\ge5\}.
\tag{LAG.3}
$$

Proof. A non-alpha leaf source is beta. In a branch, follow logical left
children to a leaf. Its address ends in $L$, so the defining condition of
$\mathcal D$ makes it beta. A branch has at least two logical leaves,
including one beta, hence quantity at least five. The two leaf sources
have quantities two and three. Starting with beta, perform $k\ge1$ splits
at its continuing left beta descendant. Their quantity is $3+2k$.
Promote the right alpha made by the last split to obtain $4+2k$.
Every prefix is enabled on the same source: a split replaces its target
by a branch whose left child is beta and right child alpha. Beta itself
is attained by $P_\varepsilon$ from the allocated alpha. Thus all odd
values at least five and all even values at least six are attained, and
no other value is possible. In particular quantity four is absent.
$\square$

**Theorem 2.2 (all-source, all-increment least growth).** For every actual
starting source of Definition 1.1, $L_t(0)=0$. If $t\ne\alpha$, then for
every $\Delta>0$,

$$
L_t(\Delta)=
\begin{cases}
\infty,&\Delta=1\text{ and }a(t)=0,\\
\lceil\Delta/2\rceil,&\text{otherwise}.
\end{cases}
\tag{LAG.4}
$$

At the initial alpha source the complete remaining cases are

$$
\begin{aligned}
L_\alpha(2k+1)&=k+1 &&(k\ge0),\\
L_\alpha(2)&=\infty,\\
L_\alpha(2k)&=k+1 &&(k\ge2).
\end{aligned}
\tag{LAG.5}
$$

Every finite value is attained by the explicit current-leaf words below,
without inspecting or changing the earlier chronology.

Proof. A continuation with $p$ promotions and $s$ splits has

$$
a'=a-p+s,\qquad b'=b+p,\qquad
\Delta=p+2s,\qquad p+s\ge\lceil\Delta/2\rceil.
\tag{LAG.6}
$$

These follow from the actual templates, or from AA37.1's one-state
address classifier. The state equation alone does not establish legality;
the following words provide it. AA37.2 supplies the general guarded
counter-path lifting principle; here the targets are explicit.

Suppose first $t\ne\alpha$, and acquire a current beta at address $v$.
For $\Delta=2k>0$, split successively at
$v,vL,\ldots,vL^{k-1}$. Before each split its target is the current beta
left by the preceding split, or the acquired original beta. The word has
$s=k,p=0$. For $\Delta=2k+1$ with $k\ge1$, use those $k$ splits, then
promote at $vL^{k-1}R$, the still-current right alpha made by the last
split. It has $s=k,p=1$. For $\Delta=1$, one promotion at any acquired
current alpha attains the lower bound if $a>0$. If $a=0$, an increment
of one would require $p=1,s=0$, but no first promotion is enabled.
No intervening successful event of positive increment can repair that
target. These cases prove (LAG.4).

At $t=\alpha$, the first positive event must be $P_\varepsilon$. For odd
$\Delta=2k+1$, follow it by $k$ splits at
$\varepsilon,L,\ldots,L^{k-1}$, omitting that list when $k=0$.
The counts $p=1,s=k$ attain the universal lower bound. For $\Delta=2$,
the only count possibilities are one split or two promotions. A first
split is disabled, and after the first promotion there is only beta,
so a second promotion is disabled. For even $\Delta=2k\ge4$, a nonempty
legal word has $p>0$ and (LAG.6) forces $p$ even. Therefore
$p+s=k+p/2\ge k+1$. Attain this by $P_\varepsilon$, then $k-1$ splits
at $\varepsilon,L,\ldots,L^{k-2}$, then a promotion at $L^{k-2}R$.
This last leaf was really created by the last split and remains alpha.
Here $p=2,s=k-1$. All proper prefixes are legal. Finally the empty
continuation proves the zero case and is least. These matching witnesses
and lower bounds exhaust all nonnegative integers. $\square$

**Corollary 2.3 (exact total scalar-command domains).** For positive
parameters, $A_c$ lifts at every LAB source exactly when $c\ge3$.
For $c=1$ its failure set is exactly $a(t)=0$; for $c=2$ its failure set
is exactly $t=\alpha$. Multiplication $M_m$ lifts at every LAB source
exactly when $m=1$ or $m\ge3$. The failure set for $M_2$ is exactly
$t=\alpha$. In particular, for $t\ne\alpha$ and $m\ge2$,

$$
L_t((m-1)C(t))=\left\lceil\frac{(m-1)C(t)}2\right\rceil.
\tag{LAG.7}
$$

At alpha this value is zero for $m=1$, infinite for $m=2$, and $m$ for
every $m\ge3$.

Proof. Substitute $\Delta=c$ in Theorem 2.2. For multiplication substitute
$\Delta=(m-1)C(t)$. At a non-alpha source, $C\ge3$, so $m\ge2$ gives
$\Delta\ge3$. At alpha, $\Delta=2(m-1)$, giving exactly the exceptions
and values stated. The witnesses are generated by finite traversal,
finite counter arithmetic and the displayed loops, so are uniform in
both source and finite parameter under the paid access contract of §4.
The impossible inputs are actual admitted sources, not excluded imports.
In particular $M_2$ at alpha would require a quantity-four endpoint,
contrary also to (LAG.3). $\square$

**Corollary 2.4 (attached material).** Any exact-increment continuation,
not only a least-event witness, adds exactly $\Delta$ vertices to the
attached source support.

Proof. AA22.1 gives $V(t)=2a(t)+3b(t)-1=q(t)-1$ for this material
representation, including unary markers. Subtract at the two actual
cuts, or count one vertex per promotion and two per split. Reserved
unattached objects, tapes and all work material are additional. $\square$

## 3. Independently meaningful arithmetic tasks

**Definition 3.1 (two total macro continuation tasks).** Fix $H\ge2$ and
a positive divisor $d_o\mid H$. The old arithmetic task admits

$$
\mathcal A_o=\{H+d_o\},\qquad
\mathcal M=\{1\}\cup\{m\in\mathbb Z:m\ge3\}.
\tag{LAG.8}
$$

The enlarged task replaces the addend library by
$\mathcal A_n=\{H+d_o,H+1\}$, identifying duplicate addends if $d_o=1$.
A request is an addition with its admitted addend, a multiplication with
its admitted finite parameter, or a query. A macro acts by Corollary 2.3
on the actual source; a query leaves it unchanged. Every returned macro
or query exposes a fixed success acknowledgement and

$$
F_H(C)=H/\gcd(C,H).
\tag{LAG.9}
$$

All addends are at least three, hence every admitted macro is total at
every attained starting source. Behavior compares all same finite future
arithmetic request words, their complete scalar replies and continuation
behavior at their returned successors. It does not require equality of
the underlying successor trees. Initial values can be observed by query.
No time, work meter, internal Growth address, source query, legacy-request
interleaving, tape read or raw arithmetic-record read is an observation
or selector input of these scalar tasks. Their actual channels and
resources remain present in the richer process of §4.

**Proposition 3.2 (old and enlarged endpoint kernels).** On the actual
domain of Definition 1.1, old arithmetic behavior is classified exactly
by $B(C)=\eta_{H,d_o}(C)$ of ARM1.2 and FARG100.3. Enlarged arithmetic
behavior is classified exactly by $C\bmod H$.

Proof. Every operation and readout factors through the current residue
modulo $H$. Compare with FARG100.1–100.3's positive-integer arithmetic
task with the same addend library and all positive multipliers. Its only
multiplier absent from (LAG.8) is two. In any finite word of that task,
replace each $M_2$ by the admitted $M_{H+2}$. These have the same action
modulo $H$ on every current integer; induction on the word preserves
every endpoint $F_H$, including intermediate observations. This is
only a modulo-$H$ replacement, not an implementation of $C\mapsto2C$.

Thus two quantities are separated by the full scalar library if and
only if they are separated by the present total macro library. All
replacement macros really exist at every successor by Corollary 2.3.
FARG's classification applies with
$\gcd(H,H+d_o)=d_o$ for the old task and
$\gcd(H,H+d_o,H+1)=1$ for the enlarged task. With parameter one, its
local codes retain the complete residues. Conversely equal respective
codes give equal scalar replies and related codes at every successor,
by that same continuation classification. Finally every residue mod
$H$ has a representative at least five and therefore an actual LAB
source by Lemma 2.1. Restricting to LAB loses none of these behavioral
classes. Different shapes and histories with the same quantity remain
indistinguishable only for this declared scalar projection. $\square$

**Definition 3.3 (the reused current records).** Write
$H=\prod_{p^h\parallel H}p^h$, $e_p=v_p(d_o)$, and use the exact typed
local code of ARM1.2: for $r=\min(v_p(C),h)$ and $k=h-e_p$, it is
$S(r,(C/p^r)\bmod p^k)$ when $r<e_p$, and
$D((C/p^{e_p})\bmod p^k)$ otherwise. Zero residues use depth $h$;
the modulus-one coordinate is a singleton. These codes are well-defined
functions of $C\bmod H$. Put

$$
P=\prod_{\substack{p^h\parallel H:\ e_p>0,\ (p,h)\ne(2,1)}}p^h,
\qquad R(C)=C\bmod P,\qquad E(C)=(B(C),R(C)).
\tag{LAG.10}
$$

The empty product is one. Reuse ARM3.1's decoder
$D_E(E(C))=C\bmod H$: on selected prime-power axes use $R$, on an
unselected $e_p=0$ axis use $B$'s complete residue, and on the possible
unselected modulus-two axis use $B$'s parity. Combine by fixed CRT
constants. Every pair used below is in this same-source joint image.
All residues occur on LAB, so this image is the same $H$-element image
as ARM5.2, without importing ARM's lower-bound hypotheses.

Here $B$ has the independent old-continuation meaning of Proposition 3.2;
$R$ has the separate source-canonical and independent-update obligation
of §5. These meanings do not define either record by a desired inverse.
No assertion that $P$ is a least supplementary alphabet for this LAB
installation follows: ARM's minimum quantifies all positive sources and
all positive multipliers under its own record contract.

## 4. One installed, paid supervisor on the actual source

**Definition 4.1 (wiring and complete public interfaces).** Install before
the schedule one source-independent finite supervisor, fixed constants
$H,d_o$, the chosen addend policy, factorization/CRT data, finite-list
integer routines and two owned writable record fields. Use only AA20.1's
field, allocation, reference, bit and acknowledgement primitives. This
is an explicit extension of control and channel wiring, not a consequence
of a semantic integer or a new source-access oracle.

There are three bound connections in this single installation. The
arithmetic ingress/egress connects a requester to the supervisor. A
distinct internal request/reply connection binds that supervisor to
the actual AA20 driver on the same root and current grants. The public
legacy connection still offers all seven AA20.2 requests and their
complete literal replies, including FetchGrowth and Next. An owned
arbiter admits one complete call at a time at an outer idle cut. Once
an ingress starts a frame, the other ingress cannot start until return;
partial input retains its lock. No request archive, private allocation
ordinal, elapsed-time readout or resource-exhaustion branch is exposed.
All channel endpoints, latch and arbitration fields are installed and paid.

On the arithmetic connection use two-bit tags: $00$ for Add, $01$ for
Multiply, $10$ for Query and $11$ for BadFrame. Add and Multiply take
$U(n)=1^n0$, with positive $n$ required. A completed zero payload or a
parameter outside the installed policy returns BadParameter without
source change. The tag $11$ returns BadFrame with no payload. A proper
payload prefix waits for its suffix. Successful macro and query replies
are $00\,U(F_H(C))$: the fixed tag is the success acknowledgement and
the unary payload is the entire scalar result. Error replies are $01$
(BadFrame) and $10$ (BadParameter), with no payload. Each sealed finite
reply is really printed, followed by End; a separate supplied local
acknowledgement enables actual return and cleanup. Tag $11$ is unused
on replies. All actual bits, End and acknowledgement actions are paid.
Bad-parameter behavior depends on the frame, not on hidden source shape;
Definition 3.1's continuation tasks use admitted positive parameters.

Internal calls use the unchanged AA20.2 three-bit grammar, address
frame $A(p)=1^{|p|}0p$, reply tags and complete payloads. In particular a
successful growth prints its actual kind and literal address, not a
silent event or a scalar substitute. Its reply goes to the bound
supervisor receiver, which backs, parses and consumes every bit and End,
then performs the local acknowledgement. The saved call-continuation
and source binding survive the driver's root return. Legacy requests
instead print to their public legacy receiver, with their original
complete outputs. Neither routing choice deletes a produced public
reply: these are declared call origins with different actual recipients.
Their union is a richer observable service than the scalar task.

The scalar projection selects only its own endpoint replies and returned
cuts during arithmetic-only schedules. It grants no legacy read or
selection authority. If a requester is given the internal traffic, work
timing, original seven-request behavior or legacy interleavings, that is
the richer task; Proposition 3.2 is not its kernel assertion.

**Definition 4.2 (earned observation and word generation).** At an owned
quiescent cut, lock this source and perform AA26.2's finite source
traversal when required. A backed depth-first stack holds actual vertex
references, logical paths and traversal subphases. Read left/right/null
fields to parse arity; treat a unary marker as part of beta, never as
a logical child. At a branch traverse its real left and right children;
push/pop actual stack cells and maintain the corresponding acquired
address bits. A full traversal increments backed counters for $a,b$.
It can retain the first encountered leaf of each required type as both
its actual reference and acquired logical address. This uses no numeric
cast to an object and no persistent full syntax copy.

For $A_c$, acquire the root tag and, unless it is alpha, a current beta
locator by that traversal; exact leaf counts are unnecessary. For
$M_m$ with $m\ge3$, traverse and count the actual current leaves,
compute $C=2a+3b$ and $\Delta=(m-1)C$ in finite backed binary counters.
This is ordinary paid integer arithmetic on acquired counts, not a
source multiplication primitive. $M_1$ uses no traversal or growth.
Generate the corresponding witness of Theorem 2.2 with a remaining-split
counter, current beta address/reference and, if needed, the last-created
right-alpha locator. The alpha start uses its forced initial promotion.
After a split at $p$, update the beta locator to its real left child
at $pL$, and the new alpha locator to its real right child at $pR$.
No disjoint leaf or prior history is needed by these words.

For each planned event, really construct its internal addressed $P/S$
frame. The AA20 handler navigates again from the bound root, tests the
current tag/authority and executes its existing template. Retaining a
locator is not permission to bypass the actual guard. Reserve obtains
source and tape material before the edit. The original parent-chain
maintenance appends the actual event's side at each proper ancestor;
all old tapes remain the full callable tapes of the extended actual
generation word. The supervisor verifies the returned Growth kind and
address against its saved call, consumes the full reply and resumes its
finite loop only after the driver's real return. Theorem 2.2 proves
that these planned calls never receive a refusal in the stated model.

This one finite program handles arbitrary finite parameters through
backed loops; it has no table indexed by unknown sources. Installing
binary increment, multiplication, division-with-remainder and CRT
evaluation uses finite bit-list algorithms. Their intermediate operands,
loop controls, constants and bit work are charged, not oracle answers.
The word-generation subroutine works for every finite $c\ge3$ and
$m=1$ or $m\ge3$; installing that whole decidable dispatch domain gives
Corollary 2.3's uniform lifts. The two arithmetic tasks instead enforce
their stated finite addition libraries at Dispatch. A subroutine's wider
parameter domain does not enlarge either task's admitted outer requests.

## 5. Earned initialization and synchronized arithmetic commits

**Definition 5.1 (installation and event commit).** At the true allocated
alpha initialization, derive $C=2$ from that known constructed root and
write $B(2)$ and $2\bmod P$ into the actual record fields, with paid
computation and writes. If adding the supervisor at any later attained
quiescent cut, keep the existing root/tapes and lock them. Traverse that
actual source as in Definition 4.2, earn its exact counts, compute its
current $C$, and write both fields. Clear the acquired count/locator
scratch before making the arithmetic entry available. This is a
nondestructive paid initialization under the LAB owner's existing field
access; it does not assume an installed Native Read port on LAB, nor
assume ARM6.1's missing reader. Neither source acquisition nor the
syntax-to-count-to-residue fold is a new theorem here.

Modify only the mathematical control specification of this derived
installation as follows. Immediately before each successful source edit,
after guard success and before overwriting either arithmetic field, read
the pre-edit pair $(B,r)$ into backed temporary fields and compute

$$
\begin{aligned}
z&=D_E(B,r),\\
r^+&=(r+\delta_e)\bmod P,\\
B^+&=\eta_{H,d_o}((z+\delta_e)\bmod H),\qquad
\delta_e=\begin{cases}1,&e=P_p,\\2,&e=S_p.\end{cases}
\end{aligned}
\tag{LAG.11}
$$

Then execute that actual guarded source event and its tape maintenance,
write the two successors, finish all pending appends and only then
release a reply or permit another source request. The record receiver
for $r$ gets only its own pre-edit value and the kind of the actually
accepted event; it does not read $B,z,C$, a target endpoint or a locator.
The old-boundary updater may read the pair. Queries and refusals have
$\delta_e=0$ and leave both fields unchanged. The same commit hook
handles legacy addressed growth and the actual new event chosen by
legacy Next; it does not use Next's recalled old event as the increment.
No query, competing writer or outer availability intervenes between
an edit and these commits. There is no crash/interrupt recovery assertion.

The helper increments in (LAG.11) are private record algebra matched to
real $P/S$ events. They are not added external scalar commands $A_1,A_2$.
In particular they do not circumvent the alpha $+2$ obstruction.

**Definition 5.2 (outer Ready and busy checkpoints).** ArithmeticReady
has the same root cursor, valid full tapes and current rights, correct
current pair, idle arbiter, and empty request, output, arithmetic operand,
loop, snapshot, locator and traversal scratch. Only fixed code/constants,
bindings/grants, the retained actual source/tapes and the two added
arithmetic records remain callable. Old source/tapes are not counted as
part of the two-record payload and are not erased or free.

Busy control has Receive, Dispatch, Acquire, ComputeTarget, Plan,
CallSource, Commit, ConsumeReply, BuildScalar, PrintScalar and Return
subphases, with the backed fields described in §§4–5. Receive copies
an occupied bit latch into backing before clearing it. Partial frames
and unsupplied suffixes remain genuine busy states. CallSource includes
AA20.2's Reserve, edit, Maintain, answer, Print and Return subphases;
Commit is completed before its answer is released. The inner driver
may regain its own source Ready between calls while macro counters are
live. That is a busy macro checkpoint with extra fields, even if its
records already equal $E(q(t_j))$. It is not ArithmeticReady and no
external query or legacy call is enabled there.

On finishing a macro, decode the current pair, compute (LAG.9), build
and print its complete response and End, take the supplied local
acknowledgement, return both source and supervisor cursors to the same
root, and clear/reuse all source-dependent arithmetic scratch. Clear
the input backing, counters, locators, snapshots and output backing
before admitting another outer call. Legacy return also waits for
the commit, complete original reply, acknowledgement and cleanup.
Output and input backing are not a hidden persistent arithmetic archive.

**Theorem 5.3 (same-source continued use and real completion).** Under
Definitions 4.1 and 5.1's installed rights, finite programs, connected
receivers and sufficient finite resources, every actually supplied
complete admitted finite arithmetic frame from ArithmeticReady returns
its specified full reply on the same source binding and returns to
ArithmeticReady. Every successful-event checkpoint after commit has
the true pair $E(q(t_j))$ and the true extended ancestral tapes.
At returned macro endpoints,

$$
\begin{aligned}
q(t_{\rm after})&=q(t_{\rm before})+c &&\text{for Add }c,\\
q(t_{\rm after})&=m q(t_{\rm before}) &&\text{for Multiply }m,\\
E(q(t_{\rm after}))&=(B_{\rm actual},r_{\rm actual}).
\end{aligned}
\tag{LAG.12}
$$

These assertions extend to every finite arithmetic schedule and to
finite serialized schedules with complete legacy calls, retaining all
legacy outputs and the source/tape invariant. The scalar kernel assertion
of Proposition 3.2 remains restricted to its arithmetic-only task.

Proof. Initialization earns the actual current counts, or uses the
actually constructed seed, so its writes give the true pair. Suppose
the pair is correct before an event. Decoder correctness gives
$z=q(t_j)\bmod H$. The guarded event actually changes quantity by
$\delta_e$, so (LAG.11) gives precisely $E(q(t_{j+1}))$. Both new
values were calculated from the pre-edit snapshot. AA19.2 and AA20.3
restore the full-tape invariant for this same event before the call
returns. Refusals and queries leave these invariants unchanged; Next's
new event is covered by the same argument and AA20.5. Induction on
actual events proves both record and tape assertions, irrespective of
how long the earlier attained history was.

The locked finite source traversal terminates: each stack step visits
a remaining part of the actual finite tree or discharges a pending
return. Counts and locators therefore concern this source at this cut.
Finite integer routines compute a finite target. Each split loop strictly
decreases its finite remaining count; the fixed initial/final promotions
add finitely many calls. Theorem 2.2 proves each guard, and AA20.3's
finite parent-chain maintenance, finite reply printing and root return
prove completion of each internal call. The bound receiver consumes
every finite reply without an unprovided external acknowledgement.
No unknown selector or prospective endpoint is used in this induction.
Sum the actual increments in the witness: they equal $c$, or the
computed $(m-1)q(t_{\rm before})$, proving the first two squares in
(LAG.12). $M_1$ is the empty event word. The event invariant supplies
the third equality, hence the returned $F_H$ is correct by (LAG.9).

The scalar response is finite, so its actual printing, supplied local
acknowledgement, root return and finite scratch clearing terminate.
This proves an outer return with no hidden count or locator. Complete
invalid frames likewise give their fixed errors without growth.
Induct on completed outer calls for any finite schedule; the legacy
cases use AA20.3–20.5 and the same event hook. A proper input prefix
has not completed a call and may wait; supplying its finite completion
resumes the proof. Neither an infinite realized schedule nor any uniform
memory, runtime or capacity bound is asserted. $\square$

**Corollary 5.4 (arithmetic route agreement).** At the stated returned
cuts, reading the actual source and folding $q$ then reducing mod $H$
agrees with reading the two callable current records and applying $D_E$.
Both routes commute with every admitted returned arithmetic macro.
For the supplementary record alone the endpoint identities are

$$
r_{\rm after}=r_{\rm before}+c\pmod P,
\qquad r_{\rm after}=m r_{\rm before}\pmod P.
\tag{LAG.13}
$$

Proof. Both routes return $q(t)\bmod H$ by Theorem 5.3. Equation
(LAG.12) gives the same addition or multiplication on this residue
after either route. Summing (LAG.11) modulo $P$ and using the exact
quantity endpoint proves (LAG.13). The realized updater nevertheless
performs one update per actual growth event and uses actual source
navigation; these endpoint identities do not give ARM6.2's primitive
call bill or a source-free multiplication actuator. $\square$

## 6. Same-run resources and the precise optimum

**Definition 6.1 (separate resource coordinates).** In a returned macro
let $p,s$ be its actual promotion/split counts, $N=p+s$, and
$J=\sum_e|\operatorname{addr}(e)|$ over its actual growth events.
The displayed supervisor uses exactly $N=L_t(\Delta)$ successful growth
events. It adds exactly $\Delta=p+2s$ attached source vertices, $s$
tape headers and $J$ tape cells/side-bit appends. By AA22.1's layout,
its incremental located source-field assignments are $4p+8s$, and
its additional auxiliary-slot/header/tape assignments are
$\Delta+3s+4J$. These counts exclude allocation/grant operations,
reference-bit expansion and all other work. Starting at an arbitrary
later source does not remove the already retained source/tape cost.

The internal $P/S$ request at depth $d$ has $2d+4$ bits and its full
Growth reply has $2d+5$ bits under AA20.2. Thus for these successful
calls the supervisor generates $2J+4N$ request bits and actually
receives $2J+5N$ reply bits, also paying their transmission, backing,
parsing and clearing, plus $N$ End and $N$ local-acknowledgement actions.
Every reply's literal address is really emitted and consumed. Source
navigation, source-driver return and the saved continuation are additional;
this traffic is not compressed to the scalar reply for costing purposes.

An arithmetic parameter $n$ receives $n+3$ bits including the two-bit
tag; Query receives two. Each successful response emits $F_H(C)+3$
bits, plus its End and local acknowledgement. Unary input backing and
any binary parameter/counter conversion both occupy actual paid storage.
Every arithmetic or legacy error, query and original legacy reply has
its own actual frame and traffic. Record queries pay their actual reads,
decoder/gcd computation, output backing and emission; $M_1$ has zero
growth but still pays these input, control, response and return costs.

At each successful edit the specified implementation reads each old
arithmetic record, computes its backed snapshot/decoder and both
successors, and writes each successor before publication. Initialization
and endpoint output reads are additional. If a singleton $P=1$ record
is implemented as a constant, its zero data width removes no binding,
control or nonconstant old-boundary cost; if physically retained, its
accesses and backing are paid. No exact total-bit tariff is assumed for
these logical label reads/writes.

The same run separately pays all actual source-tag/arity and link reads,
reference/null tests, logical/physical-address correspondence and address
widths, traversal stacks, leaf locators and reference widths, $a,b,C$,
$\Delta$, parameter and remaining-loop counters, pending call/edit and
append state, reserved source/tape objects, all allocations and grants,
parent-chain maintenance, CRT/eta/gcd and ordinary bit arithmetic, both
record banks and their temporary values, channel latches, all output
and acknowledgements, root returns and scratch clearing/reuse. Installed
code, constants, factorization, CRT tables, endpoint/arbiter state and
their bindings are additional persistent resources. Peak simultaneous
material includes live scratch and unattached reserved material, not
only source vertices and the final two records.

**Proposition 6.2 (what is optimal).** Theorem 2.2's optimum is exactly
the successful-$P/S$ event coordinate for the given exact quantity
target and unrestricted endpoint shape in $\mathcal D$. No optimum of
total runtime, bit work, bit traffic, reference storage, peak material,
supplementary-record alphabet or physical cost is asserted here.

Proof. Theorem 2.2 minimizes that coordinate over all legal source
continuations and the supervisor attains its words. The other resource
coordinates just listed are not bounded below by $p+s$ alone and were
not minimized in its proof. In particular changing addresses changes
$J$, arithmetic parameters/counters and traversals cost work, and the
unchanged full tapes remain retained. ARM3.2's lower bound uses its
full positive-source/multiplier domain and independent-record contract;
the present domain lacks quantity four and total $M_2$. Its sufficient
decoder is reused without transferring that minimum. $\square$

The generator resources are relative to this declared process: promotion
is the only way to leave the initialized alpha, and split is the only
way to create another logical leaf. Removing either changes its command
domain. A callable arithmetic record needs actual field access and
binding; computation on an unbound description does not replace them.
Exact counts here are transient operands used for multiplication, not
a proved necessary representation for every conceivable actuator.
Likewise the full tapes are retained to preserve the legacy recall task,
not proved necessary for the smaller scalar task. The construction
claims no universal minimal generator set or bounded total memory.

## 7. Independent views, failures of recovery and falsifiers

**Proposition 7.1 (the connected recovery directions).** At the stated
quiescent domain, AA's bare oriented source space $S_0$ and terminal
antichain $B_0$ determine the actual ordered source, hence $q$, its
arithmetic behavior and the current records. The source-space and
terminal-boundary conversions agree with the two arithmetic routes of
Corollary 5.4. The actual generation chronology determines the weighted
change $\#P+2\#S$ and its actually maintained records. Callable $E$
determines exactly the enlarged scalar continuation behavior, and its
$B$ component classifies the old scalar behavior. None of these scalar
conclusions supplies a general inverse to shape, terminal antichain,
literal addresses, legal LAB menus or complete chronology.

Proof. AA17.3 and AA21.2 give the independent spatial/boundary meanings
and exact source conversions, retaining unary markers. Folding (LAG.2)
and Theorem 5.3 give the same current arithmetic values. The source
support also gives $q=V+1$. Equation (LAG.6) yields the chronological
weighted change; source/tapes retain AA's stronger generation semantics.
Propositions 3.2 and ARM's decoder give the stated arithmetic behavior
directions. The following explicit fibre separates the stronger task.
The reachable sources

$$
t_1=\langle\langle\beta,\beta\rangle,\alpha\rangle,
\qquad t_2=\langle\beta,\langle\beta,\alpha\rangle\rangle
\tag{LAG.14}
$$

are reached respectively by
$P_\varepsilon S_\varepsilon S_LP_{LR}$ and
$P_\varepsilon S_\varepsilon P_RS_R$. Both have $(a,b)=(1,2)$ and
$q=8$, hence identical $E$ for every fixed $H,d_o$. But $P_R$ is enabled
at $t_1$ and refused at $t_2$, where $R$ is a branch. Their shapes and
source boundaries also differ. Thus $E$ cannot be the complete original
seven-request boundary. AA18/21's distinct serial extensions at a fixed
source likewise prevent recovering chronology from $q$ or $E$; original
ancestral tapes remain the separately charged serial complement. Even
$M_1$ changes the complete call chronology while preserving source and
records. An arbitrary busy checkpoint additionally needs its pending
input, call, edit/commit and output fields. $\square$

The new connection is from actual legal local growth to an exact
arithmetic endpoint and an earned, callable current boundary on one
joint process. It supplies neither a new shape inverse nor a new
acquisition theorem. Native global-$\rho$ dynamics remains distinct:
FARG5.1's equal-$q=6$ compositions with successor quantities nine and
ten already preclude a quantity-only global-$\rho$ update. The present
local macros do not implement scalar multiplication on that apparatus.

**Definition 7.2 (falsification criteria).** A legal word shorter than
(LAG.4)–(LAG.5), or a displayed witness with a noncurrent/wrong-type next
target, refutes Theorem 2.2. In particular alpha/$\Delta=2$ has no word,
alpha/$\Delta=4$ needs three events, and all-beta/$\Delta=1$ has no word.
A returned macro whose actual source quantity fails (LAG.12), a returned
pair unequal to the current source's $E$, an unconsumed internal literal
reply, or a surviving callable arithmetic counter omitted from the
outer record/resource specification refutes the respective installation
claim. Giving the scalar requester internal addresses, busy queries,
legacy selectors or a work meter changes the task and requires another
boundary proof; a proof about the restricted projection would not
establish it. These criteria test actual source/control correspondence,
not correctness of a detached integer calculation.

The original fixed-$G_{\rm gc}$, original-$Q$, parked-consumer and
unchanged-initialization obligations retain their original statements.
Unknown-source weaker-access acquisition, arbitrary all-phase recovery,
Native global-$\rho$ continuation, the unrestricted positive scalar
interface, physical realization and whole-resource parsimony remain
outside the theorems here. There is no general mutual recovery of
independently meaningful space, time, boundary and memory, and this
bounded result does not complete that sustained objective.

## 8. Suppliers and literature boundaries

The definitions, optimization proofs and concrete joining of the
existing LAB actuator/access contract to the arithmetic task are
`repo-derived`. The indispensable supplier correspondences are as follows.

| Supplier | Exact reuse and remaining distinction |
| --- | --- |
| AA17–23 | Reachable $\mathcal D$, actual material source, full driver/replies/return, tapes and their task kernels; none is newly supplied by the quantity calculation. AA22 gives $V=q-1$ and the field/tape account. |
| AA26.1–26.2 | Locked actual-source traversal, real-reference/logical-address correspondence and backed finite conversion. Here the traversal earns counts and locators; it does not grant a Native Read port. |
| AA37.1–37.2 | Guarded finite leaf-counter transitions and prefix-legal lifting on each particular source. The added result is the closed all-increment least-event function, its forced-start exceptions and exact total scalar-command domains. |
| ARM1.2–1.4, 3.1, 5.1–6.2 | Exact eta code, selected-prime-power $P$, joint-image decoder and current-boundary algebra. Initialization here is actually earned on LAB and updates are per real source event. ARM's $P$ minimum, primitive scalar-call bill and source-free continued actuation are not transferred. |
| FARG2–5, 100.1–100.3 | Ordered syntax, original counts/quantity, the global-substitution obstruction and positive affine gcd-behavior classification. The only new task comparison is the explicitly justified modulo-$H$ replacement for the missing multiplier two. |
| [Transport Memory Completion][TM] §19.8 and §21.12 | Readable-syntax counting and paid finite modular derivation are already supplied. Their $M/G$ or digit/reset interfaces are different from actual LAB growth. |
| [Process Geometry][PG] §32 and [Native Clocked Recovery and Order][NCR] §§5–8 | Complete response/successor kernels and acquired clock/order complements already exist. NCR retains its fixed-controller atomic-Native-source and supplied clock hypotheses; the present result adds no all-cut recovery or clock. |
| [Native Paid View Conversion][PVC] §§1, 6, 10 | Actual acquisition, owner-installed converters, complete publication, acknowledgement and return are suppliers. Its fixed-$H$ entrance, once-only installation and unused-verifier-lane premises are not LAB capabilities or unchanged-old-controller conclusions. |
| [Transport Memory Completion][TM] §57 (PR57), especially D1–D3, D5 and T2 | Constructed tapes, actual paid source supply and complete guarded whole-action realization are supplied on PR57's original global-substitution/graft menu and Clifford Read. Their original ports, meter and capacity guard are not LAB's local edits or this tariff. |
| [Native Structural Storage Atlas][SSA] §§7, 9, 13.7 and [Native Callable Storage Atlas][ATLAS] | Structural inverses, acquired fixed-$H$ patches, backing, callable publication/return and source-specific continued use retain their own access/atomicity contracts. The gain here is the exact LAB weighted-target actuator spectrum and its paid current-boundary application, not a new generic converter, replay apparatus or four-view theorem. |

The associated formal sources retain their own hypotheses. In
`D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean`, `Source`
is `FreeMagma Bool` and `composition` is the two-leaf count fold;
`substitution` is global, not (LAG.1). In
`D5/S0/Computability/PreorderTreeEvaluation.lean`, `uniform_tree_fold`
supplies effective parameterized folds under its primitive-codable and
primitive-recursive hypotheses. Their same-path owning Blueprint Scribes
document those scopes. No new fold or formal computational certificate
is claimed for this installation.

`D5/S3/Factorization/PrimePowers/AffineGcdBehavior.lean`'s
`affine_action_realization`, the adjacent `GlobalAffineGcdBehavior.lean`'s
`global_encoding_complete`, and
`D5/S3/Arith/Congruence/PrimePowerAffineBehavior.lean`'s
`local_classification`, with their owning Scribes, supply the positive
scalar/local code mathematics reused in Proposition 3.2. They do not
give the source changes, access rights or output routing of §4.

The Native observer files `NativeSerialMachine`, `NativeFullSourceProducer`,
`NativeEffectiveSourceProducer` and `NativeSourceSelectorCode` under
`D5/S3/Arith/FibonacciAtomic/Observer/`, with their owning Scribes, already
supply actual nondestructive full finite-tree acquisition, numeric syntax
names, effective selection and concrete closed selector code.
`NativeSourceSelectorCode.realization` is consumed by
`NativeSerialEffective.original_code_service_simulation`. A syntax name
is not the quantity, but folding earned syntax is existing mathematics;
its classical `sourceDecoder` is not a needed actuator oracle. Native's
only source mutation remains global substitution. Those declarations do
not authorize addressed LAB edits or make them scalar multiplications.

| Primary reference | Literature-attested scope and correspondence |
| --- | --- |
| Geffroy–Leroux–Sutre, [*Occam's Razor Applied to the Petri Net Coverability Problem*, arXiv:1607.05956v1](https://arxiv.org/html/1607.05956v1), §2 and §5 | Nonnegative markings, input-token guards and firing semantics. With places alpha/beta, promotion consumes alpha and produces beta; split consumes beta and produces beta plus alpha. A state equation does not guarantee prefix legality. Theorem 2.2 uses actual spine words, not coverability or a continuous relaxation, for exact-target attainability and cost. |
| Engelfriet, [*Tree Automata and Tree Grammars*, arXiv:1510.02036](https://ar5iv.labs.arxiv.org/html/1510.02036), Definitions 3.1 and 3.62 | Recursive bottom-up evaluation and tree homomorphisms. Finite modular folding is supplied method; a tree homomorphism's ability to copy/delete/permute grants no such source operations here. |
| Forney, [*Codes on Graphs: Fundamentals*, arXiv:1306.6264v2](https://arxiv.org/html/1306.6264v2), §§2.1 and 2.3 | Joint valid configurations and internal/external behavior projection. Here channels, source and records are jointly realized before projection. Its linear/group realization theorems do not classify nonlinear eta labels or install source rights/readers. |

The pinned upstream mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`,
[`Mathlib/Algebra/Free.lean`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Free.lean),
supplies `FreeMagma`, `hom_ext`, `liftAux` and `lift`; universal folds
are reused, not an uncovered contribution. This is a bounded
source-and-operation comparison with the named suppliers. It makes
no nonexistence or originality inference from an absent API name, and
no finite example or numerical experiment substitutes for the quantified
proofs. All installation conclusions are conditional on the explicit
ideal owned primitives and finite-resource premises, not physical-device
claims or an unrestricted scalar-interface realization.

[AA]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md
[ARM]: RECURSIVE_RELATIONAL_OBSERVATION_ARITHMETIC_REFINEMENT_MEMORY.md
[TM]: RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md
[PG]: RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md
[NCR]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CLOCKED_RECOVERY_AND_ORDER.md
[PVC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_VIEW_CONVERSION.md
[SSA]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_STRUCTURAL_STORAGE_ATLAS.md
[ATLAS]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CALLABLE_STORAGE_ATLAS.md

## 追加锚（本行以下为增补区）

## 9. Actual pair actions and exact composition reachability

**Definition 9.1 (the pair extension of the literal LAB installation).**
Retain exactly the source representation, source binding, current exclusive
rights, ancestral routing tapes and seven-request driver of AA17–23 and
Definitions 1.1, 4.1 and 5.1 above. In particular the tape at every branch
records both kinds of actual generation event, not merely splits. Write

$$
v(t)=\binom{a(t)}{b(t)},\qquad
\mathcal D_+=\mathcal D\setminus\{\alpha\},\qquad
\alpha_{\rm vec}=\binom10,\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
\tag{LAGP.1}
$$

A composition target $(A,B)\in\mathbb N^2$ is reachable from a particular
$t$ if some finite legal addressed LAB continuation from that very source
ends at a term with those counts. This does not specify the endpoint
shape or erase the earlier attained history. All material, completion,
serialization and rights assumptions remain those of AA20.1. A call below
is a mathematical finite-control procedure on those objects, not a new
source primitive.

**Theorem 9.2 (exact source-relative pair reach criterion).** Let
$t\in\mathcal D_+$ have composition $(a,b)$, so $b\ge1$. For every
$(A,B)\in\mathbb N^2$,

$$
t\longrightarrow^* \{u:v(u)=(A,B)\}
\quad\Longleftrightarrow\quad
B\ge b\ \hbox{ and }\ A+B\ge a+b.
\tag{LAGP.2}
$$

Whenever this holds, every realizing word has precisely

$$
p=B-b,\qquad s=A+B-a-b
\tag{LAGP.3}
$$

promotions and splits. From the excluded source alpha the exact criterion
is instead $(A,B)=(1,0)$ or $B\ge1$. Consequently
$v[\mathcal D_+]=\mathbb N\times\mathbb N_{>0}$.

Proof. Every actual promotion changes composition by $(-1,1)$, and every
split by $(1,0)$. Thus $B=b+p$ and $A=a-p+s$, proving necessity and
(LAGP.3), including their nonnegativity.

For sufficiency acquire a current beta leaf at address $z$. Carry out
$s$ splits on its continuing left beta spine, at
$z,zL,\ldots,zL^{s-1}$, with an empty list when $s=0$. Each target is the
beta left by the preceding split. The current counts are now $(a+s,b)$.
The target inequalities give $0\le p\le a+s$. Traverse the current finite
source and promote its first $p$ alpha leaves in preorder. Promotions at
distinct leaves preserve the other leaves, so all these operations are
enabled. The resulting counts are $(A,B)$. This is a legal addressed word
on each particular starting source, not just a solution of its state
equation. It is also the one-state instance of AA37.2's supplied
current-leaf lifting principle.

At alpha, a nonempty word must start with the root promotion, after which
the preceding construction applies to $(0,1)$. For any $A\ge0,B\ge1$,
use $s=A+B-1$ splits and then $p=B-1$ further promotions; $p\le s$.
The empty word is the only possibility with $B=0$, since beta count
never decreases. This proves the alpha criterion and realizes every
stated positive-beta composition from the known seed. Lemma 2.1's
beta assertion, or the leftmost-leaf argument in its proof, identifies
these sources with exactly $\mathcal D_+$. $\square$

**Definition 9.3 (the two actual macros).** For a current finite source
$t$, acquire its complete logical leaf frontier in left-first order,
while the source is stationary. A frontier row contains the actual
target reference, its backed logical address and its acquired alpha/beta
tag. Rows have real next links. Exclude every material unary marker.
The finite traversal of Definition 4.2 constructs this list through
individual field operations; the list is not an input supplied by an
unknown source.

The macro $\mathsf R$ traverses this sealed entry list once. For an
entry-alpha row at $p$ it calls the original addressed $P_p$; for an
entry-beta row it calls the original $S_p$. It consumes the complete
literal reply and real return of each inner call before advancing the
list. Newly created leaves never enter this old list.

For $t\in\mathcal D_+$, follow current logical left children from the bound
root to its first leaf, acquiring the path and actual reference. Let
$\lambda(t)$ be this acquired address. The macro $\mathsf G$ makes the
single original call $S_{\lambda(t)}$, consumes its complete literal
reply and returns. All calls navigate from the same bound root, check
the current guard and compare the reached reference with the acquired
operand. Holding a reference does not bypass current authority or a guard.

**Theorem 9.4 (exact replacement, alpha translation and the alpha
obstruction).** On every particular $t\in\mathcal D_+$ and every admitted
earlier history ending there, the procedures of Definition 9.3 terminate
under the stated finite-resource premises, use only original legal source
events and satisfy

$$
\mathsf R(t)=\rho(t),\qquad
v(\mathsf R(t))=Mv(t)=(b,a+b),\qquad
v(\mathsf G(t))=(a+1,b).
\tag{LAGP.4}
$$

Their successful-event counts are respectively $(p,s)=(a,b)$ and $(0,1)$.
These event counts are forced for their respective pair targets.
Both successors lie in $\mathcal D_+$. The action $\mathsf R$ alone also
works at alpha, but there is no LAB procedure with the claimed
$\mathsf G$ pair effect there. Thus $\mathcal D_+$ is exactly the domain
within $\mathcal D$ where both pair actions can be total.

Proof. Distinct entry leaf addresses are prefix-incomparable. A local
edit at one changes no subtree rooted at another, and does not move its
root reference. Induct over the sealed list: before its next row the
acquired tag, address and reference are still current at that target.
Its original guard therefore succeeds. An original alpha becomes beta;
an original beta becomes $\langle\beta,\alpha\rangle$. Every original
branch and its ordered child positions persist. Structural induction
now identifies the endpoint with FARG3.1's literal $\rho(t)$, not merely
a term of equal quantity. In particular the unary marker reused during a
split was not an entry logical leaf and never receives another scheduled
edit. Finite list length and AA20.3's finite inner calls prove termination.

The leftmost leaf of a non-alpha source in $\mathcal D$ is beta: if the
root is not itself beta, the final edge of its left descent is $L$, where
alpha is forbidden. Thus the single split defining $\mathsf G$ is enabled
and has effect $(1,0)$. Each procedure preserves the beta-positive domain.
The forced counts follow by substituting the two targets in (LAGP.3).

For alpha the desired target would be $(2,0)$, excluded by Theorem 9.2.
Equivalently any promotion irreversibly creates beta, whereas a first
split is disabled. Reads, arithmetic and rejected calls cannot repair
this obstruction. The macro $\mathsf G$ is a local split, not a literal
root graft $t\mapsto\langle t,\alpha\rangle$: at
$t=\langle\beta,\beta\rangle$ its endpoint is
$\langle\langle\beta,\alpha\rangle,\beta\rangle$, different from
$\langle\langle\beta,\beta\rangle,\alpha\rangle$. This $t$ is attained by
$P_\varepsilon S_\varepsilon P_R$. No new parent, rerooting or graft right
has been used. $\square$

## 10. Earned pair memory and complete finite pair calls

**Definition 10.1 (initial acquisition and retained fields).** Fix a
public pair modulus $H\ge1$. Keep the scalar service's existing modulus
$H_s\ge2$ and divisor $d_o\mid H_s$; one may choose $H_s=H$ when $H\ge2$.
All inherited scalar symbols $E,B,P,r_s$ below retain that scalar
modulus. Add two owned pair fields $e,c\in A_H^2$, where
$A_H=\mathbb Z/H\mathbb Z$. The immutable
$e$ records the pair at attachment; the mutable $c$ records the current
source pair. They supplement the existing scalar fields
$E(q(t))=(B(q(t)),r_s(q(t)))$, with $r_s=q(t)\bmod P$ as in (LAG.10).
They do not replace those scalar fields or the ancestral tapes.

At an attained quiescent attachment cut $t_0$, lock the actual source
and traverse its logical leaves through its existing read rights.
Initialize a scratch residue pair to $(0,0)$; each actually observed alpha
adds $(1,0)$ and each beta adds $(0,1)$, modulo $H$. The stationary finite
traversal visits each logical leaf exactly once. Really write its result
to $e$ and $c$, then clear the traversal, path and accumulator scratch
before enabling new outer calls. Existing source, tapes, scalar records,
bindings and rights remain attached. At the actually constructed alpha
seed the pair $(1,0)$ is instead known from that construction and may
be written directly. In either case all computation, reads, writes,
allocation and cleanup are charged.

The attachment need not acquire exact integer counts or the previous
word. At a later cut it uses actual source access, not a supplied unknown
seed, a Native Read port or a hypothetical complete behavior oracle.
Attachment at alpha maintains correct fields, but successful pair calls
have the domain $\mathcal D_+$ specified below; existing legacy or scalar
growth can subsequently enter that domain.

**Definition 10.2 (one coexisting connection and framing contract).**
Keep the scalar and public legacy connections, and their internal bound
driver connection, of Definition 4.1. Add a distinct pair requester and
reply connection to that same supervisor. A single owned arbiter
serializes all three outer ingresses from a returned idle cut. A call
holds the lock through input, inner calls, commits, complete output,
local acknowledgement, root return and cleanup. Inner returns do not
release the outer lock. All connection fields, grants and arbiter
storage are part of the installation.

On the pair connection use the following complete grammar, with
$U(k)=1^k0$ and word bits $0=\mathsf R$, $1=\mathsf G$.

| Pair request | Complete input | Complete reply at a source in $\mathcal D_+$ |
| --- | --- | --- |
| $\mathsf R$ | $00$ | $00$, a fixed acknowledgement |
| $\mathsf G$ | $01$ | $00$, the same fixed acknowledgement |
| $\operatorname{Out}$ | $10$ | $01\,U(d)$, where $d=\gcd(2c_1+3c_2,H)$ |
| $\operatorname{Predict}(W)$ | $11\,U(k)\,w_1\cdots w_k$, $k=|W|$ | $10\,U(k)\,U(d_0)\cdots U(d_k)$ |

For prediction let $\xi_0=c$ and, for $0\le i<k$, put
$\xi_{i+1}=M\xi_i$ for $w_{i+1}=0$ and
$\xi_{i+1}=\xi_i+(1,0)$ for $w_{i+1}=1$. Its payload has
$d_i=\gcd(2\xi_{i,1}+3\xi_{i,2},H)$ for every prefix, including the empty
one. Gcd is evaluated on integer residue representatives; it is
representative-independent. Prediction changes neither source nor current
records. The $k=0$ request returns precisely the one current value.

After receiving the complete frame, test the actual root constructor.
At alpha every pair request returns $11$ with no payload and no source
change. Thus an alpha refusal is not decided from a modular pair that
might coincide with an admitted source's pair. Every complete pair frame
is one of these cases; there is no unused request tag. Concatenated calls
are parsed successively. A proper frame prefix retains its acquired bits,
parser subphase and remaining length and waits for its supplied suffix;
it has no premature reply or implicit timeout.

Every finite reply is sealed in backing, really printed to that call's
pair receiver and followed by End. The supplied local acknowledgement
enables real return and cleanup. Rights failures, competing writers,
interruptions and resource exhaustion have the same excluded status as
in AA20.1, rather than extra source-dependent reply tags.

**Definition 10.3 (unchanged recipients and complete inner traffic).**
Scalar Add, Multiply, Query and their invalid frames keep exactly
Definition 4.1's grammar, allowed parameters and replies. The seven
public legacy calls keep AA20.2's exact request/reply grammar. In
particular Tag, HasPromotion, HasSplit, addressed $P/S$, FetchGrowth and
Next retain their original complete results and original legacy receiver.
An out-of-range Next has no new growth. An in-range Next still outputs
both the acquired old event and the actual newly selected event.

Every $P/S$ call made by either scalar or pair macros uses the original
internal addressed frame and prints the full Growth kind/address reply
to the bound supervisor receiver. The receiver backs and parses every
bit and End, checks its saved kind/address and actual continuation,
acknowledges and consumes the driver's real return. A legacy-origin
Growth or Next reply instead goes to its original public receiver.
There is no suppression of a literal reply because a larger macro later
returns only a fixed acknowledgement or scalar value. These distinct
recipients are fixed actual connections, not a retrospective deletion
of outputs. All their traffic belongs to the joint process.

## 11. A single all-event synchronization invariant

**Definition 11.1 (pre-edit banks and accepted-event commit).** Extend the
existing commit of Definition 5.1 at every successful source event,
irrespective of its outer or inner origin. After actual guard success,
reserve the required material, retain the accepted kind, target
reference/address and unfinished maintenance cursor, and read the
pre-edit arithmetic fields into backed temporary fields. From the
pre-edit pair $c^-$ compute

$$
c^+=
\begin{cases}
c^-+(-1,1),&P_p,\\
c^-+(1,0),&S_p,
\end{cases}
\quad\text{in }A_H^2.
\tag{LAGP.5}
$$

Compute the two scalar successors from the pre-edit scalar snapshot by
(LAG.11), with increment one or two respectively. Execute the actual
guarded source template, complete all ancestral tape appends, write every
arithmetic successor, and discharge the pending edit/append/commit state.
Only then may BuildAnswer release that event's original literal reply.
Keep $e$ unchanged. All simultaneous formulas use old operands; a field
overwritten while computing another is not a substitute for its snapshot.

Queries, predictions, refusals, input/output work and acknowledgements do
not change any source arithmetic record. For Next the hook is attached
to its one newly executed $P/S$ event. Its recalled old event is an
operand of the selector, not another edit or increment. Legacy growth,
Next growth, scalar-macro growth and pair-macro growth all pass this
same accepted-event hook. Source-independent arithmetic changes are not
additional edits.

PairReady is the returned idle domain with root cursor, true full
ancestral tapes, current rights/bindings, correct scalar fields and
$c=\overline{v(t)}$, immutable $e=\overline{v(t_0)}$, and empty transient
input, output, traversal, frontier, locator, call, arithmetic and pending
fields. The source need not be in $\mathcal D_+$ for this idle predicate;
that is separately the success domain of pair requests. Busy states
retain their actual finite backing: received bits and remaining lengths;
old-frontier rows and list cursor; source root/current reference and path;
saved inner continuation; reserved objects and pending appends; old/new
arithmetic banks; prediction word, cursor and scratch pair; and sealed
output with emission cursor. None is identified with PairReady merely
because the inner driver has reached its own Ready.

**Theorem 11.2 (common-source acquisition, synchronization and completion).**
Under Definitions 9.1 and 10.1–11.1, every supplied complete finite outer
call returns on the same bound root with its specified full reply and
reenters PairReady. Every finite serialized mixture of all three outer
interfaces has, at each returned cut,

$$
c=\overline{v(t)},\qquad
(B,r_s)=E(q(t)),\qquad
e=\overline{v(t_0)},
\tag{LAGP.6}
$$

and the original literal tapes for its entire actual generation word,
including every pair/scalar macro edit and every new Next edit.
At a completed pair action the exact source and vector laws are
(LAGP.4), not merely congruences.

Proof. The initial leaf traversal earns the residue fold of the actual
stationary tree, so its writes establish (LAGP.6). Existing scalar
correctness and tape invariants hold at the attachment cut by the
hypotheses. They are also established directly at the known seed.
Suppose they hold before an accepted event. Its two actual vector
increments are exactly those in (LAGP.5), and its actual quantity
increments are those in (LAG.11). Both pre-edit snapshots therefore
give the true successors. AA19.2 and AA20.3 give exactly the proper
ancestral appends for that very event. Completing all three changes
before publication proves the invariant at its next available cut.

The argument applies to Next's actual new kind/address after its real
recall and current left descent. Its old kind can differ from the new
one, so counting the recalled event instead would not prove the
invariant. OutOfRange, queries, refusals and prediction have no edit.
Induction on actual accepted events establishes (LAGP.6) without any
assumption on the earlier chronology at a fixed source.

For $\mathsf R$, stationary finite traversal constructs the old-frontier
operands. Theorem 9.4 proves each next guard and the exact endpoint;
AA20.3 proves that each inner call, literal output and return terminates.
The caller's list cursor and remaining rows survive these inner returns
until consumed. The finite list then exhausts. For $\mathsf G$, finite
left descent and its single accepted split prove the same assertions.
Every intermediate commit has the true current pair; no erroneous
macro-end overwrite by $Mc$ or $c+(1,0)$ is performed after these
per-event updates.

Out reads the correct finite pair and performs finite gcd arithmetic.
Predict consumes its actual finite word, copies $c$ to scratch, performs
the stated finite updates and builds all $k+1$ results. Neither uses a
source response table. At alpha the actual root guard gives the fixed
refusal after full input receipt. Original scalar calls terminate by
Theorem 5.3 and the same hook; legacy calls terminate by AA20.3–20.5.
Every result word is finite. Its Print, End, supplied acknowledgement,
root return and finite clearing/reuse of transient backing restore
PairReady. Proper prefixes instead remain busy until their completion
is supplied. Induction on returned calls proves the entire mixture.
No intermediate macro cut admits another outer call. $\square$

## 12. The selected arithmetic task and its exact recovery domain

**Definition 12.1 (pair task, source projection and independent fields).**
The selected task $Q_{\rm pair}$ uses only the four pair requests at
returned cuts with $t\in\mathcal D_+$. Its observations are their complete
pair-channel replies, legality and continued $Q_{\rm pair}$ behavior at
the actual returned successors. All same finite pair-request sequences
are compared. The task admits no legacy or scalar interleaving, raw
source/record reads, internal driver traffic, scratch read, time/work
meter, allocation ordinal or observable capacity guard as observation or
selector input. These remain distinct resources or channels of the
larger process. Authentic binding and rights are fixed at this domain;
they are retained premises, not values encoded by a residue.

Write $F_W(t)$ for the actual source reached by the chronological
$\mathsf R/\mathsf G$ word $W$. Define the following arithmetic fields
independently:

$$
\begin{aligned}
\mathcal S_H(t)&=\overline{v(t)},\\
\mathcal T_H(t)(k)&=(2,3)M^k v(t)\pmod H,\quad k\ge0,\\
\mathcal B_H(t)(W)&=\gcd(q(F_W(t)),H).
\end{aligned}
\tag{LAGP.7}
$$

$\mathcal S_H$ counts occurrences of the two actual logical leaf types.
$\mathcal T_H$ is the prospective quantity progression of successive
whole-frontier replacements, not actual elapsed time or a supplied
clock. $\mathcal B_H$ is the controlled continuation boundary of the
declared pair actions, not just its current gcd. The acquired memory
contains actual $e,c$, source/tapes, code, bindings, rights and retained
work facilities. Its current pair field computes these arithmetic
expressions; the expressions do not define that whole installation.

**Theorem 12.2 (operation correspondence and restricted recovery).**
For every $t\in\mathcal D_+$ and finite chronological $W$,

$$
v(F_W(t))=\operatorname{Run}(W,v(t)),\qquad
\operatorname{Run}(\mathsf R,u)=Mu,\quad
\operatorname{Run}(\mathsf G,u)=u+\alpha_{\rm vec}.
\tag{LAGP.8}
$$

Under Theorem 11.2, the actual callable $c$ supports current Out and
every specified prediction, with

$$
c_W=\overline{v(F_W(t))},\qquad
d_i=\gcd(q(F_{W_{\le i}}(t)),H)
\quad(0\le i\le |W|).
\tag{LAGP.9}
$$

The fields in (LAGP.7) mutually recover one another on their actual
arithmetic images, their routes agree, and they commute with these
pair actions. Equality of $Q_{\rm pair}$ behavior is exactly equality
of $\overline{v(t)}$. There are exactly $H^2$ behavior classes across
all admitted attained starting sources. When $H_s=H$, at a returned cut
the pair Out value times the existing scalar Query value is exactly $H$.

Proof. Theorem 9.4 supplies each actual action, its authentic operands,
same-source legality and exact vector effect. The beta-positive domain
is invariant, so induction on $W$ proves (LAGP.8) at every prefix.
Theorem 11.2 then gives the first equality in (LAGP.9). Scratch execution
has the same residue updates, proving the entire prediction reply,
including the empty prefix. This proves the actual source correspondence
required before using an arithmetic supplier. When $H_s=H$, the
same-source current records give Out equal to $g=\gcd(q(t),H)$ and scalar
Query equal to $H/g$, proving their stated product. This identity concerns their
current replies, not equality of their future task kernels.

Now reuse the mathematical recovery and synchronized-continuation
formulas of [Arithmetic Acquisition Return][AQBR] Definition 9.2,
(AQBRP.22)–(AQBRP.23), and Theorem 10.3. The parameter correspondence
is its same $H$, $q=(2,3)$, $M$, alpha translation, chronological words,
current residue and fixed action acknowledgements, restricted here to
the invariant image $\mathbb N\times\mathbb N_{>0}$. Our initial pair
is earned by the stronger field access of Definition 10.1, and the
macro source/commit bridge is Theorems 9.4 and 11.2. Thus this reuse is
of its recovery/continuation conclusion, not its opaque-port acquisition
procedure, read-count theorem or literal source model.

Concretely its supplied FARG5.4 inverse applies to the first two terms
of $\mathcal T_H$:

$$
\binom{n}{z}=
\begin{pmatrix}2&3\\3&5\end{pmatrix}\mathcal S_H,\qquad
\mathcal S_H=\binom{5n-3z}{-3n+2z}\quad\text{in }A_H^2.
\tag{LAGP.10}
$$

The forward progression and the boundary are computed from this same
pair by (LAGP.8). FARG130.5, or GraftAffineClosure.result with actual
graft composition $(1,0)$, says that different residues are separated
by a common positive $\mathsf R/\mathsf G$ word's terminal gcd. Every
such word is actually legal from every LAB source in this domain.
Thus restriction to beta-positive compositions loses no separating
word. Equal residues give all same replies and equal successor residues;
Predictions add only the corresponding finite prefix replies. Conversely
execute a separating word and Out to distinguish unequal residues.
This proves the exact task kernel and the boundary-to-pair recovery
on its actual image.

All residues occur here: for residues $x,y$ choose $A=x$'s least
nonnegative representative and $B=y$'s representative if positive,
or $B=H$ if it is zero. Theorem 9.2 constructs an attained LAB source
of $(A,B)$. Hence the kernel has exactly $H^2$ classes. The same
separating-word argument forces any autonomous representation for this
selected task across all these starting sources to distinguish them.
It is a task-state alphabet assertion, not a minimum for the retained
literal installation.

Every route just described evaluates the same current residue.
At $H=1$ it is the singleton pair and every arithmetic output is one;
the same actual source actions, domain guards and literal traffic remain.
For $\mathsf R$ the progression shifts by one; for $\mathsf G$ its
$k$th term increases by $(2,3)M^k\alpha_{\rm vec}$. Boundary successors
prefix the same actual action to the tested word. These identities and
(LAGP.9) prove route agreement and dynamics compatibility. They do not
recover actual chronology from a prospective progression. $\square$

**Theorem 12.3 (strict limits of the arithmetic kernel).** The
$H^2$-class assertion is not a classification of the joint legacy,
scalar and pair process, its Tag/legal-address behavior, its literal
tapes or its complete chronology. Equality of scalar quantity does not
imply equality of vector successors or even scalar successors under
$\mathsf R$.

Proof. The two sources of (LAG.14) have the same exact composition and
therefore the same pair residues for every $H$. Nevertheless $P_R$ is
enabled at one and refused at the other, and Tag at $R$ separates them.
AA20.5's two histories at its common source have identical composition
but different FetchGrowth$(3)$, Next output and Next successor.
The literal-backend invariant of Theorem 11.2 retains these distinctions;
no arithmetic theorem identifies them.

For a counterexample entirely within $\mathcal D_+$, take compositions
$(3,1)$ and $(0,3)$, both attained by Theorem 9.2. Their quantities both
equal nine, whereas their replacement compositions are $(1,4)$ and
$(3,3)$, with quantities fourteen and fifteen. Modulus three already
separates their post-replacement gcds. Thus neither a scalar endpoint
nor the existing scalar records can authorize a vector-successor
identity. The new $\mathsf R$ is not one of the old scalar Add/Multiply
macros.

Finally $\mathsf G^H$ changes the actual source, adds $H$ real splits
and extends the old tapes, while returning its pair residue and every
selected arithmetic continuation behavior to their entry values.
Consequently the arithmetic fields recover neither the syntax, event
word, literal traffic, actual time/work nor whole memory. Their
mathematical inverses do not grant new references or rights. $\square$

## 13. A single same-run resource account

**Definition 13.1 (located work and backing on the joint run).** For
any finite suffix of the one actual execution let $p,s$ be its successful
promotion/split counts and let

$$
N=p+s,\qquad J=\sum_{\text{actual new events }e}|\operatorname{addr}(e)|.
\tag{LAGP.11}
$$

Count events from all pair macros, scalar macros, accepted legacy
addressed calls and in-range Next calls once. Recalled old events,
queries, prediction, refusals and acknowledgements contribute no event
to this sum. Add the source, headers and tapes already present at
attachment; no account discards that earlier material.

For each completed pair $\mathsf R$ whose entry counts are $(a,b)$,
its event list has

$$
p_{\mathsf R}=a,\quad s_{\mathsf R}=b,\quad
N_{\mathsf R}=a+b,\quad
J_{\mathsf R}=\sum_{z\in\operatorname{Leaves}(t)}|z|.
\tag{LAGP.12}
$$

For $\mathsf G$ with acquired leftmost address of depth $d$ the
corresponding values are $p_{\mathsf G}=0,s_{\mathsf G}=1,
N_{\mathsf G}=1,J_{\mathsf G}=d$. Traversal, field access, operand-list
construction, arithmetic, output and return are additional actual
work, rather than successful source events.

**Theorem 13.2 (literal source, tapes, traffic and operands are jointly
accounted).** On this same finite suffix the incremental attached
source/tape resources are

$$
\begin{aligned}
\text{source vertices}&=p+2s,\\
\text{tape headers}&=s,\\
\text{tape cells and side appends}&=J,\\
\text{located source-field assignments}&=4p+8s,\\
\text{auxiliary-slot/header/tape assignments}&=p+5s+4J.
\end{aligned}
\tag{LAGP.13}
$$

The two assignment coordinates use precisely AA22.1's layout and
exclude allocation, grants and reference-bit expansion. Across any
set of macro-origin successful inner calls with values $N,J$, the
request/reply bit totals are respectively $2J+4N$ and $2J+5N$, together
with $N$ reply End and local acknowledgement actions. Each such reply
is actually received by the supervisor. Legacy-origin calls instead
retain their original complete public traffic, charged separately.

Proof. AA22.1 and Definition 6.1 count one or two new source vertices
per actual promotion or split, one header per split and one appended
side cell per proper ancestor. Every present event, including each
Next-selected edit, satisfies exactly that layout. Summing its located
assignments gives (LAGP.13); the last expression is
$(p+2s)+3s+4J$. No event is charged twice merely because both a pair
record and a scalar record observe it.

For an inner event at depth $d$, AA20.2's addressed request has $2d+4$
bits and Growth reply has $2d+5$. Summation proves the totals.
Their full kind/address payloads are not replaced in the account by
the shorter outer acknowledgement. A successful legacy Next has its
original pair of old/new kind-address payloads, hence $2d_{\rm old}
+2d_{\rm new}+7$ reply bits, plus End and acknowledgement. An in-range
FetchGrowth has $2d_{\rm old}+5$ reply bits; OutOfRange has its three-bit
tag. Other legacy payloads and scalar calls retain their exact original
frames from AA20.2 and Definition 4.1. All their input, backing,
navigation, emission, acknowledgement and return work is additional.
$\square$

**Definition 13.3 (remaining simultaneous resources).** Pair input
costs two bits for $\mathsf R,\mathsf G,\operatorname{Out}$ and $2k+3$
bits for a length-$k$ prediction. Successful action replies have two
bits, Out has $d+3$, and prediction has

$$
k+3+\sum_{i=0}^{k}(d_i+1)
\tag{LAGP.14}
$$

bits. Each has its own End and supplied local acknowledgement.
An alpha refusal has two reply bits. Received input bits remain backed
until parsing/consumption; emitted bits remain backed through their
required output phases. Their clearing/reuse is paid.

The logical payloads of $e,c$ use $4\lceil\log_2 H\rceil$ bits in a
fixed-width binary layout, beyond the installed scalar fields,
bindings and callable source/tapes. Field framing, references and rights
are additional. At each accepted event the old $c$ pair and its two
successor coordinates are backed while the old scalar snapshot, decoded
quantity residue and scalar successors of (LAG.11) are live. All reads,
finite modular arithmetic and writes are charged. No whole-macro
update is charged in place of these real per-event commits.

The displayed $\mathsf R$ acquires one row per entry leaf, its kind bit,
actual target reference, next link and backed address; its copied
address content totals $J_{\mathsf R}$ direction bits, with list/path
framing and actual reference widths additional. Its construction stack,
row cursor, saved inner call, requested address, pending target and
unfinished tape appends coexist when their phases overlap. Consumed
rows are cleared/reused at finite cost before outer return. This is
transient old-frontier memory, not a permanent source copy or a free
selector. $\mathsf G$ pays its real left descent, depth-$d$ path backing
and current reference. Prediction pays the received finite word, its
scratch pair, prefix/output buffers and loops. Initialization pays the
full stationary traversal, stack and modulo counters.

The one joint state also retains all actual source vertices and
ancestral records, root and record references, connection latches,
arbiter, installed scalar/pair/legacy finite controls and constants,
current source/record/channel grants, work arenas, reserved unattached
objects, bit arithmetic operands, output cursors and acknowledgement
state. Reference widths are not assumed constant. Source requests
re-navigate and guard their targets; cached rows save no unperformed
driver work. No fixed physical quota, source-dependent failure reply,
free storage supplier or unit-cost global replacement is asserted.

**Theorem 13.4 (scope of the resource claims).** The event counts for
the pair targets in Theorem 9.4 are exact, but neither the pair-field
width nor these counts establish a minimum total memory, traffic, work
or material cost for the joint installation. The current Out and
prediction values are computed from an earned modular pair; they are
not fresh acquisitions through a gcd-only source observation.

Proof. Theorem 9.2 forces the successful-event multiplicities for each
specified pair target. All other listed resources have separate
operands, loops and simultaneous lifetimes; they were not minimized
by that equation. The $H^2$ arithmetic alphabet concerns only
$Q_{\rm pair}$ and omits the retained original source, tapes, references
and control. It therefore supplies no bound of that size on the full
literal service.

Definition 10.1 observes actual leaf types and links. Later local gcd
arithmetic and prediction use this acquired information. FARG133 and
AQBR10.2 instead lower-bound policies with initially no source label
and only paid complete current/terminal gcd replies, fixed action
acknowledgements and no field traversal. Their sole-observation
hypothesis fails here. Charging these stronger field operations does
not turn their observations into gcd replies or make their lower
bound applicable. No gcd-query optimum, reset access, narrower-port
acquisition or physical cost bound follows. $\square$

## 14. Supplier correspondence and the remaining recovery boundary

**Definition 14.1 (source-relative contribution and exact subtraction).**
The contribution is the actual two-coordinate LAB action/access/commit
bridge on $\mathcal D_+$, including the exact source-relative composition
reach criterion and the alpha obstruction. Its arithmetic consequence
uses an existing pair recovery theorem after that bridge is proved.
The following correspondences fix what is reused.

| Supplier | Reused mathematics and retained boundary |
| --- | --- |
| AA17–23 and AA37.1–37.2 | Birth-typed reachable terms, actual field/ref/rights installation, literal all-event tapes, complete seven-call grammar, Next and guarded count-path lifting. The new pair reach formula specializes and solves that lifting problem; the event-record theorem itself is reused. |
| This volume §§1–7, especially Definition 5.1 | Actual scalar actuators, paid traversal, full inner/public traffic and every-event scalar commit, including Next. The added pair fields and exact whole-frontier action are different from scalar quantity targets. |
| FARG2–5 and FARG130.1–130.5 | Syntax fold, literal global substitution, the matrix and unimodular quantity pair, affine-word law and full-alpha continuation quotient. Definition 9.3 supplies their actual LAB action realization; Definition 10.1 supplies earned initialization. No new arithmetic classification is claimed. |
| AQBR9–12 | Arithmetic field meanings, entry/current distinction, actual continued output/prediction and residue-transport formulas. Only their recovery/continuation conclusion is used for $Q_{\rm pair}$; their gcd-only acquisition and sharp read budget are not transferred. |
| Native Entry Reference and Graft Order §§20–23 | Actual newly acquired operand rows, entry frontier rather than newly born leaves, real bindings, old/pending operand distinctions and complete return are existing methods. Its received-body codec, encoded source, changing root-port reference, canonical event bank and row tariffs are not LAB primitives or this installation's tariff. |

In the owning formal sources,
GraftAffineClosure.step, quantity, observe, run, residue and
residueReadout and the internal castRun, wordAffine, period, classifier
and separates arguments of its result have the arithmetic meanings
used in Theorem 12.2. They neither acquire our frontier nor grant its
local edits. Its owning Blueprint Scribe fixes the same parameters and
the all-initializations scope. Here the positive-beta representatives
and actual macro legality supply the additional restriction argument.

There are opposite Boolean conventions in these suppliers.
GraftAffineClosure.run and realizationWord use false for $\mathsf R$
and true for $\mathsf G$, agreeing with Definition 10.2's word bits.
TerminalGcdAcquisitionCost.runWord uses true for $\mathsf R$ and false
for $\mathsf G$; PositiveProbeCompiler.emit/compile and
CommonDirectionScheduler.compiledReply use that latter interpreter.
Transporting a chronological Boolean list between them requires
pointwise Boolean negation, without reversal. Named words throughout
(LAGP.7)–(LAGP.10) avoid this encoding ambiguity.

PositiveProbeCompiler's private run_append, run_replacements,
quantity_graft and emit_spec already prove the positive compiler's
word/quantity correspondence. CommonDirectionScheduler's private
effective_common_direction, decode_scalars and closing_cut already
identify its requested reply tape and the entry-residue condition at
an experiment cut. Their owning Scribes expressly retain a separate
paid current gcd and closing-trajectory obligation.
TerminalGcdAcquisitionCost's scalar_word_realization, word_affine,
word_response and simulation arguments and its owning Scribe concern
sole terminal gcd acquisition from a common entry. None is a new
LAB-access or unknown-source acquisition result in this extension;
Theorem 13.4 excludes their acquisition lower bound here.

The intermediate mathematical tools are literature-attested.
Geffroy, Leroux and Sutre,
[*Occam's Razor Applied to the Petri Net Coverability Problem*,
Section 2](https://arxiv.org/html/1607.05956v1), define enabled transitions
by input-token inequalities and consumption/production. The two places
here count alpha and beta; promotion consumes alpha and produces beta,
and split consumes beta and produces beta plus alpha. This identifies
the count abstraction, while the explicit same-source spine and leaf
words in Theorem 9.2 supply its concrete LAB legality. No coverability
algorithm or relaxation is used to infer an exact endpoint.
Engelfriet, [*Tree Automata and Tree Grammars*, Definition 3.62](https://arxiv.org/html/1510.02036),
supplies the standard tree-homomorphism interpretation of replacement.
Its ability to describe substitution does not authorize local source
edits, acquired rows or live references; those are the separate bridge
of Theorem 9.4. The source-specific synthesis is repo-derived, without
a worldwide literature-priority assertion.

**Theorem 14.2 (precise remaining scope).** This construction supplies
an earned, retained, actually usable common-source pair realization
for the selected arithmetic task. It does not settle general recovery
of independently meaningful space, actual time, full boundary and
whole memory, any original fixed-model acquisition obstruction or
universal generator/resource minimality.

Proof. Theorems 9.4 and 11.2 establish the actual retained source,
lawful actions, authentic operands, complete replies, records and
return. Theorem 12.2 supplies the restricted arithmetic recovery
directions on that same source. Theorem 12.3 gives actual fibres that
lose syntax, history and original legal menus, and $\mathsf G^H$
separates actual growth chronology from identical arithmetic behavior.
Theorem 13.4 separates the strong-access acquisition from the
gcd-only interface and its cost theorem. Rights and installation data
were supplied and retained, not recovered from a residue. Busy states
still need their listed operands and pending fields. Thus unknown-source
acquisition with narrower access, whole-service recovery including
legacy selectors and literal traffic, all-phase inversion, physical
realization, actual metric/duration interpretation and whole-resource
parsimony remain separate obligations. Original fixed-$G_{\rm gc}$,
original-$Q$, parked-consumer and unchanged-initialization claims keep
their original domains. No full-programme completion follows. $\square$

[AQBR]: RECURSIVE_RELATIONAL_OBSERVATION_ARITHMETIC_ACQUISITION_RETURN.md

## 追加锚（本行以下为增补区）

## 15. Old-frontier batches without a fixed left-first schedule

**Definition 15.1 (one acquired cohort and its projected observation).**
Use the attained domain $\mathcal D_+$, actual $P/S$ guards and material
representation of Definitions 1.1 and 9.1. At an entry $u\in\mathcal D_+$,
acquire and seal the complete OLD logical frontier as in Definition 9.3:
each row has its authentic address, alpha/beta tag and actual reference.
A batch selects distinct rows of this one cohort, in any supplied order,
and calls $P_p$ on an entry-alpha row or $S_p$ on an entry-beta row.
Each old row is used at most once; new children and beta's unary marker
are ineligible. There are no intervening source edits. Consider only cuts
after complete inner return, including its tape/arithmetic maintenance,
literal reply and acknowledgement; an unfinished inner commit is excluded.
An empty prefix and a prefix leaving unused old rows are admitted.

This is the union of these legal supplied schedules, an alternative
contract to the installed left-first $\mathsf R$ (native $F$), not a new
opcode or a change to that macro. Row acquisition, supplied selection and
order, retained row/selection backing, exact counting and all original
navigation, reference comparisons, guards, records, traffic and returns
are charged. Assumption AA20.1's common root/epoch, exclusive current
rights and sufficient finite material per finite run remain premises.
No fixed finite arena is asserted for the union of all finite batches.

Write $\Lambda(t)$ for logical leaf addresses and $h$ for the literal
successful-event word of this batch prefix. Its projected observation is
$(y,k)$, where $y$ is the acquired current logical syntax and $k=|h|$ is
an exact acquired successful count, or an internal mathematical projection
when not acquired. Residues do not supply this exact count. The projection
forgets the entry list, operands, schedule and ancestral tapes; these may
still exist in the full state. The fibres below count logical descriptions,
not collisions of complete controllers or equality of physical references.

**Theorem 15.2 (complete source, support and indexed-suffix inverse).**
For $y\in\mathcal D_+$ define the following tagged candidate positions:

$$
\begin{aligned}
C_S(y)&=\{p:y_p=\langle\beta,\alpha\rangle\},\\
C_P(y)&=\{p\in\Lambda(y):y_p=\beta,\ p\text{ ends in }R\},\\
C(y)&=C_S(y)\sqcup C_P(y),\qquad M(y)=|C(y)|.
\end{aligned}
\tag{LAGB.1}
$$

The tag specifies $e_p=S_p$ or $P_p$. Positions in $C(y)$ are pairwise
prefix-incomparable. For $A\subseteq C(y)$ let $U_A(y)$ replace each
selected exact cherry by beta and each selected bare beta leaf by alpha.
These are operations on DESCRIPTIONS, not permitted reverse source edits.
Then $U_A(y)\in\mathcal D_+$, different $A$ give different entries, and
the entire projected fibre is

$$
\{(u,h):u\xrightarrow[\rm old]{h}y,\ |h|=k\}
 =\{(U_A(y),(e_{p_1},\ldots,e_{p_k})):
       A\subseteq C(y),\ |A|=k,\ (p_1,\ldots,p_k)\in\operatorname{Perm}(A)\}.
\tag{LAGB.2}
$$

Here the left side ranges over exactly Definition 15.1's batches.
It is empty for a negative/noninteger $k$ or $k>M(y)$; otherwise its
entry/support alternatives number $\binom{M(y)}k$ and its literal
chronological suffix alternatives number $\binom{M(y)}k k!$.

Let $E(t)$ be AA17.1's labelled generation-event set and
$n(t)=a(t)+2b(t)-1=|E(t)|$. For every listed alternative,

$$
E(U_A(y))=E(y)\setminus\{e_p:p\in A\},\qquad
n(U_A(y))=n(y)-k.
\tag{LAGB.3}
$$

If $A_i=\{p_1,\ldots,p_i\}$, its $i$th batch cut is
$U_{A\setminus A_i}(y)$ and event $e_{p_i}$ has full generation index
$n(y)-k+i$. This determines the batch suffix and its source cuts when
$A$ and its order are supplied, without selecting the earlier ancestral
chronology.

Proof. Distinct original leaves are prefix-incomparable. LAB9.4's actual
operand argument applies in every order: an edit at one old row changes
neither another row's subtree nor its root reference. Before a selected
row is called, its acquired tag, reference and address therefore still
agree with the current source. Its original guard succeeds; no newly
created leaf is a selected row. Completed original calls give the stated
coherent cuts under AA20.1 and LAB11.2's accepted-event invariant.

A processed beta row is consequently an exact $\langle\beta,\alpha\rangle$
cherry at $y$: neither child is an old target. A processed alpha row is
a bare beta. Its address ends in $R$, since an entry in $\mathcal D_+$
has neither a root alpha nor an $L$-ending alpha. Thus every actual
processed support is a subset of (LAGB.1). Exact cherries contain no
candidate below them: their left beta ends in $L$, and their right leaf
is alpha. Bare candidate leaves have no logical descendants. This proves
prefix-incomparability and makes all the descriptive replacements disjoint.

Conversely, reverse any chosen candidates descriptively. Reversing a
cherry inserts beta, and inserting alpha at a bare candidate is allowed
only at an $R$-ending address, so the birth-type condition is preserved.
The result remains beta-positive: its leftmost beta cannot be reversed
to alpha; a selected cherry containing it replaces it by beta. If the
root cherry is selected the result is beta, never alpha. AA17.2 therefore
makes this an attained entry in $\mathcal D_+$. Each chosen position is
now a distinct original leaf of the correct tag. The preceding actual
guard argument realizes every permutation, with endpoint exactly $y$.
At any candidate position the two choices leave different constructors
in the entry; disjointness prevents another choice from hiding that
difference. This proves both completeness and injectivity. Ordinary
subset/permutation counting gives the displayed sizes, with $0!=1$.

At a reversed promotion only $P_p$ is removed from AA17.1's event set;
at a reversed exact cherry only $S_p$ is removed. That cherry's born-beta
left child and untouched born-alpha right child have no local events.
All other events persist. These removed events are maximal, so the
remaining set is a lower causal cut. AA17.2's source correspondence gives
(LAGB.3); applying the same replacements to the unexecuted selected
positions gives every intermediate cut. Each $P/S$ adds one event,
proving the index formula. Any earlier lawful word ending at $U_A(y)$
can precede the suffix; that earlier word has not been reconstructed.
At $y=\beta$, $C(y)$ is empty: only the empty batch at beta is admitted,
not a root promotion from excluded alpha. At the root cherry,
$C(y)=\{\varepsilon:S\}$: the zero-event entry is $y$, and the sole one-event
entry is beta. Thus root cherries are included while root beta reversal
is excluded. $\square$

**Theorem 15.3 (the exact remaining original-call menu).** For a processed
support $A=A_S\sqcup A_P$ in Theorem 15.2 put

$$
\begin{aligned}
B_y(A)&=A_P\ \cup\ \bigcup_{p\in A_S}\{pL,pR\},\\
\mathcal N_y(A)&=\{P_q:q\in\Lambda(y)\setminus B_y(A),\ y_q=\alpha\}
 \ \cup\ \{S_q:q\in\Lambda(y)\setminus B_y(A),\ y_q=\beta\}.
\end{aligned}
\tag{LAGB.4}
$$

This is precisely the allowable remaining ORIGINAL-row source-call menu,
independent of the order already used. For fixed $y$ the map
$A\mapsto\mathcal N_y(A)$ is injective. Exhaustion holds exactly when
$\Lambda(y)=B_y(A)$, equivalently when
$A=C(y)$ AND $\Lambda(y)=B_y(C(y))$. In particular $k=M(y)$ alone is not
an exhaustion test.

Proof. Every untouched original row is still a current leaf with its
original tag, reference and enabled guard. A processed promotion leaves
a current beta at its old row, but that row has already been used: its
primitive $S$ guard does not grant old-cohort eligibility. A processed
split replaces its old row by two new leaves, both ineligible. These
are exactly the exclusions in $B_y(A)$; all other current leaves are
untouched original rows. Actual calls still require their authentic
operands and current authority. A saved control location may first owe
selection, list advancement, output or return rather than a source call;
$\mathcal N_y(A)$ is a source-call menu, not that protocol instruction.

For $p\in C_P(y)$, $S_p$ belongs to this menu exactly when $p\notin A$.
For $p\in C_S(y)$, both $S_{pL}$ and $P_{pR}$ belong exactly when
$p\notin A$. Their disjoint address blocks recover every membership
bit of $A$, proving injectivity. The menu is empty exactly when all
current leaves are excluded. Every unselected candidate leaves its
nonempty block in the menu, proving the equivalent exhaustion condition.

For a concrete boundary take $y=\langle\beta,\beta\rangle$. Here
$C(y)=\{R:P\}$ and $M=1$. Choosing all candidates gives entry
$\langle\beta,\alpha\rangle$ and suffix $P_R$, but leaves
$\mathcal N_y(A)=\{S_L\}$. At beta, even $k=M=0$ leaves $S_\varepsilon$.
Thus maximal candidate selection can leave an unprocessed original leaf
outside all candidate blocks. $\square$

**Proposition 15.4 (known policies and a deterministic collision).**
Suppose a known deterministic policy $\pi$ assigns to each entry $u$ a
complete permutation of its old rows; any further policy inputs are
fixed and declared. Only PREFIXES of that permutation are admitted.
In (LAGB.2) keep exactly those pairs $(A,\sigma)$ for which $\sigma$ is
the length-$k$ prefix of $\pi(U_A(y))$. This is the complete policy-filtered
fibre. On a nonempty such fibre, entry, processed support and remaining
menu are recoverable from $(y,k,\pi)$ exactly when the surviving support
set is a singleton. Determinism alone does not ensure this condition.

Proof. Filtering is precisely the added scheduling premise, so necessity
and sufficiency follow from Theorem 15.2. Its entry injectivity and
Theorem 15.3's menu injectivity identify the three recovery conditions.
More generally, for a declared family $\mathscr P_\pi(u)$ of admitted
prefixes, keep exactly those $(A,\sigma)$ with
$\sigma\in\mathscr P_\pi(U_A(y))$; the same singleton-support criterion
holds. This also allows declared stopping conditions. Each support has
at most one admitted order when the policy has no projected hidden input.
Sorting a selected subset by a comparator would give a different
contract: its sorted word need not be a prefix of the FULL old-row order.
If a deterministic controller has additional hidden acquired inputs,
use its admitted-prefix relation over those inputs instead; determinism
of the full controller cannot silently fix their projection.

For an explicit counterexample, order all old rows by increasing logical
depth and then lexicographically with $L<R$. Let

$$
y=\langle\langle\beta,\alpha\rangle,\beta\rangle,\qquad k=1.
\tag{LAGB.5}
$$

Its two candidates are $L:S$ and $R:P$. Entry
$u_1=\langle\beta,\beta\rangle$ has breadth-first first row $L$ and suffix
$S_L$; entry $u_2=\langle\langle\beta,\alpha\rangle,\alpha\rangle$
has first row $R$ and suffix $P_R$. Both give exactly (LAGB.5).
The entries are attained respectively by
$P_\varepsilon S_\varepsilon P_R$ and
$P_\varepsilon S_\varepsilon S_L$. Their remaining menus are respectively
$\{S_R\}$ and $\{S_{LL},P_{LR}\}$, so the collision affects lawful
continuation, not just a name for the past.

In contrast, [Rooted Boundary History §43, Theorem 43.2][RBHBATCH]
supplies at most one native left-first entry at each fixed admissible
$(y,k)$ on $\mathcal D_+$. That schedule premise removes the conditional
support distinction on its own domain; it neither supplies an exact
count for free nor reconstructs arbitrary earlier primitive chronology.
Its native full-prefix, Busy and acquisition conditions remain in force.
$\square$

**Proposition 15.5 (conditional labels and the four source views).**
On Definition 15.1's projected observation contract, for an admissible
$(y,k)$ a separating finite supplement needs and can attain exactly
$\binom{M(y)}k$ conditional values for entry, processed support or complete
remaining menu, and exactly $\binom{M(y)}k k!$ for the literal chronological
batch suffix. The corresponding static fixed-width content bounds are

$$
\left\lceil\log_2\binom{M(y)}k\right\rceil,
\qquad
\left\lceil\log_2\left(\binom{M(y)}k k!\right)\right\rceil.
\tag{LAGB.6}
$$

The same statements hold when $y$ is instead its acquired oriented
material source support, its terminal boundary or its labelled causal
membership order. They do not recover an arbitrary ancestral serial
history or constitute an inverse source actuator.

Proof. Theorems 15.2–15.3 give exactly the distinct task answers on this
same fibre. A supplement must distinguish them; numbering the finite
subsets, or the subsets with their permutations, attains these conditional
alphabet sizes. This is the ordinary finite-fibre separation argument
already used in AA19.2, not a new coding or online retention theorem.
A known policy or a further supplied observation $Z$ instead restricts
(LAGB.2) to its compatible pairs. The exact bounds then use the number
of surviving supports for the first task and surviving ordered suffixes
for the second; an empty fibre is an incompatible observation.

For example a complete tagged OLD frontier determines the entry by
prefix parsing, and comparison with $y$ determines which old rows were
processed. Tagged processed operands with their backed logical addresses
determine support; their chronological trace also determines suffix order.
Retained indices or request traces determine these only when their
interpretation actually identifies the completed addressed events.
If the complete AA tapes are lawfully acquired, AA19.2 recovers the whole
primitive word at $y$; its last $k$ events give the batch suffix and the
preceding source cut. Thus these stronger inputs can shrink or remove
the displayed ambiguity. No compulsory extra archive or collision of the
actual tape-retaining LAB controller follows. AA's Ready-only recall
service has not become a new external read port during an outer Busy call.

For the source views use AA17.3 literally: terminal alpha, unary beta,
binary branch. Prefix closure of the actual terminal antichain gives
material support; maximal support addresses give that antichain; arity
parses the syntax. Retain beta's unary marker, excluding auxiliary tape
edges. A bare untyped logical skeleton is insufficient for this parsing.
AA17.2 identifies the syntax with its labelled causal membership order.
Hence each of these current acquired views computes $C(y)$ and the same
inverse entries, menus and source cuts. The supplement's order coordinate
supplies the relative serial batch time; causal membership alone supplies
no such order. All acquisition, bindings, rights and finite backing remain
separate premises from the abstract inverse on acquired descriptions.

The generic configuration/enabling distinction is classical in Winskel,
[*Event Structures* (1987), §§1.1.1–1.1.3][WINBATCH]; commutation of
independent letters is the trace-monoid framework of Abbes–Mairesse,
[arXiv:1407.5879v3, §2.1][AMBATCH]. The existing
[EnabledPathSwapConnectivity.result][SWAPBATCH] and
[ConfigurationPathTransport finite histories][PATHBATCH] supply generic
extension, exchange and event-count facts, not the source-specific
candidate/menu correspondence (LAGB.1)–(LAGB.4). That correspondence is a
`repo-derived` application of AA17–19 and LAB9's actual guards, with LAB10–13's
same-run ownership and record conditions. It carries no worldwide-novelty
or fresh Lean-certification claim. Static label sizes do not minimize total
memory, online maintenance, navigation, traffic, elapsed duration or source
material, and no primitive deletion, reset or reverse permission is added.
$\square$

[RBHBATCH]: RECURSIVE_RELATIONAL_OBSERVATION_ROOTED_BOUNDARY_HISTORY_RECOVERY.md#43-native-partial-frontier-recognizability-and-complete-unfinished-history-fibres
[WINBATCH]: https://www.cl.cam.ac.uk/~gw104/Winskel1987_Chapter_EventStructures.pdf
[AMBATCH]: https://arxiv.org/abs/1407.5879v3
[SWAPBATCH]: ../../../D5/S3/ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity.lean
[PATHBATCH]: ../../../D5/S3/ConceptDynamics/Fibers/ConfigurationPathTransport.lean

## 追加锚（本行以下为增补区）

## 16. One old-row decision versus a complete native continuation

**Definition 16.1 (the conditional continuation contract).** Fix a
nonempty acquired fibre $(y,k)$ of Definition 15.1, so $y\in\mathcal D_+$
and $0\le k\le M(y)$. All cuts are after complete inner return, at the
same declared outer phase. Use Theorems 15.2–15.3 as suppliers, writing
$C=C_S(y)$, $P=C_P(y)$ and $A=C\sqcup P$, $M=|A|$, for their candidate basis;
thus this $A$ is their $C(y)$. Keep candidate types explicit as $(C,p)$
and $(P,p)$. For $J\subseteq A$, $|J|=k$, write $x_J(y)=U_J(y)$ for
Theorem 15.2's inverse entry, and put

$$
\begin{aligned}
B_{(C,p)}&=\{pL,pR\},& B_{(P,p)}&=\{p\},\\
Z_y&=\Lambda(y)\setminus\bigcup_{c\in A}B_c,&
U_y(J)&=Z_y\sqcup\bigsqcup_{c\in A\setminus J}B_c.
\end{aligned}
\tag{LAGC.1}
$$

The suppliers identify all $\binom Mk$ supports with distinct attained
entries and distinct remaining original-row menus, whose address sets
are $U_y(J)$. The nonempty blocks are disjoint. Exhaustion is exactly
$Z_y=\varnothing$ and $J=A$. Chronological order is not a target here.

Compare two tasks on this SAME fibre. Task A chooses one eligible
original call, with Stop exactly when exhausted. Task B deterministically
executes every remaining original logical leaf exactly once, excludes
newly born leaves, and then completes the outer reply, acknowledgement,
root return and cleanup. This is the arbitrary-order single-frontier
contract of §15, not the installed fixed-left $\mathsf R$ or native $F$.
The common outer binding, connections, pending protocol obligations and
all other task inputs are fixed and declared. The ordinary source-based
return tail and arithmetic/tape invariant remain those of §§10–11.

An initial supplementary label is the only input allowed to depend on
the omitted past. Subsequent source reads, guards and replies depend
only on the current logical source and the actually chosen primitive;
scratch may retain the decoder's own subsequent observations and choices.
No hidden cohort, old-list cursor, FetchGrowth/Next, tape query, allocation
ordinal, history-bearing pointer identity, refusal, capacity/timing
observation, refreshed hidden-state readout or cut-specific program is
another input. The source's genuine root/grants and authentic operand
acquisition are still required. Their paid use does not expose an erased
old-cohort flag. The initial label is a finite description with owned
backing, not an object reference or permission.

**Theorem 16.2 (exact support transport through an original call).**
Let $q\in U_y(J)$ and execute its current-tag $P_q$ or $S_q$ to full
inner return, obtaining $y'$. Set $c_q=(P,q)$ after promotion and
$c_q=(C,q)$ after split. The old candidates that disappear are exactly

$$
D_q=\bigl(\{(P,q)\}\cap A\bigr)\ \cup\
\{(C,p)\in A:q=pL\text{ or }q=pR\}.
\tag{LAGC.2}
$$

This set has at most one member, all unselected. Typed logical addresses
give the canonical inclusion $i:A\setminus D_q\hookrightarrow A(y')$,
and

$$
\begin{aligned}
A(y')&=i(A\setminus D_q)\sqcup\{c_q\},\\
J'&=i(J)\sqcup\{c_q\},& k'&=k+1,\\
x_{J'}(y')&=x_J(y),& U_{y'}(J')&=U_y(J)\setminus\{q\}.
\end{aligned}
\tag{LAGC.3}
$$

No child born in this call becomes eligible. The inclusion preserves
typed addresses, not integer positions in an enumeration of candidates.

Proof. Eligibility excludes every block of a selected candidate, so no
selected bare beta or exact cherry can be altered by this call. An alpha
at $q$ ends in $R$; promotion creates $(P,q)$ and destroys an old exact
parent cherry precisely when that alpha was its right leaf. It creates
no parent cherry. A beta split creates the exact cherry $(C,q)$; it
destroys $(P,q)$ when $q$ ends in $R$, or an exact parent cherry when
$q$ was its left beta. These two cases cannot coexist, because that
left child ends in $L$. All other candidates are disjoint and persist;
no other position can change its candidate status. This proves (LAGC.2)
and the first line of (LAGC.3), including the assertion that $D_q\cap J$
is empty. In particular an unselected bare beta can change from type P
to type C AT THE SAME ADDRESS; disappearance is not confined to parents.

The new event is at a previously unused original row. Reversing $c_q$
descriptively undoes exactly that event, and reversing the persistent
selected candidates then gives $x_J(y)$. The supplier's inverse therefore
gives $x_{J'}(y')=x_J(y)$. A promotion leaves its old leaf at $q$, now
excluded by $B_{c_q}$. A split replaces $q$ by $qL,qR$, both excluded
by $B_{c_q}$. Other selected blocks and other untouched original leaves
are unchanged. This proves the menu update and the exclusion of new
children. At the root beta, $A=J=\varnothing$, $U=\{\varepsilon\}$;
the split gives the selected root cherry and an empty menu. Thus root
splitting requires no root P candidate. At a disappearing parent cherry
the parent was unselected, while the new child-address event is selected;
the inverse and menu arguments still apply. $\square$

**Theorem 16.3 (exact conditional one-decision alphabet).** Under
Definition 16.1 the minimum number of supplementary label values for
Task A is

$$
L_A(y,k)=
\begin{cases}
1,&Z_y\ne\varnothing\text{ or }k=M,\\
k+1,&Z_y=\varnothing\text{ and }k<M.
\end{cases}
\tag{LAGC.4}
$$

Proof. Apply the existing [safe-compatible partition equivalence][SAFECONT],
`supports_deterministic_safe_policy_iff_safe_compatible_partition`, with
states the size-$k$ subsets of $A$, actions the current-tag calls together
with Stop, and legal actions the supplier's menu, or just Stop at
exhaustion. Its common-enabled-action criterion is supplied by
`deterministic_safe_policy_exists_iff`; it need not be reproved here.

If $Z_y$ is nonempty, choose its lexicographically first leaf. If $k=M$
and $Z_y$ is empty, choose Stop. These constant readouts are surjective
onto a singleton because the fibre is nonempty. In the remaining case
fix publicly $k+1$ distinct candidates $d_1,\ldots,d_{k+1}$. Label a
support by the first $i$ with $d_i\notin J$, and choose a canonical leaf
of $B_{d_i}$. This is safe. Every label is attained: the support
$\{d_1,\ldots,d_{k+1}\}\setminus\{d_i\}$ has size $k$ and its first
omitted candidate in this list is exactly $d_i$. This verifies the finite
SURJECTIVE interface rather than counting unused symbols.

Conversely suppose at most $k$ effective labels suffice in this case.
Every menu is nonempty, so no label can correctly choose Stop. Each
label's fixed safe call lies in one unique candidate block. The at most
$k$ such candidates extend to a size-$k$ support $J$. Whichever label
this $J$ receives, its prescribed call is in a selected block and is
forbidden. This contradicts the common-enabled-action criterion.
For $k=0$ a nonempty fibre still requires at least one value. Thus all
cases attain the stated minimum. This one-decision label need not have
an update that solves the next decision. $\square$

**Theorem 16.4 (exact initial alphabet for one complete continuation).**
Under the same contract, the minimum INITIAL supplementary alphabet
for Task B is

$$
L_B(y,k)=\binom{M(y)}k.
\tag{LAGC.5}
$$

Proof. Suppose distinct supports $J_1,J_2$ receive the same label under
one proposed complete policy. The acquired source, exact count, declared
outer phase and every other decoder input agree. Determinism and the
source-only observation contract imply identical future choices and
observations as long as both executions remain legal. A call forbidden
in either execution is already failure; probing it for a refusal is not
an admissible way to learn. Stop while either menu is nonempty is also
failure. If both runs succeed finitely, their common word must enumerate
both $U_y(J_1)$ and $U_y(J_2)$ exactly once and then Stop. Those sets are
unequal by Theorem 15.3, so this is impossible. Hence initial labels must
separate all $\binom Mk$ supports. This argument concerns ONE chosen
successful policy, without assuming preservation of every possible action.

For the upper bound, enumerate the typed candidates from the acquired
source and encode the actual size-$k$ subset by its finite-subset rank.
Ranking/unranking is the mature constant-weight enumeration of Cover,
[*Enumerative Source Encoding*, IEEE TIT 19(1), 73–77, §I Propositions
1–2 and inverse, §II Example 2][COVERCONT]. All $\binom Mk$ ranks occur
by Theorem 15.2. Decode $J$, derive $U_y(J)$, and choose its first leaf
when nonempty. Acquire the REAL current operand by paid traversal from
the bound root, parsing terminal alpha, unary beta and binary branch;
construct the actual addressed frame and execute the original guarded
call, all tape/arithmetic maintenance, literal reply, acknowledgement
and inner return. Theorem 16.2 supplies $J'$ from this known call and
the current source. Re-enumerate $A(y')$ and re-rank $J'$ against that
basis before repeating. The natural number $|U|$ decreases by one at
each iteration. At zero, take the declared finite outer return tail,
including its full reply, supplied acknowledgement, root return and
clearing of owned transient backing as in Theorem 11.2. The existing
guard, synchronization and completion suppliers apply to every chosen
original row; no source edit or reverse actuator has been added.

This is one finite procedure with backed loops and the sufficient finite
resources of AA20.1, not a program chosen separately for each hidden
entry. At actual batch entry $J=\varnothing$; each really completed call
earns the update. At an arbitrary later cut, $y,k$ alone do not recreate
a forgotten non-singleton support. An old rank or positional mask is
not invariant under (LAGC.3): candidates can disappear or change type,
and enumeration positions can shift. Later conditional radices
$\binom{M(y')}{k+1}$ and working alphabets may grow. The upper bound
claims an initial label size, not constant-width working space. In
particular the refreshed $r(\mathrm{successor})$ in
[FiniteConfigurationAcquisition][REFRESHCONT] is a different input
contract; that oracle is not used here. $\square$

**Proposition 16.5 (a strict native separation).** At

$$
y=\langle\langle\beta,\beta\rangle,\beta\rangle,\qquad k=1,
\tag{LAGC.6}
$$

$C=\varnothing$, $P=\{LR,R\}$ and $Z_y=\{LL\}$, so $L_A=1$ while
$L_B=2$. More generally the left comb of $m+1$ beta leaves has
$L_A=1$ and $L_B=\binom mk$ for $0\le k\le m$.

Proof. Entry $x_1=\langle\langle\beta,\alpha\rangle,\beta\rangle$
followed by $P_{LR}$ gives (LAGC.6) with $U_1=\{LL,R\}$; entry
$x_2=\langle\langle\beta,\beta\rangle,\alpha\rangle$ followed by
$P_R$ gives the same source and count with $U_2=\{LL,LR\}$. Both entries
are in $\mathcal D_+$ by AA17.2. One label can choose the common call
$S_{LL}$. After its full inner return, both current syntaxes are
$\langle\langle\langle\beta,\alpha\rangle,\beta\rangle,\beta\rangle$,
but the residual sets are respectively $\{R\}$ and $\{LR\}$. Neither a
common next call nor a common correct Stop exists. For the comb, write
$t_0=\beta$, $t_{m+1}=\langle t_m,\beta\rangle$. Its $m$ candidates
are exactly its $R$-ending bare beta leaves, and its only uncovered leaf
is $L^m$; apply (LAGC.4)–(LAGC.5). $\square$

**Proposition 16.6 (source-view transport and conditional price).**
Theorems 16.2–16.4 hold with the public $y$ replaced by its acquired
oriented material source support, terminal boundary, or labelled causal
membership order on that SAME root/source. Their initial fixed-width
supplementary content prices are $\lceil\log_2 L_A\rceil$ and
$\lceil\log_2 L_B\rceil$ bits, conditional on the fixed exact $y,k$
and Definition 16.1's reduced input contract. They are not total-memory,
acquisition, navigation, traffic, duration or source-material optima.

Proof. AA17.3 gives prefix closure from terminal boundary to material
support, maximal addresses in the reverse direction, and arity parsing
to syntax; the unary beta marker is retained and auxiliary tape edges
are excluded. AA17.2 gives the corresponding labelled causal membership
order. These inverses recover precisely the same $y$, hence the same
typed candidates, blocks, supports and updates. With $J$ they recover
the entry and its residual old cohort, without selecting an ancestral
serial order. Mere descriptions, parsing and mathematical recovery do
not grant a root binding, operand reference, current authority or an
execution right. A split may reuse an old material unary marker as its
new left logical child: material pointer age is not old logical-cohort
membership. No numeral-to-capability cast follows from any label.

The bit prices are the ordinary fixed-width encoding of the attained
label alphabets. They exclude the public source and count, genuine
references/grants, source tapes, scratch, finite program, full traffic,
acquisition and all operations/backing; these remain owned and paid
under §§9–15 and AA20.1. A retained complete OLD list or lawfully acquired
full AA event tapes can already determine $J$, as Proposition 15.5
explains. Condition on those inputs and their actual compatible fibre
instead of duplicating an archive or claiming additional-memory lower
bounds for the installed tape-retaining apparatus. No Ready-only tape
service is thereby exposed during Busy. The new source-specific content
is (LAGC.2)–(LAGC.5)'s transport and chosen-task distinction, a
`repo-derived` consequence of the stated suppliers. The generic safe
partition and finite enumeration results do not themselves compute
these native counts. No fresh Lean certification or worldwide novelty
is asserted. $\square$

[SAFECONT]: ../../../D5/S3/ConceptDynamics/Agency/MinimumSafeObservationAlphabet.lean
[COVERCONT]: https://isl.stanford.edu/~cover/papers/transIT/0073cove.pdf
[REFRESHCONT]: ../../../D5/S3/ConceptDynamics/Agency/FiniteConfigurationAcquisition.lean

## 追加锚（本行以下为增补区）

## 17. A prescribed old-row horizon and its covering alphabet

**Definition 17.1 (one earned label for a bounded original-row prefix).**
Retain [§15's native inverse and menu](#15-old-frontier-batches-without-a-fixed-left-first-schedule)
and [§16's source-only continuation contract](#16-one-old-row-decision-versus-a-complete-native-continuation).
Fix the same nonempty acquired fibre $(y,k)$, with $y\in\mathcal D_+$
and $0\le k\le M$. Use Definition 16.1's typed candidates
$A=C\sqcup P$, $M=|A|$, disjoint leaf blocks $B_p$ and free leaves $Z_y$.
Write

$$
\begin{aligned}
w_p&=|B_p|=\begin{cases}2,&p\in C,\\1,&p\in P,\end{cases}
& w(T)&=\sum_{p\in T}w_p,\\
W&=w(A),&c&=|C|,&z&=|Z_y|,\\
U_y(J)&=Z_y\sqcup\bigsqcup_{p\in A\setminus J}B_p,
& J&\in\binom Ak.
\end{aligned}
\tag{LAGH.1}
$$

The task is to execute exactly $h$ DISTINCT eligible ORIGINAL-row calls,
each through complete inner return, and then give the declared finite
bounded-prefix report and return. This report asserts completion of those
$h$ calls; it makes no exhaustion claim. Any report, acknowledgement,
root return and clearing obligations of this prefix interface are fixed
and source-based. In particular this task neither adopts Task A's
Stop-if-and-only-if-exhausted rule nor completes Task B or the installed
full old macro. New children remain ineligible. The admissible horizons are

$$
h\in\mathbb N,\qquad
0\le h\le z+W-k-\min(k,c).
\tag{LAGH.2}
$$

One actual earned INITIAL supplementary label is the only decoder input
allowed to depend on the omitted past. A single deterministic decoder may
use the acquired current source, the fixed declared inputs $k,h$ and
outer phase, this label, and its own subsequent permitted traffic and
computation. Reads, guards and replies obey Definition 16.1's source-only
congruence. No old frontier list or cursor, cohort-refusal test, ancestral
tape or FetchGrowth/Next query, hidden program, refreshed hidden-state
readout, pointer age, permission, capacity or timing channel supplies
another distinction. Unsafe old-row probing is failure, even when its
primitive source guard would succeed.

The label is a backed finite description earned from the actual batch;
it grants no reference or authority. Authentic acquired current-root
access, current source rights and sufficient finite resources remain
AA20.1's premises. All original navigation, operand acquisition and
comparison, guards, label and work backing, record/arithmetic maintenance,
inner replies, acknowledgements and returns are paid. The richer retained
OLD-list or tape observations of Proposition 15.5 give a different
conditioned fibre. The minimum below counts effective initial label values
on this one fibre, including all its admitted earlier orders.

**Theorem 17.2 (exact native finite-horizon alphabet).** In Definition
17.1, put $r=\max(0,h-z)$. The exact minimum effective initial alphabet is

$$
\tau_h(y,k)=\min\left\{|\mathcal F|:
\begin{array}{l}
\mathcal F\subseteq\mathcal P(A),\quad w(T)\ge r\quad(T\in\mathcal F),\\
\forall J\in\binom Ak\ \exists T\in\mathcal F:\ T\cap J=\varnothing
\end{array}\right\}.
\tag{LAGH.3}
$$

Permitted source-only adaptivity has the same optimum as one fixed ordered
$h$-list of current-$y$ leaf addresses per label. Equivalently, (LAGH.3)
is the ordinary INTEGRAL UNIT-COST SET COVER of universe $\binom Ak$ by

$$
\left\{\binom Qk:Q\subseteq A,\ w(Q)\le W-r\right\}.
\tag{LAGH.4}
$$

Here the point weights restrict allowed covering sets; every selected set
has cost one. At $h=0$, or whenever $\binom Mk=1$, the answer is one for
every admissible horizon. A horizon exceeding (LAGH.2) is infeasible
regardless of the number of labels.

Proof. By Theorems 15.2–15.3 every size-$k$ support is attained, and its
initial remaining menu has size $z+W-w(J)$. Since $w(J)=k+|J\cap C|$,
its maximum removed weight is $k+\min(k,c)$: choose as many of the $c$
cherries as possible and fill the other places with promotions. Thus
(LAGH.2) is exactly the least remaining-menu size. Above it one attained
history has fewer than $h$ original rows. Within it, taking $T=A\setminus J$
for every support supplies a feasible finite family in (LAGH.3), so its
minimum exists.

For the new interface bridge, fix any successful proposed decoder and
one of its effective INITIAL labels $\ell$. Apply Theorem 16.4's
source-response/common-run argument up to the $h$th completed call,
without its final exhaustion test. All histories receiving $\ell$ begin
with the same allowed source inputs; that result forces the same permitted
traffic and choices while the executions remain legal. A forbidden call
cannot be used to distinguish them. Success on the whole label fibre
therefore yields one common ordered trace
$(q_1,\ldots,q_h)$ of distinct original rows. Theorem 16.2's exact menu
transport identifies them with distinct members of the INITIAL $U_y(J)$
for every history in this label fibre. Complete inner returns introduce
no extra decoder observation beyond the stipulated source-only interface.
This is a common successful $h$-trace, without recovery of the remaining
menu or of an earlier chronological suffix.

Let $T_\ell$ be the candidates whose blocks this common trace touches.
At most $z$ entries lie in $Z_y$, so $w(T_\ell)\ge h-z$ and hence
$w(T_\ell)\ge r$. Legality gives $T_\ell\cap J=\varnothing$ for every
support in that label fibre. For each size-$k$ $J$, choose an attained
history supplied by Theorem 15.2 and its actual label. Consequently the
family of distinct $T_\ell$ covers all supports in (LAGH.3); its size is
at most the number of effective labels. This proves the lower bound even
if a label encoder also depends on the omitted chronological order.

Conversely use one fixed finite enumeration procedure on public $y,k,h$
to choose a canonical minimum family $\mathcal F$ in (LAGH.3) and its order;
all this computation and backing is charged. Label an actual support $J$
by its first disjoint $T$.
The encoder uses the actual support, earned from the batch's real addressed
successful calls while that information is lawfully available. This is
not a recovery of $J$ from the projected $y,k$ alone. No additional old
list or cursor is passed to the decoder. Every label is effective: in a
minimum family each $T$ has some support $J_T$ disjoint from it and from
no other member, since otherwise $T$ could be deleted. That attained
support necessarily receives $T$'s label.

For each label $T$, form from public $y$ and $T$ the leaf set
$V_T=Z_y\sqcup\bigsqcup_{p\in T}B_p$. It has at least $h$ members.
Take its first $h$ addresses in a fixed public order. For every support
assigned this label the entire list lies in $U_y(J)$. Theorems 15.3 and
16.2 supply precisely these original rows and their successive removal.
Acquire each REAL operand through paid traversal from the bound current
root, check its authentic guard, and complete its original call with all
maintenance, reply, acknowledgement and inner return before advancing.
Edits at the other distinct original leaves preserve the next target's
current tag and reference, as in §15. The decoder executes exactly $h$
calls and then the stipulated bounded-prefix report/return. It need not
execute whole blocks: the first $h$ leaves may include just one child
of a cherry, even though $w_p=2$. At $h=0$ the list is empty.

This attains the lower bound with a fixed ordered $h$-list per label.
It is a conditional initial-label construction, with earned provenance
and finite backing required; it does not assert that optimal labels for
different horizons have nested fibres or dynamically maintainable updates.
The upper uses no $r(\mathrm{successor})$ readout from
[FiniteConfigurationAcquisition.Run.step][REFRESHCONT]. Post-label state
is computed only from the label, source and the decoder's own traffic.

Finally set $Q=A\setminus T$. Then $T\cap J=\varnothing$ means $J\subseteq Q$,
and $w(T)\ge r$ means $w(Q)\le W-r$, proving (LAGH.4) with the same
number of selected sets. No fractional equality or general closed
numerical formula is implied. For $h=0$, $\mathcal F=\{\varnothing\}$
works. On a singleton-support domain choose that support's complement;
nonemptiness requires at least one effective value in both cases.

For the compact classical specialization take §16.5's all-beta left comb
$t_0=\beta$, $t_{m+1}=\langle t_m,\beta\rangle$. Here $M=m$, $z=1$
and every weight is one. For admissible $h\ge1$ put $b=m-h+1$, so
$k\le b\le m$. Every allowed $Q$ has size at most $b$ and can be enlarged
to a $b$-subset without losing coverage. Thus the native formula is

$$
\tau_h(t_m,k)=C(m,m-h+1,k),\qquad 1\le h\le m-k+1,
\tag{LAGH.5}
$$

where $C(v,b,t)$ is the classical minimum number of $b$-subsets covering
all $t$-subsets, not a binomial coefficient. This is the covering-number
definition of Gordon–Kuperberg–Patashnik–Spencer,
[*Asymptotically optimal covering designs*, arXiv:math/9511224v1,
abstract and §1][DESIGNHORIZON]; the zero-target case is interpreted
directly by its single empty target. Hence $h=1$ gives one, $h=2$ when
feasible gives $k+1$, and $h=m-k+1$ gives $\binom mk$. For $h=2$ the
$b=m-1$ blocks omit individual points: their omitted points must escape
every $k$-set, requiring and attained by $k+1$ distinct points. At the
last horizon $b=k$, each block covers only itself. For $k=0$, including
$m=0$, one label directly supplies every feasible list; $h=0$ was already
settled. These are classical combinatorial values used inside the native
application, not additional design results.

The abstract supplier [MinimumSafeObservationAlphabet][SAFECONT] has
states $X=\binom Ak$, actions ordered $h$-tuples of distinct current-$y$
leaves, and legality precisely tuple membership in $U_y(J)$.
`deterministic_safe_policy_exists_iff` supplies its common-safe-fibre
interface; `minimum_safe_observation_alphabet` supplies its `IsLeast`
interface. The effective-value argument above checks the required
surjectivity. Neither supplier proves the native common-$h$-trace bridge
or computes the covering number. For mixed weights the allowed $Q$ may
have different profiles $(|Q\cap C|,|Q\cap P|)$; this is not directly the
fixed block-size-vector family of Bailey–Burgess–Cavers–Meagher,
[*Generalized covering designs and clique coverings*, arXiv:1011.3804v2,
Definitions 1.1 and 2.1][PROFILEHORIZON]. The mature owner is finite set
cover, with (LAGH.5) its classical fixed-size specialization. The repository
already applies $C(m,3,2)$ in [KBonacci continuation X, Theorem 211.10][KBCHORIZON].
The `repo-derived` increment here is only the native finite-horizon bridge
and its exact allowed-cover family, using [AA §§17, 20–21][AA] and
LAB9/15/16.
The supplied source-view inverses of Proposition 16.6 transport the same
calculation to acquired oriented support, terminal boundary and labelled
causal membership on the same source. They supply no actual root access,
operand, grant or ancestral serial order. The result is an initial
conditional alphabet optimum, without a fresh Lean-certification or
worldwide-novelty claim, and without optimizing total storage, navigation,
traffic, duration, decoder computation or installation. $\square$

**Proposition 17.3 (two successful calls need not complete the cohort).**
Let $\chi=\langle\beta,\alpha\rangle$ and

$$
y=\langle\langle\chi,\beta\rangle,\beta\rangle,\qquad k=1.
\tag{LAGH.6}
$$

Here $C=\{LL\}$, $P=\{LR,R\}$, weights are $(2,1,1)$ and $Z_y$ is empty.
The three attained remaining menus, written as leaf addresses, are

$$
\begin{aligned}
U_y(\{LL\})&=\{LR,R\},\\
U_y(\{LR\})&=\{LLL,LLR,R\},\\
U_y(\{R\})&=\{LLL,LLR,LR\}.
\end{aligned}
\tag{LAGH.7}
$$

The largest uniformly feasible horizon is $h=2$, and $\tau_2(y,1)=2$,
whereas complete continuation under the SAME input conditioning needs
three initial values. Two successful calls do not uniformly certify
exhaustion.

Proof. The inverse entries are respectively
$\langle\langle\beta,\beta\rangle,\beta\rangle$,
$\langle\langle\chi,\alpha\rangle,\beta\rangle$ and
$\langle\langle\chi,\beta\rangle,\alpha\rangle$.
They belong to AA17.2's attained domain; their respective original-row
suffixes $S_{LL}$, $P_{LR}$ and $P_R$ give exactly $y,k$.
Theorem 15.3 gives (LAGH.7). Its least menu size is two, also
$z+W-k-\min(k,c)=0+4-1-1$.

One label cannot supply a common first row: the intersection of all
three menus is empty. Two labels suffice. For $J=\{LR\}$ or $\{R\}$,
choose the ordered calls $(S_{LLL},P_{LLR})$, the two leaves of block $LL$.
For $J=\{LL\}$ choose $(S_{LR},S_R)$. Both labels are attained, and
Theorems 15.3 and 16.2 make every call legal through full inner return.
Equivalently the two sets $T=\{LL\}$ and $T=\{LR,R\}$ have weight two
and cover all supports in (LAGH.3).

After these two calls the first of the three menus has been exhausted,
but the other two each have one original row left. The successful
bounded-prefix report consequently carries no assertion of universal
exhaustion. Full continuation needs $\binom31=3$ initial values by
Theorem 16.4, with exactly the same acquired $y,k$, source-only reads,
root rights and paid inner-call obligations. A larger initial alphabet
cannot make $h=3$ feasible on this whole fibre. $\square$

[DESIGNHORIZON]: https://arxiv.org/pdf/math/9511224v1
[PROFILEHORIZON]: https://arxiv.org/pdf/1011.3804v2
[KBCHORIZON]: KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_X.md#2113-a-fixed-menu-of-actual-joint-measures

## 追加锚（本行以下为增补区）

## 18. Writing an old-cohort distinction into the source before a logical reset

**Definition 18.1 (one source, one reset and two continuation contracts).**
Fix the acquired $y\in\mathcal D_+$ and exact $k$ of Definition 16.1,
with $0\le k\le M$. Retain its typed basis $A=C\sqcup P$, disjoint
nonempty original-leaf blocks $B_p$, and uncovered leaves $Z=Z_y$.
Write $L=\Lambda(y)$ and

$$
\mathcal J=\{J\subseteq A:|J|=k\},\qquad
U_J=Z\sqcup\bigsqcup_{p\in A\setminus J}B_p.
\tag{LAGR.1}
$$

The hidden alternative is the actually acquired support $J$, with
attained original entry $x_J(y)$ and remaining original-row menu $U_J$
from Theorems 15.2–15.3. Thus ORIGINAL below refers to that entry's
cohort, not every current logical leaf of $y$. Chronology before $y$
is not a target. Choose an integer $r\ge0$. Before a declared reset,
the selector may use its acquired $J$ to execute exactly $r$ distinct
rows of $U_J$, each by its current-tag original $P/S$ call through full
inner return. These calls write a set $Q\subseteq U_J$, $|Q|=r$.
There are no other source edits.

The reset removes ALL supplementary pre-reset private control and ordered
transcripts, including the acquired $J$, old cohort/list/cursor, prefix
order, labels, saved selections, and their readable scratch or archives.
It preserves the current source, fixed public $y,k,r$, one finite
$J$-independent program/codebook, and the declared authentic fixed root
binding, grants and common protocol obligations. A prefix-dependent saved
continuation is not one of these fixed inputs. This is a LOGICAL input
restriction. It neither deletes the physical ancestral tapes nor supplies
a native reverse edit, thermodynamic erasure, or a reset opcode.

After reset both selectors must exhaust exactly every row of
$U_J\setminus Q$ once and then choose Stop, with the declared full outer
reply, acknowledgement, root return and cleanup. Newly born children
remain ineligible. Stop is correct exactly at original-cohort exhaustion;
$r$ calls or native-guard exhaustion is not this condition. A geometry
selector $G$ chooses each next original-row call or Stop solely from the
CURRENT source geometry and the fixed inputs. Its decision scratch must
be derived from that current source and fixed inputs; it cannot preserve
an earlier decision's supplementary state. A transcript selector $T$
starts with the same reset private state, but may retain all observations
and traffic it actually acquires AFTER reset, including its newly read
initial $Q$. It cannot retain the erased prefix order. Selectors here
are deterministic and must succeed for every $J\in\mathcal J$.

The observation/call premise is explicit. At each complete-inner-return
cut, the task admits owned traversal of the stationary current source,
authenticated internal dispatch on that same bound root, and the full
original primitive guard, reservation, edit, tape/arithmetic maintenance,
literal reply, End, acknowledgement and inner return. All backing and
traffic are paid. AA17.3 supplies the material arity parser; AA20.1 supplies
actual references, current rights, finite material and field operations.
LAB9.3–9.4 supply frontier acquisition and the authentic addressed-operand
argument; LAB10.2–10.3 supply the serialized INTERNAL connection and its
complete receiver; LAB11.1–11.2 supply the accepted-event commit and finite
return obligations. Their installed macros retain their own old lists;
these suppliers do not install a resettable arbitrary selector.

In particular AA21.1–21.2 factor the $Q_c$ replies and settled SOURCE
successor through current syntax only on their stated READY domain,
with fixed rights and raw fresh names disregarded. LAB15's cuts follow
a full INNER return; LAB10.2 and LAB11.1 still allow the outer supervisor
to be BUSY with external ingress locked. No external Ready-only Tag or
recall service is admitted at an arbitrary Busy cut. The present task
requires its own lawful owned source traversal and internal-call access
at these selection cuts, with a common reset/resumption state and a lawful
finite return tail. For the installed outer supervisor, the phase-correct
reset/reacquisition/selection continuation bridge remains unverified.
The statements below are conditional on these admitted accesses and reset
contract; mathematical source views alone do not supply that installation.

All selector-visible source observations and successful-call replies at
these cuts must depend only on current syntax, fixed rights and the chosen
call, as the scoped AA21 $Q_c$ semantics does at Ready. Original-row
eligibility is a TASK constraint, not a hidden-membership or refusal oracle.
Exclude tape reads, FetchGrowth/Next, old lists/cursors, pointer age/name,
authority/timing/capacity channels, and refreshed hidden-state readouts.
Tapes and other physical records may remain attached but are not selector
inputs. Reference acquisition and equality used to authenticate a currently
traversed operand do not expose a history-bearing identity. Finite codebook
storage, its construction/search, public-data backing, traversal scratch,
operand acquisition, every source call and every protocol operation are
separate charges. A codebook contains descriptions, never a free
address-to-reference or description-to-authority cast.

**Theorem 18.2 (the observable source image of a legal prefix).**
The menus $(U_J)_{J\in\mathcal J}$ are distinct and form an antichain
under inclusion, even when their cardinalities differ. For $Q\subseteq L$
let $E_y(Q)$ replace each ORIGINAL $y$-alpha at an address in $Q$ by beta,
and each ORIGINAL $y$-beta there by $\langle\beta,\alpha\rangle$, leaving
all other original leaves and branches unchanged. On Definition 18.1's
legal image, $Q\subseteq U_J$, and $E_y(Q)$ is exactly the current source
after those additional calls. The map $Q\mapsto E_y(Q)$ is injective,
its inverse is obtainable by the admitted actual source traversal relative
to fixed $y$, and no order of these disjoint edits is encoded by this
source observation. Every intermediate subset of $U_J$ is attainable by
legal original-row calls on the same source, through complete inner returns.

Proof. If $J_1\ne J_2$, their equal cardinalities give both
$p\in J_1\setminus J_2$ and $q\in J_2\setminus J_1$. The nonempty block
$B_p$ lies in $U_{J_2}\setminus U_{J_1}$ and $B_q$ in the reverse
difference. Disjointness of all blocks and $Z$ prevents cancellation.
This proves the asserted injective antichain; when $\mathcal J$ is a
singleton the assertion includes an empty terminal menu.

The original $y$-leaf addresses are prefix-incomparable. At an untouched
one its original constructor, reference and enabled primitive guard
persist; an edit elsewhere does not change them. LAB9.4 and LAB15.2's
same-row argument therefore applies to every ordering of any
$Q\subseteq U_J$. A selected alpha is promoted once; a selected beta
is split once, with neither new child becoming a scheduled target.
Consequently the endpoint is precisely $E_y(Q)\in\mathcal D_+$,
independent of that order. The source at a prefix $R$ is $E_y(R)$ and
the remaining original rows are $U_J\setminus R$. This is also the
fixed-$y$ description of LAB16.2's typed candidate transport; it does not
keep a stale index into the changing candidate basis of the successor.

To recover $Q$, traverse the actual source from the surviving genuine
root, using AA17.3's terminal/unary/binary parser and excluding tape
edges and beta's marker from the logical frontier. Relative to each
leaf position $a$ in fixed $y$, an original alpha is either still alpha
or now beta; an original beta is either still beta or now the exact
cherry $\langle\beta,\alpha\rangle$. The second case in each pair marks
$a\in Q$. These distinguishable local constructors recover every bit
of $Q$, proving injectivity and giving a finite traversal algorithm.
The root and original branch skeleton persist. This algorithm acquires
actual target references when needed; the mathematical list of addresses
does not create them. Different edit orders can leave different tapes,
but tapes are excluded and the current source is identical. $\square$

**Theorem 18.3 (reset geometry, complete continuation and reassigned
saturated paths).** Under Definition 18.1, set

$$
F_J=\{Q\subseteq U_J:|Q|=r\}.
\tag{LAGR.2}
$$

There is a successful prefix encoder and transcript selector $T$ if and
only if $(F_J)_{J\in\mathcal J}$ has a system of distinct representatives,
equivalently

$$
\left|\bigcup_{J\in H}F_J\right|\ge |H|
\quad\text{for every }H\subseteq\mathcal J.
\tag{LAGR.3}
$$

There is a successful prefix encoder and geometry selector $G$ if and
only if the distinct terminal menus $U_J$ admit mutually vertex-disjoint
saturated increasing paths in $2^L$, one from a rank-$r$ start to each
terminal. A saturated step adds exactly one address; a singleton
start-equals-terminal path is allowed. With the encoder FREELY CHOSEN
or reassigned, these two existential feasibility conditions coincide.
This does not promise preservation of a specified encoder/pairing or of
an individual $T$ policy.

Proof. A prefix encoder selects some $Q_J\in F_J$; every such choice
is realizable by Theorem 18.2. Suppose $Q_{J_1}=Q_{J_2}=Q$ for distinct
supports. Immediately after reset the source is the same $E_y(Q)$ and
all other permitted INITIAL state and inputs are the same. By the declared
observation/call factorization, determinism gives the same future choices,
replies and source successors as long as both runs remain legal. An
ineligible call already violates the task; it cannot be used as a probe.
A common finite successful suffix would enumerate both
$U_{J_1}\setminus Q$ and $U_{J_2}\setminus Q$ and then Stop. Those sets
differ by Theorem 18.2, so this is impossible. Thus the initial $Q_J$
must be distinct. This argument uses the SAME INITIAL reset geometry
and state, not equality of two later $T$ geometries with different new
transcripts.

Conversely an SDR gives one fixed finite table $Q_J\mapsto J$, shared
by all alternatives. After reset $T$ actually reads $Q_J$ from the current
source, decodes $J$ using that backed table, and retains this NEWLY acquired
information. It can then enumerate $U_J\setminus Q_J$, acquire each
real operand by traversal and execute its original full call once, before
the finite return tail. This terminates because the residual set loses
one row each time. The equivalence of the SDR with (LAGR.3) is the
existing finite Hall theorem, in the form
`Finset.all_card_le_biUnion_card_iff_existsInjective'` in the pinned
mathlib `Mathlib/Combinatorics/Hall/Finite.lean`, with index type
$\mathcal J$, representative type $2^L$, and family $J\mapsto F_J$.
The generic Hall result is reused, not re-proved here.

For $G$, the successful run from $Q_J$ successively adds one address
of $U_J$ until its terminal $U_J$, so it is a saturated increasing path.
If runs for different terminal menus share a vertex $R$, Theorem 18.2
identifies their current source as $E_y(R)$. A geometry selector has the
same next decision there and at each subsequent common vertex. Its two
successful tails must therefore have the same terminal; an earlier Stop
cannot be correct for a different nonempty residual set. The menus are
distinct, so paths for different $J$ are vertex-disjoint. In the reverse
direction, store the disjoint paths as a single fixed finite codebook.
From the currently traversed $R$, $G$ finds its unique path vertex,
chooses the next added address, or Stop at its endpoint. Scratch for
this lookup is current-source-derived. Every vertex on the path to $U_J$
is a subset of $U_J$; hence every added row is still an eligible original
row by Theorem 18.2. Reacquire its actual reference and use the admitted
complete call and return obligations. This proves the $G$ equivalence.

It remains to connect Hall to these paths, rather than infer paths from
total rank capacity. Start with any SDR $(Q_J)$. The rank-$r$ starts
are an antichain; Theorem 18.2 gives the terminal antichain, with all
$|U_J|\ge r$. The endpoint family

$$
\mathcal E=\{Q_J:J\in\mathcal J\}\cup\{U_J:J\in\mathcal J\}
\tag{LAGR.4}
$$

has a decomposition into $N=|\mathcal J|$ disjoint chains
$\{Q_J,U_J\}$, using a singleton if they are equal. Indeed equality
$Q_i=U_j$ implies $U_j\subseteq U_i$, so terminal antichainness forces
$i=j$; SDR injectivity excludes every other overlap.
Apply Bastide–Groenland–Jacob–Johnston,
[*Exact antichain saturation numbers via a generalisation of a result of
Lehman-Ron*, arXiv:2207.07391v2, Theorem 2][SATRESET]. Its ground-set
parameter is $n=|L|$ after an arbitrary fixed bijection $L\simeq[n]$,
its number of chains is $m=N$, and its family $\mathcal F$ is exactly
$\mathcal E$. The hypothesis is the just constructed chain decomposition;
its conclusion is $N$ pairwise disjoint skipless chains COVERING
$\mathcal E$, not paths preserving the input pairs.

Each output chain contains at most one rank-$r$ start and at most one
terminal, by the two antichains. There are $N$ of each and exactly $N$
chains, so each chain contains one of each. The terminal has rank at
least $r$, hence is above its chain's start. Trim the chain to that closed
interval. The resulting paths remain saturated and disjoint, including
singletons when ranks coincide. Their start-to-terminal pairing may differ
from the SDR pairing. Assign to the history $J$ the start of the path
whose terminal is $U_J$ and rewrite the prefix using that start. This is
a permitted RE-ENCODING: the new start has rank $r$ and is contained in
$U_J$, and all its subsequent intermediate subsets are likewise native
legal. The disjoint-path selector above now supplies $G$. Conversely
$G$ is a particular $T$, or its disjoint starts themselves form an SDR.
This proves existential coincidence without a prescribed-pairs claim.
For $r=0$, Hall forces $N=1$; for an empty menu the sole feasible start
is the singleton path at $\varnothing$. Thus these cases require no
strict-rank version of the published theorem. $\square$

**Corollary 18.4 (sharp beta-comb threshold, including the uncovered row).**
Let $y_0=\beta$ and $y_{m+1}=\langle y_m,\beta\rangle$, $m\ge0$.
Label its $m$ right-ending candidate leaves by $[m]$ and its uncovered
leftmost leaf $z=L^m$. For $0\le k\le m$ put

$$
N=\binom mk,\qquad t=m-k,\qquad
U_J=([m]\setminus J)\cup\{z\}.
\tag{LAGR.5}
$$

For each integer $0\le r\le t+1$, both reset contracts are feasible
exactly when

$$
\binom{m+1}{r}\ge N.
\tag{LAGR.6}
$$

Outside this range exactly $r$ distinct original-row calls are impossible.
The minimum feasible prefix length is

$$
r_*(m,k)=\min\{r\in\{0,\ldots,t+1\}:\binom{m+1}{r}\ge\binom mk\}.
\tag{LAGR.7}
$$

In particular $r_*(6,3)=2$: there are $20$ supports, while ranks one
and two on the SEVEN addresses, including $z$, have sizes $7$ and $21$.

Proof. LAB16.5 supplies precisely these candidates and the uncovered
row on this attained LAB source. Theorem 18.2 realizes their prefixes
as actual once-only splits at the corresponding beta leaves. Necessity
of (LAGR.6) follows from the SDR in Theorem 18.3, since its starts are
distinct rank-$r$ subsets of $[m]\cup\{z\}$. Sufficiency needs every
Hall subfamily, not just this total capacity.

Identify a support with $W=[m]\setminus J$, a $t$-subset of $[m]$.
First take $1\le r\le t$. Allowed starts have two disjoint types:
$r$-subsets of $W$ without $z$, and $\{z\}\cup R$ with
$R\subseteq W$, $|R|=r-1$. The numbers of starts of these types in the
whole ground set, their degrees from any fixed $W$, and the numbers
of $t$-sets containing any fixed start are respectively

$$
\begin{aligned}
v_0&=\binom mr,& d_0&=\binom tr,&
e_0&=\binom{m-r}{t-r},\\
v_1&=\binom m{r-1},& d_1&=\binom t{r-1},&
e_1&=\binom{m-r+1}{t-r+1}.
\end{aligned}
\tag{LAGR.8}
$$

Both types are nonempty in this interior range, and $e_0,e_1>0$.
Counting their incidences gives $Nd_i=v_ie_i$. For ANY family $H$
of $t$-sets, let $\Gamma_i(H)$ be its allowed starts of type $i$.
Counting incidences from $H$ to those starts gives
$|H|d_i\le|\Gamma_i(H)|e_i$, so

$$
\begin{aligned}
|\Gamma_0(H)|+|\Gamma_1(H)|
&\ge |H|\frac{v_0+v_1}{N}\\
&=|H|\frac{\binom{m+1}r}{N}\ge |H|.
\end{aligned}
\tag{LAGR.9}
$$

This is (LAGR.3) for every $H$, including the empty family, and proves
Hall sufficiency throughout the interior range.

At $r=0$ every $F_J$ is $\{\varnothing\}$, so feasibility is exactly
$N=1$, just (LAGR.6). At $r=t+1$, each $F_J$ consists solely of the
full menu $W\cup\{z\}$. These menus are distinct, giving an SDR and
singleton continuation paths directly. Also
$\binom{m+1}{t+1}=\frac{m+1}{t+1}\binom mt\ge N$.
Here starts of size $t+1$ WITHOUT $z$ have no incident menu; they must
not be included in an orbit-degree division. No division by that zero
degree, or by an empty orbit, is used. For $k=0$ or $k=m$, $N=1$ and
$r_*=0$; all lengths in $[0,t+1]$ work for this single menu. For $m=0$
this says $k=0$, $U=\{z\}$, and exactly $r=0,1$ are admitted. The
interior proof is unnecessary when $t=0$. A menu always has $t+1$
rows, excluding longer or negative lengths. Finally for $(m,k)=(6,3)$,
rank zero has size $1$, ranks one and two have the stated sizes, and
$r=2\le t+1=4$. Theorems 18.2–18.3 turn Hall sufficiency into the
claimed same-source feasibility and sharp minimum. $\square$

**Proposition 18.5 (erased prefix order and newly retained observations
have different roles).** At $(m,k,r)=(7,3,2)$, the prefixes $(4,3)$
and $(3,4)$ cannot distinguish $J_1=\{1,2,5\}$ and
$J_2=\{1,2,7\}$ after Definition 18.1's reset: both leave $Q=\{3,4\}$.
Nevertheless later equal geometries may carry different NEW $T$
transcripts. This distinguishes individual policies, not existential
feasibility of the two reset contracts.

Proof. Both prefixes are legal for both supports, and Theorem 18.2 gives
the same source $E_y(\{3,4\})$. The complete pre-reset order and private
control are erased. The remaining menus are respectively
$\{z,6,7\}$ and $\{z,5,6\}$. The initial-state argument of Theorem 18.3
therefore prevents one successful $T$ continuation for this collided
encoding. A primitive guard does not supply the missing cohort bit:
calling a previously used original row can be native-enabled and still
violate the task.

For a later meeting instead use $(m,k,r)=(3,1,1)$ and index the three
supports by their omitted candidate $i$. Their menus are
$U_1=\{z,2,3\}$, $U_2=\{z,1,3\}$, $U_3=\{z,1,2\}$.
Choose the respective starts $\{z\},\{3\},\{1\}$. Two possible $T$
paths are

$$
\{z\}\subset\{z,3\}\subset U_1,\qquad
\{3\}\subset\{z,3\}\subset U_2;
\tag{LAGR.10}
$$

the third can be $\{1\}\subset\{1,2\}\subset U_3$.
At the meeting vertex $\{z,3\}$, the first two runs have retained
different initial observations acquired AFTER reset and different new
calls. They can choose $2$ and $1$ respectively. A geometry selector
cannot implement those particular two tails at that shared vertex.
It can instead use the disjoint paths

$$
\{z\}\subset\{z,2\}\subset U_1,\qquad
\{3\}\subset\{1,3\}\subset U_2,\qquad
\{1\}\subset\{1,2\}\subset U_3.
\tag{LAGR.11}
$$

All paths are native legal by Theorem 18.2. Thus the policy distinction
uses only new observations and gives no existential $G/T$ gap.
The memoryless/prefix-dependent distinction itself is already explicit
in Boundary Dynamics §80; the new claim here is this reset and
original-row correspondence on the LAB source. $\square$

**Proposition 18.6 (same-source transport and the recovery boundary).**
The preceding criteria and prefix-length threshold are unchanged when
the current source syntax is presented by its acquired oriented material
support, its terminal boundary, or its labelled causal membership order,
on the same actual source and with Definition 18.1's access/reset premises.
They concern recovery sufficient for COMPLETE original-cohort continuation;
they do not recover an erased serial order or minimize total resources.

Proof. AA17.2–17.3 and LAB16.6 give the existing round trips among these
source views, retaining beta's unary material marker and excluding tape
edges. Applying those inverses at the current source gives precisely
$E_y(Q)$; Theorem 18.2 then recovers $Q$. At the INITIAL reset cut,
the SDR codebook decodes this newly acquired $Q$ to $J$, hence the entry
$x_J(y)$ and remaining original cohort, but not the erased prefix order.
At later $T$ cuts, its newly retained transcript is still an additional
input: a later geometry alone need not decode $J$, as Proposition 18.5
shows. Changing source view transports that same transcript unchanged.
For $G$, each current set locates its unique disjoint codebook path.
Conversely the current edited-address set computes the same syntax and
hence each source view. Every route describes the SAME source, so these
compositions agree and a one-address path step is the same actual $P/S$
event in every view.
Acquiring a causal description or boundary does not by itself grant
traversal, bindings or calls; their current lawful access remains a
separate premise, including the unresolved Busy reset/continuation bridge.

The mature Hall criterion and the disjoint skipless-chain covering theorem
are intermediate results in Theorem 18.3, with their parameter maps given
there; neither is a new matching theorem here. ABT12's broader geometric
encoding, Boundary Dynamics §80's selector distinction, the symmetric-chain
argument (CL.22) in Common Live Cones, and the Hall applications of
Acquired Relation History are existing results. The source image after
a declared reset, its native complete-continuation correspondence and the
sharp comb application above are `repo-derived` ordinary mathematical
deductions from the stated suppliers. They add neither a worldwide-novelty
claim nor a fresh Lean-certification claim. In particular §17's fixed-length
prefix task is different: its retained initial supplement and bounded
success condition are not the post-reset full-exhaustion task here.
All public/codebook storage, source construction and traversal, reference
acquisition, scratch, inaccessible tapes, maintenance, full traffic and
returns remain separate paid resources under Definition 18.1. The logical
reset restriction gives no physical-erasure or new-controller existence
conclusion. $\square$

[SATRESET]: https://arxiv.org/html/2207.07391v2#Thmtheorem2

## 追加锚（本行以下为增补区）

## 19. Transient source encoding of an attained order and mandatory terminal recall

**Definition 19.1 (old serial content and the added terminal task).**
Keep exactly Definition 18.1's source, access, reset and full-return
premises, with the acquired fixed $y,k$, candidate basis $A$, supports
$\mathcal J$ and remaining ORIGINAL-row menus $U_J$ of (LAGR.1).
For each $J$ let $\Sigma_J$ be a declared nonempty family of ACTUALLY
attained length-$k$ ordered lists of successful typed original events
on that support, and put

$$
\mathcal H=\{(J,\sigma):J\in\mathcal J,\ \sigma\in\Sigma_J\},
\qquad d_J=|\Sigma_J|.
\tag{LAGS.1}
$$

Theorem 15.2 supplies $\Sigma_J=\operatorname{Perm}(\{e_p:p\in J\})$
and $d_J=k!$ for Definition 15.1's supplied arbitrary-order schedule
family. Its original-row guard argument, with LAB9.3–9.4's acquired
authentic addresses, tags and references, realizes every such order:
an edit at one old leaf changes neither another old leaf's constructor
nor its root reference. Each event is taken through its complete inner
return. These are alternative actual supplied schedules, not multiple
executions of one choice-free deterministic preparer. The word $\sigma$
contains only these addressed typed successful events, not full controller
traffic, raw identities, elapsed time or an annotation on an unchanged run.

An encoder that has actually acquired $h=(J,\sigma)$ may perform exactly
$r$ further distinct eligible ORIGINAL-row writes $Q\subseteq U_J$,
each through full inner return. The logical reset erases ALL supplementary
pre-reset private control and ordered records, including $h$, write order,
old lists, cursors, scratch and readable private archives. Only current
source geometry, fixed public $y,k,r$, one finite $h$-independent
program/codebook, authentic fixed access bindings and common protocol
obligations remain. As in §18, attached physical tapes are inaccessible
selector inputs. The codebook is backed public data, not another source
edit or a surviving run-dependent control state.

After reset every run must complete exactly $U_J\setminus Q$, with
no new-row or decorative write, and only at the completed cut output the
exact old word $\sigma$, then discharge the full declared reply,
acknowledgement, return and cleanup. No earlier output archive is allowed.
Both $G$'s choices AND its final recall value depend only on current source
geometry and fixed inputs. A last reply, saved selection, phase tag or
history-dependent final control cannot supplement that final value.
$T$ may retain only observations it actually acquires AFTER reset.
There is no tape/Next/FetchGrowth access, pointer age, hidden-state readout
or cohort-refusal probing. Every permitted observation and source reply
has Definition 18.1's current-source factorization.

**Corollary 19.2 (exact constrained transient encoding and terminal
survival).** Under Definition 19.1, put
$F_J=\{Q\subseteq U_J:|Q|=r\}$. A prefix encoder and $T$ can satisfy
this complete success-and-recall task if and only if

$$
\left|\bigcup_{J\in\mathcal S}F_J\right|
\ \ge\ \sum_{J\in\mathcal S}d_J
\qquad\text{for every }\mathcal S\subseteq\mathcal J.
\tag{LAGS.2}
$$

If any $d_J\ge2$, no prefix encoder and $G$ can satisfy the task,
regardless of whether (LAGS.2) holds. When every $d_J=1$, the unique
publicly specified order for each support adds no distinction, and
Theorem 18.3's exhaustion-only feasibility criterion also suffices for $G$.

For the attained beta comb of Corollary 18.4, with all supplied orders,
write $N=\binom mk$, $t=m-k$, $d=k!$, $0\le k\le m$. The exact $T$
capacity is

$$
\begin{array}{c|c}
\text{prefix length}&\text{feasibility of completion and exact old-order recall}\\ \hline
r=0&dN=1\\
1\le r\le t&dN\le\binom{m+1}{r}\\
r=t+1&d=1
\end{array}
\tag{LAGS.3}
$$

Outside $0\le r\le t+1$ there is no such prefix. In particular the
attained case $(m,k,r)=(5,2,3)$ has twenty admissibly encoded ordered
histories, one remaining original call per run, and ten terminal sources
with two orders each. Here $T$ succeeds at $r=3$ and fails at $r=4$;
$G$ fails for the added recall task at either length.

Proof of the history criterion. By Theorem 18.2, every allowed code
$Q\in F_J$ is realized by genuine original calls and its initial reset
geometry is exactly $E_y(Q)$, with an injective acquired inverse to $Q$.
Suppose distinct histories receive the same $Q$. Their INITIAL reset
sources and all other permitted initial inputs then agree. Determinism
and the current-source observation/reply premise force identical future
choices, replies and successors for as long as both runs remain legal.
An ineligible original-row call already fails the task; its refusal is
not an extra observation. If the supports differ, their distinct menus
$U_J$ cannot both be exhausted by the same suffix from this common $Q$,
as in Theorem 18.3. If the supports agree but their orders differ, a
common successful suffix cannot produce both required final words.
Thus distinct histories require distinct INITIAL reset geometries even
for $T$. This does not prohibit later equal $T$ geometries with different
newly acquired transcripts.

Conversely, distinct admissible codes give one fixed inverse table
$Q\mapsto(J,\sigma)$. After reset, $T$ actually traverses its current
source, recovers $Q$, decodes this table and retains that NEW observation's
information. It completes $U_J\setminus Q$ once in a public order and
recalls the decoded $\sigma$ only at exhaustion. A logical address in the
table grants no call right: traversal from the surviving authentic bound
root must acquire the CURRENT target reference, check its correspondence
to the backed address and current tag, and use authenticated dispatch
with current authority. Disjoint original rows preserve these references
until called. Sufficient backing, complete source/arithmetic/tape
maintenance, literal replies, acknowledgements and inner returns are
required throughout. Codebook construction, acquisition, navigation,
computation, retention and all traffic are paid separately.

The matching step is the existing finite Hall theorem already used in
§18 and [Acquired Relation History §9][ARHSERIAL], specifically pinned
mathlib's `Finset.all_card_le_biUnion_card_iff_existsInjective'` in
`Mathlib/Combinatorics/Hall/Finite.lean`. Its indices here are histories
$h\in\mathcal H$, its representatives are subsets of $\Lambda(y)$,
and the allowed set for $(J,\sigma)$ is $F_J$. Applying Hall to all
histories over a support subfamily gives necessity of (LAGS.2).
Conversely, any history subfamily $K\subseteq\mathcal H$ has support
projection $\mathcal S$, neighborhood $\bigcup_{J\in\mathcal S}F_J$
and size at most $\sum_{J\in\mathcal S}d_J$. Hence (LAGS.2) supplies
Hall for EVERY history subfamily, proving sufficiency. Repetition of a
menu is therefore counted by its actual attained order multiplicity,
not by inventing additional geometric codes.

Proof of the terminal obstruction. For a fixed $J$, two encoders of
different orders may select different $Q$ and have different residual
sets $U_J\setminus Q$. Nevertheless every successful complete run has
TOTAL completed set $U_J$, hence terminal source $E_y(U_J)$ by
Theorem 18.2. This source depends on $J$ and not $\sigma$. A final
recall value derived only from that geometry and fixed inputs must agree
for two orders on this support, contradicting exact recall. Changing the
intermediate pairing or path cannot change this terminal equality.
When $d_J=1$ for all $J$, Theorem 18.3 instead provides disjoint source
paths whenever support Hall holds. Their terminal $U_J$ identifies $J$
and its unique fixed order, so $G$ can also supply the final value.
This is the existing task-kernel obstruction applied to the ADDED recall
task. It leaves §18's exhaustion-only existential $G/T$ equivalence intact.

Proof of the comb capacity, including all Hall subfamilies. Write
$W=[m]\setminus J$, so $|W|=t$ and $U_J=W\cup\{z\}$.
For $1\le r\le t$, the two disjoint allowed-code types are the
$r$-subsets of $W$ without $z$ and $\{z\}\cup R$ with
$R\subseteq W$, $|R|=r-1$. Use exactly the incidence counts
$(v_i,d_i,e_i)$ of (LAGR.8): $v_0=\binom mr$,
$v_1=\binom m{r-1}$, and $Nd_i=v_ie_i$ with $e_i>0$.
For any support subfamily $\mathcal S$, its type-$i$ neighborhood
$\Gamma_i(\mathcal S)$ satisfies
$|\mathcal S|d_i\le|\Gamma_i(\mathcal S)|e_i$. Therefore

$$
\left|\bigcup_{J\in\mathcal S}F_J\right|
=|\Gamma_0(\mathcal S)|+|\Gamma_1(\mathcal S)|
\ge |\mathcal S|\frac{\binom{m+1}r}{N}
\ge d|\mathcal S|
\tag{LAGS.4}
$$

whenever the interior inequality in (LAGS.3) holds. This proves every
weighted Hall inequality, not merely total counting. Conversely the
whole family reaches exactly these two orbits, of total size
$\binom{m+1}r$, so (LAGS.2) forces that inequality.

At $r=0$ the only code is $\varnothing$, requiring $dN=1$.
At $r=t+1$ each history over $J$ has ONLY code $U_J$. The reachable
code set has size exactly $N$, with one distinct code per support;
(LAGS.2) holds exactly when $d=1$. The nominal rank count
$\binom{m+1}{t+1}$ is not the reachable code count. In particular
size-$(t+1)$ sets without $z$ have zero incidence and cannot enter a
positive-degree orbit argument; empty orbits are omitted as well.
Each menu has $t+1$ rows, excluding all outside lengths. For $k=0$,
$d=N=1$ and all lengths $0,\ldots,m+1$ work. For $k=1$, $d=1$,
$N=m$: every $r=1,\ldots,m$ works, and $r=0$ works only at $m=1$.
For $k=m\ge2$, $t=0$, $N=1$, $d=m!>1$, so neither $r=0$ nor
$r=1$ works. At $m=0$, necessarily $k=0$ and $U=\{z\}$; precisely
$r=0,1$ work. These cases also cover the overlaps at $m=1$ without
using an interior orbit when $t=0$.

Proof by an explicit attained comb codebook. For $m=5$ label candidate
$i$ by the authentic logical address $p_i=L^{i-1}R$, and put $z=L^5$.
For $i<j$ the two old words on $J=\{i,j\}$ are
$(P_{p_i},P_{p_j})$ and $(P_{p_j},P_{p_i})$. The following is one fixed
codebook; entries list the three ORIGINAL $y$-rows to split before reset.

| $J$ | $Q$ for $(i,j)$ | $Q$ for $(j,i)$ |
| --- | --- | --- |
| $\{1,2\}$ | $\{3,4,5\}$ | $\{z,3,5\}$ |
| $\{1,3\}$ | $\{2,4,5\}$ | $\{z,2,4\}$ |
| $\{1,4\}$ | $\{2,3,5\}$ | $\{z,2,3\}$ |
| $\{1,5\}$ | $\{2,3,4\}$ | $\{z,3,4\}$ |
| $\{2,3\}$ | $\{1,4,5\}$ | $\{z,4,5\}$ |
| $\{2,4\}$ | $\{1,3,5\}$ | $\{z,1,5\}$ |
| $\{2,5\}$ | $\{1,3,4\}$ | $\{z,1,3\}$ |
| $\{3,4\}$ | $\{1,2,5\}$ | $\{z,2,5\}$ |
| $\{3,5\}$ | $\{1,2,4\}$ | $\{z,1,4\}$ |
| $\{4,5\}$ | $\{1,2,3\}$ | $\{z,1,2\}$ |

Each entry is contained in $U_J=([5]\setminus J)\cup\{z\}$.
The first column of codes contains all ten triples without $z$; the
second contains $z$ with each of the ten pairs exactly once. Thus all
twenty codes are distinct. Every menu has four rows, leaving exactly
one original call after this length-three prefix. Both orders on a
support finish at the same $E_y(U_J)$, and different supports give
different terminal sources by injectivity in Theorem 18.2. There are
therefore exactly ten terminal sources with two old orders each.

These histories have actual source preparations. From the known alpha
root, promote the root; split successively at
$\varepsilon,L,\ldots,L^4$, and promote the born right alpha at $p_i$
exactly when $i\notin J$. This attains $x_J(y_5)$, whose original
frontier is then lawfully acquired and sealed. Execute the two remaining
promotions at $p_i,p_j$ in the specified supplied order, acquiring their
successful events and completing each inner return. This attains $y_5$
with the stated KNOWN old history. The three code writes are now splits
at disjoint eligible old beta rows, in any fixed code-dependent public
order. None targets a new child. These different actual schedules supply
the information used by the encoder before reset; no order is freely
attached to a source description. At $r=4$, by contrast, every prefix
has already written its full four-row menu, leaving just ten reachable
codes for twenty histories. $T$ cannot recover the erased order from
such an initial reset source. Availability is thus not monotone in the
number of prescribed writes.

Finally, AA17.2–17.3 and Proposition 18.6 transport this same current
source among syntax, oriented material support, terminal boundary and
labelled causal membership order. At the reset cut a successful codebook
therefore makes the old serial word recoverable from ANY of these
actually acquired views. Mandatory completion identifies the two orders
on a support in ALL these source views; $T$'s newly acquired retained
information can survive that identification. This is a constrained
transient encoding versus terminal survival correspondence on the
original atomic $P/S$ source. Generic chronological nonrecovery and
factorial supplements are already supplied by [Native Cutoff Completion
Frontiers §§8–9][CCFSERIAL]; [AAII Definition 67.2][AAIISERIAL] retains the
erased-order boundary of earned current syntax. The finite matching step
is reused, not a new matching theorem. The present conditional corollary
and sharp original-row application are `repo-derived`.

All recovery is conditional on the admitted lawful owned traversal,
authenticated dispatch, sufficient backing and complete maintenance and
INNER-return cuts of Definition 18.1. AA21 is READY-scoped; the outer
LAB supervisor may still be BUSY at these cuts. No Ready-only external
service is imported. The resettable outer installation/phase bridge is
UNVERIFIED. The reset is a declared logical controller operation, not a
native inverse or thermodynamic deletion. There is no assertion of a
total-resource optimum, fresh Lean certification, worldwide novelty or
completion of the broader space–time–boundary–memory programme. $\square$

[ARHSERIAL]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md#9-mathematical-scope-suppliers-and-remaining-obligations
[CCFSERIAL]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CUTOFF_COMPLETION_FRONTIERS.md#8-exact-joint-price-of-discarded-labels-and-sweep-order
[AAIISERIAL]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_II.md#67-supplier-correspondence-and-exact-applicability-boundary

## 追加锚（本行以下为增补区）

## 20. A paid private scrub and source-only resumption in a separate session

**Definition 20.1 (fixed public data and actual hidden alternatives).**
Fix the actually backed public syntax $y$, exact integers $k,r$, root
binding and current grants of Definition 18.1. Let $\mathcal H$ be either
its finite support family, or Definition 19.1's finite, effectively
enumerated family of attained ordered histories. Write $J(h)$ for the
support of $h\in\mathcal H$. The alternatives are actual schedules in
that SAME acquired LAB fibre, with the authentic frontier acquisition,
successful events and complete inner returns of §§9–11 and 15. A
history description supplied without those events is not an alternative.

Fix one effective program and publicly backed finite codebook $K$,
independent of which $h$ is attained. It computes

$$
Q_h=K(h)\subseteq U_{J(h)},\qquad |Q_h|=r.
\tag{LAGI.1}
$$

Its prefix procedure lists these distinct ORIGINAL $y$-leaf addresses
in a fixed public order and executes their current-tag calls. The
program may compute the codebook by terminating finite enumeration on
public parameters, or interpret a supplied finite table. It is not an
uncomputed infinite table of source responses. Public backing contains
syntax, parameters and fixed codebook data, not a saved acquired
address/reference correspondence or a hidden-history-dependent choice
of program. Denote these fixed public data collectively by $\mathsf P$.

A continuation policy, when supplied, is an effective $G$ or $T$ of
Definition 18.1, with its declared output function. Correct complete
continuation, and any injectivity of $h\mapsto Q_h$ needed for recovery
of $J$ or order, are separate premises supplied by §§18–19. Neither
follows merely from (LAGI.1). The fixed twenty-code table in §19.2, for
example, supplies a finite codebook and a post-cut $T$ policy without
requiring a new matching or capacity theorem.

**Assumption 20.2 (owner-installed session and its access boundary).**
Before the selected hidden schedule, the owner installs one NEW session
request/reply connection and finite session control in the actual LAB
supervisor. Its ingress is serialized by the existing arbiter. It enters
only at genuine returned outer idle, with the inherited tape/arithmetic
invariants and empty old transient fields; no scalar or pair macro is
active. It holds that actual lock throughout the session. The session
may acquire its old frontier and receive the selected finite schedule,
thereby attaining and acquiring $h$ at $y$, before its $r$ code writes.
All such input, including its consumed-position state, is supplementary
private state. No hidden schedule suffix remains available after the cut.

Its fixed outer control follows

$$
\mathsf{Prefix}\longrightarrow\mathsf{Scrub}
\longrightarrow\mathsf{Reacquire}\longrightarrow\mathsf{Continue}
\longrightarrow\mathsf{Print}\longrightarrow\mathsf{End}
\longrightarrow\mathsf{ACK}\longrightarrow\mathsf{Return}.
\tag{LAGI.2}
$$

Prefix and Continue have finite loops through the original internal
source connection. The actual supervisor's dispatch and maintenance
owner accepts these session-origin calls and returns to the designated
session continuation after the inner driver's REAL root return. An
internal return leaves the session lock held. Scrub is a new internal
cut, not PairReady, and grants no external ingress. The eventual session
report is a function only of $\mathsf P$ and permitted newly acquired
continuation state. Its contract owes no old scalar/pair result, old
frontier tail or unconsumed pre-cut reply. Its final full output,
acknowledgement, root return and cleanup must restore the old returned idle.

Every accepted event still uses Definition 11.1's SAME hook: original
navigation and guard, reservation, actual source edit, all proper-ancestor
tape appends, arithmetic successors computed from pre-edit banks, and
discharge of pending work before the complete Growth reply is released.
The bound internal receiver backs and consumes every literal kind/address
bit and End, acknowledges, and waits for real inner return. Its session
copies belong to the scratch below. Protected source headers/tapes,
immutable attachment $e$, scalar/pair synchronization, original receivers
and every literal legacy reply retain their meanings. No dispatch owner
is bypassed and no produced traffic is suppressed. After session return
the seven original public calls and scalar/pair connections remain usable.

The post-cut session observer may traverse CURRENT logical source fields
through the authentic root/grants and use its new scratch. It cannot read
the auxiliary header/tapes, $e$, protected service banks or old receivers;
call FetchGrowth/Next; inspect old paths or last-call state; enumerate
resource/ownership metadata; or observe allocation names/age, representation
width, elapsed work, capacity or exhaustion. Reference equality is used
only to authenticate current traversed operands and bindings, with no raw
name channel. Root, program, public backing and the fixed workspace layout
are common on the fibre. There is no other alias, callback, request archive
or later hidden input into this observer. This wiring and authority
separation is an INSTALLATION premise: common ownership alone does not
imply it. Protected legacy recall can still distinguish old histories for
its own authorized users. Erasure below is relative to this session access
boundary, conditional on the retained current source.

All finite runs have sufficient finite material, exclusive current rights,
complete supplied inputs and acknowledgements, and no interruption,
revocation or competing writer. These are AA20.1's ideal finite-execution
conditions, not a claim about an existing fixed-capacity device.

**Definition 20.3 (public-shaped private backing).** Reserve before the
hidden schedule a finite padded arena with a fixed public slot layout and
authentic field references. Each writable slot has a fixed type and neutral
value. Its immutable public navigation spine and slot schema contain no
history-dependent data; they remain usable while data fields are cleared.
Variable lists use occupancy fields within this SAME backing, rather than
history-dependent allocated chains that could survive as a length channel.

The data slots and a fixed register bank cover ALL supplementary pre-cut
copies: received input and its cursor; $h,J$, order, selected code and
labels; OLD/frontier rows, address bits and reference lists; parser and
output buffers; counters and loop cursors; arithmetic operands and banks;
saved continuations and call results; latches, phase flags and source
cursors; allocator descriptors, occupancy/free-list fields and every
mutable alias. Any supplementary supervisor/receiver copy is included.
Original inner-service scratch must already be empty at its returned
Ready, as required by AA20.2; a pending inner operation cannot enter Scrub.
No supplementary pre-cut object is left outside this coverage. Source
objects, committed tape backing and public data are separate retained
components, not cells falsely counted as erased scratch.

For fixed public parameters such backing is sufficient: the admitted
$\mathcal H$ is finite, the codebook computations terminate, and each
prefix is a finite sequence of finite traversals and complete calls.
Execute their description-level procedures on every member of the finite
enumeration to obtain a finite maximum workspace requirement, and pad
all alternatives to any sufficient common size. The same argument applies
to a supplied terminating finite continuation policy if a common arena
for the whole session is desired. This is an effective finite computation,
not access to the run's hidden choice. Source/tape reservations retain
their own AA20.1 material requirements. Actual reference fields must have
sufficient finite backing under the installation's representation; the
argument bounds logical slots, not a uniform number of reference bits.
It asserts neither a uniform arena bound over arbitrary source sizes nor
free reference widths. Hidden-dependent arena length, optional spare
objects or readable allocation descriptors would violate this definition.

**Theorem 20.4 (conditional paid scrub, fresh difference acquisition and
completed-cut simulation).** Under Definitions 20.1 and 20.3 and
Assumption 20.2, a single fixed finite-control procedure using owned field
operations implements the prefix, scrub and fresh acquisition phases of
(LAGI.2). At its completed Scrub cut it has current
source $z=E_y(Q_h)$, unchanged committed protected fields, one common
private normal form $w_0$, and the common Reacquire program counter with
the session lock held. All supplementary pre-cut distinctions have been
removed from its private backing by actual writes. Fresh current-source
traversal with public $y$ then recovers EXACTLY $Q_h$ on this actual image.

At the declared complete-inner-return decision cuts, equal $\mathsf P$,
current source and allowed new memory give equal selected observations,
replies and next actions, modulo opaque fresh-name renaming. Each completed
lawful session call has its actual $P/S$ source successor, complete
tape/arithmetic successor and full literal reply. A supplied successful
continuation policy therefore gives the session's full stipulated result
and real outer return. The source relation transports through AA17's
syntax, oriented support, terminal boundary and labelled causal membership
maps on their actual images, commuting with each completed source call.
These conclusions install neither a reset command in the unchanged legacy
controller nor a successful codebook/policy where one has not been supplied.

Proof. During Prefix, really acquire the actual frontier/history and
evaluate $K$ in the padded backing. For each listed address, traverse
from the bound root, acquire the CURRENT reference, check its correspondence
with the address/tag, and submit the original addressed frame. Since its
addresses are distinct eligible original leaves, LAB9.4 and Theorem 18.2
give every guard and the endpoint $E_y(Q_h)$. After every call the actual
supervisor completes the accepted-event hook, its bound receiver consumes
the full reply, and the inner driver returns to Ready before session
control advances. Thus the last prefix call leaves no pending edit,
append, arithmetic commit or reply. The outer session is still busy.

Now enumerate the $N$ arena data slots in their fixed PUBLIC order. Write
each slot's neutral value, including unused padding. After $i$ writes the
first $i$ slots are neutral, all remaining supplementary data are confined
to the remaining slots and the designated register bank, and source,
public spine and protected committed fields are unchanged. This invariant
holds at zero by coverage. One owned write to slot $i+1$ establishes the
next case without reading any old value. The fixed public spine prevents
clearing a data link from losing the rest of the traversal. At $N$ no
arena data remain. The scrub traversal's own index, target reference and
latches reside in the designated bank, so the invariant has not silently
discarded the scrubbing machine.

Finish by explicit writes normalizing every register in that bank: source
cursor to the common root, other private references to null, counters,
flags and latches to their fixed neutral values. Set the phase to
Reacquire and jump to its one common code location. The final straight-line
tail uses only fixed public bindings; it needs no saved return address or
old register value. Its control counter has that same final value in every
run. The arbiter remains in its fixed session-held state. Thus, writing
$\operatorname{view}_{\rm sess}$ for this observer's declared post-cut view,

$$
\operatorname{view}_{\rm sess}(C_h^{\rm scrub})
  =(\mathsf P,E_y(Q_h),w_0,\mathsf{Reacquire},\mathsf{held}).
\tag{LAGI.3}
$$

Here $w_0$ is independent even of $Q_h$; the retained SOURCE may deliberately
encode $h$. Protected histories are not asserted equal. Every one of the
$N$ data writes, each final register/cursor normalization, traversal step
and control operation is charged. A hidden-dependent scrub length or final
bank-direction/phase bit would falsify (LAGI.3), so padding and final
normalization are essential. This constructs the private reset from owned
writes, rather than defining a Reset operation to forget its arguments.

Reacquire traverses the actual finite source using only parent/left/right
source fields and authentic bindings. Its logical-arity parser treats a
unary marker as part of beta, never as a logical child or OLD row. Compare
with the backed public syntax at each original leaf $p$ of $y$:

$$
\begin{array}{c|c|c}
y_p&z_p&\text{recovered membership}\\ \hline
\alpha&\alpha&p\notin Q_h\\
\alpha&\beta&p\in Q_h\\
\beta&\beta&p\notin Q_h\\
\beta&\langle\beta,\alpha\rangle&p\in Q_h
\end{array}
\tag{LAGI.4}
$$

Original leaves are prefix-incomparable and each was written at most once;
no new child was targeted. These exhaust the actual image and distinguish
all its membership bits, as in Theorem 18.2. In particular an original
alpha becoming a branch is OUTSIDE this domain, not an additional decoding
case. Original branch positions persist, so paid simultaneous traversal
of $y$ and $z$ locates every comparison and binds actual current references.
No inverse source edit, old pointer, numeral-to-reference cast, source
inverse primitive or refusal probe is used. This proves recovery of $Q_h$
for every allowed codebook, including a noninjective one. Only if the
supplied codebook is injective on supports or ordered histories can its
finite inverse additionally recover that old content. Such decoding is a
NEW observation after the cut, not a surviving old private copy.

For simulation retain as a proof invariant the actual successful word $w$,
its complete ancestral tapes, $c=\overline{v(t)}$, the correct scalar fields
$(B,r_s)=E(q(t))$, and unchanged $e$. At the cut domain, projection selects
the current source $t$ and permitted new session memory. Scrub and source
navigation stutter on the source and committed protected fields. When the
session selects a call, its OWN traversal scratch is in the arena and the
inner driver is genuinely at AA20.2 Ready: the preceding call has returned,
and local session work has created no pending source operation. The installed
dispatch edge submits its authenticated frame from that Ready, then holds
the session continuation while the original driver is busy. AA20.3 and
LAB11.1–11.2 give its guard/reservation/edit/maintenance/pre-edit commits,
complete reply, End, acknowledgement and real root return. The source-call
cut reached on return has

$$
(t,w)\longmapsto(g(t),wg),\qquad
\mathcal W\longmapsto\mathcal W(wg),\qquad
c\longmapsto\overline{v(g(t))},\qquad
(B,r_s)\longmapsto E(q(g(t))),
\tag{LAGI.5}
$$

for its actual accepted $g=P_p$ or $S_p$, with the full original Growth
reply. Here $\mathcal W(wg)$ denotes literal ancestral tapes for that very
word, not merely some compatible tapes. No intermediate pending state is
treated as a completed successor. This proves how the new outer session
reaches the actual inner cuts; an arbitrary outer Busy state supplies no
such dispatch edge.

AA21.1–21.2 is now used ONLY for this Ready-to-Ready $Q_c$ source-response
projection. Tapes may differ between two equal sources, but are not selector
inputs and do not change these guards, literal replies or source successors.
Current logical field traversal likewise gives the same observations on
isomorphic oriented trees. With no name/age channel, freshly bound references
can be matched by the same structural correspondence, preserving the equality
tests needed for authentication. Equal public data, current source and new
memory therefore give equal next choices and replies. Induction over completed
calls establishes the asserted source-only simulation; it does not equate
the two runs' protected tape contents or their complete controller traffic.

For $G$, clear all decision/call scratch after each complete inner return
and enter one common Decision location; recompute its next call or Stop
solely from the newly traversed geometry and $\mathsf P$. A retained old
decision, call count, last address or terminal branch flag is not allowed.
Temporary operands during one such decision are current-source-derived.
For $T$, start with empty old memory at (LAGI.3), then retain only observations
and choices actually acquired subsequently. Equal later geometry alone need
not imply equal $T$ memory, as Proposition 18.5 already shows. Correctness
and termination of a SUPPLIED successful policy, authentic operand acquisition
and (LAGI.5) now give precisely its finite legal continuation. Its report is
built from the declared public/new inputs, printed completely, followed by
End and supplied ACK, then real outer root return and paid cleanup. The lock
is released only at that old returned idle. The original tape/arithmetic
invariants and all old public connections remain available there.

Finally define the exact source-image domain

$$
\mathcal I_y=\{E_y(R): h\in\mathcal H,\ Q_h\subseteq R\subseteq U_{J(h)}\},
\tag{LAGI.6}
$$

restricted to the cuts actually reached by the supplied continuation when
one is fixed. These terms lie in $\mathcal D_+$. AA17.3 sends each term to
its oriented MATERIAL support, including beta's unary marker, and to the
terminal antichain of that support. Prefix closure and maximal-element
extraction are its inverse support/boundary maps; arity parses the term.
AA17.2 sends it to its labelled causal membership order with the specified
birth types. Applying these existing inverse maps, then (LAGI.4), recovers
the same $R$; applying them before a decision computes the same source input.
For a lawful next original row $p$, the source step is
$E_y(R)\mapsto E_y(R\cup\{p\})$. Taking ANY of the three views after that
actual completed call equals decoding its actual-image view, making this
same step, and taking the view again. This is the commuting correspondence,
with $T$'s new memory transported unchanged as an additional component.
It supplies no chosen ancestral serial extension, all-phase inverse, reverse
source actuator or access right from a mathematical description.

Interactive erasure and step/stutter simulation are mature methods:
Hunt–Sands, [*Just Forget It*, extended ESOP08 version, §§2–3, especially
Definitions 4–6][HSSESSION], includes state and input-cursor residue in an
interactive erasure condition; Abadi–Lamport, [*The Existence of Refinement
Mappings*, SRC Research Report 29, §2.4, conditions R1–R4][ALSESSION], supplies
the state/step/stutter refinement method. Here the preserved geometry is an
explicit allowed observation, so the claim is private normalization and
conditional future congruence, not erasure of all information about $h$.
These originals do not install LAB rights, wiring or reset. The source-specific
composition above is `repo-derived`, reusing AA17/20/21, LAB4/10/11/15–19 and
their declared guards and returns. NativeSelectedRA's local cleanup and
PhysicalDivider's clean-round/return results concern separate installations;
no mapping of their ports, backing or control to LAB is asserted. There is
no fresh Lean certification, physical spacetime conclusion, thermodynamic
deletion, unit-cost assertion or total-memory optimum. $\square$

**Proposition 20.5 (unchanged-controller and whole-installation obstructions).**
The new session theorem does not furnish a scrub/resume transition for the
unchanged installed left-first $\mathsf R$. Nor does preserving the original
legacy recall/Next semantics permit erasure of the whole installation's old
history distinctions.

Proof. Take the attained entry $\langle\beta,\alpha\rangle$, whose OLD list
in Definition 9.3 is $(L:\beta,R:\alpha)$. After its first call $S_L$ and
complete inner return, the source is
$\langle\langle\beta,\alpha\rangle,\alpha\rangle$. The inner driver is Ready,
but the outer $\mathsf R$ still owes its right-row $P_R$, list advancement
and full return tail. Definitions 10.2 and 11.1 retain that actual continuation
and lock; they do not enable Scrub. Erasing its OLD list/cursor/continuation
cannot implement that unchanged control. Waiting for ordinary macro cleanup
instead performs $P_R$ and yields
$\langle\langle\beta,\alpha\rangle,\beta\rangle$, missing the requested
$r=1$ source cut. This is the concrete old-macro obstruction supplied by
LAB9–11, rather than another generic hidden-phase theorem. The general
requirement to normalize or exclude accessible routing residue, including
phase/direction, is already [Concurrent Native Cut Workspace §11][CWSSESSION].

Separately reuse AA20.5's words
$P_\varepsilon S_\varepsilon S_LP_R$ and
$P_\varepsilon S_\varepsilon P_RS_L$. They have the same source
$\langle\langle\beta,\alpha\rangle,\beta\rangle$, but FetchGrowth$(3)$
returns $S_L$ versus $P_R$, and Next$(3)$ actually selects $S_{LL}$ versus
$S_R$, with different complete replies and source successors. Keeping these
literal semantics keeps a distinction accessible to authorized legacy users.
Assumption 20.2 excludes those channels only from the new observer; it does
not delete the records. Consequently an owner-installed session connection,
common resumable control and explicit authority separation are additional
installation obligations. Owned field writes suffice for the private scrub
UNDER those obligations; the protected legacy installation by itself has
acquired neither that command nor universal history erasure. $\square$

[HSSESSION]: https://www.cse.chalmers.se/~dave/papers/Hunt-Sands-ESOP08-extended.pdf
[ALSESSION]: https://lamport.azurewebsites.net/pubs/abadi-existence.pdf
[CWSSESSION]: RECURSIVE_RELATIONAL_OBSERVATION_CONCURRENT_NATIVE_CUT_WORKSPACE.md#11-routing-residue-and-the-row-only-handoff

## 追加锚（本行以下为增补区）

## 21. Exact post-reset label attainment at complete-call cuts

**Definition 21.1 (finite histories and the label contract).** Fix the
finite nonempty actually attained history set
$$
\mathcal H=\{(J,\sigma):J\in\mathcal J,\ \sigma\in\Sigma_J\},
\qquad d_J=|\Sigma_J|\ge1,\qquad D=\max_{J\in\mathcal J}d_J .
$$
The finite order lists $\Sigma_J$ are supplied data of the experiment.
Keep Definition 19.1's fixed public parameters, program, bindings and
common reset label. A history $h=(J,\sigma)$ has exactly $r$
distinct ORIGINAL-row writes before reset, and its reset source is
$E_y(Q_h)$, where $Q_h\in F_J=\{Q\subseteq U_J:|Q|=r\}$. At every
standardized completed-inner-call cut, the supplementary persistent
component is one label from a finite alphabet; traversal references,
temporary lookup, decoded history, codebook access, output material,
inner protocol phases and all backing are charged in their existing
coordinates and are not counted as this label. The final recall cut is
after the last required original call and before the declared literal
recall/return tail.

The label contract permits free re-encoding of the admissible starts. It
does not preserve the particular SDR or pairing chosen by an individual
policy. The label is the only state that survives a completed-call cut
besides the current source and the fixed public data. In particular, a
policy that is allowed to retain a newly acquired copy of $h$ after
reset is a different, unrestricted contract.

**Proposition 21.2 (what LAB19 already settles).** An admissible
history SDR exists exactly when
$$
\left|\bigcup_{J\in\mathcal S}F_J\right|
   \ge \sum_{J\in\mathcal S}d_J
\qquad(\mathcal S\subseteq\mathcal J).
\tag{LAGL.1}
$$
If two histories use the same initial $Q$, their permitted initial inputs
are identical, whether the supports differ or the orders differ. The
current-source factorization then forces the same legal continuation; the
former cannot exhaust two distinct menus and the latter cannot return two
different old words. Thus no later newly generated memory repairs an
initial collision. Conversely an SDR gives the post-reset transcript
selector of Corollary 19.2. An unrestricted T may traverse that source,
newly reacquire h, and retain it, giving the valid finite upper bound
$|\mathcal H|$; reset does not forbid this new acquisition.

Proof. This is precisely the weighted-history Hall criterion and its
collision argument in Corollary 19.2, including its distinction between
different supports and equal supports with different orders. The
$|\mathcal H|$-label policy is the finite lookup table from the distinct
reset sources to their histories, followed by actual traversal and
retention after reset. It makes no claim that the old pre-reset copy
survives. $\square$

**Theorem 21.3 (exact supplementary alphabet for the geometry-label
contract).** Assume (LAGL.1). Among geometry-controlled continuations
whose only persistent post-reset supplement is the label of
Definition 21.1, the minimum alphabet size at the standardized
complete-call and final recall cuts is exactly
$$
D=\max_{J\in\mathcal J}d_J .
\tag{LAGL.2}
$$
If (LAGL.1) fails, no such continuation exists. The value in (LAGL.2)
is conditional on free re-encoding and does not minimize an
unrestricted T that retains arbitrary newly acquired history.

Proof. Fix $J$. Every successful completion reaches the same terminal
source $E_y(U_J)$, independently of the order $\sigma\in\Sigma_J$.
At the final recall cut the fixed public data and this geometry are
therefore equal for all $d_J$ orders. The label must distinguish those
orders, so every alphabet has at least $d_J$ values; taking the maximum
gives the lower bound $D$. This is the source-specific terminal
instance of the static max-fibre principle in Transport Memory
Completion §16.1, whose finite equality-fibre supplier is
DefectGraphMinimumColoring.minimum_repair_labels_eq_chromatic_eq_fiber_diversity.
That supplier is reused only for the lower-bound pattern; no new generic
max-fibre theorem is asserted here.

It remains to attain the bound causally. Choose any history SDR
$Q_{J,\sigma}$ supplied by Proposition 21.2 and partition it by the
fixed local order rank $i$: layer $i$ contains the starts
$Q_{J,\sigma_i}$ for supports with $d_J\ge i$, together with the
terminals $U_J$ of those supports. The starts in a layer are distinct
rank-$r$ subsets. The terminals are distinct antichain menus by
Theorem 18.2. Pair each start with the terminal bearing the same support.
The paired endpoint sets form disjoint chains (singletons are allowed):
if a start $Q_{J,\sigma_i}$ equalled a terminal $U_K$, then
$U_K\subseteq U_J$, so terminal antichainness gives $K=J$, and SDR
injectivity excludes every other equality.

Apply Bastide--Groenland--Jacob--Johnston, arXiv:2207.07391v2,
Theorem 2, to this layer. Here $n=|\Lambda(y)|$, $m$ is the number
of histories in the layer, and the endpoint family is exactly the
distinct starts and terminals just described. Its disjoint skipless
cover can be trimmed to the intervals between rank-$r$ starts and
their terminals. Each trimmed interval is a saturated path in
$2^{\Lambda(y)}$. Re-pair only within this layer: assign the history
with support $J$ to the start of the path whose terminal is $U_J$.
This is the permitted free re-encoding. The global set of starts remains
distinct because the layers partition the original SDR, and every
intermediate set remains a subset of its own $U_J$. No path is paired
across layers, and the target order lists $\Sigma_J$ are unchanged.

Use labels $1,\ldots,D$, with common default $1$ at the reset cut.
At rank $r$, actual traversal of the current source recovers the
actual $R=Q_{J,\sigma_i}$, identifies its global start and its layer
$i$, and selects the first native edge of that layer's path. After
that edge has completed its original guard, reservation, source edit,
ancestral-tape and arithmetic maintenance, literal reply, End/ACK and
real INNER return, commit label $i$. The first selection uses the
current $R$ and needs no stored initialization flag. After any call
the rank is greater than $r$, so every later choice uses the retained
$i$ at one common selection program counter. A temporary table lookup
or decoded history is current-input-derived and is erased at the
standardized cut.

The invariant is: the current recovered set $R$ lies on the true
history's path in layer $i$, and $(R,i)$ uniquely determines the next
untouched member of $U_J$, Stop, or the final $\sigma_i$. Each edge
adds one original member of $U_J$; it never targets a newborn or
decorative row. Before every edge the supervisor traverses the bound
source, acquires the CURRENT target reference and current rights, and
then discharges the original guard/reserve/source edit/ancestral tape and
arithmetic hook, literal reply, End, acknowledgement and real INNER
return. Thus the path is a legal native continuation, rather than a
mathematical address list. After $|U_J|-r$ calls the geometry identifies
$J$, the label identifies $\sigma_i$, and the policy emits the word
only at the declared final recall cut before the lawful tail. No old
tape, refusal, name, timing, capacity or output archive is used.

The construction uses only finite search over the actually attained
finite carrier and the existing Hall and disjoint-path suppliers. It
produces a backed finite table for this effective input; it is neither
free nor an efficient procedure and is not a uniform finite ROM for
unbounded inputs. Source-derived dynamics are the current LAB parser,
original guards, references, edits, replies and returns. Label-derived
content is only the layer index $i$, together with the finite path
table used to choose among already legal original rows. The causal
first-edge commit and the $(R,i)$ invariant are the native addition
beyond the static max-fibre lower bound and the stopped-prefix
feasibility theorem. $\square$

**Corollary 21.4 (edge cases).** If $r=0$, Hall forces
$|\mathcal J|=1$ and $D=1$; the common start is $\varnothing$, so
the default label is already correct. If $U_J=\varnothing$, then
$F_J=\{\varnothing\}$, and Hall forces $d_J=1$; this is the singleton
no-call path in layer $1$. If $D=1$, one label suffices and
Theorem 21.3 reduces to the geometry-selector equivalence of
Theorem 18.3. These statements include the case of an empty menu and
the overlapping $r=0$ and singleton cases without a hidden
initialization phase.

**Corollary 21.5 (the delivered $m5k2r3$ attainment).** Reuse exactly
the twenty-start, ten-terminal table already displayed in Corollary
19.2 for $(m,k,r)=(5,2,3)$, preserving its coordinates and entries.
Its first column consists of the ten distinct $z$-free triples and
its second column of the ten distinct triples containing $z=L^5$.
Index the two supplied orders on each $J$ so that the first column is
layer $1$ and the second layer $2$. Both layers use the common
default label $1$ at rank $3$; the single remaining original call
commits the observed layer, leaving label $1$ for a $z$-free reset
triple and label $2$ for a $z$-containing reset triple. At the
terminal all ten supports have the same two-order fibre, so one label is
impossible. Theorem 21.3 gives the matching two-label construction.
Hence the exact alphabet is $2$, with no alternative table introduced.

**Proposition 21.6 (conditional realization and transport boundary).**
The preceding construction can be installed only under the current
accepted LAB20 owner-installed session: finite public-shaped backing,
authority separation, the session lock, authenticated current-reference
acquisition, sufficient material and full Ready-to-Ready/INNER return
conditions. Under those premises, transport the same source and label
through AA17's syntax/material support, terminal-boundary and labelled
causal-membership maps, and use the existing unary marker and literal
source identity. The maps preserve the current $E_y(R)\to
E_y(R\cup\{p\})$ edge and the final $(U_J,\sigma_i)$ readout.

Proof. This is the scoped source-response and completed-call construction
of Theorem 20.4, with its paid backing and authority premises retained.
The current source is traversed afresh at each decision, the target
reference is authenticated against the current tag, and all original
maintenance and complete replies occur before the label commit. AA17's
already supplied maps preserve the oriented material support, its
terminal antichain and the causal membership order, including beta's
unary marker; carrying the same finite label adds no new source edge.
This establishes a representation correspondence for the admitted
session. It does not install a resettable legacy Busy controller, prove
a deployed device, recover full controller chronology, assert a
thermodynamic deletion, or complete a universal spacetime construction.
No fresh Lean application is claimed by reading the existing code. $\square$

## 22. Sources, overlap and verification scope

The weighted Hall and stopped-prefix results are reused from LAB19,
Theorems 18.2--18.3 and Corollary 19.2; the terminal static max-fibre
pattern is attributed to Transport Memory Completion §16.1 and its named
DefectGraphMinimumColoring supplier. The disjoint saturated path step is
the primary Bastide--Groenland--Jacob--Johnston theorem cited above and is
literature-attested at that scope. LAB20 supplies the conditional paid
installation and complete-return interface. Boundary Dynamics 106 and Joint Moment Fibers 65.5 remain
separate suppliers for their own interfaces. This appendix adds the
causal acquisition of the layer label, the rank-derived path generation,
and the exact $D$-label attainment; it does not add a matching, WOM,
colouring, or Lean theorem.

All finite-search, backing, authority, current-reference, lawful-edge,
full-return and free-re-encoding conditions are part of the statements
above. No total or peak-memory bound, runtime bound, universal finite
ROM, fixed encoder/pairing claim, deployed-device claim, full chronology
recovery, thermodynamic claim, or universal spacetime completion is
made. The long-term RRO objective remains open beyond this finite
appendix.

## 追加锚（本行以下为增补区）

## 23. Fixed-encoder cut labels on the full native beta comb

**Definition 23.1 (local cut-label contract).** Fix a finite nonempty
actually attained history set
$$
\mathcal H=\{(J,\sigma):J\in\mathcal J,\ \sigma\in\Sigma_J\}.
$$
The public effective data include the current $y$, the antichain menus
$U_J$, the fixed native rank-$r$ codes
$$
Q_h\subseteq U_{J(h)},\qquad |Q_h|=r,
$$
and the common default label $0$. The codes are distinct and are fixed
before the run; they are not a history-dependent coloring. At every
declared completed-call cut and at the final recall cut, the accessible
state is the current geometry $R$ together with one value in one fixed
nonempty finite label alphabet containing $0$, shared across all cuts. All scratch, decoded identity, last reply, parser,
output, cursor, phase, control, alias, and other history-dependent
supplements are cleared at the cut. Fixed public tables, paid transient
calculation and acquisition, source material, authentic references, and
the protocol phases retain their separate costs.

For each $h$, let $\mathfrak P_h$ be the finite set of saturated legal
paths
$$
\gamma_h=(R_{h,0},\ldots,R_{h,n_h}),\qquad
R_{h,0}=Q_h,\quad R_{h,n_h}=U_{J(h)},\quad
R_{h,i+1}=R_{h,i}\cup\{p_{h,i}\},
$$
where every $p_{h,i}$ is an untouched original row of $U_{J(h)}$.
Singleton paths are allowed. For a choice
${\boldsymbol\gamma}=(\gamma_h)_{h\in\mathcal H}$ define its local
congestion by
$$
\operatorname{cong}({\boldsymbol\gamma})
 =\max_R\bigl|\{h:R\in\gamma_h\}\bigr|,
$$
where the maximum includes initial and terminal vertices. The fixed-encoder
capacity is
$$
M_{\rm fixed}
 :=\min_{{\boldsymbol\gamma}\in\prod_h\mathfrak P_h}
      \operatorname{cong}({\boldsymbol\gamma}).
\tag{LAGF.1}
$$

**Theorem 23.2 (exact prescribed-path capacity).** Under the local
cut-label contract, the least possible fixed label alphabet is exactly
the number in (LAGF.1). This statement permits $|U_J|=r$; it does not add
the condition $|U_J|>r$.

Proof. Fix a prescribed family of paths. At a cut with geometry $R$, let
$\mathcal H_R=\{h:R\in\gamma_h\}$. If two histories in $\mathcal H_R$
had the same label, deterministic permitted-state factorization would
give the same next call, next geometry, and next label. Their prescribed
tails would then coincide. Distinct supports cannot have the same
terminal menu because the $U_J$ form an antichain. Equal supports with
different $\sigma$ cannot have the same final recall. Hence the labels
at $R$ are injective on $\mathcal H_R$, giving the lower bound
$|\Lambda|\ge\operatorname{cong}({\boldsymbol\gamma})$.

In particular, an initial collision $Q_h=Q_{h'}$ would put two histories
at the same current source with the common default label. The first
permitted transition is then identical even if unbounded newly generated
memory is allowed. Different menus cannot both be completed from that
state, and different final words cannot both be recalled, so later memory
cannot repair the collision.

For the converse, fix a path family of congestion $M$ and use the one
alphabet
$$
\Lambda_M=\{0,\ldots,M-1\}
$$
at every cut, including initialization and recall. At each reached vertex
$R$, enumerate $\mathcal H_R$ in the fixed public history order and define
an injection
$$
\lambda_R:\mathcal H_R\hookrightarrow\Lambda_M,\qquad
\lambda_R(h_i)=i-1\quad(1\le i\le|\mathcal H_R|).
$$
All initial vertices have rank $r$, all later vertices have larger rank,
and the initial codes are distinct. Thus $\mathcal H_{Q_h}=\{h\}$ and
$\lambda_{Q_h}(h)=0$, literally the same default value already in
$\Lambda_M$. No additional value is identified with or adjoined to this
alphabet.

The fixed finite table has input $(R,j)$ alone. For an occupied input
$(R,\lambda_R(h))$ at a nonterminal vertex of $\gamma_h$, it returns the
next original row $p$ and the value $\lambda_{R\cup\{p\}}(h)\in\Lambda_M$;
at the terminal it returns Stop and $\sigma_h$. The injection makes this
a single-valued table even at a shared middle or terminal. A current
traversal obtains $R$, and the decoding and lookup are transient; only
the displayed value in $\Lambda_M$ crosses the next counted cut. The
current rank $|R|$ and this table determine the action without a retained
initialization marker, phase or extra symbol. At a vertex of maximal
occupancy all $M$ values are used, so this is exactly $M$ values globally,
including $0$. Taking the minimum proves (LAGF.1). This is an effective
finite search on the actually attained histories and menus. It makes no
efficient-table or uniform-global-ROM claim. If $M=1$, every label at
every cut is literally $0$, including along a nontrivial path. A singleton
path starts and stops at $(Q_h,0)$ with no call or extra state. The cases
$r=0$, terminal antichainness and path intersections are included: the
common empty initial code permits only one history under injectivity,
and intersections are counted at their shared geometry. $\square$

**Definition 23.3 (the complete paired code on the native comb).** Let
$m=2\ell$, $k=\ell-1$, and let
$$
y_0=\beta,\qquad y_{j+1}=\langle y_j,\beta\rangle.
$$
Use candidate indices $I=\{0,\ldots,2\ell-1\}$ with
$p_i=L^iR$ and the uncovered candidate $z=L^{2\ell}$. For every
$J\in\binom I{\ell-1}$ put
$$
U_J=\{z\}\cup(I\setminus J),\qquad
N=\binom{2\ell}{\ell-1}.
\tag{LAGF.2}
$$
Partition $I$ into fixed disjoint pairs
$P_1,\ldots,P_\ell$. A rank-$\ell$ code in the accepted encoder always
contains $z$. Classify the pair indices as full $A$, singleton $S$ with
one selected value in each pair, and empty $C$. Its size equation is
$$
|C|=|A|+1.
\tag{LAGF.3}
$$
For each fixed singleton data $(S,\text{selected values})$, put
$a=|A|$ and let $W$ be the remaining $2a+1$ pair indices. Choose once
and for all an effective containment perfect matching
$$
\mu_W:\binom W a\longrightarrow\binom W{a+1},
\qquad A\subset\mu_W(A).
\tag{LAGF.4}
$$
Such a matching exists because the inclusion graph is $(a+1)$-regular
on both sides; a finite lexicographic search is an effective choice. Write
$\mu_W(A)=A\cup\{c(A)\}$. Define
$$
Q(A)=\{z\}\cup\bigcup_{i\in A}P_i
       \cup\{\text{the selected value in }P_i:i\in S\},
$$
and assign to it the terminal
$$
U(A)=Q(A)\cup P_{c(A)},\qquad
J(A)=I\setminus(U(A)\setminus\{z\}).
\tag{LAGF.5}
$$
The sole old order $\sigma_{J(A)}$ is the increasing order of the
typed promotions at the members of $J(A)$.

**Theorem 23.4 (full-family bijection and free cost).** The construction
of Definition 23.3 assigns all $N$ accepted rank-$\ell$ starts and all
$N$ terminal menus exactly once. It has terminal multiplicity
$D=1$. Consequently the existing free-re-encoding theorem gives free
capacity one in this family, while the fixed encoder retains the paired
codes and may not re-pair their endpoints.

Proof. Every rank-$\ell$ subset containing $z$ has a unique triple
$(A,S,C)$ with its selected singleton values and satisfying (LAGF.3), so
(LAGF.4) assigns it exactly one $c(A)$ and one terminal. Conversely, let
$T=U_J\setminus\{z\}$ be any terminal candidate set, so $|T|=\ell+1$.
Write $B,S,C_T$ for its full, singleton and empty pair-index sets, retaining
the selected value at every singleton. Their two size equations are
$$
|B|+|S|+|C_T|=\ell,\qquad 2|B|+|S|=\ell+1.
$$
Consequently, for $a=|C_T|=|B|-1\ge0$,
$$
|B|=a+1,\qquad |S|=\ell-2a-1,\qquad |C_T|=a,
\qquad 0\le a\le\left\lfloor\frac{\ell-1}{2}\right\rfloor.
$$
In particular $W=B\cup C_T$ has size $2a+1$ and is precisely the
complement of this singleton data's pair-index set. Apply the already
chosen matching (LAGF.4) for that same singleton data: since
$B\in\binom W{a+1}$, its unique inverse is
$A=\mu_W^{-1}(B)\in\binom W a$. Containment gives $A\subset B$, so
$B\setminus A=\{c(A)\}$. The recovered code has full set $A$, the
unchanged singleton data, and empty set $W\setminus A$ of size $a+1$;
its candidate count is $2a+(\ell-2a-1)=\ell-1$. Removing the full pair
$P_{c(A)}$ from $U_J$ therefore gives exactly this accepted rank-$\ell$
code, and (LAGF.5) sends it back to $U_J$. Conversely, starting from a
code and applying this inverse returns the same $A$ by the matching's
injectivity. This proves both inverse identities for every constituent
matching, without discarding any start, terminal or support. There are
$\binom{2\ell}{\ell-1}=N$ starts and
$\binom{2\ell}{\ell+1}=N$ terminals, each used exactly once. The increasing
order is unique, so $D=1$. The terminal and free costs are therefore one
by the already established terminal/free result; this paragraph does not
alter that result. $\square$

**Theorem 23.5 (sharp fixed-encoder value).** For every $\ell\ge1$, in
the complete paired family of Definition 23.3,
$$
M_{\rm fixed}=\left\lceil\frac\ell2\right\rceil.
\tag{LAGF.6}
$$
This holds for every constituent finite matching chosen in (LAGF.4).

Proof. A code $Q(A)$ and its terminal $U(A)$ differ by the two members of
the single pair $P_{c(A)}$. Its prescribed path has exactly two possible
middle geometries, according to which member of that pair is written
first. Form a simple graph $G$ whose vertices are all such middle
geometries and whose edge for a history joins its two possible middles.
At a middle $R$, an incident edge is determined by a singleton pair
$P_i$ of $R$: deleting its displayed member recovers the preceding code,
and the matching then determines the unique history. Hence no pair gives
parallel edges and $\deg_G(R)$ is at most the number of singleton pairs,
therefore at most $\ell$.

There is a forced full subgraph. Restrict to middles with no full or
empty pair, so every pair is singleton. These $2^\ell$ vertices are the
vertices of the $\ell$-cube. For each vertex and each coordinate $i$, the
code obtained by deleting its displayed member in $P_i$ has $a=0$ and the
one-pair matching in (LAGF.4) forces $c=i$. Its history edge is exactly
the cube edge flipping coordinate $i$. Thus every constituent matching
contains the full cube, with $\ell2^{\ell-1}$ forced history edges.

Choosing one middle for each history is orienting its edge toward the
chosen middle. On the forced cube the sum of occupancies is
$\ell2^{\ell-1}$, so some vertex has occupancy at least
$\lceil\ell/2\rceil$. This proves the lower bound for every permissible
choice of the two calls.

For the upper bound use the balanced-orientation lemma: every finite
simple graph of maximum degree at most $\ell$ has an orientation with
indegree at most $\lceil\ell/2\rceil$. To see this, in each connected
component add a dummy vertex adjacent to every odd-degree vertex. All
degrees are then even, so an Euler tour, oriented along its traversal,
gives equal in- and out-degree. Deleting the dummy edges leaves at every
original vertex the two degrees differing by at most one. Orient each
history edge toward its selected middle. The resulting label occupancy
is its indegree and is at most $\lceil\ell/2\rceil$. The initial codes
are all distinct and the terminal menus are all distinct by
Theorem 23.4, so initial and final occupancies are one. The general
formula (LAGF.1) now gives (LAGF.6). $\square$

**Proposition 23.6 (native realization and transport boundary).** The
full family above is an actually attained LAB family under the same
conditional owner-installed session and paid access premises as
Definitions 18.1 and 20.1--20.3. Starting from the known alpha root,
promote the root, split the successive left-spine betas at
$L^0,L^1,\ldots,L^{2\ell-1}$, and promote the newly created right alpha
at $p_i$ exactly when $i\notin J$. This prepares the actual $x_J$.
Acquire and seal its original frontier, then perform the promotions at
the members of $J$ in increasing order, with complete returns; this
attains the common $y_{2\ell}$ and the known order $\sigma_J$.

At that source, each prescribed code write is a split at a distinct
original beta row. The two remaining writes are the two members of the
one pair $P_{c(A)}$, in the selected order. Traversal obtains each
current operand and authentic reference before the call. No newborn row,
decoration, refusal, cohort bit, old cursor, or hidden output is used.
After reset, the current geometry and the one retained label are
reacquired at each cut; the label is changed only by the local transition
table of Theorem 23.2. Every call still performs the original guard,
reservation, source edit, all ancestral-tape and arithmetic updates,
literal reply, End/ACK, full INNER return, and lawful tail.

The proof is conditional on LAB20's owner-installed session access,
authenticated current-reference acquisition, sufficient backing, and
Ready-to-Ready/INNER return premises. It does not turn an arbitrary legacy
Busy state into a reset command, and public descriptions provide neither
references nor permissions. AA17's syntax, material-support,
terminal-boundary, and labelled causal-membership maps transport the same
current geometry and label; they do not recover the erased chronology.
No full-history reconstruction, total or peak resource optimum,
thermodynamic erasure, deployed-device claim, or universal spacetime
completion follows. $\square$

**Corollary 23.7 (comparison and checks).** The fixed alphabet has
supplementary fixed-width cost
$$
\left\lceil\log_2\left\lceil\frac\ell2\right\rceil\right\rceil
$$
bits. The terminal multiplicity and free-re-encoding cost are both one;
the latter is the existing Theorem 18.3/21 result in its stated domain.
Whole-history memory newly decoded after reset is valid, while retaining
the pre-reset transcript would violate Definition 23.1. For $\ell=1,2$
the formula gives one label. For $\ell=3$, there are
$$
N=\binom62=15,\qquad 3\cdot2^2=12
$$
forced cube edges and $2^3=8$ all-single middle geometries, giving exact
fixed capacity $2$ versus free cost $1$. This is the first strict example
inside this family, not a claim of a globally smallest example. The
long-term space--time--boundary--memory objective remains open.

The matching and path suppliers are the finite Hall theorem and the
prescribed-pair warning of Bastide--Groenland--Jacob--Johnston,
arXiv:2207.07391v2, together with directed-hypercube routing of
Chakrabarty--Seshadhri, arXiv:2409.02206v2. The edge/vertex distinction
and prescribed-pair boundary are also treated by
Briet--Chakraborty--Garcia-Soriano--Matsliah, *Monotonicity Testing and Shortest-Path Routing on the Cube*, DOI 10.1007/s00493-012-2765-1. Balanced discrepancy and
pseudoarboricity supply the mature orientation language (Ghaffari et al.,
arXiv:1706.04746v2; Blumenstock--Fischer, arXiv:1811.06803v4), while
Rivest--Shamir (1982) supplies only the monotone-write/rank-phase context.
These sources are suppliers for standard combinatorics; the fixed native
intermediate-capacity synthesis and its LAB realization are repo-derived.


## 追加锚（本行以下为增补区）


## 24. Uniform minimum-gap routing with authentic source scans

The encoder in this appendix is one canonical member of Definition 23.3's
admitted matching family, fixed before any run. All supports and their
increasing old promotion orders are retained. The construction supplies a
uniform rule in place of a finite matching/routing table; it neither
changes an arbitrarily prescribed constituent matching nor re-pairs
endpoints during a run. The exact fixed-encoder capacity remains the
quantity established in Theorem 23.5.

**Definition 24.1 (coordinates, phases and counted state).** For each
integer $\ell\ge1$ use candidate indices $I=\{0,\ldots,2\ell-1\}$,
original rows $p_i=L^iR$, and $z=L^{2\ell}$ of the same common
$y=y_{2\ell}$ as Definition 23.3. Fix ordered candidate pairs
$P_j=\{2j,2j+1\}$, $0\le j<\ell$; the two values in a pair are
called $0$ and $1$ in this order. Candidate sets below abbreviate these
original logical rows, never physical reference names. For every
$J\subset I$ of size $\ell-1$ put
$$
u=I\setminus J,\qquad |u|=\ell+1,\qquad
U_J=\{z\}\cup u,\qquad |U_J|=\ell+2,
$$
and prescribe the one old word
$$
\sigma_J=(P_{p_i}:i\in J\text{ in increasing order}).
\tag{LAGU.1}
$$
Here $P_{p_i}$ denotes the native promotion, whereas $P_j$ denotes a
candidate pair. The matching below gives a unique $q\subset u$ with
$|q|=\ell-1$, and the reset code is $Q_J=\{z\}\cup q$, of TOTAL
rank $\ell$. In particular $z$ has already been split before reset.

At the original reset erase every supplementary old field, including
labels, records, input positions, phase, continuations, source cursors
and aliases, as in LAB20. Only the current $E_y(Q_J)$, the common label
$0$, and the fixed public inputs/bindings/rights remain accessible.
At subsequent standardized complete-call cuts the only additional
persistent content is a label in
$$
\Lambda_\ell=\{0,\ldots,\lceil\ell/2\rceil-1\}.
\tag{LAGU.2}
$$
All cuts use that SAME alphabet, including its literal value $0$.
After normalization there is one common Decision control location.
The non-$z$ ranks $\ell-1,\ell,\ell+1$ identify start, middle and
terminal respectively; their total ranks are $\ell,\ell+1,\ell+2$.
No private phase bit or initialization flag supplies this distinction.

**Lemma 24.2 (the exact prefix matching and its inverse).** Fix the
singleton pair positions and their selected values. Read the remaining
pair positions in increasing order, writing $1$ for a full pair and $0$
for an empty pair. A low word $v$ has length $n=2a+1$, $a$ ones and
$a+1$ zeros. Let
$$
b_i=\#\{0\text{ in }v_1\cdots v_i\}
       -\#\{1\text{ in }v_1\cdots v_i\},\quad
b_0=0,\quad b_n=1.
$$
Let $t$ be the LAST index attaining $\min_{0\le i\le n}b_i$,
including the empty prefix. Flip the $0$ in position $t+1$ to $1$.
This is a containment bijection from the low words to the high words
with $a+1$ ones and $a$ zeros. Its inverse takes the FIRST global-minimum
prefix of a high word and flips its final $1$ to $0$. The chosen full
pair depends on the singleton positions but not their values.

Proof. Write $m=\min b_i$. Since $m\le0$ and $b_n=1$, $t<n$.
The next step must be $+1$, hence $v_{t+1}=0$. With $k=t+1$, the
flipped word has balances
$$
h_i=\begin{cases}b_i,&i<k,\\b_i-2,&i\ge k.\end{cases}
$$
For $i<k$, $h_i\ge m$. For $i\ge k$, the last-minimum property and
integrality give $b_i\ge m+1$, hence $h_i\ge m-1$, with equality
at $k$. Thus the FIRST global minimum of $h$ is at $k$, and $h_n=-1$.

Conversely, let $h_0=0,h_n=-1$ be the high balances, and let $k$ be
their first minimum. Then $k>0$, the step at $k$ is $-1$, and its bit
is $1$. Put $d=h_k$. Every $i<k$ has $h_i\ge d+1$, and every
$i\ge k$ has $h_i\ge d$. Flipping this bit gives low balances
$b_i=h_i$ before $k$ and $b_i=h_i+2$ from $k$ onward. Their minimum
is $d+1$, attained at $k-1$ and never thereafter. Consequently their
LAST minimum is $k-1$, so the forward rule flips exactly this bit back.
Both inverse identities follow, and the flip adds exactly one full pair.
The deleted singleton values occur in neither calculation. This proves
the result in every fixed singleton-position/value class, including
$a=0$, where $0\leftrightarrow1$. $\square$

The tie convention is essential. The low word $010$ has balances
$0,1,0,1$ and maps to $011$. Choosing its first low minimum instead
would give $110$; that variant also sends $100$ to $110$ and is not
this bijection. Parenthesis matching and symmetric chains are mature
suppliers; the elementary argument above fixes the exact convention
used here without relying on an unread historical algorithm.

**Proposition 24.3 (all supports, distinct starts, fixed endpoints).**
Applying Lemma 24.2 in every singleton class defines an admitted
$\mu_W$ in (LAGF.4), with a single uniform rule. For each $u$ in
Definition 24.1, classify its pairs and apply the inverse rule to its
high non-single word. If the flipped full pair is $P_c$, then
$$
q=u\setminus P_c,\qquad Q_J=\{z\}\cup q,\qquad
U_J=Q_J\cup P_c.
\tag{LAGU.3}
$$
All $\binom{2\ell}{\ell-1}$ supports occur, and all reset codes are
distinct. No endpoint can be reassigned by the later routing rule.

Proof. In $u$, if $B,S,C$ are its full, singleton and empty pair
positions, then $2|B|+|S|=\ell+1$ and
$|B|+|S|+|C|=\ell$. Hence $|B|=|C|+1$, so its non-single word is
high. The inverse removes exactly one full pair, giving a candidate set
of size $\ell-1$, contained in $u$, with the same singleton data.
Conversely every such low set is mapped back to one high set by
Lemma 24.2. The two inverse identities, separately on disjoint singleton
classes, give the global bijection. Adding the common $z$ gives the
stated TOTAL ranks. Distinct $u$ give distinct $q$ by injectivity of
the inverse. This specializes, rather than reproves or enlarges,
Theorem 23.4's family. $\square$

**Definition 24.4 (middle graph and its gaps).** At candidate rank
$\ell$, let $w\subset I$ and $R=\{z\}\cup w$. A singleton pair
has a bit $x_j\in\{0,1\}$ specifying its displayed member. Delete
ALL singleton positions and read the balanced non-single word $v$:
full is $1$, empty is $0$, with equally many of each. Write its
integer balances $H_0,\ldots,H_n$, including $H_0=H_n=0$, and
$m=\min H_i$. The insertion gap $g(j)$ of a singleton position $j$
is the number of non-single positions before it. Define
$$
F(w)=\{j:j\text{ is singleton and }H_{g(j)}=m\}.
\tag{LAGU.4}
$$
Order $F(w)$ by pair index. A history edge joins its two possible
middle geometries, obtained by adding respectively the $0$ or $1$
member of its missing pair to its fixed $q$. An orientation of that
edge chooses its head as the middle to be used. This graph is a graph
of ALTERNATIVE middle geometries, not a source transition graph.
Even a directed square below never commands a native cycle: an actual
history executes only $Q_J\to R\to U_J$, adding one original row
on each of its two native calls.

**Theorem 24.5 (minimum-gap incidence and full cube components).** A
singleton coordinate $j$ at $w$ is incident to a history edge if and
only if $j\in F(w)$. Its other endpoint flips only $x_j$; its unique
low intersection is $q=w\setminus\{2j+x_j\}$ and its unique high
union is $u=w\cup\{2j+1-x_j\}$. Each connected component is the
FULL cube on $F(w)$, with all non-single data and all inactive singleton
values fixed. In particular its dimension is $f=|F(w)|\le\ell$;
$f=0$ gives an isolated vertex.

Proof. Fix a singleton $j$ with gap $g$. Removing its displayed
member makes that pair empty, so the low non-single word is obtained
by inserting a $0$ into $v$ at gap $g$. Before this inserted bit its
prefix balances are $H_i$ for $0\le i\le g$; after it they are
$H_i+1$ for $g\le i\le n$. The matching chooses precisely the
inserted bit if and only if the last minimum is immediately before it.
This is equivalent to
$$
H_i\ge H_g\quad(0\le i\le g),\qquad
H_i+1>H_g\quad(g\le i\le n).
\tag{LAGU.5}
$$
Since these are integers, the second set of inequalities is exactly
$H_i\ge H_g$ for $i\ge g$. Thus (LAGU.5) holds if and only if
$H_g=m$. This proves necessity and sufficiency, not only a way to
construct some edges. For the high union, insert a $1$ at the same
gap. Its balances are $H_i$ before and $H_i-1$ after. The inserted
bit ends the FIRST minimum exactly when
$H_i>H_g-1$ before it and $H_i-1\ge H_g-1$ after it. Integrality
again reduces both to $H_i\ge H_g$, giving the same inverse criterion.
The low/high words therefore match each other exactly as claimed.

These inequalities include gaps $0,n$. Consecutive singleton positions
share one gap because all singleton positions have been deleted; every
one of them at a minimum gap is active. Changing any singleton value
changes neither $v$, the gaps nor $F$. Flipping an active value is an
edge by the equivalence, at every assignment of all active values;
flipping an inactive value is never an edge. Along any edge the same
active set persists. Arbitrary sequences of active flips therefore
reach all $2^f$ assignments and no others. Distinct coordinates give
distinct endpoints, and the intersection and union determine the
unique history by Proposition 24.3. This proves the full-component
claim. If $v$ is empty, its only gap has balance $0$ and every one
of the $\ell$ singleton positions is active, giving the full
$\ell$-cube. If no singleton is at a minimum gap, $F$ is empty and
no history uses that vertex. $\square$

**Theorem 24.6 (local optimal orientation and decoder).** Let
$F=(j_0,\ldots,j_{f-1})$. Pair successive active coordinates
$(j_0,j_1),(j_2,j_3),\ldots$. On each such two-coordinate face use
$$
00\longrightarrow01\longrightarrow11\longrightarrow10
   \longrightarrow00.
\tag{LAGU.6}
$$
If $f$ is odd, direct the last coordinate $0\to1$. Equivalently,
the head value for the first coordinate of a pair is its partner's
value, for the second it is its partner's complement, and for an
unpaired last coordinate it is $1$. An edge in coordinate $j_k$
newly commits label $\lfloor k/2\rfloor$ after reaching its head.
At that middle, label $t$ identifies its incoming coordinate:
$$
\begin{array}{c|c}
\text{active coordinates at positions }2t,2t+1&
\text{incoming coordinate}\\ \hline
\text{both exist, equal bits}&j_{2t}\\
\text{both exist, unequal bits}&j_{2t+1}\\
2t=f-1\text{ is the unpaired last position, bit }1&j_{2t}.
\end{array}
\tag{LAGU.7}
$$
The remaining call is the other candidate of that SAME incoming pair,
never $z$. The exact common persistent alphabet has
$M=\lceil\ell/2\rceil$ values, with exact fixed-width content
$\lceil\log_2\lceil\ell/2\rceil\rceil$ bits, including zero bits
for $\ell=1,2$.

Proof. In one directed square, every vertex has exactly one incoming
edge among its two coordinates. Inspecting (LAGU.6) gives the equal/unequal
rule and the two head-value formulas. This remains true independently
of every other coordinate. Each complete coordinate pair contributes
one incoming edge at every vertex; the last unpaired coordinate
contributes either zero or one. Consequently indegree is at most
$\lceil f/2\rceil\le M$, and (LAGU.7) decodes each occupied label
uniquely. Removing that displayed candidate from the middle gives
$q$, and adding its partner gives $u$; Theorem 24.5 makes these the
same prescribed endpoints. All labels are in (LAGU.2).

For the lower bound restrict to the all-single middle cube. Each of
its $\ell2^{\ell-1}$ edges is a forced distinct history: its low set
has just one empty pair and otherwise singleton pairs, so its missing
pair is forced even without choosing a matching convention. Each
history must use one of the edge's two middle vertices. Among $2^\ell$
vertices, some middle therefore receives at least
$\lceil\ell/2\rceil$ histories. Two different histories there cannot
have the same label: equal current source, label, public data and
normalized control force the same future behavior, hence the same
terminal and old word, whereas these histories have distinct terminal
menus. This is also the faithful two-call instance of Theorem 23.2.
Thus at least $M$ labels are necessary. The orientation attains this
bound; initial and terminal geometries are each unique to a history,
so their one default value does not enlarge the alphabet. At some
all-single vertex all $M$ values occur. Fixed-width coding of exactly
$M$ values requires and suffices with $\lceil\log_2 M\rceil$ bits;
$M=1$ is the single literal label $0$ with no content bits. $\square$

**Theorem 24.7 (one table-free complete-cut rule).** One fixed finite
program, given public binary $\ell$ and actual source access in LAB20's
session, handles every support of Definition 24.1 with the prescribed
canonical encoding. Its permitted state at each counted cut is precisely
the current geometry and the label in (LAGU.2), besides fixed public
bindings and data. Its two post-reset calls exhaust the remaining
original menu and permit literal recall of (LAGU.1).

Proof. At common Decision, freshly count candidate memberships in the
actual source. At start rank $\ell-1$, recover the low set $q$ and
compute its matched empty pair $c$ by Lemma 24.2. For computation
only, treat $c$ as singleton of value $0$. This virtual middle is
$q\cup\{2c\}$; its active positions do not depend on that temporary
value. Theorem 24.5 puts $c$ in its active set. Find its zero-based
active rank $k$ and its partner if one exists. Choose the actual
candidate in $P_c$ whose bit is the head value in Theorem 24.6,
and compute the pending label $t=\lfloor k/2\rfloor$. No history
table or retained $J$ is consulted. Reacquire the actual current operand
and execute its original split through the complete inner call.
Only AFTER that call's literal reply, End, ACK and real INNER return,
commit $t$ and normalize all other supplementary fields/cursors.
This is a newly acquired label. The original reset erased the old
label; no exception lets a pre-reset value survive.

At the resulting rank-$\ell$ candidate cut the label is preserved.
There is NO second original Scrub at this middle. Fresh scans recover
$F$ and the two bits addressed by the label; (LAGU.7) identifies the
incoming coordinate $c$. Its missing candidate is still an untouched
original beta row. Select that other candidate, acquire its current
reference/rights, and complete its split through the same full return.
Clear the label to $0$ in the terminal normalization. At candidate
rank $\ell+1$, scanning the complement of $u$ now recovers $J$,
so Stop and emit its increasing literal promotion word (LAGU.1),
followed by the declared full output/return tail. Nothing uses the
label to store the old word at the terminal cut.

The invariant at each middle is that the reached vertex is the head
of the actual history edge and its label is the active coordinate
pair containing that edge. The decoder recovers exactly that edge,
so the next write reaches its unique terminal, not another support's
menu. At start and terminal, the distinct source sets already
identify the history. These facts prove every phase and completion
by induction over the two real calls. An invalid rank/label/shape is
outside this actual image; a decoder rejection is not a hidden
source-membership oracle. During one decision or busy call scratch
may contain source-derived operands and a pending label, but no
such extra field survives its next standardized cut. The same
normalization applies to receiver copies and saved selections. $\square$

**Proposition 24.8 (actual native preparation, encoding and continuation).**
Under LAB20's owner-installed separate-session, authority, backing,
exclusive-source and full-return premises, all alternatives in
Definition 24.1 are actually attained from the allocated alpha root.
Their codes and both remaining splits use the original LAB operations
on that same source, with all original protocol and arithmetic work.

Proof. Promote the root. For $i=0,\ldots,2\ell-1$, split the actual
left-spine beta at $L^i$, and promote its newly born right alpha
at $p_i$ exactly when $i\notin J$. Each preceding split really
creates the next left beta and the right alpha. After these complete
calls, the source $x_J$ has alpha exactly at the right rows in $J$,
beta at the other right rows and at $z$, and the prescribed branch
spine. Perform LAB9's actual frontier acquisition and seal: it lists
these very original rows and their current types, addresses and
bindings. Then perform the $P_{p_i}$ for $i\in J$ in increasing
order, with full inner returns. This attains common $y_{2\ell}$
and the real old word $\sigma_J$. The still-unprocessed original
cohort is exactly $U_J=\{z\}\cup u$; the promotions in $J$ are
not eligible again just because their source tags are now beta.

Compute (LAGU.3) from the acquired support before reset, and split
exactly the original rows in $Q_J=\{z\}\cup q$, for example $z$
first and then $q$ in increasing order. There are $\ell$ such calls.
They lie in $U_J$, are distinct and original, and each has current
tag beta. This realizes precisely $E_y(Q_J)$. The original Scrub
then removes ALL supplementary pre-reset state under Definition 20.3,
including the just-used support, code, reference list, labels and
prefix transcript. Its normal form has label $0$ and common control,
with $z$ already written in the preserved geometry. Theorem 24.7
performs the only remaining calls, on the two candidates of $P_c$,
as actual current beta splits. No newborn child or unary marker is
an original target.

For acquisition, use AA17.3's material arity parser and AA20.1--20.2's
actual parent/left/right fields and root binding. On this exact image,
an original beta is either unsplit beta (material unary) or the exact
split cherry $\langle\beta,\alpha\rangle$ (material binary);
LAB20's table (LAGI.4) reads its membership. The public formula for
$y$ locates expected logical rows for comparison. It supplies neither
a physical reference nor a source oracle: the actual field traversal
binds each current operand, and actual current grants authorize it.
The session submits the real addressed frame and its original guard
still tests the source. Every call reserves material, edits the actual
source, appends every proper-ancestor routing tape, performs the
pre-edit scalar/pair arithmetic hook and pending maintenance, builds
and emits the full literal Growth reply, End and ACK, and reaches
real INNER root return. The session receiver backs and consumes all
traffic. Its final report and lawful outer tail restore returned idle.

This is the supplied successful policy plugged into LAB20, not a new
reset transition for arbitrary legacy Busy. Protected tapes, arithmetic
banks and original legacy receivers retain their semantics and may
contain old distinctions; authority separation excludes their use by
this selector. No deployed runtime certification follows. $\square$

**Theorem 24.9 (uniform selector-content and owned-navigation bounds).**
On the actual image of Proposition 24.8, one decision of Theorem 24.7
uses a constant number of ordered scans, $O(\ell)$ current-source
membership probes, $O(\log(\ell+2))$ transient integer/Boolean CONTENT
bits, and a constant number of authentic reference REGISTERS. Under
the admitted direct-field contract the scans and bounded selected-operand
reacquisition require $O(\ell)$ actual field/navigation operations
per decision. Ordinary binary-counter work is conservatively
$O(\ell\log(\ell+2))$. These coordinates exclude complete-call,
frame/receiver, output and backing costs; reference widths are separate.

Proof. For a scan, start at the authentic root. At original branch
$L^i$, read its actual right field to obtain the row $p_i$, test
its bounded local shape, then follow the actual left field to
$L^{i+1}$. Stop at the public bound $i=2\ell$ and inspect $z$.
Every $L^i$ for $i<2\ell$ was already a branch in $y$; all allowed
later writes occur at its original leaves, so none removes or rewires
this spine. A right-row write changes only its own bounded subtree
from unary beta to the exact cherry. Splitting $z$ similarly leaves
all preceding branches unchanged. AA20.2's reuse of the beta marker
creates real child bindings and preserves these spine branches.
Thus each step needs a bounded number of actual source-field reads
and assignments, including material-arity checks. Logical row
membership is obtained from these readings, never a bit-array oracle.
Two consecutive right rows give one pair's occupancy and singleton
value; their traversal needs only a constant number of reference
registers. No path stack, syntax copy or stored membership array is
needed. Public counters name expected positions, not references.

Here is a constant-pass implementation of the mathematical selection.
A rank scan distinguishes the three Decision cases and verifies the
already-written $z$. At a start, one low-word pass maintains balance,
minimum and the LAST minimum's non-single prefix index; the empty
prefix is initialized explicitly. A further pass locates the next
non-single pair, namely $c$. Treat that pair virtually as singleton
in subsequent start passes. At a middle use the actual singleton
pattern instead. One balanced-word pass computes the global minimum
$m$. A further pass maintains its current prefix balance at every
singleton gap; equality with $m$ enumerates exactly the active set,
without storing $F$. Counting these active positions gives $f$ and,
at a start, $k=\operatorname{rank}_F(c)$. One more pass reads the
needed partner bit, or, at a middle, the bits at active positions
$2t,2t+1$, and determines the coordinate to use. Inactive singletons
contribute no balance step. Consecutive singletons therefore receive
the same correct gap test. Each pass has at most $\ell$ pair tests.
At most a fixed number of passes is used, independent of $\ell,J$
and the cube dimension. There is no matching, cube, routing or
membership table and no retained $F$ or complete word.

All stored integer quantities are indices, ranks, signed balances,
minima, $f,k,c,t$ or loop bounds of magnitude $O(\ell+2)$.
A fixed number of ordinary binary counters and Boolean latches
therefore needs $O(\log(\ell+2))$ content bits in total.
Each elementary increment, comparison, copy or parity/halving step
can be implemented in $O(\log(\ell+2))$ bit work, giving the stated
conservative counter bound across $O(\ell)$ iterations. A fixed
program and a fixed number of loops suffice for every binary input
$\ell$; no table indexed by unbounded parameters is in its code.

After computing the selected row index, reset the source cursor to
the authentic root and reacquire that row by one more forward spine
traversal of length at most $2\ell$. Hold only its authentic current
operand and the constant number of bindings needed for dispatch.
This is a bounded extra scan, so total direct-field/navigation work
remains $O(\ell)$. Reference registers carry actual opaque references;
their physical widths, assignment tariff, representation backing and
rights are charged separately, not compressed into the binary-counter
bound. At every counted cut, restore the source cursor to root,
clear other mutable reference registers to null, neutralize counters,
receiver scratch and aliases, and reach the one common Decision
location while preserving exactly the allowed label. This is LAB20's
paid private normalization restricted to the new scratch; it does
not clear the newly committed label at the middle.

If instead each candidate is reacquired independently from the root,
$\sum_{i<2\ell}(i+1)=\ell(2\ell+1)$ gives the simpler
$O(\ell^2)$ navigation bound. Persistent owned spine traversal
already supplies the stronger linear upper bound under the stated
field primitives. Neither bound proves optimal navigation, bounds
reference bit work, nor bounds the original complete-call workload:
address frames, ancestor maintenance, reply construction/consumption
and real return still take their separately charged operations.
$\square$

**Proposition 24.10 (material and output coordinates remain substantial).**
The selector-content bound is not a bound on total or peak memory,
total time, energy, acquisition or physical installation capacity.
In the exact AA20 literal-tape supplier, already at the common $y$
the preparation and old promotions have created exactly $4\ell^2$
routing tape cells. The addressed final old word has
$\Theta(\ell^2)$ literal payload uniformly over the supports as
$\ell$ grows.

Proof. AA22.1 counts routing cells by the actual sum of logical event
depths, including every successful promotion and split. In the present
preparation and old word these events are the root promotion, the
$2\ell$ left-spine splits and exactly one right-row promotion at
EVERY candidate, whether before or after frontier acquisition. Thus
$$
D_y=0+\sum_{i=0}^{2\ell-1}i
         +\sum_{i=0}^{2\ell-1}(i+1)
   =\ell(2\ell-1)+\ell(2\ell+1)=4\ell^2.
\tag{LAGU.8}
$$
The supplier really appends one side-bit cell per proper logical
ancestor; these are actual attached tape cells, not only a depth
statistic. Later code and continuation splits add further cells.
Headers, source vertices, reference-bearing fields and their backing,
arithmetic banks and maintenance, material reservation, parser and
receiver/output/address frames, root bindings and granted authority
all retain their own material and work costs. A constant number of
reference registers is not a constant number of reference bits.

For a recalled $P_{p_i}$, the address depth is $i+1$ and AA20.2's
literal $A(p_i)=1^{i+1}0p_i$ alone has $2(i+1)+1$ bits, besides
kind/tag/framing. If $|J|=\ell-1$, its sum of depths is at least
$1+\cdots+(\ell-1)=\ell(\ell-1)/2$ and at most
$2\ell(\ell-1)$. This proves the claimed asymptotic lower and upper
bounds for the literal old word; at $\ell=1$ it is empty. A streaming
word generator can use counters, but its actual printed bits and the
bound complete-call receiver and address/reply backing are still
material/work, and do not fit into the logarithmic selector-content
coordinate. The receiver is not permitted to retain an uncounted
copy of the target across a standardized cut.

Initial root/frontier acquisition, computation and writing of the
encoding, all complete calls and original scrub are paid separately.
For each finite $\ell$ the LAB20 installation must supply sufficient
finite common backing and current authority, including its frame,
receiver, output and normalization arenas. One uniform finite program
with growing finite supplied material is not one fixed-capacity
physical installation for all $\ell$. The bounds above establish no
total/peak-memory optimum, total-time or energy estimate, universal
physical realization or runtime certification. $\square$

**Proposition 24.11 (same-source transport and exact recovery scope).**
Carry the SAME current source $E_y(R)$ and permitted label through
AA17's syntax, oriented material-support, terminal-boundary and
labelled causal-membership maps, retaining beta's material unary
marker, original row interpretation, literal source identity, root
binding and current rights. On this actual image each recovered view
computes the same decisions, the same native successors and the
same prescribed terminal word $\sigma_J$. This is task-specific
recovery of current continuation and that increasing old word.

Proof. AA17.3's arity parser recovers the source term from its oriented
material support; maximal elements give the terminal boundary and
prefix closure recovers the support. AA17.2 recovers the same term
from its birth-typed labelled causal membership order. LAB20's
source-difference map then recovers exactly the same $R$ against
this $y$; the label is transported unchanged as an additional component.
Consequently the prefix-minimum and local decoding formulas have
identical arguments in each view. For a selected original row $p$,
taking a view after the actual completed call
$E_y(R)\to E_y(R\cup\{p\})$ equals recovering this same source,
performing that very lawful call and taking its view. No independently
chosen compatible source or history is substituted. At the terminal,
complementing $u$ gives the very $J$ whose increasing promotions
were attained in Proposition 24.8.

These are the existing same-source maps with the allowed supplement,
not authority or a reverse source actuator derived from a mathematical
view. The bare source still does not determine arbitrary generation
chronology, controller traffic or protected old records. Recovery of
this selected order follows because the experiment prescribes one
increasing order per support, not because all histories of the source
have become distinguishable. The chosen canonical fixed encoder here,
the arbitrary finite constituent matchings of §23 and the freely
re-encoded endpoint theorem of §21 retain their separate quantifiers.
The long-term space--time--boundary--memory objective remains open
beyond this finite family. $\square$

### 24.12. Suppliers and evidence boundary

[AA17, AA20--22](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md#17-birth-typed-local-growth-and-its-causal-reconstruction)
supply the source semantics, material unary/binary parser, actual
reference/field/authority contract, Ready-only source-response semantics
and located depth accounting. LAB9--11, 15 and 18--20 supply frontier
acquisition, original-cohort eligibility, synchronization and the
conditional separate-session installation. The named repository
[EnabledPathSwapConnectivity.result](../../../D5/S3/ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity.lean)
is a finite-poset enabled-execution supplier, not this source-specific
scan or routing theorem. The
[DefectGraphMinimumColoring.minimum_repair_labels_eq_chromatic_eq_fiber_diversity](../../../D5/S3/ConceptDynamics/Coding/DefectGraphMinimumColoring.lean)
supplier used in §21 concerns static finite task fibers; it is not
used to replace the intermediate-cut proof above. Reading these
sources supplies no new Lean verification.

For mature parenthesis/symmetric-chain methods, Sagan--Savage,
[*Mahonian Pairs*, arXiv:1101.4332v2, §5](https://arxiv.org/html/1101.4332v2),
describes pairing and a change of the rightmost unpaired symbol in
its stated convention. Greene--Kleitman, *Strong versions of Sperner's
theorem*, [DOI 10.1016/0097-3165(76)90079-0](https://doi.org/10.1016/0097-3165(76)90079-0),
is the bibliographic symmetric-chain attribution; its original full
text is not part of the obtained evidence, and no exact historical
algorithm correspondence is asserted here. DOI 10.37236/1755 identifies
Griggs--Killian--Savage (2004), not Greene--Kleitman. The complete
integer-prefix proof in Lemma 24.2 bears the matching claim.

Bastide--Groenland--Jacob--Johnston,
[arXiv:2207.07391v2, Theorem 2](https://arxiv.org/html/2207.07391v2),
covers sets by disjoint skipless chains without preserving chosen
endpoint pairings. Chakrabarty--Seshadhri,
[arXiv:2409.02206v2](https://arxiv.org/html/2409.02206v2), retains the
prescribed-pair caveat for directed-cube paths. Neither supplies the
fixed-pair local selector asserted here. Ghaffari et al.,
[arXiv:1706.04746v2](https://arxiv.org/html/1706.04746v2), treats
degree splitting in a distributed orientation model; its communication
bounds are not native source-navigation or memory bounds.
Rivest--Shamir,
[*How to Reuse a "Write-Once" Memory*](https://people.csail.mit.edu/rivest/pubs/RS82c.pdf),
supplies monotone-write context, not LAB source access, reset authority
or authentic operand acquisition.

The source-specific addition is the canonical minimum-gap full-cube
structure, its optimal local incoming-edge decoder, and their uniform
implementation by charged authentic spine scans with explicit cut
normalization. Matching, symmetric chains, orientations and finite
information lower bounds are mature mathematics. This is repository-derived
synthesis, with no worldwide novelty claim, fresh Lean theorem,
ingestion result or deployed-runtime claim. All installation, actual-image,
full-call, separate-charge and recovery-scope conditions above remain
part of the conclusions.

## 追加锚（本行以下为增补区）
