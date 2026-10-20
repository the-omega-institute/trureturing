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
