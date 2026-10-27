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
