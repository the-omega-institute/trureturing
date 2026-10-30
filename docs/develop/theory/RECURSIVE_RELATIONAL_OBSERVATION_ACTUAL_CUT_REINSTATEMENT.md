# Recursive Relational Observation: Actual Physical Thresholds and Cut Reinstatement

## 1. Retained law, erased cut and the actual service

**Definition 1.1 (the retained data and admissible cuts).** Use the actual
alpha-origin source of [GPO, Definition 27.1][GPO], with persistent physical
links $a<b$, actual lexicographic beta births, and the autonomous binary
class $\mathscr R_d$ of GPO Definition 29.1. Write $X_n$ for its labelled
physical tree after $n$ completed updates, $S_n$ for its physical support,
and $\partial S_n$ for its terminal antichain. Let

$$
 F_0=0,\quad F_1=1,\quad F_{i+2}=F_{i+1}+F_i,\qquad
 B_n=F_{n+1}-1\quad(n\ge2).
 \tag{ACR.1}
$$

Retain the actually acquired first $m=2d$ bits $P=z_1\cdots z_m$ and
its authentic complete behavioral descriptor

$$
 L=(r,c_0,\ldots,c_{r-1},s_0,\ldots,s_{r-1}),\qquad
 r\le d,\quad z_j=s_{j-1},\quad
 s_{i+r}=\sum_{v<r}c_vs_{i+v}\text{ in }\mathbb F_2.
 \tag{ACR.2}
$$

The descriptor includes its seed and alignment to the actual first birth;
$r=0$ denotes the zero stream. It is the descriptor previously earned by
GPO §33 and retained in GPO Definition 34.1, rather than a newly assumed
source-independent coefficient row. A nonminimal or singular descriptor
is allowed. Set

$$
 n_0=\begin{cases}
 \min\{u\ge3:F_u-1\ge m\},&m>0,\\
 2,&m=0.
 \end{cases}
 \tag{ACR.3}
$$

The current cut is some unknown finite $n\ge n_0$ on this same source.
The fixed earlier acquisition prefix, its public parameters, and any
fixed earlier acquisition information retained here are identical across
the allowed later cuts; they encode no later age.

**Assumption 1.2 (complete cut loss and surviving paid relations).** All
observer-accessible data bearing the current cut are erased: $n$, $B_n$,
the current tree, support, incidence, boundary and labels, the copied
current generator phase, current receipts and query/control history,
update counters, and lengths, capacities and allocation identities
exposing current age. The entry control and accessible backing contain
only the fixed data of Definition 1.1 and common fresh working resources.
Source allocator information, runtime and physical duration are not
observation channels. The underlying source, its actual root relation
and the authentic retained descriptor remain intact.

A genuine same-root binding, valid paid total presence-Read grant, later
update grant, owned growing readable backing, and finite local progress
are supplied. There is an exclusive completed-cut stationary interval
through every local calculation, recovery Read, retained write and final
handoff. Recovery makes no actual source update. These assumptions are
actual relations and service conditions: calculating a word, a flag or
a descriptor neither creates a handle or permission nor certifies
source authenticity or exclusion. Every submitted word, reply, local
calculation, allocation, retained write and handoff has its own charge.
No clone, reset, private-state access or extra sensor is supplied.

**Definition 1.3 (numerical synchronization and its target).** A numerical
reinstatement returns the exact actual pair $(n,B_n)$ and installs

$$
 M_n=(P,L,n,B_n)
 \tag{ACR.4}
$$

in actually readable owned backing on the surviving binding. It may also
install a behavioral recurrence phase and a callable local evaluator.
The target is the earned mathematical memory of GPO Definition 34.1;
source handles, rights and the exclusive call path remain separate actual
prerequisites. A record is exposed as ready only after its real writes
and handoff finish. No current tree or already available age is an input
to this task.

## 2. First-presence times on physical words

**Definition 2.1 (origin-orbit birth descriptors).** For a physical word
$p$, let $(b_p,\sigma_p)$ be its birth update and initial leaf label in
the full forward orbit from alpha under $L$. For the root use
$(b_\varepsilon,\sigma_\varepsilon)=(0,\alpha)$. Put

$$
 \delta(\alpha)=2,\quad\delta(\beta)=1,\qquad
 \tau_p=b_p+\delta(\sigma_p).
 \tag{ACR.5}
$$

Thus $\tau_p$ is its branch update. The actual chronological index of
that branch's birth event is computed by GPO (GPO.94)–(GPO.97):

$$
 \begin{aligned}
 \lambda_\alpha(e)&=F_e,&\lambda_\beta(e)&=F_{e+1},\\
 R_{\tau_p}(p)&=1+
 \sum_{\substack{qc\preceq p\\c=b}}
 \lambda_{\sigma_{qa}}(\tau_p-1-\tau_q),&
 j_p&=F_{\tau_p}-1+R_{\tau_p}(p).
 \end{aligned}
 \tag{ACR.6}
$$

The sum is over path edges that skip an earlier physical $a$-sibling.
For the root the sum is empty and $j_\varepsilon=1$.
Both children are born at $b_{pa}=b_{pb}=\tau_p$; their initial labels
are $(\beta,\alpha)$ at $(a,b)$ when $z_{j_p}=1$, and
$(\alpha,\beta)$ when $z_{j_p}=0$. Formula (ACR.6) includes earlier
physical sibling cones, so $j_p$ is an actual chronological index,
not the index of a chosen semantic traversal.

**Proposition 2.2 (exact threshold and shortest physical compiler).**
For every nonempty physical word $w$ of length $\ell$, its first
presence time is

$$
 b_w=2+\sum_{i=1}^{\ell-1}\delta(\sigma_{w_{\le i}}),
 \qquad \ell+1\le b_w\le2\ell,
 \qquad \operatorname{Read}_u(w)=\mathbf1_{u\ge b_w}
 \quad(u\ge0).
 \tag{ACR.7}
$$

Given $L$ and any integer $t\ge2$, one uniform effective procedure
constructs an actual physical literal $C_L(t)$ satisfying

$$
 b_{C_L(t)}=t,\qquad
 |C_L(t)|=\left\lceil\frac t2\right\rceil
 =\min\{|w|:b_w=t\}.
 \tag{ACR.8}
$$

For even $t=2k$, the shortest words have $k-1$ successive initial-alpha
proper prefixes, followed by either final physical edge. For odd
$t=2k+1$, they have $k$ nonempty proper prefixes with exactly one
initial-beta prefix and all other initial labels alpha. These describe
all shortest words; the final edge is arbitrary in both cases.
The empty word is present from update zero. No word first appears at
update one.

Proof. Both children of $p$ appear precisely when $p$ branches and
remain present thereafter. The root branches at update two. Induction
on $\ell$ gives (ACR.7), since each nonroot proper prefix adds exactly
its initial label's delay in (ACR.5). Every finite prefix eventually
branches, so all the descriptors in this argument exist in the full
origin orbit, including prefixes not yet born at the unknown current cut.

For $t=2k$, follow the initial-alpha child $k-1$ times and append $a$.
For $t=2k+1$, follow the initial-beta child once, then the initial-alpha
child $k-1$ times, and append $a$. At each proper prefix compute its
actual $j_p$ by (ACR.6), evaluate $z_{j_p}$ from the retained seeded
recurrence, and choose $a$ or $b$ according to its actual child labels.
Thus this is a finite algorithm producing physical letters. It does not
submit a semantic $L/R$ word or ask which port is alpha. GPO Proposition
39.2 proves that its chronological indices agree with the actual source.
The two constructions have the lengths and first times in (ACR.8).

Any word first born at $t$ has $t\le2|w|$, proving the length lower
bound. Equality with the minimum length forces every summand to be two
in the even case and exactly one summand to be one in the odd case.
This also proves the classification. Both children have the same birth
time, so the final edge is unrestricted. Alpha-to-beta at update one
adds no node, proving the remaining assertion. This `repo-derived` physical
correspondence uses GPO §39 rather than GPO §16's global-orientation
threshold. The fixed semantic navigation and birth thresholds of
`NativeRankedNavigationCompiler` (including its private realization
helpers) and `NativeBirthVectorDecoder`, under
`D5/S3/Arith/FibonacciAtomic/Observer/` with their corresponding Blueprint
sources, concern that native semantic orbit. They supply comparisons,
not the actual local-port chronological index (ACR.6). $\square$

**Proposition 2.3 (effective compilation price and its domain).** In a
binary bit-operation model, the compiler of Proposition 2.2 can be
realized with work

$$
 O\bigl((d+1)^3(t+1)^2+(t+1)^3\bigr)
 \tag{ACR.9}
$$

and scratch $O((d+1)^2+(d+1)(t+1)+(t+1)^2)$ bits, including its
physical literal buffer but excluding the retained input. In particular
compilation needs neither $X_n$ nor $n$ nor traversal of all earlier
births. The shortestness in (ACR.8) concerns the specified first-birth
time, equivalently threshold equality on the entire origin-cut orbit.
It is not shortestness of a predicate restricted to $n\ge n_0$.

Proof. Apply GPO Proposition 39.5's forward companion powers and physical
rank recurrence to the prefixes being generated. There are $O(t)$
prefixes and at most one needed law bit per proper prefix. Its index has
$O(t)$ bits, even though its numerical value can be exponential in $t$.
Binary companion powers cost $O(d^3t)$ per bit; rank sums, Fibonacci
integers and prefix storage have the polynomial costs counted there.
Taking the hypothetical cut $t$ in that arithmetic calculation gives
(ACR.9); retaining all prefix descriptors and rank scratch fits the
stated larger quadratic workspace. A zero-order descriptor returns zero
without a matrix operation. All powers are forward, so singular laws
are included.

For example, on the allowed zero-order domain $n\ge2$, the threshold
$t=2$ is constant true, and the empty literal already returns one.
Its length zero is smaller than $|C_L(2)|=1$. This does not change the
first-birth minimum, since the empty literal was present at cut zero.
$\square$

## 3. Paid unbounded recovery and actual writeback

**Definition 3.1 (uniform recovery control).** Compute $n_0$ from the
retained public input. Submit, one at a time, the literal presence queries

$$
 C_L(n_0+1),\ C_L(n_0+2),\ C_L(n_0+4),\ldots,
 C_L(n_0+2^k),
 \tag{ACR.10}
$$

stopping at the first zero reply. Each word is actually materialized and
submitted on the same root; local prediction does not replace the call.
For $k=0$ return $n_0$. For $k\ge1$ the last true threshold and the
first false threshold bracket the candidate interval

$$
 [n_0+2^{k-1},\ n_0+2^k-1].
 \tag{ACR.11}
$$

For each nonsingleton surviving interval $[l,u]$, set
$t=l+\lfloor(u-l+1)/2\rfloor$ and submit $C_L(t)$. On reply one
keep $[t,u]$; on reply zero keep $[l,t-1]$. Repeat until a singleton. Compute $B_n$ by Fibonacci integer
arithmetic. Actually write (ACR.4), its ready control and, if requested,
the behavioral phase to the granted retained backing; expose it only
at the completed stationary handoff.

**Theorem 3.2 (finite zero-update reinstatement with logarithmic Reads).**
Under Definition 1.1 and Assumption 1.2, Definition 3.1 is exact, finite,
uniform and initially source-blind except for its declared earned input.
Put

$$
 h=n-n_0,\qquad k=\lceil\log_2(h+1)\rceil.
 \tag{ACR.12}
$$

Its achieved paid Read and literal coordinates on that same input are

$$
 \begin{aligned}
 U_{\rm source}&=0,&
 Q(n)&=\begin{cases}1,&k=0,\\2k,&k\ge1,\end{cases}\\
 M(n)&=\left\lceil\frac{n_0+2^k}{2}\right\rceil\le n+1,&
 W(n)&=\sum_{i=0}^{k}\left\lceil\frac{n_0+2^i}{2}\right\rceil
       +\sum_{j=1}^{\max(k-1,0)}\left\lceil\frac{t_j}{2}\right\rceil
       \le Q(n)M(n),
 \end{aligned}
 \tag{ACR.13}
$$

where $t_j$ are the actual subsequent bisection thresholds on that run.
Thus $Q=O(1+\log(h+1))$, $M=O(n+1)$ and
$W=O((n+1)(1+\log(h+1)))$.

Including arithmetic, literal construction, computation of $B_n$,
behavioral phase and writeback, one realization has local work

$$
 O\bigl(m+d+(d+1)^3(n+2)^3(1+\log(n+2))\bigr)
 \tag{ACR.14}
$$

and peak owned data backing

$$
 O\bigl(m+(d+1)^2+(d+1)(n+2)+(n+2)^2\bigr)
 \tag{ACR.15}
$$

bits for its data. In addition charge the actual fixed recovery and
receiver code, its installation and entry initialization, the surviving
service apparatus and the actual handoff; none of these supplied
resources encodes the later unknown $n$. Installation includes $O(m+d+n+1)$ binary data writes for the returned
record and phase, its finite ready-control writes, and the actual binding
handoff; their native service and lifetime prices remain additional.
For fixed $d$ this gives polynomial local work and backing. It does not
specify a bound on physical Read duration, installation latency or a
weighted sum of all resources.

Proof. By Proposition 2.2, every reply in (ACR.10) is exactly the
comparison $n\ge n_0+2^i$. A finite $n$ gives a first false comparison.
For $h=0$ it is the first one. Otherwise its index is exactly the
positive $k$ in (ACR.12), with $2^{k-1}\le h<2^k$. The candidate
interval (ACR.11) contains exactly $2^{k-1}$ integers. Ordinary balanced
binary search therefore takes exactly $k-1$ more comparisons, giving
(ACR.13)'s $Q$. This is the doubling-plus-bisection supplier, not a new
unbounded-search theorem: Bentley–Yao, *An Almost Optimal Algorithm for
Unbounded Searching*, [SLAC-PUB-1679][BY], pp. 2–5, defines the monotone
comparison problem, its prefix decision tree, and Algorithm B1. Here the
new correspondence supplies each comparison as a physical literal with
its actual price and actual source alignment.

The largest threshold is $n_0+2^k$, attained in the first phase, and
every later threshold is smaller. Proposition 2.2 gives the exact $M$
and $W$ in (ACR.13). For $h>0$, $2^k\le2h$, and for $h=0$ the
largest threshold is $n_0+1$; both imply $M\le n+1$.

All thresholds are $O(n+1)$, although no such upper bound is given to
the controller beforehand. Sum (ACR.9) over the achieved number of calls.
Simple forward Fibonacci addition computes $F_{n+1}-1$ using $O(n^2)$
bit operations and $O(n+1)$ bits. The binary encoding of $n$ needs only
$O(\log(n+2))$ bits, whereas the explicit binary encoding of $B_n$ has
$\Theta(n)$ bits as $n$ grows. Writing that field is charged accordingly.
If a phase is wanted for $r>0$, apply the forward companion matrix
$C^{B_n}$ to the seed vector. It returns
$(s_{B_n},\ldots,s_{B_n+r-1})$, the behavioral register whose next
output is $z_{B_n+1}$. Binary exponentiation uses $O(d^3(n+1))$
bit operations. No private generator presentation is inverted.
These bounds, including the finite calculation of $n_0$, fit
(ACR.14)–(ACR.15). The retained input takes $O(m+d+1)$ bits and the
optional phase takes $O(d+1)$; copying them and the numerical fields
gives the stated data-write bound. Scratch may be reused between calls.

The instruction scheme is fixed; loops, integers, scratch, operands and
retained fields grow as paid ordinary data. Neither an age-dependent
control table nor an optimal strategy oracle is installed. Finite local
progress and completed Reads give termination. Presence calls and local
work consume no births, and the entire interval through the real writes
and handoff is stationary. Thus the installed $n,B_n$ are the actual
current values at handoff. $\square$

## 4. Exact bounded-window coordinates and traffic bounds

**Definition 4.1 (a complete common-entry window).** Fix one retained
$(P,L,d)$, same actual root and entry resources as in §1. Let public
integers $A,H$ satisfy $n_0\le A\le H$, and allow every cut
$n\in[A,H]$. Put $N=H-A+1$ and
$q=\lceil\log_2N\rceil$. Competitors may perform arbitrary finite
adaptive local work and arbitrary paid physical-word presence queries,
but no source update or extra observation. They must identify $n$
exactly and terminate on every cut of the window. Fixed-entry resources
are the same at all these cuts. Define $Q_*$ and $M_*$ as the minima
of worst-case Read count and peak literal length respectively; set the
peak and traffic of a no-query execution to zero. Define $W_*$ as the
minimum worst-case sum of submitted literal lengths.

**Theorem 4.2 (window Read/peak optima, with a same-run traffic bound).**
For Definition 4.1,

$$
 Q_*=q,\qquad
 M_*=\begin{cases}0,&N=1,\\\lceil H/2\rceil,&N\ge2.\end{cases}
 \tag{ACR.16}
$$

One finite arithmetic controller jointly attains these two worst-case
coordinates. For $N\ge2$, with $c_A=\lceil(A+1)/2\rceil$,

$$
 c_Aq\ \le\ W_*\ \le\ \lceil H/2\rceil q.
 \tag{ACR.17}
$$

In particular, for $H\le C A$ with fixed $C\ge1$ and $N\ge2$,
the attained optimal orders are $Q_*=\Theta(\log N)$,
$M_*=\Theta(H)$ and $W_*=\Theta(A\log N)$.
No exact value of $W_*$ is asserted in (ACR.17).

Proof. For the fixed law, every physical word has exactly the step
response (ACR.7), or is the constant-present empty word. Its replies
have two values. Every deterministic controller terminating on these finitely many
candidates therefore induces a finite binary decision tree after
restriction to their runs. Removing all
constant-reply queries and local computation preserves $N$ distinct
leaves. Some path has at least $q$ informative queries, establishing
the Read lower bound. The constant-query contraction and same-run bill
reuse [CAB, Theorem 6.2 and §§7.1–7.4][CAB], as intermediate arguments.
CAB's four-reply native scaffold and
`NativeStationaryIntervalResources` do not give the two-reply physical
capacity without (ACR.7). Each informative query here has first birth in $[A+1,H]$,
hence length at least $c_A$ by Proposition 2.2. The same path therefore
has traffic at least $c_Aq$; this multiplies costs on one run.

The cuts $H-1,H$ are both allowed when $N\ge2$. A physical presence
query separates them only if its first-birth time is exactly $H$.
Induction on the two adaptive runs forces such a query on their common
prefix before their outputs can differ. Its length is at least
$\lceil H/2\rceil$, proving the peak lower bound. Conversely bisect
the actual candidate interval using thresholds $t\in[A+1,H]$ and
compile each one by Proposition 2.2. A midpoint split leaves at most
$\lceil N/2\rceil$ candidates; iteration uses at most $q$ queries.
All words have length at most $\lceil H/2\rceil$, proving joint
attainment and the traffic upper bound. For $N=1$, return $A$ without
a Read. The order statements follow from these inequalities.

For zero-error randomized controllers terminating almost surely on this
finite window, intersect the finitely many probability-one correctness
and termination events. Any coin tape in that intersection induces the
same deterministic lower-bound problem. The stated worst-case bounds
therefore also hold for worst-case call/traffic budgets with zero error;
no expected-cost optimum is asserted. $\square$

**Proposition 4.3 (entry information and necessary same-input traffic).**
If an apparent window $[A,H]$ includes cuts below $n_0$, its effective
candidate set is $[\max(A,n_0),H]$, if nonempty; (ACR.16)–(ACR.17)
use that interval and its actual cardinality. They give no lower bound
based on excluded cuts.

In Definition 4.1, on every run at an interior age $A<n<H$, any exact
deterministic controller must submit both a first-birth-$n$ literal
and a first-birth-$(n+1)$ literal. Consequently on that very input

$$
 W(n)\ge\lceil n/2\rceil+\lceil(n+1)/2\rceil=n+1,
 \qquad M(n)\ge\lceil(n+1)/2\rceil.
 \tag{ACR.18}
$$

The same conclusion holds on every $n>n_0$ for an exact controller on
the whole unbounded domain $[n_0,\infty)$. At its lower endpoint it
must at least submit a first-birth-$(n_0+1)$ literal.

Proof. The maturity promise excludes precisely the lower cuts specified
in the first assertion; source-independent common entry supplies no
further age information. For (ACR.18), compare the run at $n$ first
with that at $n-1$. Until a different reply they have identical control.
The sole threshold separating these ages is $n$, so their first
difference requires a first-birth-$n$ query on the run at $n$.
Comparison instead with $n+1$ forces a first-birth-$(n+1)$ query on
that same run. These are distinct query occurrences. Proposition 2.2
bounds their separate lengths, giving the sum and maximum. The
unbounded domain has both neighbours of every $n>n_0$, and its endpoint
has the upper neighbour. This is a per-input necessary bill, not a
pointwise simultaneous optimality claim for one universal controller.
$\square$

## 5. Few replies and the physical cost of an overshoot

**Proposition 5.1 (two logarithmic-Read controls on the same actual inputs).**
Fix $d$, retained $P,L$ and $n_0$. Besides Definition 3.1, consider a
control using successive thresholds

$$
 n_0+2^{2^0},\ n_0+2^{2^1},\ n_0+2^{2^2},\ldots
 \tag{ACR.19}
$$

until its first false reply, followed by balanced bisection of the
remaining interval, using $n_0$ as lower bound if the first reply was
false. It is finite and exact and has $O(1+\log(n+2))$ paid Reads.
Nevertheless, on the very same physical sources at ages
$n=n_0+h_j$, $h_j=2^{2^j}$, $j\ge0$, this control has

$$
 M\ge\left\lceil\frac{n_0+h_j^2}{2}\right\rceil,
 \qquad W\ge\left\lceil\frac{n_0+h_j^2}{2}\right\rceil,
 \tag{ACR.20}
$$

whereas Definition 3.1 has $M\le n+1$ and
$W=O((n+1)(1+\log(n+2)))$ on those same inputs. Thus logarithmic
reply count alone permits quadratically larger single operands and a
traffic ratio growing at least as $h_j/\log(h_j+2)$ for fixed $n_0$.

Proof. Threshold correctness makes (ACR.19) an ordinary bracketing
search. If the last true offset is $v\ge2$, its successor offset is
$v^2$. The first false offset $T$ is therefore at most $(h+1)^2$
for $h=n-n_0\ge2$; the smaller cases have fixed finite brackets.
There are $O(1+\log\log(h+2))$ bracketing calls and at most
$O(1+\log(h+2))$ subsequent bisection calls. On $h=h_j$, the offset
$h_j$ replies true and its successor $h_j^2$ replies false. Compiling
that actually submitted latter threshold gives (ACR.20). In contrast,
(ACR.13) gives the stated linear peak and $O(n\log n)$ traffic.
The lower traffic bound for one control and upper traffic bound for the
other are evaluated on identical $L,n$, rather than on unrelated worst
realizations. This derives a physical-word resource separation; neither
bracketing method is claimed as a new search algorithm or as a globally
weighted optimum. $\square$

## 6. Reinstalled views, behavioral phase and continuation

**Theorem 6.1 (reinstatement into the earned same-source consumers).**
At the completed handoff of Theorem 3.2 the actual record (ACR.4) satisfies
GPO Definition 34.1 with its separately surviving binding and grants.
On the original domain $n\ge n_0$, it therefore determines exactly

$$
 S_n,\quad\partial S_n,\quad
 \mathcal T_n^{\rm birth}=
 \bigl(n;(t_j,p_j,z_j)_{1\le j\le B_n}\bigr),\quad X_n,
 \tag{ACR.21}
$$

and the complete finite-request behavior of that same source. The
GPO Theorem 34.2 round trips agree on these data images. Without expanding
the whole tree, GPO Definition 39.3 can answer each supplied physical
word's label, presence and terminal status with the request-local work
of GPO Proposition 39.5. With GPO Theorem 34.3's continued real binding,
rights, completed-call synchronization, progress, retention and backing,
these consumers remain correct through every finite actual serial
continuation, including real paid Reads and completed updates.

Proof. The old retained prefix and complete seeded descriptor are
unchanged. Theorem 3.2 has reinstated precisely the two numerical fields
missing from GPO (GPO.84). The stationary interval includes installation,
so they name the actual handoff cut. All other premises of GPO Definition
34.1 are Assumption 1.2's actual surviving relations, not inferred
consequences of numerical equality. The maturity bound is exactly that
of GPO Theorem 34.2, including its separate zero-order case. Apply that
theorem to obtain (ACR.21) and its commuting round trips.

GPO Theorem 39.4 identifies the physical evaluator on these same $L,n$
with actual readout at every finite word, including absent words. GPO
Theorem 34.3 then advances $n,B_n$ only on real completed updates and
commits new local data before exposing another callable cut. Its invariant
and continuation premises yield the assertion by induction on actual
calls. Reconstructing a behavioral phase as in Theorem 3.2 is sufficient;
it requires no inverse of a singular transition and no identification
of a private register implementation. An expanded tree or full event
trace in (ACR.21) still costs its explicit output and backing.

The projections in (ACR.21) omit arbitrary stationary observer actions:
inserting a stationary Read or local calculation before erasure changes
the observer journal while leaving $L,n,B_n$ and every birth event
unchanged. Thus these inverses do not recover arbitrary lost journals,
all material memory bytes, lost capabilities or physical durations.
$\square$

**Proposition 6.2 (scope under unchanged classical premises).** Fix any
extension of the source description that leaves Definitions 1.1–1.3,
(ACR.5)–(ACR.7) and Assumption 1.2 true with the same paid observations.
Theorems 3.2 and 6.1 remain true for that extension's classical
projection, irrespective of whether its additional data have an inverse.

Proof. Each control choice and reply used in Theorem 3.2 depends only
on the declared retained data and (ACR.7). Its computation and stationary
handoff therefore produce the same numerical record. Theorem 6.1 uses
only that record and the named GPO premises. No step refers to an
additional clock, a Hilbert-space preparation or an inverse for those
additional variables. Hence proving recovery of such further variables
is an independent obligation unless the extension changes a premise
used here. $\square$

## 7. Admissible indistinguishability and the handoff boundary

**Proposition 7.1 (two mature cuts after total erasure require live input).**
For every $d\ge0$ there are two admissible inputs of §1 with identical
retained data and common entry resources but different numerical target
and physical support. No source-blind source-free local calculation
can recover the numerical cut on both, even with unlimited finite work
and growing backing.

Proof. Choose the identically zero member of $\mathscr R_d$. For
$d>0$, execute the actual acquisition of GPO §33 once and retain its
fixed acquired zero prefix and selected authentic seeded zero-law
descriptor. For $d=0$ use its zero-order descriptor. Consider that same
origin orbit at cuts $u$ and $u+1$, with any $u\ge n_0$, after making
the stipulated complete erasure. Choose equal accessible entry control
and backing, and retain the same root binding and valid rights. Both
cuts satisfy the original maturity domain. The fixed earlier acquisition
data are identical. Neither a copied phase nor an allocation/counter
channel survives. The stationary interval is available on each input.

Their targets differ: $u\ne u+1$, and
$B_{u+1}-B_u=F_u>0$. Their physical supports differ as well, since
update $u+1$ splits at least one beta leaf and adds persistent children;
indeed its count increases from $2F_{u+1}-1$ to $2F_{u+2}-1$.
A local program receiving no live reply has identical state transitions
on the two equal entry memories, hence identical output if it terminates.
It cannot output both cuts. For zero-error randomness couple the coin
tape; the two output distributions are identical, while the required
exact outputs differ. Growing local work cannot split this information
fiber. $\square$

**Definition 7.2 (a handoff gap without completed-cut exclusion).** Keep
the same source, retained data and granted operations, but weaken the
stationary interval so it ends after the recovery controller's final
live observation. Before its record is handed off, allow either no
update or one legal completed same-root update by an authorized invoker,
without a delivered update-count observation to that controller. All
its subsequent backing writes and handoff are local. The invoker's
acknowledgement is not delivered as a new sensor to the recovering
controller. All source replacements still follow GPO Definition 27.1.

**Proposition 7.3 (a final observation does not certify a later cut).**
Under Definition 7.2, no finite exact observer can guarantee that the
numerical cut inferred at its final observation is the current cut at
handoff on every allowed execution. Requiring exclusion through
writeback and handoff, or actually acquiring the intervening update
count, removes this particular ambiguity.

Proof. Use the genuine zero-law source and a mature cut $u\ge n_0$
from Proposition 7.1. Take a terminating recovery execution while it is
stationary at $u$. Its live replies are all legitimate. In one allowed
extension to handoff make no source update; in a second, perform one
legal actual update after the last live observation but before handoff.
That update consumes its autonomous birth batch in the prescribed
physical lexicographic order. The two executions have identical retained
input, observed replies, recovering control and all later local writes.
Their actual handoff cuts are $u$ and $u+1$, with different $B$ values
and supports as above. The installed output is the same, so cannot be
correct for both. The same coupling proves the zero-error version.
These are admissible source executions for the expressly weakened gap
service, not counterexamples within Assumption 1.2's stationary interval.
Exclusion forbids the second extension. An actually supplied exact
intervening count instead permits advancing the behavioral law and
numerical fields before a new synchronized handoff, subject to the same
write/continuation premises. $\square$

## 8. The already sufficient complete scan on the same task

**Proposition 8.1 (same-task complete-scan supplier and its expanded bill).**
The complete physical presence scan used in GPO Theorem 23.1 and
Proposition 25.2 is already a finite zero-update numerical reinstatement
supplier under §1. On the actual input $L,n$ it has exact Read and
literal coordinates

$$
 \begin{aligned}
 Q_{\rm scan}&=|S_n|=2F_{n+1}-1,\\
 M_{\rm scan}&=n,\\
 W_{\rm scan}&=\sum_{p\in S_n}(|p|+1),\\
 (\lfloor n/2\rfloor+1)F_{n+1}
 &\le W_{\rm scan}\le n(2F_{n+1}-1).
 \end{aligned}
 \tag{ACR.22}
$$

Its full expanded support has $\Theta(F_{n+1})$ nodes, and its literal
traffic is $\Theta(nF_{n+1})$. With the same retained $P,L$ and actual
binding, it can install the same (ACR.4) and reach Theorem 6.1's same
consumers. The new recovery construction replaces this exponential
scan segment by logarithmic paid Reads and polynomial local work for
fixed $d$, rather than proving finite recoverability for the first time.

Proof. The root is known present. At each confirmed node $p$, submit
Read$(pa)$. The physical tree is full binary, so reply one identifies
a branch and justifies scheduling both $pa,pb$; reply zero identifies
a terminal node. Stack exhaustion terminates on the finite current tree
without an initial height, size or age bound. This pays exactly one
query per actual node and reconstructs its support and boundary.
Its leaf count is $F_{n+1}$, strictly increasing on $n\ge2$, so finite
integer search recovers $n$, then $B_n$. This is precisely the complete
scan supplier, specialized to the same task and same erasure assumptions.
Its final retained writes and handoff remain paid and stationary. The
native results `NativeFullSourceProducer`, `NativeFibonacciStaticScan`
and `NativeSerialMachine`, in the same D5 Observer directory and their
Blueprint sources, supply full traversal and paid serial execution in
their declared native domains; no hidden full-source port is imported.
`ActualFibonacciSupportChain` supplies a native bounded-address comparison;
the physical depth bounds needed here follow directly from (ACR.7).

For $n\ge2$ the maximum physical depth is $n-1$: following successive
initial-beta children gives a node born at every successive update,
whereas (ACR.7) forbids a present word of length exceeding $n-1$.
Hence the scan peak is exactly $n$. A terminal node of depth $\ell$
branches no later than update $2\ell+2$ by (ACR.5)–(ACR.7).
Being terminal at cut $n$ therefore forces
$n<2\ell+2$, equivalently $\ell\ge\lfloor n/2\rfloor$.
Its $F_{n+1}$ terminal queries give the lower traffic bound. All queries
have length at most $n$, giving the upper bound and (ACR.22).
The full binary node count proves the expanded output size. Encoding
all output addresses separately may cost still more than node count.

Combining (ACR.13)–(ACR.15) with (ACR.22) compares the two procedures on
the identical input. The ratio of scan Reads to reinstatement Reads and
the ratio of scan traffic to reinstatement traffic grow without bound
as $n\to\infty$ at fixed $d$. The full source still has exponentially
many material nodes, and expanding it after either recovery still costs
that output. The comparison does not erase the earlier earning of
$P,L$, bound every installation apparatus, or imply all-parameter
or total-latency dominance. If $d$ varies, the explicit polynomial
$d$-factors in local work must be compared; neither a reply count nor
a bit-operation count alone determines physical completion time.
$\square$

[GPO]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GLOBAL_PORT_ORIENTATION.md
[CAB]: RECURSIVE_RELATIONAL_OBSERVATION_CONCURRENT_ACQUIRED_CLOCK_BRIDGES.md
[BY]: https://www.slac.stanford.edu/pubs/slacpubs/1500/slac-pub-1679.pdf

## 追加锚（本行以下为增补区）

## 9. Joint erasure and an acquired physical spine

**Definition 9.1 (the joint entrance and its target).** Use exactly GPO
Definition 27.1's actual alpha origin, persistent physical links $a<b$,
actual lexicographic beta-birth order and autonomous all-index class
$\mathscr R_d$. Only the authentic public integer $d\ge0$ is numerical
source information at entry. Put

$$
 n_0=\begin{cases}N(2d),&d>0,\\2,&d=0,\end{cases}
 \qquad N(m)=\min\{u\ge3:F_u-1\ge m\}.
 \tag{ACR.23}
$$

The actual completed cut is an arbitrary finite $n\ge n_0$; no upper
bound is supplied. Erase all accessible source bits, seeded law, age,
phase, tree, support, boundary, labels, archives, receipts and histories,
including age-bearing control, allocation, capacity and duration data.
The actual source and its genuine same-root binding survive. Supply
valid total paid physical-literal presence-Read and later update grants,
common finite source-blind code, fresh growing owned readable backing,
finite local progress and completed Reads. An exclusive completed-cut
stationary interval covers all recovery calculations, Reads, allocations,
intermediate and retained writes, and the actual completed handoff.
Recovery makes zero source updates. Service apparatus, initialization,
retention, writes and handoff retain their actual charges as in Assumption
1.2; no source conformance, root or grant is inferred from a bit string.

Write $\mathscr C_d$ for the distinct infinite output behaviors in
$\mathscr R_d$. GPO (GPO.88), with its semi-infinite, singular and
finite-transient convention, supplies

$$
 D_d=|\mathscr C_d|=\frac{2\,4^d+1}{3}.
 \tag{ACR.24}
$$

For an authentic length-$2d$ prefix $P$, let $K_d(P)$ be **the same fixed
synthesis** used in GPO Lemma 29.2 and Definition 34.1. For $d>0$ it
selects the first passing order-$d$ coefficient row in that already fixed
enumeration, with the first $d$ bits of $P$ as seed; for $d=0$ it is the
zero descriptor. The enumeration is a common source-independent code
convention. It is not replaced by a new ordering or a minimal private
presentation. The target is to acquire and actually install

$$
 (P,K_d(P),n,B_n),\qquad P=z_1\cdots z_{2d},\qquad B_n=F_{n+1}-1.
 \tag{ACR.25}
$$

Acquisition here means exact inference from paid current-source replies
and real readable writeback. It does not assert that these bits were
previously queried at their origin births.

Let $e_d$ and $v_d$ be the bit work and peak working bits of generating
all rows once by that original fixed public enumeration, counting its
operands and intermediate writes. They are finite constants at each
fixed $d$, independent of the actual stream and cut; take both zero at
$d=0$. This retains the original unspecified enumeration rather than
assuming an efficient new one. For the usual binary-counter ordering
one has $e_d=O((d+1)2^d)$ and $v_d=O(d+1)$; the statements below
charge the actual $e_d,v_d$ without requiring that particular ordering.

**Proposition 9.2 (a physical spine gives two ages per behavior).** Define

$$
 h=\max\{\ell\ge1:a^\ell\in S_n\},\qquad
 k=\lceil\log_2(h+1)\rceil.
 \tag{ACR.26}
$$

There is a source-blind paid procedure acquiring $h$: query
$a,a^2,a^4,\ldots,a^{2^k}$ through the first absence, then bisect the
remaining integer interval of possible maximum lengths. On this actual
input it uses exactly $2k$ Reads, peak literal $2^k\le2h$ and traffic
at most $2k\,2^k$. No law, semantic-port choice or age is used to form
these words. Moreover

$$
 1\le h\le n-1,\qquad h+1\le n\le2h+1.
 \tag{ACR.27}
$$

For any proposed behavior $s\in\mathscr C_d$, compute its origin-orbit
birth times by (ACR.5)--(ACR.6). Its cuts compatible with this acquired
spine are precisely

$$
 I_s(h)=[b_s(a^h),\ b_s(a^{h+1})-1]\cap[n_0,\infty).
 \tag{ACR.28}
$$

This interval has at most two integers, all at most $2h+1$. Thus the
unbounded entrance has been reduced by actual Reads to at most $2D_d$
distinct mature law/cut data, including its actual $(s,n)$.

Proof. The root has branched by every allowed cut, so $a$ is present.
By (ACR.7), a length-$\ell$ nonempty word is born in $[\ell+1,2\ell]$.
Hence the spine is finite, and presence along it is a prefix predicate.
The first absent power has exponent $k\ge1$, with
$2^{k-1}\le h<2^k$. Its preceding present power and the absent power
leave $2^{k-1}$ possible maxima; balanced bisection takes $k-1$ further
calls. Including the $k+1$ power calls gives $2k$, and every submitted
length is at most $2^k\le2h$.

Presence of $a^h$ gives $n\ge h+1$. Absence of $a^{h+1}$ gives
$n<b_s(a^{h+1})\le2h+2$, proving (ACR.27). For each hypothetical law,
those two same replies say exactly (ACR.28). Consecutive nonempty spine
births obey

$$
 b_s(a^{h+1})-b_s(a^h)=\delta(\sigma_{a^h})\in\{1,2\}.
 \tag{ACR.29}
$$

They leave at most two cuts, before the maturity intersection. The actual
law obeys both acquired replies and maturity, so its actual cut remains.
Computing these hypothetical birth times uses forward descriptors, not
an observation of the hypothetical or actual whole tree. Doubling and
bisection are the classical unbounded-search supplier [BY]; the additional
source correspondence is the bounded age fiber (ACR.28)--(ACR.29) for a
single actually acquired physical spine. $\square$

## 10. Executable physical separators with polynomial backing

**Definition 10.1 (implicit subtree ranks).** For a present descriptor
$(b_p,\sigma_p)$ at a hypothetical cut $u$, define

$$
 \kappa_u(p)=u-b_p+\mathbf1_{\sigma_p=\beta},\qquad
 f(q)=F_{q+1}\quad(q\ge0).
 \tag{ACR.30}
$$

The subtree has $f(\kappa_u(p))$ terminal leaves. It is a singleton
exactly at ranks zero and one, and a branch at every rank at least two.
A branch of rank $q$ has child ranks $q-1,q-2$, with rank $q-1$ at
$a$ iff its actual orientation bit is one. These are ranks of the
orientation-independent leaf counts, not names of fixed physical
semantic children. Their meaning follows by the two label transitions
and the recurrence $f(q)=f(q-1)+f(q-2)$ for $q\ge2$, as in GPO
Theorem 24.2. In particular $f(0)=f(1)=1$: tests below compare leaf
counts, and do not treat ranks zero and one as unequal supports.

**Proposition 10.2 (constructive separator for mature candidate data).**
Given distinct mature data $x=(s,u)$ and $y=(t,v)$, with each behavior
specified by any order-at-most-$d$ seeded presentation, there is a uniform
procedure constructing a physical word $w$ and its two opposite predicted
presence replies such that, for $H=\max(u,v)$,

$$
 \operatorname{Read}^{s}_{u}(w)\ne\operatorname{Read}^{t}_{v}(w),
 \qquad |w|\le H-1.
 \tag{ACR.31}
$$

The procedure uses no Read, complete-tree expansion, stored tree, scan
or backward recurrence. One binary implementation, including construction
of both first-$2d$ prefixes when needed, has work at most

$$
 C\bigl((d+1)^3(H+2)^2+(H+2)^3+(d+1)^2\bigr)
 \tag{ACR.32}
$$

and reusable scratch
$O((d+1)^2+(d+1)(H+2)+(H+2)^2)$ bits. The generated literal, operands,
Fibonacci and rank integers, intermediate writes and predicted replies
are included. Presentations of equal behaviors are distinguished only
when their cuts differ.

Proof. First specify an unequal-count descent. At a common physical
prefix $p$, maintain its present descriptors in both candidates and the
invariant that their subtree leaf counts differ. If one is terminal and
the other a branch, return $pa$: it is absent in the former and present
in the latter. If both are branches, compute each parent orientation
from its own actual chronological index (ACR.6), then its two child
ranks by Definition 10.1. Choose $a$ if the two $a$-child leaf counts
differ; otherwise choose $b$. At least one side differs, since the sums
of the two child counts differ. Descend that side, update both physical
prefix descriptors and repeat. Both children of a branch are present,
so the invariant is maintained. Both candidates cannot be terminal
under unequal counts. The maximum rank decreases by at least one at
each descent. Induction on that maximum shows that the returned suffix
from this starting prefix has length at most
$\max(\kappa_u(p),\kappa_v(p))-1$. This specifies every choice and
termination step; an unknown lexicographic symmetric difference is not
an input to the procedure.

If $u\ne v$, start at the root, with ranks $u,v\ge2$. The counts
$F_{u+1},F_{v+1}$ differ, since Fibonacci leaf counts strictly increase
on ranks at least one. The preceding descent gives (ACR.31).

If $u=v$ and $s\ne t$, compute their first differing birth bit $j$.
GPO Lemma 29.2 gives $1\le j\le2d$; this case is absent at $d=0$.
Let

$$
 \tau=\min\{e\ge2:j\le F_{e+1}-1\},\qquad
 R=j-(F_\tau-1).
 \tag{ACR.33}
$$

Maturity gives $j\le F_u-1=B_{u-1}$, hence $\tau\le u-1$.
The two histories before birth $j$ coincide. We now construct its
common parent $p_j$, rather than enumerate earlier parents.

At the fixed old cut $\tau-1$, start at the root with remaining rank
$R$ among beta leaves. Maintain a present prefix descriptor $(b,\sigma)$
and a remaining rank between one and its number of beta leaves,
$\lambda_\sigma(\tau-1-b)$. If that prefix is a beta terminal,
return it; its remaining rank must be one. An alpha terminal has beta
mass zero and is never selected. Otherwise it is a branch: compute
its branch time, chronological index by (ACR.6), orientation bit and
the two child descriptors. For its $a$-child, born at that branch time
$\tau_p$, compute the mass

$$
 A_p=\lambda_{\sigma_{pa}}(\tau-1-\tau_p).
 \tag{ACR.34}
$$

If the remaining rank is at most $A_p$, descend to $pa$ with that
rank; otherwise descend to $pb$ and subtract $A_p$. This includes
$A_p=0$. All these branches were born by $\tau-1$, so their event
indices are at most $B_{\tau-1}<j$. Their bits and child descriptors
therefore agree in the two candidates. The disjoint physical $a$- then
$b$-subtree beta-leaf lists have exactly the masses used in (ACR.34),
by GPO (GPO.94). Induction proves that this unranking selects the
$R$th beta leaf of the actual old physical lexicographic list. GPO
Proposition 39.2 then identifies it with the actual parent $p_j$.
No rank oracle or semantic traversal is supplied. At each branch the
chosen child's branch time is later, so the descent is finite; a parent
branching at $\tau$ has $|p_j|\le\tau-2$ by (ACR.7).

At $p_j$ the two candidate orientations are opposite. At their common
cut $u\ge\tau+1$, their physical $a$-child ranks are $u-\tau+1$
and $u-\tau$ in one order. Their leaf counts differ, including the
endpoint pair of ranks two and one. Begin the unequal-count descent
at $p_ja$. Its returned word has length at most

$$
 |p_j|+1+(u-\tau+1)-1\le u-1.
 \tag{ACR.35}
$$

The opposite predicted replies in either case are obtained from which
candidate is terminal at the final step. This proves correctness,
including the first mature cut and different equivalent presentations.

For the bounds, first generate two prefixes of length $2d$ by forward
recurrence in $O((d+1)^2)$ bit operations. Both unranking and the
unequal-count descent visit $O(H+1)$ prefixes in total. Retain their
birth descriptors along each current path. At each prefix compute the
chronological rank by the sibling sum (ACR.6), with the already determined
sibling labels. The relevant branch indices are at most $B_H$ and have
$O(H+1)$ bits; intermediate sums have the same bound. A table of
$F_0,\ldots,F_{2H+4}$ takes $O((H+2)^2)$ bits and bit operations.
Each prefix rank sum has $O(H+1)$ terms of $O(H+1)$ bits, so all
rank calculations use $O((H+2)^3)$ bit work. A forward companion power
at each required index costs $O((d+1)^3(H+2))$, and there are $O(H+1)$
such evaluations for each of the two candidates. This is the GPO
Proposition 39.5 evaluator applied to the paths explicitly selected
above. The local ranks, beta masses and comparisons have smaller bounds.
There is no iteration through $B_H$ births. The stated table, two paths,
companion scratch, presentations and literal buffers fit the displayed
workspace. Counting each binary read, write and initialized workspace bit
as work gives (ACR.32), including the constructed word and replies.
No inverse matrix is used, so zero taps, singular transitions, nonminimal
rows, the zero stream and finite transients are included. $\square$

## 11. Unbounded paid acquisition and the same-source consumers

**Definition 11.1 (streamed joint acquisition).** First acquire $h$ by
Proposition 9.2. For $d>0$ enumerate the $4^d$ order-$d$ row/seed
presentations, using ordinary $d$-bit row and seed counters; for $d=0$
enumerate just the zero presentation. For each presentation $s$, compute
its first $2d$ bits and (ACR.28), and emit its at most two mature cuts.
No table of all presentations, transcript of all tests or expanded tree
is retained. Padding an order-$r$ annihilator by $E^{d-r}$, as in GPO
Lemma 29.2, ensures that every behavior occurs; repeated presentations
are allowed. The emitted list has some finite length $K$, with

$$
 1\le K\le2\,4^d,\qquad \max\{u:(s,u)\text{ is emitted}\}\le2h+1.
 \tag{ACR.36}
$$

Maintain a single current candidate. Initialize it to the first emitted
datum. Compare each further datum with the current one. If their
length-$2d$ prefixes and cuts coincide, keep the current one without a
Read. Otherwise construct the separator of Proposition 10.2, really
submit that physical word on the genuine stationary root, and keep the
one of the two candidates whose predicted reply equals the actual
binary reply. Release the other candidate's scratch. After exhausting
the counters, generate the surviving prefix $P$, run exactly $K_d(P)$,
compute $B_n$ by Fibonacci addition, and really write (ACR.25), its
ready control and any requested behavioral phase. Make the actual
handoff only after all writes finish, while the same completed cut is
still stationary. A candidate's computed prediction never stands in
for the paid call.

**Theorem 11.2 (joint acquisition on every unbounded mature input).**
Under Definition 9.1, Definition 11.1 terminates on every admitted
actual $(s,n)$ with the correct installed data (ACR.25). On **that
same run**, for its actually acquired $h,k$ and actual emitted count
$K$, let $J$ be the number of candidate comparisons that really make
a Read. Then

$$
 \begin{aligned}
 U_{\rm source}&=0,& Q&=2k+J\le2k+K-1\le2k+2\,4^d-1,\\
 M&\le\max(2^k,2h)\le2h\le2n-2,&
 W&=W_{\rm spine}+\sum_{i=1}^{J}|w_i|\le2h\,Q.
 \end{aligned}
 \tag{ACR.37}
$$

In particular the required same-input orders are

$$
 Q=O(\log(n+2)+4^d),\qquad M=O(n),\qquad
 W=O\bigl(n(\log(n+2)+4^d)\bigr).
 \tag{ACR.38}
$$

For an absolute binary-operation-model constant $C$, one implementation
has local bit work, including all literal and data writes, at most

$$
 e_d+C\left[(4^d+1)\bigl((d+1)^3(n+2)^2+(n+2)^3\bigr)
       +(n+2)^2(1+\log_2(n+2))\right],
 \tag{ACR.39}
$$

and reusable owned data backing

$$
 v_d+O\bigl((d+1)^2+(d+1)(n+2)+(n+2)^2\bigr)\text{ bits}.
 \tag{ACR.40}
$$

The returned record and optional phase require $O(d+n+1)$ binary data
writes, including an explicit $\Theta(n)$-bit $B_n$ field. The actual
fixed code, installation, call service, binding/grants, backing lifetime
and handoff apparatus have their separate actual charges. Neither their
physical tariffs nor Read, allocation or handoff durations are bounded
by (ACR.39). Thus this is polynomial local work for each fixed $d$,
and polynomial reusable data backing for each fixed $d$, without a total
physical-time or weighted-resource optimum. The explicit $e_d,v_d$
charge the exact public canonical enumeration; no complexity bound in
$d$ is inferred from an unspecified ordering.

Proof. The actual behavior has an order-$d$ presentation when $d>0$,
including a padded presentation of a lower order. By Proposition 9.2,
its actual cut occurs in the emitted list. At $d=0$ the same assertion
uses the one known zero behavior, whose age remains to be acquired.
The list is finite and nonempty regardless of which duplicate
presentations are enumerated.

The comparison invariant is that the actual behavioral datum is either
the current candidate or still occurs among the unprocessed candidates.
It holds initially. If the actual datum is current, every comparison
retains it because its predicted reply is correct. If it arrives as the
next candidate, the separator's opposite replies select it. If neither
candidate is actual, the actual datum still lies later in the list.
Equality of the first $2d$ bits and the cut means equality of the datum
by GPO Lemma 29.2, so skipping duplicates preserves the invariant.
This is the usual finite comparison/elimination argument, used here as
an intermediate step. It needs no stored reply history or generally
balanced splitting hypothesis. At exhaustion the invariant makes the
survivor actual. Its generated prefix is therefore the authentic $P$,
earned from this run's replies rather than retained source advice.

For canonical equality, the survivor's raw row is only a computational
presentation. Applying the **original fixed** synthesis to its authentic
$P$ gives exactly the $K_d(P)$ field selected in GPO §§29 and 34.
Equal output behavior alone is not used to equate distinct coefficient
rows. In particular a zero behavior at $d>0$ does not authorize
replacing that field by a newly selected minimal order-zero row.

There are $2k$ actual spine calls and at most $K-1$ comparison calls.
By (ACR.36), Proposition 10.2 constructs every comparison word with
length at most $(2h+1)-1=2h$. Proposition 9.2 bounds the spine's
peak by the same $2h$. Summing the actual lengths of these very calls
gives (ACR.37); no maxima from different inputs are combined. Since
$h\le n-1$, $k\le\lceil\log_2 n\rceil$, proving (ACR.38).
The supplied interval was unbounded; $2h+1$ is a bound obtained during
this run, and is never supplied as entry age information.

For work, materializing and submitting spine literals, updating their
binary length brackets, copying replies and initializing their buffers
uses $O((n+2)^2(1+\log(n+2)))$ bit operations as a conservative bound.
Computing $n_0$ by Fibonacci addition also fits, since $n_0\le n$.
For each of $4^d$ presentations, generating the first $2d$ bits costs
$O((d+1)^2)$. Computing the two spine thresholds uses $O(h+1)$
forward path descriptors and the (ACR.32) arithmetic bound, with
hypothetical times at most $2h+2$. There are at most twice as many
comparison constructions, each bounded by (ACR.32) with $H\le2h+1$.
The row/seed counters and every emitted age are explicitly generated
and written. Final canonical synthesis generates its rows by the
original fixed enumerator, charging $e_d$, and tests at most $2^d$
rows with the fixed seed in $O(2^d(d+1)^2)$ further bit operations.
All remaining costs fit the polynomial terms of (ACR.39), since $h<n$.

Forward Fibonacci addition computes $B_n$ in $O((n+2)^2)$ bit work
and $O(n+1)$ bits. If requested, the forward companion power
$C^{B_n}$ applied to the selected seed gives the behavioral phase whose
next output is $z_{B_n+1}$, in $O((d+1)^3(n+1))$ bit work. No private
state is recovered or inverted. The prefix, descriptor and phase take
$O(d+1)$ bits, the cut takes $O(\log(n+2))$, and the binary integer
$B_n=F_{n+1}-1$ takes $\Theta(n)$ bits. Actual copying, readable
installation and receiver data writes of these fields, along with ready
control, fit (ACR.39) and the stated data-write bill. Only two candidate
records, their prefixes, enumeration counters, two descriptor paths,
Fibonacci tables and companion scratch coexist; final canonical row
generation additionally uses at most $v_d$ working bits. Reuse their
storage between comparisons. This proves (ACR.40), without a retained
exponential candidate catalogue, an age-dependent preinstalled table or
a retained test transcript.
All intermediate operand reads and bit writes are in this bit-operation
bill; each real Read and physical service/handoff operation additionally
keeps its actual tariff. Finite progress and completed service/handoff
give finite return. The stationary premise covers those real operations
through return, so the installed $n,B_n$ still name the actual cut.
$\square$

**Theorem 11.3 (the acquired record enters the existing view inverses).**
At Theorem 11.2's completed handoff, under its surviving same-source
binding and grants, the installed (ACR.25) has the mathematical fields
and synchronization required by GPO Definition 34.1. Consequently GPO
Theorem 34.2 recovers this actual source's incidence $S_n$, terminal
boundary, marked birth chronology, current labelled $X_n$ and complete
finite-request behavior, with its commuting round trips on their data
images. Without whole-tree expansion, GPO Theorem 39.4 and Proposition
39.5 apply to each supplied finite physical literal. Under GPO Theorem
34.3's continued rights, retention, backing, completed-call synchronization
and exclusive serial path, the consumers remain correct through every
finite actual serial continuation.

Proof. Theorem 11.2 supplies the exact prefix and the identical fixed
canonical generator, rather than only an equivalent private presentation.
Its stationary completed writeback supplies the exact current counters.
The genuine binding, grants and available code/backing are separately
Definition 9.1's actual relations. These are precisely the inputs used
by GPO Theorems 34.2--34.3 and 39.4. For the zero behavior one may use
the evaluator's constant-zero shortcut; that does not change $K_d(P)$
in the retained record. Its forward row also evaluates that same stream
by the proof of GPO Proposition 39.5. At $d=0$, $P$ is empty and the
separate $n\ge2$ zero-order domain of GPO Theorem 34.2 applies.
Thus the original parameter correspondence holds on every admitted cut.

This use requires no past origin-acquisition receipts: GPO Definition
34.1 explicitly separates optional literal receipts from the predictor's
mathematical fields. The acquired record has the same data, while a claim
that an earlier particular acquisition event happened would require its
actual journal. Expansion of the entire views still pays its output,
backing and computation; the actual source already has $2F_{n+1}-1$
material nodes. As in Theorem 6.1, inserting stationary observer actions
can change an arbitrary journal without changing any recovered birth
view. A hidden equivalent register can also differ while giving every
same reply. Root/grant authenticity is a premise, and physical durations
are excluded channels. Hence these consumers recover none of those
additional objects. $\square$

## 12. Joint lower restrictions and the fixed-family boundary

**Proposition 12.1 (finite-window capacity and correctly indexed bills).**
Fix common entry resources as in Definition 9.1 and a public window
$[A,H]$. Its effective window is $[A',H]$, where $A'=\max(A,n_0)$.
If this window is nonempty, put $N_w=H-A'+1$. Any exact terminating
zero-update controller on all its $D_dN_w$ mature behavioral data has

$$
 \max_{s,n}Q(s,n)\ge\lceil\log_2(D_dN_w)\rceil.
 \tag{ACR.41}
$$

If $N_w\ge2$, it also has the **separate worst-case-coordinate** bounds

$$
 \begin{aligned}
 \max_{s,n}M(s,n)&\ge\lceil H/2\rceil,\\
 \max_{s,n}W(s,n)&\ge
 \lceil(A'+1)/2\rceil\,\lceil\log_2N_w\rceil.
 \end{aligned}
 \tag{ACR.42}
$$

For each fixed behavior, the traffic inequality is witnessed on one
actual path containing at least $\lceil\log_2N_w\rceil$ informative
age queries, each with length at least $\lceil(A'+1)/2\rceil$.
The peak is forced on the runs at $H-1,H$. These witnesses need not
be the same input as each other or the capacity witness in (ACR.41).
Every fixed-behavior restriction also obeys Proposition 4.3's existing
pointwise interior and lower-endpoint conditions, on exactly its stated
age domain. For $N_w=1$ there is no age-query or age-literal lower
bound; (ACR.41) reduces to the behavioral capacity. At $d=0,N_w=1$
it is zero, attained by returning the known cut and zero behavior
without a Read. An empty effective window supplies no instance.

Proof. Distinct behaviors have distinct length-$2d$ prefixes by GPO
Lemma 29.2; differing cuts also require different returned records.
Thus the finite common-entry reply tree needs $D_dN_w$ distinct return
leaves. A binary tree of depth at most $q$ has at most $2^q$ leaves,
giving (ACR.41), using the classical decision-tree capacity argument
already used by GPO Theorem 37.2.

Fix one behavior and restrict the same controller to its $N_w$ ages.
Each physical word is its first-presence threshold (ACR.7). Contract
constant-reply queries in that restricted reply tree. Some remaining
path has at least $\lceil\log_2N_w\rceil$ queries; every such query
has threshold in $[A'+1,H]$ and hence the stated minimum length.
Multiplication of these lengths and their count is therefore a traffic
bill on that one input. Separately, the adjacent ages $H-1,H$ have a
first different reply on their common prefix, and its threshold is
exactly $H$, forcing the peak on both runs. These are the arguments
and costs of Theorem 4.2, applied with the correct effective endpoints;
Proposition 4.3 supplies its sharper pointwise restrictions without a
new all-input optimality claim. The path-cost convention agrees with
[Cicalese--Laber--Saettler][CLS], §1, which defines cost of one object
as the sum on its root-to-leaf path, then maximizes over objects. It
does not combine separately attained maxima into a joint witness.
For independent zero-error randomness with almost-sure finite return,
intersect the finitely many probability-one correctness/termination
events; each tape in their intersection satisfies the deterministic
argument. This gives the same worst-case uniform-budget restrictions,
not an expected-cost optimum. $\square$

**Proposition 12.2 (saturation and its nontrivial-law qualification).**
For every finite physical-word family $\mathcal W$, every $d\ge0$
and every $s\in\mathscr C_d$, all words in the family are present at
all sufficiently old mature cuts. More explicitly, with
$L=\max(\{0\}\cup\{|w|:w\in\mathcal W\})$,

$$
 n\ge\max(n_0,2L)\quad\Longrightarrow\quad
 \operatorname{Read}^{s}_n(w)=1\quad(w\in\mathcal W).
 \tag{ACR.43}
$$

For $d\ge1$ this rules out a fixed age-independent finite word family
separating the behaviors on all mature cuts. For $d=0$ there is only
one behavior, and the empty family already separates behaviors
vacuously. Saturation holds in both cases. It does not obstruct the
adaptive age-dependent words in Definition 11.1.

Proof. Every nonempty $w$ is born by $2|w|$ by (ACR.7), uniformly
over the law, and the empty word is always present. Persistence proves
(ACR.43). When $d\ge1$, the constant-zero and constant-one behaviors
are distinct allowed streams, yet all the displayed replies coincide
at a common sufficiently large cut. They cannot be separated by that
family. The singleton case has no distinct pair. In Definition 11.1,
the acquired $h$ grows with the actual cut by (ACR.27), and neither
the spine family used on that run nor its later separators is fixed
independently of those acquired replies. Thus the impossibility
consequence has no application to Theorem 11.2. $\square$

**Proposition 12.3 (source subtraction and the scope of the bridge).**
The new joint entrance conclusion uses only the actual source and service
of Definition 9.1 and the paid constructions above. The classical finite
learning, unbounded search, recurrence synthesis and mature-view inverses
remain intermediate suppliers; the additional source-grounded content
is the acquired two-age-per-behavior spine fiber, the implicit physical
separator with its work/backing bound, and their same-run zero-update
acquisition and actual writeback. These statements give neither an
exponential-in-$d$ necessity nor a polynomial-in-$d$ acquisition result,
and do not claim all-parameter scan dominance or a weighted optimum.

Proof. The sole sensor throughout is a paid membership bit. [Angluin][ANG],
§§1--2, distinguishes membership from equivalence queries returning a
counterexample; no equivalence service is used here. A locally constructed
separator compares two explicit hypothetical data and obtains only one
actual binary reply. [Nowak][NOW], Lemma 1 and Theorem 1, derives fast
finite-class splitting under neighborliness and coherence hypotheses;
none is supplied by this service or assumed in the proof. The finite
comparison argument in Theorem 11.2 is an existing elementary supplier,
not the source-specific bridge itself. [Bille et al.][BIL], §1, starts
with a compressed grammar for random access. Here hypothetical rows are
enumerated from $d$, while the actual row, prefix and cut must be
acquired; compressed-representation access alone cannot discharge that
obligation. GPO §§29,37 supply finite behavior separation and counting;
GPO §39 supplies forward term evaluation and the actual physical
chronological index. Proposition 9.2 and the unranking/descent proof of
Proposition 10.2 provide the extra paid-source correspondence needed
before GPO §§34,39 can consume an authentic synchronized record.

The native declarations and their owning Blueprint Scribes under
`D5/S3/Arith/FibonacciAtomic/Observer/` give related but distinct suppliers:
`NativeRankedNavigationCompiler.atomic_navigation` concerns the fixed
native semantic orientation; its private realization lemmas do not
supply a locally wired chronological rank. `NativeBirthVectorDecoder`
proves decomposition and decoding on its recursive-code images, and
explicitly does not identify every such code with an actual least
presence epoch. `ActualFibonacciSupportChain` gives strict native support
inclusions and bounded-address agreement. `NativeFullSourceProducer`,
including its private traversal proof, returns the complete tree with
one richer native reply per node; `NativeFibonacciStaticScan`, including
its private execution/cost helpers, uses a supplied native list and
retains its routing costs. None is the erased-law, binary-physical,
no-tree entrance of Definition 9.1. The retrospective and general-cut
acquisition volumes instead assume an acquired seed, retained request
material or an installed capture/selector interface. Their premises do
not supply the erased inputs here. The original Fibonacci atomic volume
§§1--5 separately assumes two atoms, an ordered constructor, a replacement
law and observation quotients; none follows from two unrelated symbols.

At this erased entrance the existing physical complete scan also
suffices: acquire $S_n$, apply GPO Theorem 28.2 to decode $n$ and
its mature first $2d$ bits, and run the same $K_d$. Its scan segment
keeps exactly Proposition 8.1's Read and literal bills; decoding,
canonical synthesis and installed writes remain additional paid work.
For fixed $d$, Theorem 11.2's polynomial local work and logarithmic
plus constant-in-$n$ Reads may be compared on the identical actual
$(s,n)$ with the full-scan supplier and Proposition 8.1's material-size
bill; full expansion still costs exponential output. The explicit
$4^d$ enumeration and literal/installation bills remain, so no stronger
uniform resource comparison follows. The lower restrictions in
Proposition 12.1 only have logarithmic behavioral capacity in $D_d$;
they do not prove exponential-$d$ necessity. All statements are ordinary
conditional mathematical derivations from the cited suppliers, with no
additional Lean certification or worldwide novelty assertion. $\square$

[ANG]: https://link.springer.com/article/10.1023/A:1022821128753
[NOW]: https://arxiv.org/pdf/0910.4397v5
[CLS]: https://arxiv.org/pdf/1309.2796v2
[BIL]: https://arxiv.org/pdf/1001.1565v3

## 追加锚（本行以下为增补区）

## 13. Physical depth means and authenticated early parents

**Definition 13.1 (depth from a present physical cone).** Retain the
entire joint entrance of Definition 9.1. In particular the law, seed,
cut, phase, current tree and journal are absent at entry; the actual
alpha origin, all-index promise, same-root binding and grants are
premises. Stationarity includes local preparation, allocation, every
intermediate and retained write, and the completed handoff. First earn
$h,k$ by Proposition 9.2 and put $H=2h+1$. Thus

$$
 n_0\le n\le H\le2n-1.
 \tag{ACR.44}
$$

For a present physical word $p$ and a direction tape
$u\in\{0,1\}^H$, start at $v=p$. Submit the full literal $va$ to
the original root. If its reply is zero, stop; otherwise both children
of $v$ are present, and the next tape bit selects $va$ for zero or
$vb$ for one. Repeat. Write $D_{s,e,p}(u)$ for the number of edges
traversed at law $s$ and cut $e$. Tape positions are local indices,
restarted at one in each cone; they are never source-Read operands.
The last, absent-child test is part of the procedure.

**Theorem 13.2 (the depth statistic's physical consumer).** At a present
cone of rank $q=\kappa_e(p)$ from Definition 10.1, the mean over all
fair length-$H$ tapes, whenever $e\le H$, is

$$
 \mu_q=\frac{2q}{3}-\frac49+\frac49(-1/2)^q,\qquad
 \mu_0=\mu_1=0,\qquad
 \mu_q-\mu_{q-1}=\frac23\bigl(1-(-1/2)^{q-1}\bigr)\ge\frac12
 \quad(q\ge2).
 \tag{ACR.45}
$$

Suppose a single ordered list of $T$ tapes approximates these means
with absolute error strictly below $1/8$ for every admitted law,
every mature cut $e\le H$, and every present $p$ with

$$
 |p|\le h_0,\qquad
 h_0=\begin{cases}N(2d)-2,&d>0,\\0,&d=0.\end{cases}
 \tag{ACR.46}
$$

Using this same list in the root and in at most $4d$ early child cones
authenticates exactly $P=z_1\cdots z_{2d}$ and the actual $n$, without
an update or an observed rank, label or semantic port.

Proof. The unordered child ranks $q-1,q-2$ and the terminal cases
$q=0,1$ are supplied by Definition 10.1, independently of orientation.
At every reached branch, an independent fair physical direction picks
each child with probability $1/2$. Consequently the mean satisfies
$\mu_q=1+(\mu_{q-1}+\mu_{q-2})/2$ for $q\ge2$. Substitution and
the two initial values give (ACR.45). No distribution uniform on leaves
is asserted: a leaf at relative depth $r$ has probability $2^{-r}$.
For $q\ge1$ every path traverses at most $q-1$ edges; at rank zero it
traverses none. Thus the finite tapes suffice. On the actual source,
each walk has $D+1\le H$ paid Reads, including its terminal test,
and every submitted literal has length at most $n\le H$. Indeed a
present depth is at most $n-1$ by (ACR.7).

For birth $j\le2d$, compute its update
$t_j=\min\{t\ge2:j\le B_t\}$ and its physical parent $p_j$ as
follows. Reconstruct only the old labelled tree $X_{t_j-1}$ from the
already authenticated first $B_{t_j-1}<j$ origin bits, and select its
$(j-B_{t_j-1})$th beta leaf in physical lexicographic order. This is
GPO Proposition 39.2's actual parent. There are fewer than $j$ old
births, hence at most $2j-1$ nodes in this old tree. It uses no later
bit and no current support. Maturity gives $t_j\le n_0-1\le n-1$;
(ACR.7) gives $|p_j|\le t_j-2$, so both child prefixes satisfy
(ACR.46). They are present, and their ranks at the actual cut are
$n-t_j+1,n-t_j$, with the larger at $a$ precisely when $z_j=1$.
Their true mean difference has magnitude at least $1/2$, including
the endpoint pair of ranks two and one. Two errors below $1/8$ leave
the correct sign with margin greater than $1/4$. Induction authenticates
all $2d$ bits. At $d=0$ this loop is empty, as required by the
singleton zero behavior.

Let $m$ be the measured root mean. Return the nearest integer to
$3m/2+2/3$. At every allowed $n\ge2$,

$$
 \left|\frac32m+\frac23-n\right|
 <\frac3{16}+\frac23\,2^{-n}\le\frac{17}{48}<\frac12.
 \tag{ACR.47}
$$

Thus the integer is exactly $n$. No distinction between ranks zero
and one is used for age recovery outside its stated mature domain.
Uniformity over all these cones and cuts licenses the adaptive parent
choices and reuse of one list; a guarantee for just one preselected
cone would not license that inference. $\square$

## 14. A deterministic common list with a priced finite catalogue

**Definition 14.1 (the finite constraint class).** Given integers
$d\ge0,H\ge n_0$, enumerate all $4^d$ order-$d$ coefficient-row/seed
pairs by binary counters; at $d=0$ enumerate just the zero stream.
For each pair, each $e\in[n_0,H]$ and each word $p$ of length at
most $h_0$, retain the constraint $f=D_{s,e,p}$ only when $p$ is
present in that hypothetical source. This is a local computation, not
a Read of any additional source. Repeated presentations and identical
constraints remain in the list. Set

$$
 \begin{aligned}
 K_0&=4^d(H+1)2^{h_0+1},\\
 L&=2d+h_0+\lceil\log_2(H+1)\rceil+4,\\
 T&=64H^2L,\qquad Q_0=4H^2,\qquad \eta=1+Q_0^{-1}.
 \end{aligned}
 \tag{ACR.48}
$$

There are at most $K_0$ constraints. Padding the all-index annihilator
by $E^{d-r}$ as in GPO Lemma 29.2 covers every lower-order behavior,
including finite transients, singular and nonminimal presentations and
equivalent rows. No inverse recurrence is used. For $d>0$,
$F_{2t+2}\ge2^t$ gives
$h_0\le2\lceil\log_2(2d+1)\rceil$, and therefore
$2^{h_0}=O((d+1)^2)$. This shallow prefix class has polynomial size
per row/seed and cut; its row/seed factor is still $4^d$.

**Theorem 14.2 (uniform finite deterministic construction).** One
deterministic construction from $d,H$ alone outputs an ordered list
of exactly $T$ length-$H$ tapes, counting repetitions, satisfying
Theorem 13.2's strict $1/8$ guarantee. For an absolute constant $C$,
construction and complete finite-catalogue verification together use
at most

$$
 C4^d(d+H+2)^{24}
 \tag{ACR.49}
$$

binary operations and cumulative binary writes, with reusable scratch
at most $C(d+H+2)^8$ bits and exactly $TH$ output bits. All catalogue
generation and arithmetic are included; neither an expectation oracle
nor a precomputed good seed is supplied.

Proof. Define rational polynomials
$G_0(x)=G_1(x)=1$ and
$G_q(x)=x(G_{q-1}(x)+G_{q-2}(x))/2$ for $q\ge2$. The rank
recursion gives $G_q(x)=\mathbb E x^{D_q}$ for fair directions.
After fixing a tape prefix, if the walk is terminal at depth $a$ its
conditional moment is $x^a$; otherwise, at depth $a$ and residual
rank $q$, it is $x^aG_q(x)$. Unused directions remain independent
and fair. This identity holds despite all the prefix-dependent physical
orientations and is the computable source-specific conditional moment.

Temporarily let $U_1,\ldots,U_T$ be independent fair tapes. For each
constraint $f$ with mean $\mu_f=\mu_{\kappa_e(p)}$, put

$$
 \begin{aligned}
 S_f&=\sum_{t=1}^T f(U_t),&
 u_f&=\lfloor T(\mu_f+1/8)\rfloor,&
 \ell_f&=\lceil T(\mu_f-1/8)\rceil,\\
 \Psi&=\sum_f\left(\eta^{S_f-u_f}+\eta^{\ell_f-S_f}\right).
 \end{aligned}
 \tag{ACR.50}
$$

An error at least $1/8$ makes a summand at least one, so $\Psi<1$
implies every desired strict inequality. The exponential-moment step
is the classical bounded-variable concentration supplier, here with
its constants explicit: if $X\in[0,H]$, then
$g(\lambda)=\log\mathbb E e^{\lambda X}$ has
$g''(\lambda)=\operatorname{Var}_\lambda X\le H^2/4$.
The variance bound follows from $X^2\le HX$ under the tilted law.
Integrating twice gives
$\mathbb E e^{\lambda(X-\mathbb EX)}\le e^{\lambda^2H^2/8}$
for either sign of $\lambda$. For $\lambda=\log\eta$,
$1/(5H^2)\le\lambda\le1/(4H^2)$; independence of whole tapes
and the floor/ceiling errors give

$$
 \mathbb E\Psi
 \le2K_0\eta\exp\!\left(-\frac{11T}{640H^2}\right)
 \le\frac5{16}\exp\bigl((\log2-11/10)L\bigr)<1,
 \tag{ACR.51}
$$

where $K_0\le2^{L-3}$ and $\eta\le5/4$ were used. This is only
the starting bound, not yet a construction.

Fix all $TH$ tape bits, row by row. For each next bit compute both
conditional expectations of $\Psi$, and choose the smaller, with zero
breaking ties. Their average is the current conditional expectation.
For each $f$, independence between tapes factors each sign's moment
into $T$ terms. Each factor is obtained from the residual-rank identity
above at $x=\eta$ or $\eta^{-1}$, or from the completed depth. Hence
both choices are exactly computable rational numbers by streaming the
entire constraint catalogue. The final value remains below one by
(ACR.51). This applies the classical conditional-expectation and
pessimistic estimator method of [Raghavan, §§6.3--6.3.1][RRO-RAG]
to these particular physical functions. The generic method is an
intermediate supplier.

Here are explicit arithmetic and backing bounds. For a proposed row,
cut and physical path, use GPO (GPO.93)--(GPO.98) and Proposition
39.5's forward companion powers. At most $H$ path edges are needed;
their branch indices have $O(H+1)$ bits. A bound
$E=C_1(d+H+2)^5$ covers one prefix walk and its residual rank,
including its literal, descriptors, Fibonacci masses and initialization.
Presence filtering and the initial cone descriptor fit the same bound.
This uses a supplied hypothetical row only, never a hypothetical
prediction as an actual reply.

At $x=\eta$, store $G_q(x)$ with denominator $(2Q_0)^q$; at
$x=\eta^{-1}$ use $(2(Q_0+1))^q$. The recurrence computes their
integer numerators by scaling the two predecessor denominators, for
$0\le q\le H$. In a conditional factor, $a+q\le H$ when residual
rank is positive; completed depths are at most $H$. Thus every
conditional value in (ACR.50), for every bit assignment, has denominator
dividing the single known integer

$$
 \mathcal D=2^{TH}Q_0^{2T(H+1)}(Q_0+1)^{2T(H+1)}.
 \tag{ACR.52}
$$

The integer thresholds have magnitude at most $T(H+1)$. Both scaled
conditional sums fit within the explicit bit bound

$$
 J=8+TH+8T(H+1)\lceil\log_2(Q_0+1)\rceil
       +2\lceil\log_2(K_0+1)\rceil.
$$

Indeed the denominator's logarithm is at most
$TH+4T(H+1)\lceil\log_2(Q_0+1)\rceil$, and each unscaled
summand is at most $\eta^{T(H+1)}\le2^{T(H+1)}$.
Thus $J=O(TH\log(H+2)+\log(K_0+1)+1)$. Accumulate the sums as
integers over denominator $\mathcal D$, rather than multiplying
denominators across catalogue entries. Means, thresholds, powers,
scalings and comparisons are exact integer/rational operations. No
real logarithm or exponential needs to be computed: those occur only
in (ACR.51)'s proof.

With schoolbook arithmetic and repeated squaring, a conservative work
bound for the two choices over all bits is

$$
 C_3K_0TH\left[TE+(T+H+1)J^2\log_2(TH+2)\right].
 \tag{ACR.53}
$$

The first term recomputes every fixed tape prefix for each catalogue
entry. The second covers the rational tables, products, powers,
denominator scalings and streamed sums. Only the partial output list,
one candidate, rational tables and running sums need be resident;
their space is $O(TH+HJ+J+(d+H+2)^3)$. The row/seed counters and
all words are generated anew within this bill. Writing and initializing
every work bit is counted as an operation. Direct final verification
streams the same catalogue, evaluates all $T$ completed tapes for
each entry and compares their integer depth sum with the exact mean;
it costs $O(K_0T(E+J^2))$ further operations and no source Read.
Writing $s=d+H+2$, (ACR.48) gives $L=O(s)$, $T=O(s^3)$,
$K_0=O(4^d s^3)$ and $J=O(s^5)$. Substitution into (ACR.53)
and the verification bound gives (ACR.49); the displayed workspace
fits $O(s^8)$, with exponents independent of $d,H$. Output, scratch,
cumulative writes and verification are consequently all priced.
$\square$

## 15. Joint acquisition with polynomially many actual Reads

**Theorem 15.1 (one-run interaction and local-computation bills).** On
every input of Definition 9.1, earn $h,k,H$ as in Definition 13.1,
construct and verify Theorem 14.2's common list, and execute Theorem
13.2's root and early-child measurements. Run exactly the original fixed
$K_d(P)$ of Definition 9.1, compute $B_n$ explicitly, and install
$(P,K_d(P),n,B_n)$ before the same-source completed handoff. This
terminates with the authentic canonical record, under the full
stationarity and completion premises. On that same run,

$$
 \begin{aligned}
 U_{\rm source}&=0,\\
 Q_{\rm Read}&\le2k+(4d+1)TH,\\
 M&\le H,\\
 W_{\rm literal}&\le W_{\rm spine}+(4d+1)TH^2,
 \qquad W_{\rm spine}\le2k\,2^k.
 \end{aligned}
 \tag{ACR.54}
$$

Local bit work and cumulative bit writes are at most
$e_d+C4^d(d+H+2)^{24}$, and reusable data backing at most
$v_d+C(d+H+2)^8$ bits, with $e_d,v_d$ exactly as in Definition
9.1. The installed record has $O(d+n+1)$ data bits, including an
explicit $\Theta(n)$-bit $B_n$ field. Binding/grants, fixed code,
service, allocation, retention and completed handoff keep their actual
charges and durations. These bounds assert neither polynomial total
work in $d+n$ nor a bound on those physical tariffs.

Proof. The actual law has a padded catalogue presentation, and its
actual cut is at most the earned $H$. The common guarantee therefore
applies to every adaptively selected authentic cone. Theorem 13.2
earns $P,n$; at $d=0$ only the root is measured. Its proof charges
each walk through its terminal absence, with at most $H$ Reads and
literal length at most $H$. Adding the actual spine calls gives
(ACR.54). For each such Read the operand is materialized as a complete
physical word on the surviving root. There is no rank query,
equivalence query, clone, reset or source update.

The small old trees, depth counters, exact means, root rounding and
literal buffers have polynomial bit cost in $d+H$. Fibonacci addition
computes $B_n=F_{n+1}-1$ in $O((n+2)^2)$ bit work and cumulative
writes and $O(n+1)$ backing. Canonical synthesis generates rows by
the original enumerator, costing its actual $e_d,v_d$, and tests at
most $2^d$ rows in $O(2^d(d+1)^2)$ additional work. All of these
terms and the final writes fit the displayed local bounds. The
constructor's binary-counter catalogue is a different intermediate
computation: its rows do not replace the fixed first-passing canonical
row. In particular a zero stream at $d>0$ still receives precisely
$K_d(P)$, not a conveniently chosen minimal zero presentation.
Write the ready control only after the retained data writes finish.

Upon completed installation, GPO Definition 34.1 and Theorems
34.2--34.3 apply to this authentic synchronized memory and its separately
surviving binding/grants. They supply the same four mathematical views
and finite serial continuation; GPO Theorem 39.4 supplies the same-source
literal evaluator, including absent words. No arbitrary observer
journal, private register, rights or durations are recovered. The
stationary interval must extend through the entire catalogue work,
verification, canonical normalization and installation, not merely
through the last source Read.

Since $H\le2n-1$, (ACR.54) is polynomial in $d+n$ in its Read and
literal coordinates, while preparation retains $4^d$. Theorem 11.2
already has $O(\log(n+2)+4^d)$ Reads, $M\le2n-2$ and the sharper
local bound (ACR.39). The present list has a polynomial Read bound
but a larger polynomial dependence on $n$ and a charged exponential
catalogue. These are coordinate comparisons on the identical entrance;
they prove no all-input dominance or weighted optimum. Neither route
reduces the exact canonical enumerator's $e_d,v_d$ obligation.

The supplier subtraction is as follows. GPO §§27--29 provide the actual
source and mature-prefix separation; GPO §§34,39 provide synchronized
recovery and given-law physical addressing. ACR §§9--12 already provide
erased-law/cut acquisition, implicit separators and fixed-family
saturation. Native `atomic_navigation` and its private realization
lemmas in `NativeRankedNavigationCompiler` concern a fixed semantic
orientation, not the local physical beta child. `NativeBirthVectorDecoder`
concerns recursive complete-level codes, `ActualFibonacciSupportChain`
bounded native support agreement, and `NativeFullSourceProducer`'s
private traversal uses richer native replies to acquire the full tree.
Their owning Blueprint narratives preserve those domains. They provide
no substitute for the actual cone statistic and its priced construction
here. Classical concentration and conditional expectations are
intermediate suppliers in Theorem 14.2, not new generic results.
[Zuckerman][RRO-ZUC], Definitions 1.1--1.2, instead samples bounded
functions using a uniformly random seed. With domain length $H$ and
normalized function $f/H$, the needed error is $1/(8H)$; a per-function
random-seed guarantee alone selects no deterministic seed valid for
this whole catalogue. The additional mathematical content here is
repo-derived: the physical conditional-moment correspondence, its
finite exact construction and bill, and the obstruction below. $\square$

## 16. An admitted affine family reverses the first sibling sign

**Theorem 16.1 (a singular source and an exact affine certificate).**
For $k=\lceil\log_2(H+1)\rceil$, consider all $2^{k+1}$ tapes

$$
 u_i(v,c)=\langle v,\operatorname{bin}_k(i)\rangle\mathbin\oplus c,
 \quad1\le i\le H,\quad v\in\mathbb F_2^k,\quad c\in\mathbb F_2,
 \tag{ACR.55}
$$

where zero chooses physical $a$. This family fails even the early-sibling
sign consumer on an admitted mature source with an actually earned
$H$. Namely take $d=4$, coefficient row $(0,0,1,0)$ and seed
$(1,0,0,1)$, so $s_{i+4}=s_{i+2}$ at every $i\ge0$ and
$z_j=1$ exactly for $j=1$ or even $j\ge4$. At cut $n=14$ the
spine earns $h=8,H=17$, but the affine means in cones $a,b$ obey

$$
 \overline D_a=\frac{249}{32}<\frac{125}{16}=\overline D_b,
 \qquad z_1=1.
 \tag{ACR.56}
$$

Proof. This is an all-index singular order-four presentation, rather
than a recurrence asserted only after a transient. Its first two
terms are $1,0$; thereafter the odd indices $i\ge3$ are one and
the even indices are zero. Here $N(8)=7\le14$. Applying the actual
chronological descriptors gives successive births of
$a,a^2,\ldots,a^9$ at
$2,3,5,7,9,10,12,13,15$. Thus $a^8$ is present and $a^9$ absent
at cut 14; Proposition 9.2 really earns $H=17$, not an externally
chosen truncation. The root's bit one puts the larger child at $a$,
with ranks $13,12$ and true means
$\mu_{13}=16839/2048$, $\mu_{12}=7737/1024$.

For completeness, the following finite table certifies the affine
depths. Its columns are $D_a(v,0),D_b(v,0),D_a(v,1),D_b(v,1)$.
The row for $v+16$ equals that for $v$: every listed depth is at
most ten, before index 16 can use the fifth coordinate of $v$.

| $v$ | $D_a(v,0)$ | $D_b(v,0)$ | $D_a(v,1)$ | $D_b(v,1)$ |
|---|---|---|---|---|
| 0 | 7 | 8 | 9 | 7 |
| 1 | 8 | 7 | 8 | 7 |
| 2 | 7 | 9 | 7 | 8 |
| 3 | 10 | 6 | 9 | 6 |
| 4 | 7 | 9 | 8 | 8 |
| 5 | 9 | 7 | 9 | 8 |
| 6 | 7 | 9 | 7 | 8 |
| 7 | 8 | 7 | 7 | 8 |
| 8 | 7 | 8 | 8 | 7 |
| 9 | 8 | 7 | 8 | 7 |
| 10 | 7 | 10 | 7 | 9 |
| 11 | 9 | 6 | 8 | 6 |
| 12 | 7 | 10 | 8 | 9 |
| 13 | 8 | 7 | 8 | 8 |
| 14 | 7 | 10 | 7 | 9 |
| 15 | 8 | 7 | 7 | 8 |

Each entry is determined by this exact recursion, which also specifies
an independent way to check the certificate. Encode initial alpha by
zero and beta by one. Start with $(b_\varepsilon,\sigma_\varepsilon)
=(0,0)$ and use the actual GPO §39 chronological formula

$$
 \begin{aligned}
 \tau_p&=b_p+2-\sigma_p,\\
 j_p&=F_{\tau_p}+
   \sum_{\substack{qc\preceq p\\c=b}}
       F_{\tau_p-1-\tau_q+\sigma_{qa}},\\
 b_{pa}&=b_{pb}=\tau_p,\qquad
 \sigma_{pa}=z_{j_p},\qquad\sigma_{pb}=1-z_{j_p}.
 \end{aligned}
 \tag{ACR.57}
$$

In either starting cone, stop when $14-b_p+\sigma_p\le1$;
otherwise follow the next bit of (ACR.55) and count one edge. The
sibling sum in (ACR.57) prices no hidden rank sensor: it is a finite
integer calculation of the actual physical chronology. The given row,
seed, Fibonacci initial values and stopping rule determine every table
entry without unspecified source data. Summing the table and doubling
for $v+16$ gives depth totals $498,500$ over the 64 tapes, proving
(ACR.56). The true sibling difference is $1365/2048>0$, while the
affine difference is $-1/32$. Hence the sign decoder returns zero
for the actual first bit one. Its individual mean errors are
$-903/2048$ and $263/1024$, both exceeding $1/8$ in magnitude.
This refutes this named affine family and this consumer, not every
deterministic acquisition procedure or another tape construction.
$\square$

## 17. The remaining uniform-work question

**Definition 17.1 (a sufficient aggregation and normalization task).**
For the explicit potential (ACR.50), seek a deterministic procedure
which, from $d,H$ and each already fixed tape prefix, selects a next
bit whose conditional expectation does not increase, with one fixed
polynomial in $d+H$ bounding the work and cumulative writes for all
$TH$ selections together, and with polynomial backing and a priced
correctness guarantee. The rational precision is already polynomial;
Theorem 14.2 pays $4^d$ to aggregate the recurrence-addressed constraints.
A polynomial aggregation, or a different proved uniform constructor,
would remove that factor from this route. Evaluating these particular
sums is a sufficient task, not a necessary form of every solution.
Separately seek a polynomial procedure returning exactly the original
GPO29 first-passing canonical descriptor, including its seed, rather
than an arbitrary equivalent row. Neither task is settled here; no
hardness or exponential lower bound is asserted. The original
unknown-law/unknown-cut target with both construction and canonical
normalization charged in polynomial total work remains open.

[RRO-RAG]: https://www2.eecs.berkeley.edu/Pubs/TechRpts/1987/CSD-87-312.pdf
[RRO-ZUC]: https://www.cs.utexas.edu/~diz/pubs/sampler.pdf

## 追加锚（本行以下为增补区）

## 18. Exponential approximate Walsh norm on an actual order-one source

**Definition 18.1 (the physical sibling observable and its approximate norm).**
Keep the entire joint entrance of Definition 9.1, earn $h$ by Proposition
9.2, and set $H=2h+1$ as in Definition 13.1. For the actual chronological
parent $p_j$ of birth $j\le2d$, use Definition 13.1's paid physical walks
and define

$$
 g_{s,n,j}(u)=D_{s,n,p_ja}(u)-D_{s,n,p_jb}(u),
 \qquad u\in\{0,1\}^H.
 \tag{ACR.58}
$$

Zero chooses physical $a$, one chooses physical $b$, and the same tape
restarts at position one in each child cone. Both cones retain their
full original-root prefix in every literal submitted to the source.
The rank in Definition 10.1 is a proof variable, not an observed field.
Maturity and Theorem 13.2 supply present children, authentic parents
from previously earned bits, and

$$
 (2z_j-1)\mathbb E_U g_{s,n,j}
 =\mu_{n-t_j+1}-\mu_{n-t_j}\ge\frac12,
 \tag{ACR.59}
$$

where $U$ is uniform on the physical tape cube. For a real function $f$
on $\{0,1\}^v$, use normalized Walsh coefficients and put

$$
 \begin{aligned}
 \chi_A(x)&=(-1)^{\sum_{i\in A}x_i},&
 \widehat f(A)&=2^{-v}\sum_x f(x)\chi_A(x),\\
 \rho(f)&=\sum_{\varnothing\ne A\subseteq[v]}|\widehat f(A)|,&
 \rho_\epsilon(f)&=\inf_{\|p-f\|_\infty\le\epsilon}\rho(p).
 \end{aligned}
 \tag{ACR.60}
$$

The infimum ranges over all real functions on the cube, without a degree,
symmetry, coefficient-precision or algorithm restriction. The full
Fourier $\ell_1$ norm is $|\widehat f(\varnothing)|+\rho(f)$.
These are the standard normalized character conventions of
[Naor--Naor, §2][ACR-NN] and [Ada--Fawzi--Kulkarni, §2][ACR-AFK];
(ACR.60) explicitly separates the constant coefficient.

**Theorem 18.2 (an earned-horizon, approximation-robust obstruction).**
For every integer $k\ge2$, take the admitted actual source with public
$d=1$, coefficient $c_0=1$, seed $s_0=1$, and completed cut $n=2k+4$.
Its first chronological parent is $p_1=\varepsilon$ at $t_1=2$.
Proposition 9.2 actually earns

$$
 h=n-1=2k+3,\qquad H=2n-1=4k+7.
 \tag{ACR.61}
$$

Writing $g_k=g_{s,n,1}$ on this earned cube, for every
$0\le\epsilon<1/2$ one has

$$
 \rho_\epsilon(g_k)\ge
 \frac5{24}(1-2\epsilon)\left(\frac2{\sqrt3}\right)^k,
 \qquad
 \rho_{1/64}(g_k)\ge
 \frac{155}{768}\left(\frac2{\sqrt3}\right)^{(H-7)/4}.
 \tag{ACR.62}
$$

In particular no single polynomial $M(d,H)$ bounds
$\rho_{1/64}(g_{s,n,j})$ for all admitted actual sources, mature cuts
and required early siblings. This is a lower bound for the specified
approximate nonconstant Walsh norm.

Proof. The all-index recurrence $s_{i+1}=s_i$ with seed one produces
$z_j=1$ at every birth. Under GPO Definition 27.1, every actual split
therefore puts beta at $a$ and alpha at $b$. The root first splits at
update two, and its two child ranks at cut $n$ are $n-1,n-2$ by
Definition 10.1. Every proper prefix on the physical $a$-ray is initially
beta, so (ACR.7) gives $b(a^\ell)=\ell+1$ for $\ell\ge1$.
The actual spine acquisition consequently returns (ACR.61). The cut is
mature since $N(2)=4\le n$. Neither its law nor its age is entry advice.

In any cone of rank $q\ge2$ on this source, a physical $a$ step lowers
rank by one, and a physical $b$ step lowers rank by two. Both terminal
ranks zero and one have depth zero. For a tape $u$ put

$$
 A_0=0,\qquad A_\ell=\sum_{i=1}^\ell(1+u_i)\quad(0\le\ell\le H),
 \qquad T_m=\min\{0\le\ell\le H:A_\ell\ge m\}\quad(0\le m\le H).
 \tag{ACR.63}
$$

For $q\ge1$ its actual terminal depth is $T_{q-1}$: before the first
crossing the residual rank is at least two, and at the crossing it is
zero or one. For the two child cones the needed crossings occur within
$H$ positions, since all increments are at least one and the largest
threshold is $n-2<H$. Thus, with the same locally restarted physical
tape in the two cones,

$$
 g_k(u)=T_{n-2}-T_{n-3}
       =\mathbf1_{\{A_\ell=n-3\text{ for some }0\le\ell\le H\}}.
 \tag{ACR.64}
$$

Indeed a hit of $n-3$ requires exactly one more step to cross $n-2$;
an overshoot of $n-3$ is exactly $n-2$, crossing both thresholds at
once. This derives the observable from actual support and the actual
first parent. It introduces no rank or label sensor.

Restrict the first $k$ coordinates to free $x\in\{0,1\}^k$ and fix
all remaining physical directions to $a,b,a,b,\ldots$ through position
$H$. Write $w=|x|$. At the end of the free block, $A_k=k+w\le2k$,
strictly below $n-3=2k+1$; no earlier hit is possible. The remaining
distance is $k+1-w$. The alternating tail has partial sums
$0,1,3,4,6,7,\ldots$, precisely the nonnegative integers with residues
zero or one modulo three. Its $H-k=3k+7$ positions suffice even to
cross the larger remaining threshold $k+2$. Hence this coordinate
restriction $R$ of the actual tape cube satisfies

$$
 g_k(Rx)=f_k(x):=1-\mathbf1_{\{|x|\equiv r_k\pmod3\}},
 \qquad r_k\equiv k-1\pmod3.
 \tag{ACR.65}
$$

This substitution is used only in the norm proof; it is not a claim
that the restricted tape law is uniform on the original cube.

Here is the restriction inequality with its constant term accounted
for. For any real $p$ on the original cube and fixed tail $v$, expansion
in characters gives, for every $A\subseteq[k]$,

$$
 \widehat{p(\cdot,v)}(A)=
 \sum_{B\subseteq\{k+1,\ldots,H\}}
       \widehat p(A\cup B)\chi_B(v),\qquad
 \rho(p\circ R)\le\rho(p).
 \tag{ACR.66}
$$

To prove the inequality, take absolute values and sum only over
nonempty $A$. The groups $A\cup B$ are disjoint for distinct $A$,
and each such group contains only nonempty original supports. The
original constant can contribute only to the restricted constant.
Uniform approximation error also cannot increase under $R$.

For completeness, the required approximation lower bound for this
specific modular restriction has an elementary dual proof. Let
$\omega=e^{2\pi i/3}$, $a=(1+\omega)/2$, $b=(1-\omega)/2$, so
$|a|=1/2$ and $|b|=\sqrt3/2$. The root-of-unity identity

$$
 I_r(x):=\mathbf1_{\{|x|\equiv r\pmod3\}}
 =\frac{1+\omega^{-r}\omega^{|x|}
             +\omega^{-2r}\omega^{2|x|}}3
 \tag{ACR.67}
$$

gives $\widehat{\omega^{|x|}}(A)=a^{k-|A|}b^{|A|}$ by factoring
the uniform sum into its $k$ coordinates. The other term is its
complex conjugate after multiplication by its phase. Thus, for every
nonempty $A$,

$$
 \begin{aligned}
 |\widehat f_k(A)|
 &\le\frac23(1/2)^{k-|A|}(\sqrt3/2)^{|A|}
 \le\frac23(\sqrt3/2)^k,\\
 \left|\pi_k-\frac13\right|&\le\frac2{3\,2^k},\qquad
 \pi_k:=\mathbb E_U I_{r_k}\in[1/6,1/2],\qquad
 \operatorname{Var}_U(f_k)=\pi_k(1-\pi_k)\ge\frac5{36}.
 \end{aligned}
 \tag{ACR.68}
$$

The estimate for $\pi_k$ is (ACR.67) at the empty Fourier support;
its stated interval uses $k\ge2$. Set $\psi=f_k-\mathbb E_U f_k$.
Then $\mathbb E_U\psi=0$, $\mathbb E_U f_k\psi=\operatorname{Var}_U(f_k)$
and $\mathbb E_U|\psi|=2\operatorname{Var}_U(f_k)$, the last equality
following by evaluating the two values of the Boolean $f_k$.
For any real $q$ with $\|q-f_k\|_\infty\le\epsilon$, orthogonality of
the finite character basis gives

$$
 \begin{aligned}
 (1-2\epsilon)\operatorname{Var}_U(f_k)
 &\le\mathbb E_U q\psi
 =\sum_{A\ne\varnothing}\widehat q(A)\widehat\psi(A)\\
 &\le\rho(q)\max_{A\ne\varnothing}|\widehat f_k(A)|.
 \end{aligned}
 \tag{ACR.69}
$$

The first inequality uses the pointwise approximation at every input,
not merely correlation of $f_k$ with itself. Combining (ACR.68)--(ACR.69)
gives $\rho(q)\ge(5/24)(1-2\epsilon)(2/\sqrt3)^k$.
For any allowed approximant $p$ to $g_k$, take $q=p\circ R$ and apply
(ACR.65)--(ACR.66). This proves the infimum bound in (ACR.62), including
all real nonsymmetric approximants of unrestricted degree.

There is no unpriced constant-coefficient loophole: since $g_k,f_k$
take values in $\{0,1\}$, any such $p,q$ obey
$|\widehat p(\varnothing)|,|\widehat q(\varnothing)|\le1+\epsilon$,
in particular $65/64$ at the specified error. More strongly,
$\widehat\psi(\varnothing)=0$ removes their constants exactly from
(ACR.69). The bound is directly on $\rho$, rather than a full-norm
bound with its constant silently discarded. Substituting
$\epsilon=1/64$ yields $5\cdot31/(24\cdot32)=155/768$.
As $H=4k+7$ and $d=1$, the exponential dominates every polynomial in
$d+H$, proving the last assertion.

The Fourier framework and the distinction between exact and pointwise
approximate norm are classical; [Ada--Fawzi--Kulkarni, §2 and Theorem
3.4][ACR-AFK] study the approximate full norm for symmetric Boolean
functions. Their theorem is not needed for the explicit modular dual
above. The repo-derived content is the actual-origin stopping identity,
its earned-horizon restriction and the resulting quantified bound on
(ACR.58). This is ordinary conditional mathematics, with no additional
Lean certificate or worldwide novelty claim. $\square$

## 19. Lawful sign acquisition on the same full one-order class

**Theorem 19.1 (two constant tapes separate sign recovery from norm approximation).**
Under the entire joint entrance of Definition 9.1 with public $d=1$,
there is a source-blind zero-update consumer of the two tapes
$a^H,b^H$ which earns the unknown law and cut and actually installs
exactly $(P,K_1(P),n,B_n)$. It works on all three behaviors of
$\mathscr R_1$, at every mature cut $n\ge4$, including every source
and cut in Theorem 18.2. It requires no uniform pointwise approximant.

Proof. Reuse GPO Proposition 37.3's classification
$\mathscr C_1=\{0^\infty,10^\infty,1^\infty\}$ and its authentic
prefixes $00,10,11$. First acquire $h,k_\mathrm{sp}$ by Proposition
9.2, where $k_\mathrm{sp}=\lceil\log_2(h+1)\rceil$, and set $H=2h+1$.
Generate the two length-$H$ constant tapes, charging $2H$ data writes
and $O(H)$ generation work. For $j=1,2$, perform the two paid walks
in each child cone of the authentic $p_j$ and return one for a positive
sum of depth differences, zero for a negative sum. The walks are
exactly Definition 13.1's full-root literal procedure, including each
terminal absent-child test. There are eight walks in total.

At the first stage $p_1=\varepsilon,t_1=2$. After the first bit has
been earned, $p_2=a$ if $z_1=1$ and $p_2=b$ otherwise, with $t_2=3$.
This is the beta child of the actual root at update two, hence the sole
old beta parent at update three. No current label, source-law input,
semantic port or later bit is used to choose it. This is the $d=1$
instance of Theorem 13.2's earned-parent construction.

In each of the two descendant cones being compared, every subsequent
branch has a common constant orientation: one for $1^\infty$, zero
for $0^\infty$ and $10^\infty$. For the impulse, its sole exceptional
bit is the original root's first birth, outside all these child cones.
For a rank-$q$ cone with this constant descendant orientation, following
the larger-rank port forever has depth $\max(q-1,0)$, and following
the other port forever has depth $\lfloor q/2\rfloor$. The first
formula subtracts one until rank one; the second subtracts two until
rank zero or one. Thus for the adjacent child ranks
$q=n-t_j+1\ge2$ and $q-1$, the two constant tapes give exactly

$$
 (2z_j-1)\bigl(g_{s,n,j}(a^H)+g_{s,n,j}(b^H)\bigr)
 =1+\left\lfloor\frac q2\right\rfloor
      -\left\lfloor\frac{q-1}2\right\rfloor\in\{1,2\}.
 \tag{ACR.70}
$$

Here a physical tape written with letters denotes its zero/one encoding
in (ACR.58). The same descendant orientation in both cones licenses the
adjacent-rank comparison. Both tapes are long enough by $H\ge n$.
The sums never vanish and have the actual orientation signs. Induction
therefore earns both bits; the impulse, constant zero and constant one
are all included, rather than only the obstruction's constant-one law.

Run exactly the original fixed $K_1(P)$, retaining its original row
ordering and seed. An equivalent minimal row is not substituted, even
on prefix $00$, for which either order-one coefficient might pass.
GPO Lemma 29.2 authenticates its complete behavior. The already earned
$h$ then permits the following paid age completion, with at most one
additional Read:

$$
 n=\begin{cases}
 h+1,&P=11,\\
 2h+\operatorname{Read}(ba^h),&P=00,\\
 2h-1+\operatorname{Read}(ba^{h-1}),&P=10.
 \end{cases}
 \tag{ACR.71}
$$

To verify these literals on the original root, apply (ACR.5)--(ACR.7).
For $00$, $b(a^\ell)=2\ell$ and $b(ba^h)=2h+1$, so the two possible
ages are $2h,2h+1$. For $10$, $b(a)=2$ and
$b(a^\ell)=2\ell-1$ for $\ell\ge2$; maturity gives $h\ge2$.
The possible ages are $2h-1,2h$, and $b(ba^{h-1})=2h$: the root's
$b$ child is initially alpha, branches at four, and each later $a$
proper prefix is initially alpha. For $11$, the spine birth formula
is $b(a^\ell)=\ell+1$. These computations prove (ACR.71) without an
age oracle or a richer reply. In the $10,h=2$ endpoint maturity already
excludes age three; the displayed paid Read remains valid and returns
one. No update occurs in any case.

Compute $B_n=F_{n+1}-1$ by forward integer addition and really write
$(P,K_1(P),n,B_n)$, its ready control and any requested forward phase
into the granted readable backing. Finish the actual handoff while the
same completed cut remains stationary. The installed canonical record
is precisely (ACR.25), so the same-source consumers of GPO §§34,39 apply
with their original binding/grant and execution premises.

The achieved same-run resource coordinates can be stated separately:

$$
 \begin{aligned}
 U_{\rm source}&=0,&
 Q_{\rm Read}&\le2k_\mathrm{sp}+8n+1,\\
 M_{\rm literal}&\le2n-2,&
 W_{\rm literal}&\le2k_\mathrm{sp}2^{k_\mathrm{sp}}+8n^2+n.
 \end{aligned}
 \tag{ACR.72}
$$

Every walk uses at most $n$ paid Reads and literals of length at most
$n$, by (ACR.7), including its terminal test. The spine has its actual
overshoot $2^{k_\mathrm{sp}}\le2h\le2n-2$ and the traffic of Proposition
9.2. The final age literal has length at most $h+1\le n$.
These facts give (ACR.72); computed depths never replace paid calls.

In the binary-operation model, one realization including tape generation,
all full-literal copies, counters, sums, arithmetic, initialized scratch
and cumulative data writes has work
$e_1+O((n+2)^2\log_2(n+2))$ and reusable owned data backing
$v_1+O(n+1)$ bits. Here $e_1,v_1$ are the actual original canonical
enumeration costs of Definition 9.1, not a newly ordered enumeration.
To obtain these bounds, reuse one $O(n)$-bit literal buffer and the two
tapes. Depth and length counters have $O(\log(n+2))$ bits; the eight
walks and spine use the number of calls in (ACR.72), with $O(n)$ copying
and at most $O(n\log(n+2))$ local bit work per call. Forward Fibonacci
addition uses $O(n^2)$ work and cumulative writes with $O(n)$ resident
bits. Testing the at most two order-one rows, computing an optional
phase by forward powers, and actually installing the remaining fields
fit the same bounds. The explicit $B_n$ requires $\Theta(n)$ final
binary writes, with $O(n+1)$ final data writes overall; it is not
replaced by a short unevaluated Fibonacci expression.

Actual root/grant acquisition, source generation and material, fixed
code and its installation, service, backing allocation and lifetime,
retained write tariffs and completed handoff retain their separate
actual charges. In particular (ACR.72) is not a physical-duration bound.
The stationary interval covers tape preparation, every calculation,
Read, intermediate write, canonical normalization, final write and
handoff. Fresh owned growing backing, reliable completion and finite
local progress remain the premises of Definition 9.1.

This is a restricted-class separation between a strong analytic
requirement and this sign consumer. Theorem 11.2 already acquires all
of $\mathscr R_d$, including $d=1$, with its stated finite-enumeration
bill; no improvement on that acquisition theorem or optimality of
(ACR.72) is asserted. GPO Proposition 37.3 supplies the class and early
parents, not an unknown-cut stationary acquisition at arbitrary $n$.
The additional conclusion is that the two constant tapes suffice on
that whole class despite (ACR.62). $\square$

## 20. The failed sufficient bridge and the unchanged full-class task

**Proposition 20.1 (scope of the analytic obstruction).** For the physical
observables (ACR.58), the following sufficient route to sign recovery
has a false uniform polynomial-norm premise. Suppose a distribution
$\nu$ on length-$H$ tapes has $|\mathbb E_\nu\chi_A|\le\eta$ for every
nonempty $A$, and $\|p-g_{s,n,j}\|_\infty\le\epsilon$. Then

$$
 |\mathbb E_\nu g_{s,n,j}-\mathbb E_U g_{s,n,j}|
 \le2\epsilon+\eta\rho(p).
 \tag{ACR.73}
$$

Consequently $\epsilon=1/64$ and $\eta\rho(p)\le1/64$ preserve the
sign in (ACR.59), with signed mean at least $29/64$. But the premise
that all these observables have $\rho(p)\le M(d,H)$ for one fixed
polynomial $M$ is refuted by Theorem 18.2.

Proof. The standard small-bias estimate, in the conventions of
[Naor--Naor, §2][ACR-NN], follows by expanding $p$ in normalized
characters. The constant cancels between the two probability laws;
each nonconstant expectation is bounded by $\eta$, so their total
contribution is at most $\eta\rho(p)$. The two pointwise approximation
errors each contribute at most $\epsilon$, proving (ACR.73).
Combine with (ACR.59). This valid implication supplies no polynomial
norm bound of its own, and (ACR.62) disproves that universal premise.

For a specified common nonempty multiset $\mathcal A$ of tapes
constructed from $d,H$ alone, this equal-weight sign consumer instead
needs only

$$
 (2z_j-1)\sum_{u\in\mathcal A}g_{s,n,j}(u)>0
 \quad\text{for every admitted actual }(s,n),\ j\le2d
 \text{ in its earned bracket }n_0\le n\le H.
 \tag{ACR.74}
$$

These are necessary and sufficient inequalities for the signs returned
by this particular consumer at the authentic early parents. Simultaneous
validity licenses their inductive choice by Theorem 13.2; it is not a
minimality claim among all legal acquisition protocols. Equation
(ACR.70) proves them on the entire $\mathscr R_1$ class using two tapes.
For those tapes all even-size nonempty parities have bias one when
$H\ge2$, so this construction is not a small-bias construction.
No pointwise norm premise is needed for (ACR.74).

Given its displayed target $n-3$, (ACR.64) itself has a direct exact
evaluator with $O(H)$ counter steps and an $O(\log(H+2))$-bit running
sum; this supplied-target evaluation is not erased-cut acquisition.
Its exponential approximate
Walsh norm is compatible with a short exact evaluator and with the
lawful acquisition of Theorem 19.1. The obstruction proves no lower
bound for arbitrary representations, circuits, approximation algorithms,
samplers or legal acquisition protocols. It neither denies finite
exact Fourier expansions nor rules out a different successful small-bias
use. A one-sided minorant requirement, such as
$\ell\le(2z_j-1)g_{s,n,j}$ with positive uniform mean and small
$\rho(\ell)$, is a different condition: the two-sided error step in
(ACR.69) does not follow from that requirement. No existence or
impossibility result for such minorants is supplied here. $\square$

**Definition 20.2 (the retained acquisition and normalization gaps).**
For the full original $\mathscr R_d$, the remaining uniform-work task
is to construct and enumerate a common sign-correct tape family, or
another legal acquisition procedure, with total bit work, preparation,
literal traffic, writes and owned backing bounded by fixed polynomials
in $d+n$, and with the unknown law and cut both acquired. A common
family has to satisfy (ACR.74) on the entire authentic class, including
singular, nonminimal and finite-transient behaviors; the order-one
result does not restrict that class. Exact installation still requires
the original $K_d(P)$, with its original ordering and seed, and its
separately charged $e_d,v_d$ until a suitable polynomial normalization
procedure is established. An arbitrary equivalent passing row does
not discharge that exact output obligation.

Theorem 14.2's finite-catalogue constructor and Theorem 15.1's
polynomial-Read acquisition remain suppliers with their stated $4^d$
preparation cost; their moment construction does not assume the
polynomial approximate norm refuted here. Theorem 11.2 retains its
own finite candidate comparison and costs. Their published conclusions
are not replaced by (ACR.62). The source-specific mean and earned-parent
proofs of §13 are reused in (ACR.59), without duplicating the constructor
or affine certificate of §§14--16.

The native `NativeRankedNavigationCompiler.atomic_navigation` and its
private realization helpers concern fixed semantic orientation;
`ActualFibonacciSupportChain` and its proof-local recurrence establish
native support comparisons. `NativeBirthVectorDecoder` concerns its
recursive birth codes, and `NativeFullSourceProducer`'s private traversal
uses richer native replies. `NativeFibonacciStaticScan`'s private
execution and cost helpers retain their supplied address lists. Their
owning Blueprint narratives have the same boundaries. They supply
neither the unknown local physical orientations nor (ACR.62).
The Walsh functions and bounded-degree spaces in
`D5/S3/Combinatorics/IsingUniquenessSets.lean` supply standard character
algebra, not an approximate norm bound for this actual stopping function.
No fresh formal certification of these applications is asserted.
The new source-specific results leave full-class polynomial sign-family
construction, total acquisition and exact canonical normalization
unresolved; no universal acquisition impossibility follows.

[ACR-NN]: https://www.wisdom.weizmann.ac.il/~naor/PAPERS/bias.pdf
[ACR-AFK]: https://arxiv.org/pdf/1704.03176v1

## 追加锚（本行以下为增补区）

## 21. Source-faithful Hankel fibres, typed normalization, and conditional ordinal access

**Definition 21.1 (row, seed, and canonical descriptor).** For $d\ge1$, let
$P=(\zeta _0,\ldots,\zeta _{2d-1})$ be the actually acquired prefix,
with $\zeta_i=z_{i+1}$ in Definition 9.1. Put

$$
 H(P)_{ij}=\zeta_{i+j},\qquad y(P)_i=\zeta_{i+d}
 \quad(0\le i,j<d).
 \tag{ACR.75}
$$

Let $s_d(P)=(\zeta _0,\ldots,\zeta _{d-1})\in\mathbb F_2^d$ be the
original first-$d$ seed, and let $\rho_d$ be the same fixed bijective
coefficient-row enumeration used by Definition 9.1. Define the row
projection

$$
 \kappa_d(P)=\rho_d(i_P),\qquad
 i_P=\min\{i<2^d:H(P)\rho_d(i)=y(P)\},
 \tag{ACR.76}
$$

and define the full descriptor

$$
 \operatorname{EN}_d(P)=\bigl(\kappa_d(P),s_d(P)\bigr)\in
 \mathbb F_2^d\times\mathbb F_2^d.
 \tag{ACR.77}
$$

Thus $K_d(P)$ in the original target is this full descriptor:
$K_d(P)=\operatorname{EN}_d(P)$. Its first component is the original
first passing row; its second component is copied from the authentic
prefix and is never fabricated from that row. For $d=0$, set
$\operatorname{EN}_0(\varnothing)=(\varnothing,\varnothing)$, the
original zero descriptor.

For $c\in\mathbb F_2^d$, write

$$
 p_c(E)=E^d-\sum_{j<d}c_jE^j.
 \tag{ACR.78}
$$

**Theorem 21.2 (the exact all-index affine fibre).** Let $P$ be the
authentic first $2d$ values of a stream in $\mathscr R_d$, let $m_P$ be
its monic least all-index annihilator, and put $r=\deg m_P\le d$; for
the zero stream take $m_P=1$ and $r=0$. Then

$$
 \{c\in\mathbb F_2^d:H(P)c=y(P)\}
 =\{c\in\mathbb F_2^d:m_P\mid p_c\},
 \tag{ACR.79}
$$

and

$$
 \operatorname{rank}H(P)=r,\quad
 \left|\{c:H(P)c=y(P)\}\right|=2^{d-r}.
 \tag{ACR.80}
$$

The assertion includes singular companion recurrences, nonminimal
presentations, finite transients, and the zero stream; it does not
assume a nonzero constant coefficient or an invertible transition.

Proof. The equation $H(P)c=y(P)$ is exactly the order-$d$ recurrence
with seed $s_d(P)$ evaluated at the next $d$ positions. A passing row
therefore generates a member of $\mathscr R_d$ agreeing with the
authentic stream in its first $2d$ values. GPO Lemma 29.2 makes the two
all-index streams equal, so $p_c$ annihilates the authentic stream.
Conversely, an all-index annihilator of degree $d$ gives the displayed
Hankel equations. If an annihilator $p$ is divided by the monic $m_P$,
the remainder also annihilates the stream; minimality forces the
remainder to vanish. This proves (ACR.79), including the cases in which
$m_P$ has zero constant coefficient.

For the rank, every row of $H(P)$ after the first $r$ rows is an
$\mathbb F_2$-linear combination of those rows by the order-$r$
recurrence, so the rank is at most $r$. If the leading $r\times r$
Hankel block had a nonzero column relation, the associated nonzero
polynomial $q$ of degree $<r$ would produce a sequence $q(E)s$ whose
first $r$ values vanish. The sequence $q(E)s$ satisfies the same
order-$r$ recurrence, so forward induction makes it identically zero,
contradicting minimality. Hence the leading block has rank $r$, and so
does $H(P)$. The consistent binary system then has affine dimension
$d-r$, proving (ACR.80). For $r=0$, $H(P)=0$ and $y(P)=0$, so the same
statement gives $2^d$ passing rows. Consequently, on this entire
zero-stream fibre, for every original enumeration,
$\kappa_d(0^{2d})=\rho_d(0)$ and
$\operatorname{EN}_d(0^{2d})=(\rho_d(0),0^d)$; the row need not be
zero. The empty descriptor belongs to the separate $d=0$ case. $\square$

The finite-prefix minimal-synthesis supplier used below is Massey,
*Shift-Register Synthesis and BCH Decoding*: its §II LFSR length setup
and its §III Theorem 3 with corollary ([MAS]). That result supplies the
shortest shift-register synthesis and the $2r$-symbol uniqueness
threshold. It is used here as
an intermediate supplier for this source-specific fibre theorem; it is
not evidence for a count of nonsingular Hankel blocks, and no such
incidental count is claimed.

**Corollary 21.3 (the full-domain hybrid normalizer).** Once the
authentic prefix has been earned, compute the exact rank of $H(P)$. If
$r=d$, solve the single system $H(P)c=y(P)$ and return

$$
 (c,s_d(P))=\operatorname{EN}_d(P).
 \tag{ACR.81}
$$

The solution is unique, so this row is the same first row selected by
$\rho_d$, whatever that enumeration is. If $r<d$, run the original
$\rho_d$ first-passing enumeration and return
$(\kappa_d(P),s_d(P))$. Keep the $d=0$ zero descriptor. Thus every
branch returns the original order-$d$ row together with the original
first-$d$ seed, including deficient-rank and finite-transient fibres.
No entrance assumption or physical source action is added.

**Theorem 21.4 (typed local interreductions under the original
enumeration).** Fix $d\ge1$. Let

$$
 \mathcal M_d=\{m\in\mathbb F_2[E]:m\text{ monic},\ \deg m\le d\},
$$

and for $m\in\mathcal M_d$ define the row-valued task

$$
 \operatorname{FM}_d(m)=\rho_d(i_m),\qquad
 i_m=\min\{i<2^d:m\mid p_{\rho_d(i)}\}\in\{0,\ldots,2^d-1\}.
 \tag{ACR.82}
$$

For $r=\deg m>0$, let $\iota_r=0^{r-1}1\in\mathbb F_2^r$; set
$\iota_0=\varnothing$ for $m=1$. Let $s^{m}$ be the all-index
stream generated by $m$ from the initial $r$ values $\iota_r$ (and the
zero stream when $r=0$), let

$$
 P_m=(s^m_0,\ldots,s^m_{2d-1}),\qquad
 \sigma_{m,d}=(s^m_0,\ldots,s^m_{d-1}),
 \tag{ACR.83}
$$

and regard $\operatorname{EN}_d(P_m)$ as a value in
$\mathbb F_2^d\times\mathbb F_2^d$. The two exact reductions are

$$
 \begin{aligned}
 R_{P\to m}(P)&=\bigl(\operatorname{FM}_d(m_P),s_d(P)\bigr),\\
 R_{m\to P}(m)&=\operatorname{EN}_d(P_m)
   =\bigl(\operatorname{FM}_d(m),\sigma_{m,d}\bigr).
 \end{aligned}
 \tag{ACR.84}
$$

The first map has row output in its first component and the authentic
seed in its second; the second has the same row type and the explicitly
generated order-$d$ seed in its second. In particular,
$\pi_1R_{P\to m}(P)=\kappa_d(P)$ and
$\pi_1R_{m\to P}(m)=\operatorname{FM}_d(m)$. The reverse input
$P_m$ is a constructed input to this local normalization reduction
only; it is never substituted for the physical source prefix.

Proof. Run the Berlekamp--Massey LFSR synthesis on the $2d$ bits of
an authentic $P$. In Massey's connection-polynomial convention, retain
the shortest register length $r$ and reverse the coefficient convention
to the forward-shift polynomial $m_P(E)=E^rC(E^{-1})$, padding the
trailing zero coefficients when the recurrence is singular. The output
is then a shortest recurrence for the finite prefix; since
$\deg m_P\le d$, the $2r\le2d$-symbol uniqueness supplier cited above
and GPO Lemma 29.2 force it to be the least all-index annihilator.
Equation (ACR.79) then gives the first component of $R_{P\to m}$,
while the second is copied verbatim from $P$.

For the reverse map, the recurrence with initial values $\iota_r$ is
annihilated by $m$. If a nonzero polynomial $q$ of degree $t<r$ were an
annihilator, evaluate $q(E)s^m$ at index $r-1-t$: its leading term sees
the unique one at index $r-1$, while every lower term sees a zero in the
initial prefix. This is impossible. Thus $m$ is the least annihilator,
even when its constant coefficient is zero and the stream has a finite
transient. Theorem 21.2 identifies the passing rows with the monic
degree-$d$ multiples of $m$ in the very same order $\rho_d$, proving the
first component of $R_{m\to P}$; its second component is exactly the
constructed $\sigma_{m,d}$. For $m=1$ and every $d\ge1$, the
constructed stream is zero, every degree-$d$ monic polynomial is a
multiple of $1$, and therefore
$\operatorname{FM}_d(1)=\rho_d(0)$ and
$\operatorname{EN}_d(P_1)=(\rho_d(0),0^d)$. This is the same identity
on every authentic zero-stream input, not a choice of a new first row.
For example, $d=1$, $\rho_1=(1,0)$ gives descriptor $(1,0)$.
Only $d=0$ has the empty descriptor; the synthetic seed in the reverse
map is still distinct in provenance from the acquired seed. $\square$

The reductions have polynomial local overhead in $d$ besides their one
call to the other row/descriptor task; that call retains its own costs,
including the original enumeration when used. The following local model
makes the overhead executable without a fixed address-width assumption.
Use a fixed finite number of sequential binary tapes, with explicit end
markers and finitely many tracks. One symbol read/write or one-cell head
move costs one unit of bit work. Every written bit, including scratch,
indices, counters, markers and control, counts cumulatively; reusable
backing counts every visited tape cell, including blank cells traversed.
Each symbol has a fixed-size binary encoding. There is no random access,
head teleportation, implicit integer register, or free relocation.
Integers are binary strings on tapes, and copying or returning a head
across a string costs its actual scans. Allocation and actual physical
writes retain their separate tariffs.

For the $d$-local reductions put
$\ell_d=\lceil\log_2(64(d+2)^4)\rceil$. This suffices to represent
all local array positions, lengths and polynomial-loop counters; it is
not an address width imposed on other routines. A requested access to
an $M$-bit local array can be implemented by scanning from its left
marker with a binary position counter, then returning the head. With
$\ell$ bits sufficient for its positions and loop indices, this costs
$O((M+1)\ell^2)$ work and cumulative writes and $O(\ell)$ counter
backing. Counter increments, comparisons, address arithmetic in the
index description, initialization and return scans are included. This
loose bound follows by at most $M+1$ cell visits, with $O(\ell^2)$
bit work and writes for each counter operation; it does not grant a
unit-cost array access.

A Berlekamp--Massey pass uses three $O(d+1)$-bit work arrays and
$O(d^2)$ binary updates. Its complete local costs, including scan and
counter writes, consequently satisfy

$$
 C_{\rm BM}(d)=O((d+1)^3\ell_d^2),\qquad
 W_{\rm BM}(d)=O((d+1)^3\ell_d^2),\qquad
 V_{\rm BM}(d)=O(d+1+\ell_d).
 \tag{ACR.85}
$$

Writing its polynomial output and copying the authentic seed are
included in these conservative bounds. Generating $P_m$ by the
recurrence, retaining its first $d$ bits, and copying the typed task
input/output obey the same work/write bound and $O(d+1+\ell_d)$
backing bound: there are $O(d^2)$ binary updates on $O(d+1)$ data.
All $O(d)$ generated data bits are really written; the larger cumulative
write bound also pays their intermediate accumulators, scans and
counters. A called task receives and returns explicit bit strings; its
own computation is not replaced by a unit-cost answer. In particular,
no supplied original-enumeration cost is declared polynomial here.

**Definition 21.5 (uniform affine ordinal-prefix access).** Interpret a
binary word $u\in\{0,1\}^t$ as its integer value $[u]_2$. The original
enumeration has the affine prefix-image property if a single uniform
procedure $\operatorname{Img}(d,t,u)$, for every $0\le t\le d$,
constructs an exact record

$$
 \operatorname{Img}(d,t,u)=(a_{d,t,u},B_{d,t,u},\mathsf{idx}_{d,t,u}),
 \quad
 A_{d,t,u}=a_{d,t,u}+\operatorname{im}B_{d,t,u},
 \tag{ACR.86}
$$

where

$$
 A_{d,t,u}=\left\{\rho_d(i):0\le i<2^d,
 \left\lfloor i/2^{d-t}\right\rfloor=[u]_2\right\}.
 \tag{ACR.87}
$$

The base $a$, an explicit basis matrix $B$ over $\mathbb F_2$, and the
ordinal index record $\mathsf{idx}$ are all returned, with exact
feasibility and no free feasibility bit. Let $C_{\rm img}(d)$,
$W_{\rm img}(d)$, and $V_{\rm img}(d)$ be uniform upper bounds over
$t,u$ for bit work including address generation, cumulative bits written
including retained output, and peak reusable backing, respectively.
These are costs of a uniform implementation in the serial local model
just specified, including every working and output tape, explicit record
encoding, index data, counter write and head return. The property
requires all three bounds to be fixed polynomials in $d$; all
source-independent index preparation is included in them. In particular,
$V_{\rm img}$ includes the returned record, whose length is no greater
than its visited backing. The record is delimited and explicitly parsed;
a large index record cannot be treated as a free constant-size object.

**Theorem 21.6 (constructive conditional canonical normalization).**
Assume Definition 21.5. For $d=0$ use the original zero descriptor. For
$d\ge1$, from an authentic $P$, first represent the fibre
in (ACR.79) by an affine base and kernel basis using exact Gaussian
elimination. At depth $t$, test the child prefix $u0$ by constructing
$\operatorname{Img}(d,t+1,u0)$ and intersecting its affine image with
the earned fibre. Retain $u0$ when the intersection is nonempty; if it
is empty, construct and retain $u1$. At depth $d$, the retained cell is
a singleton, and its row is exactly $\kappa_d(P)$. Append the unchanged
seed $s_d(P)$ to obtain $\operatorname{EN}_d(P)$.

At most two child images are constructed at each depth. Put

$$
 \ell_{\rm aff}=\left\lceil\log_2
 \bigl(64(d+2)^4+2V_{\rm img}(d)+2\bigr)\right\rceil.
$$

The image routine runs on its own counted tapes; the caller keeps only
one image at a time. Parsing its full record and copying its base and
basis into $O(d^2)$ caller data costs
$O((V_{\rm img}+(d+1)^2)\ell_{\rm aff}^2)$ work and cumulative
writes. All movements through its index record are paid even though
firstness uses the ordinal prefix, rather than an inverse-index oracle.
The prefix $u$ itself is an explicit at-most-$d$-bit word, not a
unit-cost ordinal register. Forming the intersection equations, including
the product $H B$, and Gaussian elimination require $O((d+1)^3)$
binary updates on $O((d+1)^2)$ data. The scan implementation above
therefore costs $O((d+1)^5\ell_{\rm aff}^2)$ work and cumulative
writes, with $O((d+1)^2+\ell_{\rm aff})$ caller backing. The bounds
include construction of the earned fibre, every feasibility test,
descriptor emission and the seed copy. Thus, for an absolute constant,

$$
 \begin{aligned}
 C_{\rm aff}(d)&\le C_1\left[(d+1)\left(C_{\rm img}(d)
    +\bigl(V_{\rm img}(d)+(d+1)^5\bigr)\ell_{\rm aff}^2\right)
    +(d+1)^5\ell_{\rm aff}^2\right],\\
 W_{\rm aff}(d)&\le C_1\left[(d+1)\left(W_{\rm img}(d)
    +\bigl(V_{\rm img}(d)+(d+1)^5\bigr)\ell_{\rm aff}^2\right)
    +(d+1)^5\ell_{\rm aff}^2\right],\\
 V_{\rm aff}(d)&\le V_{\rm img}(d)
    +C_1\bigl((d+1)^2+\ell_{\rm aff}\bigr).
 \end{aligned}
 \tag{ACR.88}
$$

These remain polynomials in $d$ under Definition 21.5; in particular the
image's working data and its caller's counters both fit the backing.

The final normalizer emits $2d$ descriptor bits and retains the original
$2d$-bit $P$; no affine feasibility result is treated as a proof without
its returned base and basis. The child-prefix induction proves exact
firstness: the fibre is nonempty, its ordinal cells partition at every
depth, and the chosen child is the first nonempty cell. This conclusion
is conditional on the stated property; the unspecified original
$\rho_d$ is not asserted to have it.

**Theorem 21.7 (source-faithful composition, charged writeback, and the
remaining boundary).** Run Theorem 15.1 unchanged through its authentic
$P$, earned $n$ and $H$, including Theorem 14.2's $4^d$ catalogue
preparation, every actual Read and literal, all grants and stationarity.
Let $(C_{\rm sup},W_{\rm sup},V_{\rm sup})$ denote exactly the already
charged non-normalization supplier terms of that theorem: the physical
acquisition, source-independent catalogue and measurement work, and
their writes and backing. This notation removes only the old final row
search, the explicit Fibonacci construction of $B_n$, and the final
payload write from that supplier bill; it does not remove or reprice any
source action, literal, grant, catalogue entry, or physical tariff.

The composed access model retains the original suppliers as costed
subroutines in their supplied execution model and uses the serial
controller above for the new local routines. It does not claim a free
simulation of a supplier in the tape model. Their bit-work terms retain
all their own original operand/address operations, and their backing
terms include those operands. Transfers between the two parts are
additional operations. Here is a conservative explicit transfer rule.
For a supplier with $v$ backing bits returning $q$ explicit bits, each
returned bit is copied to a local tape. Its supplied output address,
length and running index are represented, not machine integers. At
most $b=O(v+q+1)$ bits suffice for those operands: existing address
operands are already part of $v$, and the additional index needs only
$O(\log(q+2))$ bits. A variable-length bit-addressed transfer uses
$O(b^2)$ bit work and writes per bit, including forming/copying its
address, accessing the supplied output cell, advancing its binary
counter and writing the destination tape. There is no parallel-word
operation. Transfer scratch takes $O(b)$ bits; its address registers
and backing are counted. Every referenced cell belongs to already
charged supplier backing; the variable address can encode each supplied
reference, independently of $d$ or $n$. No cells are accessed through an
uncharged window. The supplier's original generation is charged once and this
extra read/copy is charged separately. If it already emits sequential
output, the actual transfer can be smaller. Physical access, allocation
and write tariffs remain the actual ones in either implementation.

In particular, export the earned $P,n$ (and any needed finite control)
from the acquisition supplier, with the following loose bounds, also
charging the retained local copies:

$$
 \begin{aligned}
 C_X,W_X&=O\bigl((d+n+1)(V_{\rm sup}+d+n+2)^2\bigr),\\
 V_X&=O(V_{\rm sup}+d+n+1).
 \end{aligned}
$$

This transfer does not reread the physical source or change a literal.
Its backing may be reused after the export. The new local routines
then work on tapes and need no absolute address into the earlier
catalogue. In particular, the old supplier retains its $4^d$
preparation; these interface terms do not assert a faster preparation.

Use Corollary 21.3 for the final normalization. On a full-rank fibre,
Gaussian elimination with the charged scans gives

$$
 (C_{\rm norm},W_{\rm norm},V_{\rm norm})
 =\bigl(O((d+1)^5\ell_d^2),O((d+1)^5\ell_d^2),
        O((d+1)^2+\ell_d)\bigr).
 \tag{ACR.89}
$$

On a deficient fibre, invoke the original fixed enumeration verbatim,
with its original $e_d,v_d$ and cumulative writes $\omega_d$.
Export each tested row to the tape controller using the transfer rule,
at an additional cost at most
$O((d+1)(v_d+d+2)^2)$ work and writes per row. The controller's
Hankel row test has at most $O((d+1)^2)$ binary updates on
$O((d+1)^2)$ data, and its rank computation was already charged.
A conservative bound for the added terms is therefore

$$
 \begin{aligned}
 C_{\rm norm}&\le e_d+O\left((d+1)^5\ell_d^2+
  2^d\bigl((d+1)^4\ell_d^2+(d+1)(v_d+d+2)^2\bigr)\right),\\
 W_{\rm norm}&\le\omega_d+O\left((d+1)^5\ell_d^2+
  2^d\bigl((d+1)^4\ell_d^2+(d+1)(v_d+d+2)^2\bigr)\right),\\
 V_{\rm norm}&\le v_d+O\bigl(v_d+(d+1)^2+\ell_d\bigr).
 \end{aligned}
 \tag{ACR.90}
$$

These terms include both the row-transfer scratch and all row-test
counter writes. The supplied enumeration costs are separate and are
not assumed polynomial in $d$. On full rank there is no enumeration
or row export. Under Definition 21.5, use (ACR.88) at every rank,
with no $e_d,\omega_d,v_d$ or enumerator-transfer term. At $d=0$
use the empty descriptor, with constant local normalization costs.

For the arbitrary earned cut, put
$L_n=\lceil\log_2(64(n+2)^4)\rceil$. Compute the cut field by
forward ripple-carry Fibonacci addition on serial tapes, followed by
explicit subtraction of one. All intermediate Fibonacci numbers through
$F_{n+2}$ fit $n+2$ bits since $F_{n+2}\le2^{n+1}$ for $n\ge0$.
A fixed number of buffers therefore takes $O(n+1)$ bits. Store $n$,
the iteration number, buffer lengths and scan indices as binary strings
of at most $L_n$ bits. Each of the $O(n+2)$ rounds costs
$O((n+2)L_n^2)$ work and writes: scan and ripple-add the buffers,
copy the next pair, reset each head by paid moves, and update the
counters. Growing/initializing the buffers and the final subtract-one
and output copy obey the same bound. This gives

$$
 (C_B(n),W_B(n),V_B(n))
 =\bigl(O((n+2)^2L_n^2),O((n+2)^2L_n^2),O(n+1+L_n)\bigr).
 \tag{ACR.91}
$$

Every intermediate carry, overwritten buffer and counter write is in
$W_B$. No $d$-only register represents $n$ or addresses this field:
a tape head reaches its $j$th cell by $j$ charged moves, and all visited
cells count as backing. This works for fixed $d=0$ or $1$ and arbitrarily
large finite $n$; neither an upper cut bound nor an integer-valued
unevaluated output is used.

Finally write the completed original payload

$$
 \bigl(P,\operatorname{EN}_d(P),n,F_{n+1}-1\bigr)
 =\bigl(P,K_d(P),n,F_{n+1}-1\bigr),
 \tag{ACR.92}
$$

and its ready control into the granted readable backing. Set
$L_{d,n}=\lceil\log_2(64(d+n+2)^4)\rceil$. The explicit record
has $O(d+n+1)$ data bits: $2d$ for $P$, $2d$ for row/seed,
$O(\log(n+2))$ for $n$, and $O(n+1)$ for the binary $B_n$
(which is $\Theta(n)$ as $n$ grows). Its final sequential copy,
field/control writes and the copy counters cost
$O((d+n+1)L_{d,n}^2)$ work and cumulative writes and
$O(d+n+1+L_{d,n})$ backing. The data writes alone are linear in
the record length; the displayed larger write bill also includes its
counter and control writes. Set ready only after all data, including any
requested phase, are installed.

If a forward phase is requested and $d>0$, compute it explicitly from
the selected original row and seed by forward binary powering
$C^{B_n}s_d(P)$. Scan the already computed binary exponent in a fixed
direction; there are $O(n+2)$ squarings/multiplications, not $B_n$
unit-cost iterations. Dense binary matrix multiplication has
$O((d+1)^3)$ binary updates on $O((d+1)^2)$ tape data, so the
same charged-scan construction gives additional bounds

$$
 C_\phi,W_\phi=O((n+2)(d+1)^5L_{d,n}^2),\qquad
 V_\phi=O((d+1)^2+L_{d,n}).
$$

The exponent tape is already in $V_B$ and is read by paid moves; matrix
buffers, copies, counters and intermediate writes belong to these phase
terms. The final $d$ phase bits are copied in the final-write term
above. For no requested phase or for $d=0$, take all phase terms zero.
No private actual generator state is recovered or inverted. Exclude this
optional computation from $C_{\rm sup},W_{\rm sup},V_{\rm sup}$
when adding these phase terms; otherwise use its already charged
supplier implementation and do not add them a second time.

With the optional phase charged in the new local part, the disjoint
work/write bill and conservative sum of peak backing bounds are

$$
 \begin{aligned}
 C_{\rm total}&\le C_{\rm sup}+C_X+C_{\rm norm}+C_B+C_\phi
                      +O((d+n+1)L_{d,n}^2),\\
 W_{\rm total}&\le W_{\rm sup}+W_X+W_{\rm norm}+W_B+W_\phi
                      +O((d+n+1)L_{d,n}^2),\\
 V_{\rm total}&\le V_{\rm sup}+V_X+V_{\rm norm}+V_B+V_\phi
                      +O(d+n+1+L_{d,n}).
 \end{aligned}
 \tag{ACR.93}
$$

The supplied work, every transfer, normalization, cut arithmetic, optional
phase and final copy are different operations; scratch reuse can only
reduce the backing sum. The old supplier retains every actual physical
Read/literal charge, catalogue entry, grant and stationarity premise.
The physical service, allocation, retention and handoff tariffs and
durations remain actual; these bit-operation bounds do not infer a
physical duration. In particular stationarity must cover the transfers,
all intermediate and retained writes, any requested phase and handoff.

The writeback is source-faithful because $P$ is the prefix earned from
the original unknown-law, unknown-cut source, and the hybrid changes no
source Read, source update, literal, grant, stationarity premise, or
canonical enumeration fallback. The reverse map in Theorem 21.4 remains
a constructed local input. A uniform polynomial total acquisition for
the full all-index class, including the original $4^d$ preparation and
its total resource contract, remains open. The affine-prefix property
for the unspecified original $\rho_d$ remains unproved, so the
conditional polynomial normalizer does not settle that general case.
$\square$

[MAS]: https://www.isiweb.ee.ethz.ch/archive/massey_pub/pdf/BI411.pdf

## 追加锚（本行以下为增补区）

## 22. Paid certificates for the authentic cut and chronological prefix

**Definition 22.1 (same-root certificate relation).** Retain Definition
9.1 in its entirety. In particular the authentic all-index bound is
$d$, the actual cut is mature, and the only source replies used here
are paid total physical-literal presence bits at the one surviving
stationary root. Earn $h,H=2h+1$ by Proposition 9.2. A proposed answer
is $(\nu,A)$ with $n_0\le\nu\le H$ and
$A=(a_1,\ldots,a_{2d})\in\{0,1\}^{2d}$; a malformed answer is
rejected before source interaction. Letters $a,b$ below remain the
physical ports; a numerical bit $a_j$ is not a port name.

For a present cone $p$ and a proposed rank $\nu\ge2$, a rank
certificate consists of physical suffixes $x,y$. Require
$|x|=\nu-1$ and $\operatorname{Read}(px)=1$. The additional tests are

$$
\begin{array}{c|c|c}
\nu&|y|&\text{required paid replies}\\
2k+1&k&\operatorname{Read}(pya)=0\\
2k&k-1&\operatorname{Read}(pyaa)=\operatorname{Read}(pyba)=0.
\end{array}
\tag{ACR.94}
$$

The checker does not assume that the supplied $y$ is present, and
does not consult a supplied rank or an estimated mean. All displayed
words are submitted literally to the original root. The root uses
$p=\varepsilon$. Thus it needs at most three certificate Reads.

After this root test, check the proposed prefix in increasing birth
order. For birth $j$ compute
$\tau_j=\min\{u\ge2:j\le F_{u+1}-1\}$ and reconstruct the old
labelled tree at cut $\tau_j-1$ using the proposed first
$B_{\tau_j-1}<j$ bits. Select its
$(j-B_{\tau_j-1})$th beta leaf in physical lexicographic order;
call its address $p_j(A)$. Put $t_j=\nu-\tau_j\ge1$ and
$c_j=a$ for proposed bit one, $c_j=b$ for proposed bit zero.
The birth witness is a suffix $v_j$ of length $t_j$, with required
reply

$$
\operatorname{Read}\bigl(p_j(A)c_jv_j\bigr)=1.
\tag{ACR.95}
$$

Accept exactly when every length, maturity, rank and birth test passes.
A transcript records the actual paid replies to these tests, rather
than predictions of them. Witness construction is outside this
checking relation and has its own work, writes, backing and any
discovery Reads.

**Theorem 22.2 (soundness, completeness and the terminal boundary).**
For every actual source and cut of Definition 9.1, the relation in
Definition 22.1 has an accepting certificate for $(\nu,A)$ exactly
when

$$
\nu=n,\qquad A=P=z_1\cdots z_{2d}.
\tag{ACR.96}
$$

Checking a supplied certificate uses at most $2d+3$ source Reads,
maximum literal length at most $\nu$, and literal traffic
$O((d+1)(\nu+1))$. A certificate has $O((d+1)(\nu+1))$ bits.
Checking has uniform polynomial local bit work, cumulative writes
and backing in $d+H+2$, including parsing and old-tree construction.
These statements include $d=0$, singular and nonminimal laws, and
finite transients in the all-index class. They do not distinguish
the two terminal ranks zero and one of a general present cone.

Proof. Definition 10.1 implies that a cone of rank $q\ge1$ has
maximum present suffix depth $q-1$, whereas rank zero has depth zero.
For $q\ge2$, following a rank-$(q-1)$ child until the final branch
attains depth $q-1$; either child of the final rank-two branch is
adequate. Every descent subtracts either one or two before it reaches
a terminal rank. In particular every word of length $\ell$ is
present whenever $q\ge2\ell$.

The positive length $\nu-1$ witness forces $q\ge\nu$. If
$\nu=2k+1$ and $q\ge\nu+1=2k+2$, every word of length $k+1$
would be present, contradicting the odd test in (ACR.94). If
$\nu=2k$ and $q\ge\nu+1=2k+1$, every length-$(k-1)$ prefix $y$
would be present with residual rank at least three. At least one of
its two children then has rank at least two, so at least one of
$yaa,yba$ is present. This contradicts the even tests. Thus a passing
rank certificate forces $q=\nu$ even when the supplied short prefix
was not separately queried. Conversely, at $q=\nu$, a longest path
supplies $x$. Repeatedly choose a rank-$(q-2)$ child for $y$: the
odd case ends at rank one after $k$ steps; the even case ends at
rank two after $k-1$ steps. The required absences follow. At $\nu=2$
the even prefix is empty and the tests are $aa,ba$ absent. Ranks
zero and one cannot pass any $\nu\ge2$ test and have identical
singleton presence supports. No terminal-rank sensor is inferred.

Applied to the root, this proves $\nu=n$. Suppose inductively that
the bits before $j$ have been authenticated. The old tree used in
Definition 22.1 is then the actual $X_{\tau_j-1}$. GPO Proposition
39.2 and the actual chronological rule make $p_j(A)$ the actual
birth parent, independently of every later bit. This old tree has
$2B_{\tau_j-1}+1\le2j-1$ nodes. Maturity gives
$\tau_j\le n_0-1\le n-1$, and $|p_j|\le\tau_j-2$.
At cut $n$ the original beta child has rank $t_j+1$, and the original
alpha child has rank $t_j$, where $t_j=n-\tau_j\ge1$. A wrong
proposed orientation therefore has no present suffix of length $t_j$;
a correct orientation has one. Hence (ACR.95) authenticates the
proposed bit. Conversely, for the authentic prefix, choose a longest
path in the larger child for each $v_j$. Induction proves (ACR.96)
and completeness. The birth literal has length at most
$\tau_j-2+1+n-\tau_j=n-1$.

Only the rank tests can require length $\nu$, at the endpoint
$\nu=2$. The number and lengths of the supplied words give the
Read, traffic and certificate-size bounds. Constructing each small
old tree, sorting or traversing its leaves in physical order, and
copying its literal are polynomial operations on explicitly stored
finite words. Sequential scans as in §21 pay for every index,
marker, intermediate copy and head return, so they retain polynomial
work and writes without a unit-cost address assumption. No recurrence
needs to be synthesized to check the relation. At $d=0$, the birth
loop and prefix are empty and the root certificate still identifies
every allowed $n\ge2$. All source-law qualifications follow because
the proof uses actual chronological replacement and maturity, not
invertibility or a minimal presentation. $\square$

**Corollary 22.3 (proper-candidate verification).** With $h,H$ already
earned as in Definition 22.1, let a candidate stream be explicitly
supplied by any homogeneous all-index recurrence
of presented order $r\le d$, with its seed, and a proposed mature
cut $\nu\in[n_0,H]$. There is a deterministic verifier using at most
$d+r+3$ paid Reads. Its witnesses can be constructed from this
candidate with polynomial local work, writes and backing in
$d+\nu+2$, without discovery Reads. It accepts exactly when the
candidate behavior and cut are the actual behavior and cut.

Proof. Construct the root witnesses in the candidate and check them
on the actual root. Then construct and check (ACR.95) for only the
first $d+r$ candidate bits. Length and maturity are valid because
$d+r\le2d$. A successful root test proves the actual cut; successful
birth tests authenticate these candidate bits by Theorem 22.2's
induction. The product of an actual monic annihilator of degree at
most $d$ and the candidate's monic degree-$r$ annihilator annihilates
their difference. Agreement on $d+r$ initial positions forces the
difference to vanish by forward induction, exactly as in GPO Lemma
29.2. Degree zero is allowed, and no shift is inverted.

For construction, candidate descriptors, chronological indices and
orientation bits along each longest or shortest witness are computed
by GPO (GPO.93)--(GPO.98) and forward companion powers. There are
$O((d+1)(\nu+1))$ edges to construct, indices have $O(\nu+1)$
bits, and Proposition 39.5 bounds their local evaluation polynomially.
Only the early old trees are expanded, never the whole cut-$\nu$
tree. A correct candidate supplies all the required witnesses.
An incorrect candidate cannot pass the authenticated-prefix argument.
Witness construction and the final certificate checks are separate
bills. This is a verifier for a supplied proper candidate, not an
equivalence oracle or a polynomial way to find that candidate. In the
general certificate relation a missing witness may also accompany a
correct answer: a failed test alone certifies neither a wrong bit nor
the position of a first disagreement. $\square$

## 23. Guarded acquisition with independent controller coins

**Definition 23.1 (supplemental coin entrance and bounded search).**
Keep all premises and source actions of Definition 9.1. Add a paid
observer-owned stream of independent fair local bits, independent of
the actual source, cut and prior controller state. Charge generated
and consumed bits, buffering, scratch and control writes. The coins
neither observe nor advance the source. The original entrance alone
does not assert this coin grant. The stationary interval covers every
realized operation through normalization, retained writes and the
actual completed handoff; an expected operation count supplies no
fixed-duration lease.

After earning $H$, put

$$
S=d+H+2,\quad L=2d+1,\quad m=256H,\quad
R=\min\{r\text{ odd}:r\ge\lceil\log_2(64(H+2))\rceil\}.
\tag{ACR.97}
$$

An estimate of a present cone is the median of $R$ block means,
each containing $m$ independent physical depth walks of Definition
13.1. Every walk uses fresh fair directions and includes its terminal
absence Read. Store integer block sums; division by the common $m$
is just a comparison convention. Only $R$ sums need be retained.

All search operations have the following guards. Every Read operand
is materialized as a complete original-root literal of length at most
$H$. A depth walk stops at its first absent-child test; it may never
submit a longer word or execute more than $H$ tests. Before estimating
a proposed child, test its presence and reject an absent start.
Before taking a search edge, test both child literals and reject unless
both are present. Compare fresh child estimates to choose a larger
or smaller child, with a fixed tie rule. If a required search edge
cannot be taken within these length and iteration bounds, return FAIL.
Each requested search path has its prescribed finite length; a guessed
rank never changes these bounds.

A cut attempt estimates the root, rounds $3\widehat\mu/2+2/3$
to the nearest integer with a fixed tie rule, and rejects a proposed
$\nu\notin[n_0,H]$. It constructs $x$ by $\nu-1$ successive
larger-child choices. It constructs $y$ by $k$ smaller-child choices
if $\nu=2k+1$, or $k-1$ such choices if $\nu=2k$. Finally it
executes the actual root certificate (ACR.94), including its positive
test. The cut is certified only if that certificate passes.

Once the cut and first $j-1$ bits are certified, a birth attempt
constructs the actual early parent as in Definition 22.1, estimates
its two children, and proposes the orientation of the larger estimate.
Starting at that proposed child, it constructs a suffix of exactly
$t_j=n-\tau_j$ edges by successive larger-child choices. It then
executes (ACR.95). Only a passing reply appends a certified bit. FAIL
leaves the certified cut and prefix unchanged. In particular a rejected
proposal creates no first-disagreement claim.

**Theorem 23.2 (uniform guarded-attempt success and its charges).**
For each fixed actual source and cut, condition on any past controller
history whose retained cut and prefix are certified. A fresh cut or
next-birth attempt in Definition 23.1 has success probability at least
$3/4$. Every accepted answer is exact on every coin tape, including
tapes on which estimates are inaccurate. Every attempt terminates,
including wrong-cut and incomplete-path branches. With absolute
constants, a single attempt has bounds

$$
\begin{aligned}
Q_A&\le C(H+2)^3R,&
J_A&\le C(H+2)^4R,& M_A&\le H,\\
\mathsf{coins}_A&\le C(H+2)^3R,&
C_A,W_A&\le CS^{12},&V_A&\le CS^3.
\end{aligned}
\tag{ACR.98}
$$

Here $Q$ counts actual Reads, $J$ counts literal traffic, $C$ counts
local bit work, $W$ counts every cumulative local bit write and $V$
counts peak visited backing, including coin buffers. These are
acquisition-control bounds in §21's sequential tape model; actual
coin service, physical Read, allocation and retention tariffs remain
separate charges.

Proof. Reuse the exact means (ACR.45). The variance $v_q$ of a fair
depth walk satisfies

$$
v_0=v_1=0,\qquad
v_q=\frac{v_{q-1}+v_{q-2}}2+
       \frac{(\mu_{q-1}-\mu_{q-2})^2}{4}\le\frac q6.
\tag{ACR.99}
$$

Indeed adjacent mean differences lie in $[0,1]$, including the
terminal pair; induction bounds the right side by
$(2q-3)/12+1/4=q/6$. At every queried present cone $q\le H$.
Chebyshev's inequality for the mean of $m=256H$ independent walks
gives probability at most $1/24$ for an error exceeding $1/8$.
If the odd median has error exceeding $1/8$, at least $R/2$ blocks
do. Independence of the blocks and a union bound over subsets give

$$
\Pr\{|\widehat\mu-\mu_q|>1/8\}
\le 2^R(1/24)^{R/2}\le2^{-R}
\le\frac1{64(H+2)}.
\tag{ACR.100}
$$

This uses the non-strict good event $|\widehat\mu-\mu_q|\le1/8$.
It does not replace a presence reply by a probabilistic assertion.

There are fewer than $4(H+2)$ estimates in one attempt. The cut
attempt uses one root estimate and at most two per edge of its long
and short searches; a birth attempt uses two initial estimates and
at most two per suffix edge. Condition on the history before the
first inaccurate estimate. Its cone is present and fixed by that
history, and its fresh block directions have the law just analysed.
Summing these conditional first-error probabilities shows that all
estimates are accurate with probability at least $15/16$. This
adaptive argument needs no independence between the chosen cones.

On that event root rounding is correct, since the non-strict version
of (ACR.47) still gives
$|3\widehat\mu/2+2/3-n|\le17/48<1/2$. At a branch of rank
at least three, the child ranks are distinct by at least one above
the terminal pair, and their mean gap is at least $1/2$. Two errors
of at most $1/8$ leave the correct sign. At rank two the child
means coincide, but either child completes a longest path's final
edge. A shortest path used here only selects children at ranks at
least three: its odd endpoint is rank one and its even endpoint is
rank two. Thus the correct cut supplies exactly the witnesses in
Theorem 22.2. For a birth attempt the initial ranks $t_j+1,t_j$ have
a mean gap at least $1/2$, even when $t_j=1$. The correct larger
child and a longest suffix pass (ACR.95). All relevant full words
have length at most $n$ and the guards never abort a good search.
Consequently success probability is at least $15/16$, hence at least
$3/4$. Off that event the guards still terminate the attempt, and
Theorem 22.2 makes every acceptance sound.

Each estimate has $mR$ walks, each at most $H$ Reads and $H$ coin
bits. There are $O(H+2)$ estimates. Child-start and search-edge
tests and final certificate tests add only $O(H+2)$ Reads; the
literal bound gives (ACR.98)'s traffic bound. Fair bits may be
generated one walk at a time and their buffer overwritten; no history
of the random walks is retained. Even an inaccurate estimate at an
arbitrary reached cone obeys these same limits.

For explicit local accounting, store the early tree using at most
$O((d+1)^2)$ bits, two $H$-letter search buffers, walk/literal
buffers, $R$ integer block sums, counters, the certified prefix and
the binary cut. Their total data is $O(S^2)$; $O(\log(S+2))$-bit
counters suffice for every polynomially bounded loop. An elementary
description uses at most $O(S^6)$ binary array operations: this
includes all $O(H^3R)$ walk tests and coin generations, full-literal
copying, child comparisons, sorting the $R$ block sums by explicit
integer comparisons, rounding, and rebuilding early trees. Replace
each array operation by an actual scan of at most $O(S^2)$ cells
with the paid counters of §21. Initialization, head returns, all
scratch, buffer, counter, marker and output writes then fit
$CS^{12}$ work and cumulative writes and $CS^3$ visited cells.
The loose exponents absorb $R=O(\log(H+2))$ and every counter scan.
No source history or unbounded address register is stored. $\square$

**Theorem 23.3 (zero error and the limit of uncapped retries).** Retry
a failed attempt with fresh coins until it succeeds, through the cut
and the $2d$ birth phases. Under Definition 23.1, no execution returns
an incorrect $(n,P)$, termination is almost sure, and the expected
attempt count is at most $4L/3$. Expected acquisition work, cumulative
writes, Reads, literal traffic and coin consumption are polynomial in
$d+H+2$; reusable backing is polynomial on every execution. This
uncapped protocol has no every-execution termination guarantee.

Proof. Conditioned on any failed attempts of a pending certified
phase, its next failure probability is at most $1/4$. Its tail after
$u$ attempts is therefore at most $4^{-u}$, and summing tails gives
mean at most $4/3$. There are $L$ phases. The bounds in (ACR.98)
apply to every failed as well as successful attempt, so multiplying
them by $4L/3$ proves the expected bounds. A finite-state retry flag
and overwritable buffers suffice; no ever-growing attempt counter or
retry archive is needed. Every finite return is exact by the
certificate induction.

For a concrete nontermination tape, take the admitted zero stream
with public bound $d=1$ and cut $n=6$. The physical $a$-spine has
$h=3$, hence $H=7$. On an all-zero controller tape every walk follows
physical $a$, the smaller child at each zero-law birth, and each root
walk has depth three. Every root estimate is three, so the proposed
cut is the rounded value of $31/6$, namely five. It cannot pass a
rank certificate on the actual rank-six root. Hence every root
attempt fails on that tape. Arbitrarily many such failures are also
forced by sufficiently long finite zero prefixes, each of positive
probability. This is a counterexample to a uniform bound for this
uncapped procedure, not to deterministic acquisition in general.
$\square$

## 24. Every-tape return with an exponentially priced rare fallback

**Theorem 24.1 (total supplemental acquisition with polynomial expected
local cost).** Set

$$
K=d+\left\lceil\log_4(4L)\right\rceil.
\tag{ACR.101}
$$

Allow at most $K$ attempts in each certified phase of Definition
23.1. If one phase exhausts its attempts, abandon the fast acquisition
and run the deterministic acquisition of Theorems 14.2 and 13.2 on
the same unchanged root, using the already earned $h,H$. Stop that
supplier after acquiring $P,n$, before any canonical normalization.
After either route returns, execute the original normalization and
writeback specified in §26 exactly once.

For every actual source and cut, this supplemented acquisition returns
the authentic $P,n$ on every coin tape. For absolute constants and
with $S=d+H+2$, before normalization and its output arithmetic,

$$
\begin{aligned}
Q_{\rm acq}&\le CS^6,&J_{\rm acq}&\le CS^7,&M_{\rm acq}&\le H,\\
\mathsf{coins}_{\rm acq}&\le CS^6,&V_{\rm acq}&\le CS^8,\\
\mathbb E C_{\rm acq},\ \mathbb E W_{\rm acq}&\le CS^{24},&
C_{\rm acq},W_{\rm acq}&\le C4^dS^{24}.
\end{aligned}
\tag{ACR.102}
$$

The first line and the coin/backing bounds hold on every execution,
including fallback executions. Expectations are only over the added
fair coins, uniformly for each fixed source and cut. The last bound
honestly retains exponential worst-case local work and writes.
Source updates, resets, cloning and source-generator advances are zero.
No polynomial bound on physical tariffs or elapsed service duration
is asserted.

Proof. Every failed phase preserves a certified state. Conditional
failure bounds from Theorem 23.2 give

$$
\Pr\{\text{fallback}\}\le L4^{-K}\le\frac14\,4^{-d}.
\tag{ACR.103}
$$

This is a union bound over exhausted phases, including the possibility
that later phases are never reached. The fast part has at most $LK$
attempts, whether or not it falls back. Its local work and writes
are $O(S^{14})$ by (ACR.98), since $L,K=O(S)$.
Its Reads and coins are $O(LK(H+2)^3R)=O(S^6)$ and its traffic
is $O(S^7)$. These bounds include all failed attempts and their
buffer, coin and counter writes. A bounded binary counter now records
the at-most-$K$ attempts; it is part of the stated storage and writes.

The fallback constructs and verifies the original common list, then
measures the actual root and early child cones. Theorems 14.2--15.1
give its complete acquisition work and writes at most
$C4^dS^{24}$, acquisition backing $CS^8$, polynomially many Reads
$O((4d+1)TH)$, and polynomial traffic $O((4d+1)TH^2)$, with
$T$ exactly (ACR.48). Thus these interaction terms are at most
$CS^5,CS^6$. Its catalogue preparation is still paid on every
fallback run. The retained partial fast prefix is unnecessary to the
fallback, but nothing is reset, cloned, advanced or replaced: only
the local inference is restarted against the same stationary source.
The already acquired spine remains valid.

Keep the fallback's supplied bit-operation model and operand/backing
costs; no free sequential simulation is presumed. Transfer its explicit
earned $P,n$ into the local controller by §21.7's charged rule.
With $O(S^8)$ supplier backing and $O(S)$ returned bits, the extra
work and writes are $O(S^{17})$ and backing $O(S^8)$. These are
included in the displayed fallback envelope, not in a repeated
normalization. The pure fast part is already in the sequential model.
Clearing fast buffers and initializing fallback buffers are paid writes.

Multiplying the acquisition-only fallback work/write bound by
(ACR.103) gives at most $CS^{24}/4$ in expectation; adding all fast
work and the spine proves the expected terms of (ACR.102). No
operation is erased from a realized fallback bill. The deterministic
fallback terminates and returns authentic data on every source;
all fast paths are finitely capped. Every coin tape therefore returns,
including the all-zero tape of Theorem 23.3. Finite progress and
completion premises are the original ones, and the stationary interval
must cover the full realized exponential fallback when it occurs.
This is stronger than almost-sure return but still weaker than the
original every-execution polynomial TOTAL requirement. $\square$

## 25. Native accepting transcripts and deterministic hitting

**Definition 25.1 (bounded finder and its source-specific acceptance
functions).** Put $K_0=\lceil\log_4(4L)\rceil$. Let
$\mathcal B_{d,H}$ be the guarded finder of §23 capped at $K_0$
attempts per phase, returning either a certified $(n,P)$ or FAIL,
with no deterministic fallback. The local inputs include the earned
$h,H$; they are not treated as an upper bound supplied at entrance.
Fix slots for every potential estimate, block, walk and direction bit
in every potential attempt, even when an earlier success makes a slot
unused. With $E=4(H+2)$ estimate slots per attempt, a sufficient
fixed tape length is

$$
b(d,H)=LK_0EmRH.
\tag{ACR.104}
$$

Unused slots are ignored. On independent fair tapes this gives the
same distribution as fresh streaming coins. In an actual streaming
run only generated bits are charged; in a deterministic tape-list
implementation all generated list bits, including unused slots, are
charged. A short or malformed supplied tape returns FAIL rather than
accessing an unowned cell.

For a hypothetical properly presented source $s\in\mathscr R_d$
and mature cut $n\le H$ whose actual $a$-spine is the fixed $h$,
define $C_{s,n}(u)=1$ exactly when $\mathcal B_{d,H}$ returns a
certified answer using tape $u\in\{0,1\}^{b(d,H)}$ against that
source's literal presence replies. Presentations which denote the
same source have the same function. This definition supplies no hidden
law, cut, reply or advice to the actual acquisition controller.

**Theorem 25.2 (polynomial native simulation and circuit correspondence).**
Every function $C_{s,n}$ of Definition 25.1 has a Boolean circuit of
size polynomial in $S=d+H+2$, with

$$
\Pr_{u\ \mathrm{fair}}\{C_{s,n}(u)=1\}\ge3/4.
\tag{ACR.105}
$$

One uniform polynomial-work procedure constructs such a circuit from
the explicit hypothetical recurrence, seed, cut and $d,H$. This is
a representation theorem for the actual source-specific functions,
not an actual-root simulation granted to the law-erased controller.

Proof. Certificates make the bounded finder zero error. Its failure
probability is at most $L4^{-K_0}\le1/4$, by the same conditional
phase argument as (ACR.103). Its step, literal, index, tape and backing
bounds are polynomial on every input tape, including FAIL branches.

For a supplied hypothetical source only, replace each Read by GPO
Definition 39.3's forward physical evaluator, using that source's
presented order at most $d$. Its proof of literal correctness is an
induction on the actual chronological descriptor relations, not a
minimality or invertibility argument, so any such presentation works.
No supplied actual-law presentation is needed by the physical finder.
Every literal has length at most $H$, and its required birth-bit
indices are at most $F_{2H+1}-1$, with $O(H+1)$ binary digits.
Forward companion powers, Fibonacci sibling masses and comparisons
with the supplied cut implement each reply in polynomial bit work
and backing, by GPO Proposition 39.5. They never iterate over the
possibly exponentially many birth indices or expand the whole tree.
All arrays here have polynomial length. Implementing their accesses
by paid sequential scans as in §21 increases the operation count by
only a polynomial factor, including every operand, counter and copy.
Composing with the bounded finder gives a deterministic sequential
machine of some fixed polynomial time $t(S)$, with tape $u$ as its
only varying input and all the supplied source data as constants.

For completeness, encode the finite control, tape symbols and head
positions of that machine on the at-most-$t(S)$ visited cells.
At each of $t(S)$ steps a fixed finite Boolean local rule computes
the next symbol/head/control flags; copy unchanged cells as well.
Unrolling the steps gives $O(t(S)^2)$ bounded-fan-in gates, plus
polynomial initialization and output gates. The accepting flag equals
the physical finder's flag because each simulated reply equals that
same source's literal reply. The uniform compiler can emit these
gates in polynomial work and writes with explicit binary wire indices.
Conversely, evaluating this compiled circuit on $u$ yields exactly
the finder's success flag on that hypothetical source; its satisfying
tape is not a source certificate without the actual paid checks.
This proves the claimed correspondence, including singular laws,
finite transients and $d=0$. It asserts no converse representation of
arbitrary circuits by actual FIB sources. $\square$

**Theorem 25.3 (sufficient uniform accepting-transcript hitting).**
Suppose a single source-blind algorithm, given $d,H$, constructs a
list $\mathcal U_{d,H}\subseteq\{0,1\}^{b(d,H)}$ of polynomially
many explicit tapes in polynomial TOTAL work, cumulative writes and
backing. Assume that for every admitted source and mature cut with
the earned spine $h=(H-1)/2$, some list member satisfies
$C_{s,n}(u)=1$. Then the original coin-free entrance admits
deterministic acquisition of $P,n$ with polynomial every-execution
preparation, local work, writes, Reads, literal traffic and backing.

Proof. Earn the spine, construct the list and run the bounded finder
on its members against the actual root. Failed runs leave their
certified prefixes unused and may be overwritten; each run remains
on the same stationary source and uses no updates. The assumed
hitting member returns an authentic answer by Theorem 22.2.
Polynomial list length times polynomial per-run bounds, plus full
list construction and copying, proves every charged acquisition
coordinate polynomial. No membership test for the hidden source or
enumeration of its law is used. This condition hits an accepting
adaptive transcript; it requires neither pointwise approximation of
every depth function nor a small Walsh norm. Canonical normalization
and the physical tariffs still have their separate bills. $\square$

**Theorem 25.4 (short common lists exist without a uniform constructor).**
For each $d,H$ in Definition 25.1 there is a polynomial-total-length
list hitting all its source-specific acceptance functions. This
existence does not supply the algorithm assumed in Theorem 25.3.

Proof. Pad every order-at-most-$d$ all-index source to order $d$ by
multiplying its annihilator by $E^{d-r}$. At most
$M=4^d(H+1)$ row/seed/cut presentations must be covered, including
all singular, nonminimal and finite-transient sources. Restricting
to the fixed earned spine only decreases this number. Independently
sample $m_* =\lceil\log_4(2M)\rceil$ tapes of length $b(d,H)$.
By (ACR.105), a particular function misses them all with probability
at most $4^{-m_*}$. A union bound over the at-most-$M$ functions
is at most $1/2$. Hence some list hits them all, and its length
$m_*b(d,H)$ is polynomial in $d+H+2$.

This proof neither identifies the list nor tests its universality in
polynomial work. Exhaustively checking it over these presentations
retains the source catalogue. ACR §14 already supplies common lists
with charged exponential construction for the stronger pointwise
measurement requirement; the new sufficient condition concerns
successful certified transcripts. No generic derandomization lower
bound, arbitrary-circuit encoding, hardness-based generator corollary
or space-generator resource bound follows from the one-direction
source-to-circuit correspondence proved here. The unresolved step is
a uniform polynomial-total constructor for this native hitting
condition, or another source-faithful polynomial-total acquisition
method. $\square$

## 26. Original canonical output and same-source recovery after acquisition

**Theorem 26.1 (undiscounted normalization and completed handoff).**
Use Theorem 24.1, or Theorem 25.3 when its hypothesis is established,
only through its authentic $P,n$. At every rank, normalize that actual
prefix exactly as in Definitions 9.1 and 21.1 and Corollary 21.3.
For $d>0$ form the actual Hankel system and retain

$$
\begin{aligned}
i_P&=\min\{i<2^d:H(P)\rho_d(i)=y(P)\},\\
K_d(P)&=\operatorname{EN}_d(P)
 =\bigl(\rho_d(i_P),(\zeta_0,\ldots,\zeta_{d-1})\bigr),
\qquad \zeta_i=z_{i+1}.
\end{aligned}
\tag{ACR.106}
$$

On full rank solve the unique system; on deficient rank run the
original first-passing $\rho_d$ enumeration. For $d=0$ use the
original empty row/seed zero descriptor. Compute and install the
exact original tuple

$$
\boxed{\bigl(P,K_d(P),n,B_n\bigr),\qquad
P=z_1\cdots z_{2d},\quad B_n=F_{n+1}-1.}
\tag{ACR.107}
$$

This is an all-input output obligation after either acquisition route,
including every fast success and every fallback success. In
particular the normalizer is never multiplied by a fallback
probability.

Proof. The acquisition theorems return the actual prefix and cut,
not a constructed normalization input. Theorem 21.2 identifies the
exact passing fibre, and Corollary 21.3 returns precisely the original
first row and authentic first-$d$ seed. A deficient zero-stream fibre
at positive $d$ still returns $(\rho_d(0),0^d)$, which need not have
zero coefficient row. No equivalent minimal descriptor replaces it.
Definition 21.5's affine-prefix property for the unspecified original
enumeration remains an unproved additional condition; Theorem 21.6
may be used only when that condition is actually supplied.

Write $C_{\rm norm}(P),W_{\rm norm}(P),V_{\rm norm}(P)$ for the
full original normalization bill. On full rank these are exactly
bounded as in (ACR.89); on deficient rank retain all terms in
(ACR.90), including original $e_d,\omega_d,v_d$, every tested-row
transfer and every row-test write. Its initial rank computation is
part of that bill on both branches. At $d=0$ normalization is
constant. The bound chosen for a fixed actual $P$ is incurred on
every coin tape, regardless of which acquisition branch earned it.

The acquisition result is exported explicitly when needed using the
already charged transfer of §24; in the wholly sequential fast route
its output tapes are already the input tapes here. Now perform the
binary Fibonacci construction and final retained copy of §21.7.
With $\ell_n=\lceil\log_2(64(n+2)^4)\rceil$, its actual arithmetic
has

$$
C_B,W_B=O((n+2)^2\ell_n^2),\qquad
V_B=O(n+1+\ell_n).
\tag{ACR.108}
$$

These are tape operations on the explicit binary integer $B_n$,
including all growing-buffer, carry and counter writes; the output
has $\Theta(n)$ bits as $n$ grows. With $L_{d,n}$ as in §21.7,
the final payload and ready-control copy costs
$O((d+n+1)L_{d,n}^2)$ work and cumulative writes and
$O(d+n+1+L_{d,n})$ backing. Set ready only when every data field is
installed in granted readable backing. If an explicit forward phase
is requested, add exactly the $C_\phi,W_\phi,V_\phi$ terms of
§21.7, once; its forward powering uses the selected original row
and seed and never recovers a private state.

Thus for either acquisition supplier, after all its needed output
transfers are included in its acquisition terms, the disjoint bills are

$$
\begin{aligned}
C_{\rm total}&\le C_{\rm acq}+C_{\rm norm}(P)+C_B+C_\phi
                    +O((d+n+1)L_{d,n}^2),\\
W_{\rm total}&\le W_{\rm acq}+W_{\rm norm}(P)+W_B+W_\phi
                    +O((d+n+1)L_{d,n}^2),\\
V_{\rm total}&\le V_{\rm acq}+V_{\rm norm}(P)+V_B+V_\phi
                    +O(d+n+1+L_{d,n}).
\end{aligned}
\tag{ACR.109}
$$

For Theorem 24.1, taking expectations changes only the acquisition
terms and any actually randomized acquisition service charge; the
fixed authentic-prefix normalization and output terms remain in full.
Physical service and initialization, coin grant, binding, code,
allocation, intermediate and retained physical writes, retention and
completed handoff keep their actual tariffs and durations on every
execution. No displayed bit-work bound infers a duration or grants a
right. Stationarity and sufficient backing extend through the actual
last write and completed handoff, including the deterministic
fallback and normalization when present.

Once the tuple is installed with its separately surviving actual
binding and grants, GPO Theorems 34.2--34.3 and 39.4 give the same
spatial incidence, boundary, actual birth chronology and synchronized
memory views and their finite same-source continuation. GPO
Proposition 39.5 retains request-sized literal evaluation; whole-tree,
whole-boundary or full chronological output pays its own potentially
exponential output length. No arbitrary observer journal, erased
private register, source-origin receipt, capability or physical
duration is reconstructed. These consumers are reused on the earned
same source, not on a merely compatible hypothetical realization.

The new repository-derived implications are the paid certificate
relation, its bounded fair-coin witness search, total rare-fallback
composition and native accepting-transcript sufficient condition.
The depth mean, authentic early-parent construction, source law,
finite monic separation, deterministic catalogue supplier, exact
canonical fibres and recovery consumers are the cited ACR/GPO
suppliers. Chebyshev, median amplification, finite union bounds and
bounded-computation circuit unrolling are established intermediate
methods, not novelty claims. Massey's [MAS] supplies finite-prefix
recurrence synthesis after authentic bits; it does not acquire these
bits or choose $\rho_d$'s first passing row. Zuckerman's bounded
function sampling setup [RRO-ZUC] uses an independent random seed;
it supplies neither a deterministic seed for this adaptive native
class nor a physical sample oracle. The present proof derives its
sampling bounds directly from the actual paid depth-walk law.
The existing declaration `atomic_navigation` concerns fixed semantic
orientation,
`NativeBirthVectorDecoder` a recursive complete-level code,
`actual_fibonacci_support_chain` bounded native support agreement,
and `native_source_producer` full acquisition from richer replies.
These distinct mathematical domains do not supply the new
certificate/acquisition composition.

Uniform polynomial-total deterministic acquisition for general $d$
on the original entrance remains open. Theorem 24.1 adds fair coins
and retains exponential worst-case local computation; Theorem 25.3
has an unestablished uniform hitting premise. Independent of those
acquisition gaps, the original deficient-rank enumeration and the
unspecified enumeration's affine-prefix property remain their stated
normalization boundary. The full original every-execution polynomial
TOTAL task, with its exact $K_d$ and physical charges, is therefore
not settled. $\square$

## 追加锚（本行以下为增补区）
