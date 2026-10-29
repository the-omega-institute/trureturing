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
