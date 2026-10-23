# Determining prefixes for negative additional history on native relational fibers

This volume isolates one extension of the complete acquired-fiber problem. The
old row, its repeated classes and all of its cross-class inequalities are kept;
so are the literal records, every endpoint guard, the concrete exterior and the
full original target row. The only additional relation records admitted here
are guarded negative records. The result is a terminating ordinary-theory
decision for this sign-specific family: either a finite original determining
prefix is selected and consumed by a paid static reader, or a finite-source
countercertificate is generated for every requested inclusive depth.

The result is conditional on the exact source and access contracts of [ARH,
Assumption 1.3][ARH]. It is a scoped advance for negative additional history.
It does not decide arbitrary positive or mixed signed histories, and it does
not claim a solver, a kernel certification, a complexity bound, a physical
run or literature priority.

## 1. The complete native fiber and the target

**Definition 1.1 (native trees and transport).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,
\quad \rho\beta=\langle\beta,\alpha\rangle,
\quad \rho\langle x,y\rangle=\langle\rho x,\rho y\rangle .
\tag{RNL.1}
$$

A position is a word in $\{L,R\}^{*}$, and $r_t(p)$ is the four-valued
reply $\alpha,\beta,\mathsf{branch}$ or $\mathsf{absent}$. Every tree is
finite, but there is no common bound on size, height or rank. The old cut $P$
and the target cut $Q$ are arbitrary finite prefix-free sets of original
addresses; either may be empty or contain the root.

**Assumption 1.2 (actual acquired input).** Let $R=R_P(u)$ be the complete
old row acquired from the same original source producer as in [ARH,
Definition 1.1][ARH]. It contains the complete concrete exterior, reached
holes in original order, the whole equality partition, repeated occurrences
of each old class, all cross-class and off-task inequalities, and all old
existence guards. Let $H_0$ be a finite literal history, with repetitions and
mixed epochs. Let $H^{-}$ be a finite list of additional guarded negative
records

$$
e=(a,s,b,t,\ne),
$$

where its predicate is

$$
\operatorname{Neg}_e(u)\;\Longleftrightarrow\;
 s\in\operatorname{Pos}(\rho^a u)\ \land\
 t\in\operatorname{Pos}(\rho^b u)\ \land\
 (\rho^a u)|_s\ne(\rho^b u)|_t .
\tag{RNL.2}
$$

An absent endpoint makes (RNL.2) false. It is never converted into a
successful disequality. The complete retained fiber is

$$
\begin{aligned}
D^{-}=\{u\in\mathcal T:\;&R_P(u)=R,\\
&r_{\rho^c u}(p)=d\quad((c,p,d)\in H_0),\\
&\operatorname{Neg}_e(u)\quad(e\in H^{-})\}.
\end{aligned}
\tag{RNL.3}
$$

All records constrain this same $u$. We assume $D^{-}\ne\varnothing$.

The original target is the entire $R_Q(u)$: every reached original hole, the
full concrete exterior and the complete equality partition of all reached
subtrees. No representative source, sample domain, source-size promise or
finite output list replaces $D^{-}$.

**Assumption 1.3 (authentic entry and legal service).** The retained state is
the complete accessible state of the cut in [ARH, Assumption 1.3][ARH]. The
same original-root register has actually reached a common certified epoch
$N$ at least all recorded epochs. A service may perform only paid original-root
reads at finite physical words, forward applications of $\rho$ on that register,
and an absorbing halt. It has no reset, clone, reroot, source identity,
membership query, unknown-subtree equality port, free chart, timing channel or
control state carrying an unlisted source distinction. Updates carry no extra
source-dependent information. Every source in $D^{-}$ must terminate with its
correct full $R_Q$.

Define the requested determining-prefix predicate by

$$
\operatorname{PrefDet}(D^{-},Q,h)\;:\Longleftrightarrow\;
\forall u,v\in D^{-},
\left(\forall |p|\le h,\ r_u(p)=r_v(p)\right)
\Longrightarrow R_Q(u)=R_Q(v).
\tag{RNL.4}
$$

The question is whether some $h$ satisfies (RNL.4), with a finite paid static
consumer when it does and an exact finite-source obstruction when it does not.

## 2. Exact finite original cells

**Definition 2.1 (depth-$d$ original masks).** Put

$$
 d=1+\max\bigl(\{0\}\cup\{|q|:q\in Q\}
 \cup\{|p|:(c,p,d)\in H_0\}
 \cup\{|s|,|t|:(a,s,b,t,\ne)\in H^{-}\}\bigr).
\tag{RNL.5}
$$

For each old equality class $b$ choose its representative original hole $a_b$.
A depth-$d$ mask $t_b$ records all original constructors at relative depth
less than $d$ and puts a distinct frontier variable at every reached depth-$d
position. The same $t_b$ is used at every repeated occurrence of $b$; different
classes and frontier addresses use different variable names. For a finite mask
choice $\eta$ write

$$
W_\eta=C[(t_{[i]})_i],
\qquad
\Delta_\eta=\{t_b\ne t_c:b<c\}.
\tag{RNL.6}
$$

The variables in all $t_b$ form $X_\eta$. If $x$ is the frontier variable
at relative address $s_x$ in $t_b$, fix its full original representative
position

$$
p_x=a_b s_x,\qquad |s_x|=d,\qquad
(W_\eta[v])|_{p_x}=v(x).
\tag{RNL.6a}
$$

Thus $a_b$ represents the old hole, whereas $p_x$ recovers the residual
coordinate. A valuation $v:X_\eta\to\mathcal T$ is allowed only when every
old inequality in $\Delta_\eta$, every literal
condition and every old existence guard is true. These literal and guard
conditions are structurally fixed by the selected prefix cell.

For an endpoint in a negative record, [ARH, Proposition 3.2][ARH] gives two
possibilities. If the address reaches an original frontier term $A$, the
endpoint is $\rho^a(A[v])$. If it meets a known leaf sector, the supplied
leaf-sector guard is tested and the endpoint is a concrete tree $T_j$; a failed
guard rejects the whole cell for either sign. After evaluating concrete
sectors, every surviving negative record has the form

$$
\rho^a A(v)\ne\rho^b B(v),
\tag{RNL.7}
$$

where $A,B$ are ordinary finite constructor terms over $X_\eta$ and the
constants $\alpha,\beta$. A ground side is represented by its concrete term
with outer exponent $0$. No interpreted iterate is treated as a new free
constructor. Let $\Omega^-_\eta$ be the valuations satisfying all retained
conditions and all instances of (RNL.7).

**Proposition 2.2 (exact cell correspondence and target commute).** The
nonempty cells give a disjoint union

$$
D^{-}=\coprod_{\eta}\{W_\eta[v]:v\in\Omega^-_\eta\}.
\tag{RNL.8}
$$

For each source, its unique cell is recovered by the depth-$d$ masks of its old
class trees and each frontier variable $x$ is recovered at its fixed original
address $p_x$ in (RNL.6a). Conversely, every $v\in\Omega^-_\eta$ fills a genuine finite source
in $D^{-}$. Along every cell there are a fixed reached set $J_\eta\subseteq Q$,
a concrete exterior context $E_\eta$ and one term $T_{\eta,q}$ for each reached
$q$ such that

$$
\begin{aligned}
I_Q(W_\eta[v])&=J_\eta,\qquad
C_Q(W_\eta[v])=E_\eta[v],\\
q\sim r&\Longleftrightarrow T_{\eta,q}[v]=T_{\eta,r}[v]
\quad(q,r\in J_\eta).
\end{aligned}
\tag{RNL.9}
$$

Proof. The masks are strictly below every named address, so [ARH,
Proposition 3.2][ARH] applies its guarded endpoint analysis without changing
any record. The old-row filling and recovery maps are inverse, including every
repeated class and every cross-class inequality. The same argument preserves
all literal records and both endpoint guards. Navigation to $Q$ cannot meet a
frontier variable before reaching the cut, so the reached set is fixed in the
cell; the concrete exterior is the filled context $E_\eta[v]$, and equality of
reached whole subtrees is exactly equality of the displayed terms. Thus both
source directions and both target directions hold. A finite list of cells is
not a replacement source domain: (RNL.8) quantifies over every valuation in
every cell. $\square$

**Convention 2.3 (ordinary residual domain).** The mask presentation
(RNL.6) requires no preliminary equations. If an equivalent presentation uses
ordinary constructor equations, take a fully composed idempotent
occurs-check most-general unifier $\tau$ with no fresh variables. Its remaining
coordinates are $Z_\eta=X_\eta\setminus\operatorname{dom}\tau$. For
$z\in Z_\eta$, $\tau(z)=z$, so the same fixed original address still recovers
the coordinate:

$$
(W_\eta[\tau(v)])|_{p_z}=v(z),\qquad p_z=a_b s_z,\qquad |s_z|=d.
\tag{RNL.9a}
$$

Here $\tau(v)(x)=\tau(x)[v]$ reconstructs every eliminated coordinate.
Subsequent target unification is over $Z_\eta$ and retains these full original
recovery addresses; a substitution never resets their depth to $|a_b|$.
Such a presentation must preserve the exact retained cell in both directions.
All remaining cell restrictions are the original old/literal/guard conditions
and a finite conjunction of negative records of the form (RNL.7). No target
equality is added to the retained negative domain; target equations are
diagnostic queries only.

The finite cell list is a selector only after its source correspondence is
proved. If two original sources have the same depth-$d$ mask replies, they
select the same cell. Conversely every source in a cell has that mask. This
cross-cell coverage is used below; it is not inferred from a finite semantic
row list.

## 3. Finite forbidden replacements for uniform outer powers

**Lemma 3.1 (one-coordinate finite forbidden set).** Fix all residual
coordinates except $z$, and suppose one retained negative record is true at a
finite tree $z_0$. Suppose its two sides have the form (RNL.7), with each side
one uniform outer power of an ordinary constructor term. Then the set of finite
trees $z$ that would make the displayed equality true is finite.

Proof. Let $\nu(z)=(\#\alpha(z),\#\beta(z))^{\mathsf T}$. The recurrence for
$\rho$ is

$$
\nu(\rho z)=M\nu(z),\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
\tag{RNL.10}
$$

After the other coordinates are fixed, let $r$ and $t$ be the occurrence
counts of $z$ in $A$ and $B$, and let $c_A,c_B$ be the constant leaf-count
vectors contributed by all other terms. Equality implies

$$
(rM^a-tM^b)\nu(z)=M^b c_B-M^a c_A.
\tag{RNL.11}
$$

If $a\ne b$ and $r+t>0$, assume for example $a>b$ and factor $M^b$. A singular
matrix would make $t/r$ an eigenvalue of $M^{a-b}$ when $r,t>0$. The two
 eigenvalues of $M$ are

$$
\varphi=\frac{1+\sqrt5}{2},\qquad
\psi=\frac{1-\sqrt5}{2};
$$

for every positive integer $d$, both $\varphi^d$ and $\psi^d$ are irrational:
$\varphi^d-\psi^d$ is a nonzero integer multiple of $\sqrt5$, and
$\psi^d=(-1)^d\varphi^{-d}$, so a rational value for either would make the
other rational and contradict that difference. Whereas $t/r$ is rational, so
the matrix is invertible. If exactly one of
$r,t$ is zero, it is a nonzero scalar multiple of an invertible power of $M$.
If $r=t=0$, equality is independent of $z$ and is false because the negative
record is witnessed at $z_0$.

If $a=b$, injectivity of $\rho^a$ reduces equality to $A(z)=B(z)$. After
identical outer constructors are cancelled, a first constructor conflict gives
no solution, a comparison with a ground term fixes $z$ to that term, and a
proper self-occurrence would require a finite tree to have strictly more nodes
than itself. Thus two nonidentical one-variable ordinary terms have at most one
finite solution. If $A$ and $B$ were identical, the retained negative record
could not be true at $z_0$. Therefore in every case only finitely many $z$ are
forbidden. Finally, a fixed pair of leaf counts has finitely many ordered
binary trees (a Catalan number of shapes times finitely many leaf labels), so
the finite count solutions from (RNL.11) yield finitely many finite trees.
$\square$

**Corollary 3.2 (simultaneous avoidance and deep replacement).** In a cell
with finitely many retained negative records, fix a valuation satisfying all of
them. For one coordinate $z$, the union of the forbidden sets from Lemma 3.1
is finite. There are arbitrarily large finite trees outside that union. If $z$
appears at original addresses $p_i$, choose a replacement that agrees with the
old value through local depth
$\max_i\max(0,h-|p_i|)$; then every resulting source agrees at every
original address of length at most $h$. If the current $z$ has a branch at
that local depth, the replacement can also be required to exceed any prescribed
leaf-count threshold.

Proof. Take the finite union. Replace within one child cone of a branch at
the stated local depth. This leaves replies through that depth, and hence
every global prefix of depth at most $h$, unchanged. The ordered full binary
trees obtained by filling that cone with increasingly many leaves are
pairwise distinct, so one avoids the finite union and any prescribed finite
set. Shared occurrences of $z$ are changed simultaneously, preserving every
repeated occurrence. $\square$

The lemma is deliberately syntactic. It does not apply to a mixed internal
power such as

$$
\rho^2(z)=\langle\rho(z),z\rangle,
\tag{RNL.12}
$$

whose native equality has infinitely many finite solutions. That boundary is
exactly the one exhibited in [URR, Proposition 7.1][URR].

## 4. The exact all-negative decision

**Definition 4.1 (complete row mask and the NPL split).** Write
$\mathsf{Mask}_Q(u)=R_Q(u)$. Reuse [NPL, Theorems 4.1 and 5.3][NPL] on the
entire fiber (RNL.3), with the authentic common state and the actual action
contract. The result is an exact finite/infinite split for the image of
$\mathsf{Mask}_Q$. In the infinite branch it also supplies a total generator
$G:\mathbb N\to D^{-}$ whose complete masks are pairwise distinct. In the
finite branch it supplies the exact finite image and finite original witnesses
for its elements. These witnesses are proof-side witnesses, not online
representatives or source selectors.

**Theorem 4.2 (all-negative determining-prefix criterion).** Under
Assumptions 1.2–1.3, for arbitrary finite prefix-free original $P,Q$, the
following terminating procedure is exact.

1. If the NPL mask split is infinite, it returns **negative** together with a
   finite-source generator for every requested inclusive depth $h$.
2. If the mask split is finite, it constructs all exact cells (RNL.8). For each
   cell and each reached target pair it submits the joint positive query
   $\exists v\in\Omega^-_\eta$ with $T_{\eta,q}[v]=T_{\eta,r}[v]$ to [NSF,
   Lemma 5.1 and Theorem 5.2][NSF]. An infeasible query fixes that bit false.
   A feasible query is fully composed with an occurs-check MGU. If its
   bindings are all ground, [SLH, Theorem 74.4][SLH] and the supplied ground
   criterion reduce the bit to finitely many original tests. If a feasible
   nonidentity MGU contains a free variable in a binding, the procedure
   returns **negative** with a pump producing a finite opposite-row pair at
   every requested $h$.
3. If every finite-cell query is infeasible, identically true, or has only
   ground bindings, the procedure returns **positive** with a finite $H$ such
   that $\operatorname{PrefDet}(D^{-},Q,H)$. It also returns a paid static
   service at epoch $N$ with

$$
q\le 2(2^{H+1}-1),\qquad
 a=0,\qquad
 \ell\le2(2^{H+1}-1)(H+\lceil N/2\rceil).
\tag{RNL.13}
$$

In the positive branch let $B$ be the old class set and $\mathcal E$ the
finite set of feasible cells. For each feasible positive target-pair query,
write $\theta_{\eta,qr}$ for its fully composed MGU, after any preliminary
substitution of Convention 2.3; its nonidentity bindings are all ground.
With leaf height zero, use the single original inclusive depth

$$
H=\max\left(
 \{0\}\ \cup\ \{|a_b|+d-1:b\in B\}\ \cup\
 \left\{|p_x|+\operatorname{height}(\theta_{\eta,qr}(x)):
 \substack{\eta\in\mathcal E,\ q,r\in J_\eta,\ \text{query feasible}\\
 x\in\operatorname{dom}\theta_{\eta,qr}}\right\}
 \right).
\tag{RNL.13a}
$$

Every $p_x$ is the full original coordinate address from (RNL.6a) or
(RNL.9a). Empty binding sets contribute no template depths. The same $H$
is used in (RNL.13); no optimality or execution-time claim is made.

Proof. The negative infinite-mask branch is an explicit finite-source
pigeonhole construction, not a successive-$h$ search. There are
$2^{h+1}-1$ original addresses of length at most $h$, hence at most

$$
B_h=4^{\,2^{h+1}-1}
\tag{RNL.14}
$$

four-reply prefix vectors. Generate $B_h+1$ actual finite sources
$G(0),\ldots,G(B_h)$ and compute their actual original prefix vectors. Two
vectors agree. Their complete masks differ because $G$ has pairwise distinct
masks. The selected pair is finite, jointly admissible in (RNL.3), agrees at
every original address through $h$, and has different full $R_Q$ rows. This is
a post-decision finite certificate; no infinite source, raw-prefix automaton,
or representative domain is introduced.

Assume now the finite mask branch. Proposition 2.2 gives both source
inclusions for every cell and exact full target rows. If a cell exterior
$E_\eta$ retained a free coordinate on a feasible subfamily, the same deep
replacement construction as Corollary 3.2 (with no exclusions when the
negative list is empty) would produce infinitely many distinct complete masks,
contradicting the NPL finite branch. Thus every feasible cell has a fixed concrete exterior after
its finite mask is selected.

Consider one reached pair $(q,r)$. NSF decides the joint feasibility query
using the full old row, all literal records, every negative relation, both
endpoint guards and one common source. If it is infeasible, the pair is never
equal. Otherwise let $\theta$ be the fully composed MGU for
$T_{\eta,q}=T_{\eta,r}$. The MGU is exact: every solution is precisely an
assignment to its free variables followed by $\theta$, and every such
assignment solves the target equation.

Suppose a binding $x=\theta(x)(Y)$ contains a free variable $y\in Y$. Start
with the finite witness supplied by the joint NSF query. Substitute $\theta$
into every retained negative record. Lemma 3.1 and Corollary 3.2 give only
finitely many forbidden values for $y$; choose a value outside them with
more than $2^h$ leaves. The extended valuation still satisfies every negative
record and solves the target equation, so it is a finite source $u_h\in D^{-}$
with the selected target bit true. Its value of $x$ has more than $2^h$
leaves, hence height greater than $h$ and a branch at relative depth $h$.
Replacing within one child cone of that branch preserves all replies through
relative depth $h$.

Return to the original residual domain, where the target equation is not a
retained condition. Freeze all free variables and all residual coordinates
other than this bound variable $x$. Apply Lemma 3.1 to every retained
negative record with $x$ as the varying coordinate. Corollary 3.2 supplies a
finite $x'_h$ that agrees with $x$ through relative depth $h$, and therefore
through every required original depth-$h$ cone, avoids all finite forbidden
values, has larger leaf count, and differs from
$\theta(x)(Y)$. Replace $x$ by $x'_h$ in every occurrence. The old row,
literals, guards, all repeated classes and all negative records remain true;
the two reconstructed sources are in the same exact cell and agree on every
original reply of length at most $h$. The MGU equivalence says the changed
source no longer solves $T_{\eta,q}=T_{\eta,r}$, so its full target row differs
in this equality-partition bit. This gives a jointly admissible finite
opposite-row pair for every $h$. It is crucial that the diagnostic target
equation was removed again before the second replacement.

It remains to consider feasible nonidentity MGUs with no such free binding.
Then all bindings are ground. The ordinary ground criterion of [SLH,
Theorem 74.4][SLH] and its finite delayed-template tests decide each bit on
the whole cell; an empty binding is identically true. There are finitely many
cells and finitely many reached pairs, so this finite analysis terminates.
Use the single $H$ in (RNL.13a). Each representative-mask reply is at
$a_b s$ with $|s|<d$, so $|a_b s|\le |a_b|+d-1\le H$. Therefore two sources
with equal original $H$-prefixes select the same exact mask tuple, including
all absent replies.

For a ground binding $x=g=\theta_{\eta,qr}(x)$, (RNL.6a), or (RNL.9a) after
preliminary substitution, recovers the coordinate at $p_x$. Its equality
test is exactly

$$
v(x)=g\quad\Longleftrightarrow\quad
\forall |s|\le\operatorname{height}(g),\
r_u(p_x s)=r_g(s).
\tag{RNL.15}
$$

Matching all these replies forces every constructor and terminating leaf of
the finite ground tree $g$, so no extension or different tree passes. Every
test address satisfies
$|p_x s|\le |p_x|+\operatorname{height}(g)\le H$.
This is the full original position $a_b s_x s$ used in [SLH,
(SLH.74.14)][SLH]. Thus equal original $H$-prefixes give the same result for
every ground binding, hence every target-pair bit; infeasible and identity
queries are already constant. Equation (RNL.9) gives the same reached set,
fixed concrete exterior and complete partition, hence the same $R_Q$.
The finite maximum is computed once, without prospective depth enumeration.
Cross-cell coverage follows from both directions of (RNL.8), not from a
finite row table.

For the positive consumer, use the paid historical decoder of [NSF, Theorem
6.1][NSF] (equivalently [SLH, Theorem 2.2][SLH]) at the authentic current
register. Using exactly $H$ from (RNL.13a), it recovers all
$2^{H+1}-1$ original replies through $H$, with at most two current reads per
reply and physical address length at most $H+\lceil N/2\rceil$. These are
the bounds (RNL.13). It selects the unique cell, performs the finite ground tests, and
installs the complete original row. The source used internally to compute a
constant row is only an offline feasibility witness; the online service has
no source selector or membership oracle. Therefore positive and negative
branches are exhaustive and exact. $\square$

**Corollary 4.3 (static/serial correspondence on this family).** For the
all-negative fiber, the positive branch of Theorem 4.2 is equivalent to the
existence of a uniformly finite-read serial service under the common-state
contract. This is [ARH, (2.3)][ARH] applied after the exact cell and target
analysis above; updates cannot supply an unlisted source distinction. The
negative pumps are finite sources for the original target, not an assertion
that an infinite model is required.

## 5. Boundary cases and proof obligations retained

**Proposition 5.1 (root, empty cuts and degenerate cells).** The theorem keeps
all boundary cases.

- If $Q=\{\varepsilon\}$, the target is one reached root hole and $H=0$; no
  target-pair query is needed.
- If $Q=\varnothing$, the target is the complete original source. The finite
  mask branch uses the full exterior condition; the infinite-mask branch
  supplies pairs of finite sources agreeing to every requested depth and with
  different complete sources.
- If $P=\varnothing$, the fixed complete old row contains the entire
  original tree as its concrete exterior. The remaining records either reject
  that tree or retain it: the fiber is empty or that fixed singleton.
  No old hole is assumed.
- A ground cell has no frontier variables and is checked directly. An empty
  or unreachable cell contributes no service branch. A nonempty input always
  retains at least one feasible cell.
- Repeated old classes, repeated negative records and off-task inequalities
  remain shared conjunctions. A missing original cut address contributes no
  hole and remains part of the concrete exterior when required.

Proof. These are direct specializations of (RNL.8)–(RNL.9), the endpoint
guards in (RNL.2), the joint NSF query and the NPL whole-row image. No case
introduces a representative source or a finite source-size bound. $\square$

**Proposition 5.2 (why positive or internally mixed equations are outside).**
The proof of Lemma 3.1 uses one variable in ordinary constructor terms and one
uniform outer $\rho$ power per side. URR’s equation (RNL.12) has infinitely
many native finite solutions, so the finite-forbidden replacement step is
invalid there. Likewise, a positive retained equation can force a coupled
residual set that is not preserved by changing one coordinate. The arbitrary
signed target therefore remains open even though this negative family is
decided.

The same boundary prevents importing URR’s common rank-independent residual
tuple as a source selector: [URR, Theorems 3.1, 4.6 and 5.1][URR] provide a
specified residual correspondence and a common completion on their Cartesian
and feedback/packing families, but no determining-prefix theorem for the
entire original fiber and no complete original-row selector here. Their
mixed-interior-power method is complementary to, and not duplicated by, the
finite-forbidden lemma.

## 6. Exact supplier and literature status

**References 6.1 (repository suppliers and limits).**

| Supplier | Exact use in this volume | Boundary retained |
| --- | --- | --- |
| [ARH, Assumption 1.3, Proposition 2.1, Proposition 3.2][ARH] | Complete acquired fiber, paid producer, guarded endpoint semantics, exact old-cell/source directions and serial/static/prefix contract | No positive-history decision is imported |
| [NPL, Theorems 4.1, 5.3 and 6.2][NPL] | Exact finite/infinite native mask image, pairwise-distinct finite-source generator in the infinite branch, and paid exterior consumer | A finite image is not itself a prefix selector |
| [NSF, Lemma 5.1, Theorem 5.2 and Theorem 6.1][NSF] | Joint full-fiber feasibility, complete-row two-source tests, fixed-prefix decisions and paid historical decoder | Each fixed-$h$ decision alone is not an $\exists h$ decision |
| [SLH, Theorem 2.2 and §74][SLH] | Historical two-read decoding, ordinary MGU/ground criterion, finite ordinary exclusions and deep finite perturbations | Its §74 syntax is extended here only by (RNL.11) for uniform outer powers |
| [ABC, Theorems 2.2–2.3][ABC] | Native/normal-code injectivity and transport facts used by the suppliers | No free normal-code replacement of native sources |
| [CAR, Definition 2.1 and Theorem 2.2 proof][CAR] | Fibonacci constructor mass and leaf-count recurrence when a supplier needs it | CAR’s atomic coverage hypotheses are not enlarged |
| [NFO, Theorem 3.2][NFO] | Prescribed-budget finite-obstruction boundary and same-source resource distinction | It does not decide this prefix criterion or arbitrary signed existence |
| [URR, Theorems 3.1, 4.6, 5.1 and Proposition 7.1][URR] | Exact complementary mixed-template correspondence and its counterexample boundary | No selector, prefix separation or finite-forbidden claim is taken from URR |

NFO’s prescribed budgets and conditional Pareto/rational minima are consumed
only as downstream results when a positive finite static consumer exists. This
volume does not reauthor any budget optimization or claim a fixed complete
control-state bound.

**References 6.2 (ordinary literature).** Martelli–Montanari, *An Efficient
Unification Algorithm*, ACM TOPLAS 4(2), 258–282,
[doi:10.1145/357162.357169](https://doi.org/10.1145/357162.357169), supplies
the standard finite free-term occurs-check method used by the cell MGU. Comon
and Lescanne, *Equational Problems and Disunification*, §3.2 and Appendix
B.3, [PDF](https://perso.ens-lyon.fr/pierre.lescanne/PUBLICATIONS/jsc-diseq.pdf),
supplies the ordinary finite-term disequality perspective and explicitly
warns that arbitrary equational theories need separate arguments. Barguñó,
Creus, Godoy, Jacquemard and Vacher, “Decidable Classes of Tree Automata Mixing Local and Global
Constraints Modulo Flat Theories,” [arXiv:1302.6960](https://arxiv.org/abs/1302.6960),
Theorem 5.22 and Corollaries 5.23–5.24, provides related finite-tree constraint feasibility in its stated language.
Reuß, *Normalization of Horn Clauses with Disequality Constraints*,
[PDF](https://mediatum.ub.tum.de/doc/1116533/document.pdf), Theorem 18 and
Corollary 17, gives finite ground elimination for its homomorphic
Horn/automata classes. These sources attest the component methods only; none
states the native guarded acquired-fiber correspondence or the theorem here.
The NPL image split, the source-faithful cell composition and the
Fibonacci-count finite-forbidden bridge are classified as repo-derived. No
literature-wide novelty or priority claim is made.

**Status 6.3 (scope and remaining obligation).** This is an ordinary paper
argument conditional on the named repository suppliers and acquisition
contracts. It introduces no Lean declaration, solver, experiment, physical
execution claim or programme-completion claim. The exact uncovered general
obligation is arbitrary coupled positive or mixed-epoch equations together
with every-depth finite jointly admissible opposite-row source production.
The persistent arbitrary signed NSF(3) target remains open.

[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[CAR]: RECURSIVE_RELATIONAL_OBSERVATION_CYCLIC_ATOMIC_RECOVERY.md
[NSF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[NFO]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_FINITE_OBSTRUCTION.md
[NPL]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PROJECTION_LIMITEDNESS.md
[SLH]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[URR]: RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_RESIDUAL_REALIZATION.md

## 追加锚（本行以下为增补区）

## 7. Complete-constraint preservation in the two pumps

**Proposition 7.1 (whole-cell avoidance for Theorem 4.2).** In every feasible
cell, the forbidden replacements used in Theorem 4.2 can include every old
cross-class inequality, including classes outside the target task, as well as
every additional negative record. This holds both after imposing the diagnostic
target MGU and after removing it. Consequently both finite sources in its
non-ground-binding construction belong to the original fiber (RNL.3).

Proof. Work first over the residual coordinates $Z_\eta$ of Convention 2.3.
Take $\tau$ to be the identity when no preliminary equations are used. The
complete list of variable-dependent restrictions is

$$
\begin{aligned}
\mathcal C_\eta={}&
 \{t_b[\tau]\ne t_c[\tau]:b<c\}\\
&\cup\{\rho^{a_e}(A_e[\tau])\ne
             \rho^{b_e}(B_e[\tau]):e\in H^-\}.
\end{aligned}
\tag{RNL.16}
$$

Concrete endpoint evaluations are included as ordinary ground terms, with
outer power zero. Every pair in the first line is likewise an instance of
Lemma 3.1 with both outer powers zero. No pair is omitted because one of its
classes has no occurrence in $Q$.

There are no additional variable-dependent reach or literal restrictions.
The concrete old exterior and old hole addresses are fixed by $C$. In
particular an absent old cut address cannot lie below a reached old hole,
since $P$ is prefix-free; its absent guard is fixed by that exterior. The
original constructors needed for each literal or additional endpoint are
strictly above the frontier of its mask. At a known leaf, the epoch and
remaining address determine the leaf-sector guard and reply. Otherwise
navigation stays in known original constructors to the endpoint. Thus all
retained literal replies, including absent replies and repetitions at mixed
epochs, and both guards of every negative record are constant throughout this
cell. This is the guarded correspondence of Proposition 2.2 and [ARH,
Proposition 3.2][ARH]. Filling a frontier never changes those constructors.
An exact preliminary substitution only restricts these fillings; it does not
change their guards.

Here substitution means substitution in the free ordered binary term algebra.
The terms $t_b[\tau]$, $A_e[\tau]$ and $B_e[\tau]$ are finite ordinary
constructor terms. After all but one coordinate $z$ are fixed to finite trees,
each old inequality is an ordinary one-variable inequality. The elementary
one-variable fact in the proof of [SLH, Theorem 74.4, part (ii)][SLH] applies:
cancel equal outer pair constructors until a first difference is reached.
Different constructors give no equality solution; $z$ against a ground term
fixes its unique possible value; $z$ against a proper term containing $z$
gives no finite solution by strict node-count increase. If no difference is
reached, the terms are identical and equality is universal. A current satisfying
valuation excludes this last case. Each old inequality therefore forbids at
most one value, including when its two sides contain repeated occurrences of
$z$ or share other frozen coordinates. An inequality independent of $z$
forbids none. This argument concerns trees with brackets and ordered children,
not associative concatenation equations; the latter's infinite solution
families are not in (RNL.16).

More generally let $\sigma$ be any ordinary constructor substitution and
suppose a finite valuation satisfies $\mathcal C_\eta[\sigma]$. After freezing
its other free coordinates, every member of this transformed list still has
one uniform outer power per side. Lemma 3.1 applies to the additional records,
and its zero-power case applies to all old pairs. Their finite union is the
forbidden set for this coordinate. Substitution cannot introduce an internal
interpreted iterate: only the ordinary terms inside the displayed outer
powers are substituted. In particular this argument does not apply to
(RNL.12), or to a presentation that leaves an internally mixed iterate in
place of an ordinary term.

For the first pump, let $D=\operatorname{dom}\theta$ and
$Y=Z_\eta\setminus D$ for the fully composed idempotent target MGU. A feasible
joint query supplies a finite valuation $w_0$ of $Y$ such that
$\theta(w_0)$ satisfies the whole of (RNL.16). Apply the preceding argument to
$\mathcal C_\eta[\theta]$, freezing $Y\setminus\{y\}$. The old pairs are
explicitly

$$
t_b[\tau][\theta]\ne t_c[\tau][\theta]\qquad(b<c).
\tag{RNL.17}
$$

They are ordinary terms. If any became identical, the alleged feasible joint
witness would violate that old inequality, so this query could not enter the
pump branch. Otherwise their one-coordinate forbidden sets are finite. The
same witness excludes an identically true forbidden equality for every
additional record. Choose a finite replacement for $y$ outside the union for
*both* lines of (RNL.16), with more than $2^h$ leaves; leave every other $Y$
coordinate fixed. Put $v_h=\theta(w_h)$. All bound coordinates are reconstructed
by this same $\theta$, and all preliminary eliminated coordinates by $\tau$.
Thus $u_h=W_\eta[\tau(v_h)]$ satisfies the entire original retained cell and
the diagnostic target equation. This step does not freeze a coordinate that
is required to depend on the varied $y$.

For the second pump discard the diagnostic target equation, but keep the
preliminary substitution $\tau$ and all of (RNL.16). Choose a bound coordinate
$x\in D$ whose ordinary term $\theta(x)$ contains $y$. Its current value
$v_h(x)$ has at least as many leaves as $w_h(y)$, hence more than $2^h$.
A binary tree of height at most $h$ has at most $2^h$ leaves, so there is a
branch at depth $h$ on a longer path in $v_h(x)$. Change only a child cone
below that branch. The resulting infinite family of finite replacements
agrees with $v_h(x)$ at every relative address of length at most $h$, and has
unbounded leaf count.

Now freeze every coordinate of $Z_\eta\setminus\{x\}$ at its value in $v_h$.
Use the *unsubstituted-by-$\theta$* list (RNL.16). Its old pairs are
$t_b[\tau]\ne t_c[\tau]$, and each is true at the current value $v_h(x)$.
Each again forbids at most one replacement for $x$; Lemma 3.1 supplies finite
forbidden sets for the additional records. Choose a member $x'_h$ of the
child-cone family outside their union and with larger leaf count than
$v_h(x)$. Set $v'_h=v_h[x:=x'_h]$ and
$u'_h=W_\eta[\tau(v'_h)]$. Other bound target coordinates stay fixed in this
step. Preliminary eliminated coordinates are reconstructed, rather than
independently frozen; the original source is always one filling of
$W_\eta[\tau]$. Hence $u_h,u'_h\in D^-$ with all old pairs and all additional
records true simultaneously.

Every occurrence of $x$ in the ordinary filled context $W_\eta[\tau]$ is
changed to that same $x'_h$. A global address through depth $h$ either stays
outside these occurrences or enters one at some original depth $k\ge0$ and
uses only a relative address of length at most $h-k\le h$. The common local
prefix therefore preserves every required original reply, including absence.
The recovery address $p_x$ of (RNL.9a) still recovers the actual residual
coordinate; no substitution shortens it. Since $Y\cap D=\varnothing$, the
second pump leaves $v'_h|_Y=v_h|_Y$. Every solution of the target equation must
satisfy

$$
v'_h(x)=\theta(x)[v'_h|_Y]
       =\theta(x)[v_h|_Y]=v_h(x),
\tag{RNL.18}
$$

whereas $x'_h\ne v_h(x)$. The target equality is therefore false on $u'_h$
and true on $u_h$. Proposition 2.2 gives their common reached target set and
the interpretation of this different partition bit as different full rows.

The exterior argument in Theorem 4.2 uses the same complete list (RNL.16),
with $\sigma$ the identity. If a residual coordinate occurs in $E_\eta$,
fix one feasible valuation and all other coordinates. Avoiding the finite
union for both old and added inequalities leaves infinitely many finite
values. A visible occurrence of that coordinate in the ordinary exterior
context makes these exteriors distinct by free-constructor cancellation.
This contradicts the finite complete-mask image. Thus its fixed-exterior
conclusion also holds on the whole old-row fiber.

All these choices are effective finite-source constructions: enumerate
finite trees with increasing leaf counts for the first pump, or fill the
fixed child cone with such trees for the second, and evaluate the whole
finite list (RNL.16) at each candidate. Finiteness of the forbidden union
ensures termination. A ground cell has no coordinate to pump and is checked
directly. An identity or ground-only target MGU has no binding of the required
kind, so it uses the existing constant or ground-test branch. Empty lists,
zero outer powers, coordinate-independent inequalities, $h=0$, repeated old
classes and off-task classes require no exception to the argument.

The construction produces proof-side alternative finite sources in the exact
fiber, under the authentic acquisition and complete-access hypotheses. It
supplies no new online source handle, free comparison, clone or reset, and
changes neither the common certified epoch nor the paid consumer (RNL.13).
This is a repo-derived completion of the applications of Lemma 3.1 and
[SLH, Theorem 74.4][SLH] inside Theorem 4.2; it extends neither the admitted
history signs nor the uniform-outer-power syntax. $\square$

## 追加锚（本行以下为增补区）
