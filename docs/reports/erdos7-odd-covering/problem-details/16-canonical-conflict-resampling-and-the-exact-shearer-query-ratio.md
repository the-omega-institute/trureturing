[Index](../../../../Problems/erdos-7-odd-covering-systems.md) · [Previous](15-exact-tensorization-for-two-fixed-depth-two-tree-shapes.md)

<a id="canonical-conflict-resampling-and-the-exact-shearer-query-ratio"></a>
### Canonical conflict resampling and the exact Shearer query ratio

Let Omega be a finite product probability with strictly positive coordinate
masses. Each bad event B_i fixes one assignment on a set I_i of coordinates.
Join distinct i,j precisely when their required assignments disagree on
I_i intersect I_j. Write V for the bad-event index set, p_i=Omega(B_i), and

    Z_U = sum_{J independent in U} (-1)^|J| product_{j in J} p_j.

The graph used in this polynomial has no loops; the algorithmic causality
neighborhood of a bad event includes itself. Assume Z_U>0 for every U⊆V.
Start from Omega, fix any history-dependent flaw-selection rule, and
resample all coordinates of the selected true bad event independently.
The rule is fixed throughout the conclusions below. Its terminal law is nu.

For every canonical query E, let N(E) be the original bad events whose
assignments conflict with E. Then

    nu(E) <= Omega(E) Z_(V minus N(E)) / Z_V.                 (1)

This is an ordinary mathematical consequence of the public theorem cited
below, with the extension verified here. No Lean kernel certification is
claimed, and (1) is a terminal-law bound, not an asserted exact hit bound.

<a id="structural-hypotheses"></a>
#### Structural hypotheses

Nonconflicting i,j cannot newly cause one another: while B_i holds, their
shared coordinates already have B_j's prescribed values; coordinates of
B_j outside I_i remain unchanged. Thus the conflict graph with self
neighborhoods is an undirected causality graph.

For the full-coordinate resampling kernel rho_i, the charge is exactly

    max_w [sum_(s in B_i) Omega(s) rho_i(s,w)] / Omega(w)
      = Omega(B_i)=p_i.                                    (2)

Indeed, only s matching w outside I_i contribute, and the factors on I_i
separate. The initial distribution equals the reference distribution, so
lambda_init=1.

For nonconflicting events with coordinate sets I,J, suppose
s --i--> t --j--> w is a valid trajectory. Define t' to equal s outside J,
w on J minus I, and the common required assignment on I intersect J.
Then s --j--> t' --i--> w is valid. Both products of transition
probabilities coincide coordinate by coordinate: on I intersect J they
are the mass of the common required value times the mass of w's value;
on I minus J and J minus I they are the mass of w's value. The swap is
injective since s,w recover t: t equals w on I minus J, the common
required assignment on I intersect J, and s outside I. This verifies
Iliopoulos Definition 2.1. The same proof holds after adjoining any
canonical event on an additional set of product coordinates.

<a id="rare-query-proof-of-1"></a>
#### Rare-query proof of (1)

[Iliopoulos](../../../../Library/Arith/iliopoulos2017commutative.md), arXiv:1704.02796v6, Theorem 3.2(1) and Remark 3.1, gives

    E[number of addresses of flaw i] <= q_{ {i} } / q_empty

under Shearer's condition. Here
q_S=sum_(J independent, S⊆J) (-1)^(|J|-|S|) product_(j in J) p_j.
Strict positivity of every Z_U implies q_empty=Z_V>0 and
q_S=(product_(i in S)p_i) Z_(V minus N[S])>0 for independent S;
nonindependent S have q_S=0. The theorem therefore applies and implies
finite expected total addresses, hence almost-sure original termination.

Adjoin an independent Bernoulli(epsilon) coordinate and the query flaw
E_epsilon=E intersect {coin=1}, resampling its coordinates and the coin.
Its charge is q=epsilon Omega(E), and its old neighbors are exactly N(E).
For U⊆V, the induced polynomial including the new vertex is

    Z_U - q Z_(U minus N(E)).

All old induced polynomials are positive; finitely many inequalities
therefore remain positive for every sufficiently small epsilon>0.
The extended system satisfies the structural hypotheses just verified.

Use a legal extended rule that first follows the original rule, ignoring
the coin, as long as an original flaw remains. At its first original
termination, address E_epsilon if present, and subsequently use any legal
rule. Before that first termination no action touches the coin. Thus the
expected total number of query addresses is at least epsilon nu(E).
Applying the quoted resampling bound to the extended query vertex gives

    epsilon nu(E)
      <= q Z_(V minus N(E)) / [Z_V-q Z_(V minus N(E))].

Divide by epsilon and let epsilon tend to zero. This proves (1) for the
same original terminal law, independent of the choice of query E.

<a id="one-univariate-ray-checks-every-induced-subgraph"></a>
#### One univariate ray checks every induced subgraph

Set Z_U(t)=sum_(J independent in U)(-t)^|J| product_(j in J)p_j.
If Z_V(t) has no zero on (0,1], then Z_U(1)>0 for every U⊆V.

Public source: [Scott and Sokal](../../../../Library/Arith/scottsokal2003repulsive.md), arXiv:cond-mat/0309352v2, Theorem 2.10(a)
⇔ (b′), hard-core self-repulsion. Condition (a) asks for a positive path
from 0 to -p in the negative orthant; the root-free ray supplies it since
Z_V(0)=1. Condition (b′) is exactly positivity for every induced U.

An elementary finite-polynomial verification is also available. Otherwise
let t* in (0,1] be the earliest zero among all induced polynomials. Every
Z_U(t*) is nonnegative. If Z_U(t*)=0 and v is outside U, deletion gives

    Z_(U union {v})(t*)
      = Z_U(t*) - t* p_v Z_(U minus N(v))(t*) <= 0.

Its nonnegativity forces equality. Adding vertices propagates the zero
to V, contradicting the assumed full-ray condition. Positivity merely at
t=1 is not sufficient; the entire interval condition is essential.

<a id="congruence-and-complete-layout-specialization"></a>
#### Congruence and complete-layout specialization

Encode residues modulo Q=product p^H_p by independent uniform p-adic
digits. A residue class modulo d|Q is a canonical event of probability
1/d. Apply the foregoing construction to the actual forbidden classes.
Every nonempty intersection of test classes C_d(b),C_e(b) from ONE fixed
complete layout b is canonical, with probability 1/lcm(d,e). Thus

    Gamma_Q(nu)
      <= max_b sum_(d,e|Q, C_d(b) intersect C_e(b) nonempty)
           Z_(V minus N(C_d(b) intersect C_e(b)))
           / [lcm(d,e) Z_V].                               (3)

The same nu is used for all pairs and all layouts. In (3), b assigns one
residue for every divisor, including one; do not maximize separate
summands. For a particular forbidden family, strict Shearer feasibility and a useful
bound on (3) are separate requirements. The star calculation below refutes
universal strict feasibility at the uniform-product charges `1/d`. No
unrestricted numerical Gamma_73 bound follows from these conditional estimates.

Before building the graph, remove any bad class contained in another bad
class; the avoided union and survivor set are unchanged. With one class
per distinct modulus, if d divides e then compatible assignments would
imply B_e⊆B_d. Hence every independent set of the reduced conflict graph
has moduli forming a divisor antichain. This connects its independence
polynomial to the divisor poset. It supplies no global signed-polynomial
bound by itself. Z_U uses products 1/d and is not the actual avoidance
probability computed using CRT intersection probabilities 1/lcm.

<a id="the-star-family-also-defeats-a-universal-conflict-shearer-head-criterion"></a>
#### The star family also defeats a universal conflict-Shearer head criterion

Use precisely the pure+star classes from the complete star-family construction above after removing redundant
mixed-zero classes. Let p run over the 20 odd primes through 73 and write

    a_p=sum_(e=1)^H_p p^(-e),
    B(z)=product_(p>=5) (1-z a_p).

For the canonical assignment-conflict graph, the signed independent-set
polynomial with activity z/d at modulus d is exactly

    Z(z)=(1-z a_3)B(z)
         +sum_(i=1)^H_3 [product_(p>=5)(1-z a_p(1+3^(-i)))-B(z)].  (1)

Indeed, independent sets containing no star vertex choose at most one
pure vertex for each prime, giving the first term. Star vertices in an
independent set must all use the same ternary C_(3,i), since different
such cylinders are disjoint. Once i is fixed, at each p>=5 one may choose
a pure p-vertex, a star vertex at p, or neither, but not both; each of the
two vertex groups is internally a clique. Their summed activities are
z a_p and z3^(-i)a_p. Choices at different p are compatible. A star also
conflicts with every pure ternary vertex. The product in the bracket
therefore counts precisely these choices with pure ternary excluded;
subtracting B(z) removes the no-star case. Different i correspond to
disjoint nonempty-star choices, proving (1).

At H_3=31 and H_p=8 for p>=5, exact rational evaluation of (1) gives

    -7/1000 < Z(1) < -69/10000,
    Z(1)=-0.006937138118224894... .

Since Z(0)=1, its real probability ray has a zero in (0,1). In particular
this actual, nonempty star survivor family is outside strict Shearer for
the conflict graph. The conditional commutative-resampling query theorem
remains valid, but its hypothesis cannot be asserted for all smooth
heads. Adding the redundant mixed-zero vertices cannot restore Shearer,
because the displayed failing graph remains an induced subgraph.

[verify_star_conflict_polynomial.py](../elementary-checks/verify_star_conflict_polynomial.py) uses exact fractions for the numerical
interval and independently compares (1) with all independent subsets of
the directly reconstructed 14-vertex CRT conflict graph at three rational
arguments for the height-two {3,5,7} case. This is an ordinary mathematical
identity and exact arithmetic check, not a Lean kernel result or a new
resolution of the odd covering problem.

<a id="exact-public-source-locators"></a>
#### Exact public source locators

- Fotis Iliopoulos, “Commutative Algorithms Approximate the
  LLL-distribution”, arXiv:1704.02796v6 (2019-06-08; first version 2017).
  Section 2.2 defines causality and charges; Definition 2.1 gives the
  probability-preserving injective swap; Theorem 3.2(1) and Remark 3.1
  give the Shearer resampling-count bound used above.
  https://arxiv.org/html/1704.02796v6
- Alexander D. Scott and Alan D. Sokal, “The repulsive lattice gas, the
  independent-set polynomial, and the Lovász local lemma”,
  arXiv:cond-mat/0309352v2 (2004-09-16; first version 2003),
  Theorem 2.10(a), (b′), and (f).
  https://arxiv.org/html/cond-mat/0309352v2
- [David G. Harris](../../../../Library/Arith/harris2016mosertardos.md), “New bounds for the Moser–Tardos distribution”,
  arXiv:1610.09653v7 (2019-10-10; first version 2016), Proposition 3.4.
  Its improved disjoint-union bound uses the ordinary shared-variable
  graph defined in Section 1.1. Propositions 2.7 and 3.3 retain that graph.
  It is not a cited justification for replacing it by the conflict graph.
  https://arxiv.org/html/1610.09653v7

<a id="falsifier"></a>
## Falsifier

The [exact bridge program](../bridge_checks.py)
retains two counterexamples to proposed proof steps, not to the conjecture.
Pairs below are `(residue, modulus)`.

1. Pure classes `(0,3),(0,5),(0,7),(0,11)` and mixed classes
   `(1,33),(46,55),(36,77),(136,165),(148,231),(281,385),(106,1155)`
   realize all seven nonempty old cofactors at the actual prefix `1 mod 105`.
   The old prefix has mass `1/48`; auxiliary height `(1,1,1)` has mass `4/105`.
   The quadratic count is `6`, while the aligned beta-load is `70/11 > 6`.
   Seven disjoint terminal hits give bad probability `7/10 > 2/3` and charge
   `11/20 > 1/2`. Every mixed class has an exclusive coverage witness;
   residue `106` makes cubic old cofactor `105` indispensable. Thus the
   quadratic substitution fails when the source's sparsity hypothesis is dropped.
2. History `(1,3),(1,5),(1,7),(2,15)`, current pure class `(10,11)`, and mixed
   classes `(0,33),(45,55),(35,77),(135,165),(147,231),(280,385),(105,1155)`
   leave 48 pure head survivors but 42 complete head survivors modulo 105.
   The source's normalized physical law `μ` retains the earlier mixed event
   at `δ5=0`; it differs from uniform conditioning `ν` on all 42 survivors.
   Conditioning raises the next expected charge from `11/960` to `11/840`
   and gives `ν(r5=0 | r3=2)=1/3 > 4/15`, violating the old cap. The conditioned
   quadratic expectation `1/84` is also below the actual charge `11/840`.
   This family leaves 364 residues uncovered modulo 1155, including `3`.
3. The [H73 verifier](../verify_h73.py) and
   [rational certificate](../certificates/h73_dual.json)
   refute the separate-cylinder head bound. With every odd prime at most 73
   raised to height four, an actual family containing every nonunit divisor
   has an explicit survivor, but every survivor probability has
   `κ_Q(μ) > 1621563/10000 > 138877/1000`. The proof follows below.

<a id="evidence"></a>
## Evidence

The bridge program enumerates full CRT periods and uses exact rational arithmetic.
It checks both families, actual cylinder membership, disjoint hits, exclusive
coverage witnesses, probability laws, charges, and the second uncovered count.
It does not import or execute external Lean or Python sources. Archive SHA
and source-substring comparisons bind formulas to the cited release only.

Reproduction requires Python 3.8+ and its standard library, with no installation
of third-party packages. Download the archive linked by
[schroeder2026noncoverage](../../../../Library/Arith/schroeder2026noncoverage.md), then run
from the repository root, replacing the archive argument with its location:

```sh
python3 docs/reports/erdos7-odd-covering/bridge_checks.py \
  --source-archive three_prime_factors_complete.zip
```

The program requires SHA-256
`5956327277ac47dd6e98a0a38f2a785cd61e647560c7f6ab5c73a63cf49faa51` and exits nonzero
on a mismatch even under `python3 -O`. Its paths can be supplied from any working
directory. Behavior checks ran on macOS with Python 3.14, including isolated
Python execution from a different directory with spaces in both input paths.
Other platforms and the minimum Python 3.8 runtime were not locally tested.
Source versions, pins, attribution, licenses, and completed external Lean checks
are in the Library notes. The bridge program is an original repository
experiment; it is not part of Schroeder's source release.

**H73: family and explicit survivor.** Let `P` be the 20 odd primes at most 73,
`Q = ∏_{p∈P} p⁴`, and `Q₀ = 3³·5²·7 = 4725`. The certificate's `core_residues`
contains 23 **`[modulus, residue]`** pairs, one for every nonunit divisor of
`Q₀`. Exact enumeration leaves 791 core survivors, including `3`.
For each outside prime `p ∈ P \ {3,5,7}` and `1 ≤ e ≤ 4`, assign the pure class

\[
 a_{p^e}=\frac{p^{e-1}-1}{p-1}.
\]

For a fixed prime these classes are pairwise disjoint: when `j > i`,
`a_{p^j} − a_{p^i} = p^{i−1}(1+p+⋯+p^{j−i−1})` is not divisible by `p^i`.
Thus avoiding the classes through level `e` permits exactly

\[
 N_p(e)=p^e-\sum_{i=0}^{e-1}p^i,\qquad N_p(0)=1
\]

residues modulo `p^e`. This follows by subtracting the disjoint lifts, of
sizes `p^{e−1},…,1`. Restrictions from higher levels or mixed classes can only
reduce the supported projections, so `N_p(e)` is an upper bound for them.

Put `M = ∏_{p∈P\{3,5,7}} p⁴`. Since `gcd(M,Q₀)=1`, define the explicit integer

\[
 w=\bigl(M\,((4M^{-1})\bmod Q_0)-1\bigr)\bmod Q.
\]

It satisfies `w ≡ 3 (mod Q₀)` and `w ≡ −1 (mod M)` and avoids every core and
outside pure class. On each remaining nonunit divisor `d | Q`, assign
`a_d = (w+1) mod d`. This cannot contain `w`, since `d > 1` cannot divide `1`.
All `5²⁰−1` moduli are odd, distinct and greater than one. The family includes
`Q`, so its actual least common multiple is `Q`. In particular, its survivor
set is nonempty and it does not cover the integers.

**H73: correlated-measure lifting.** Fix any probability `μ` supported on the
completed family's survivors, and project it to a probability `ν` modulo `Q₀`.
The latter is supported on the 791 core survivors. Write
`M_d(μ) = max_b μ{x : x ≡ b (mod d)}`. For `d | Q`, let `d₀ = gcd(d,Q₀)`,
`f_p = v_p(d)`, and set the core caps `a₃=3, a₅=2, a₇=1`. A fixed `d₀`-coset
meets at most

\[
 B(d)=\prod_{p\in\{3,5,7\}}p^{f_p-\min(f_p,a_p)}
       \prod_{p\in P\setminus\{3,5,7\}}N_p(f_p)
\]

supported `d`-cosets. CRT gives this counting bound on possible refinements;
it requires no independence of their probabilities. A `d₀`-coset attaining
`M_{d₀}(ν)` partitions into at most `B(d)` supported refinements. Pigeonholing
its mass, **separately for each divisor**, gives

\[
 M_d(\mu)\ge\frac{M_{d_0}(\nu)}{B(d)}.
\]

Regrouping the original coefficients `χ(d)/B(d)` by `d₀` therefore yields

\[
 \kappa_Q(\mu)\ge F\sum_{d_0\mid Q_0}\eta(d_0)M_{d_0}(\nu),\qquad
 F=\prod_{p\in P\setminus\{3,5,7\}}
       \left(1+\sum_{e=1}^4\frac{2e+1}{N_p(e)}\right).
\]

Here `η` is multiplicative on core divisors, with local coefficients

\[
 \eta(p^e)=2e+1\quad(0\le e<a_p),\qquad
 \eta(p^{a_p})=\sum_{k=0}^{4-a_p}\frac{2(a_p+k)+1}{p^k}.
\]

The sums include `d=1` and `d=Q` and retain the original `χ(p^e)=2e+1`.
The verifier independently reconstructs all 24 coefficients `η(d₀)` by
enumerating the 125 core exponent tuples in `{0,…,4}³`.

**H73: rational dual.** The certificate's 182 nonzero rational weights
`y_{d,b}` obey

\[
 y_{d,b}\ge0,\qquad \sum_b y_{d,b}\le\eta(d),\qquad
 \sum_{d\mid Q_0}y_{d,z\bmod d}\ge\alpha
 \quad\text{for every core survivor }z,\qquad
 \alpha=\frac{25730979793}{1000000000}.
\]

All omitted weights are zero. The verifier checks all 24 divisor budgets and
all 791 survivor inequalities; their minimum is exactly `α`. Consequently,

\[
 \sum_{d\mid Q_0}\eta(d)M_d(\nu)
 \ge\sum_{d,b}y_{d,b}\nu\{x:x\equiv b\pmod d\}
 =\sum_z\nu(z)\sum_{d\mid Q_0}y_{d,z\bmod d}\ge\alpha.
\]

Exact rational computation gives `α > 25`, `F > 6` and the sharper comparison

\[
 \kappa_Q(\mu)\ge\alpha F>
 \frac{1621563}{10000}>150>\frac{138877}{1000}.
\]

This proves H73 false for an actual finite height-four divisor family, for
every correlated or uncorrelated survivor measure. It is a mathematical proof
using exact finite computation, not a Lean formalization or a covering of `ℤ`.

**H73 reproduction.** The complete runtime inputs are the original repository
program `verify_h73.py` and `h73_dual.json`. The data contains only the 23 core
classes and 182 dual weights. A floating-point LP search supplied a candidate;
rational rounding and exact verification supply the certificate. No solver,
primal solution, numerical tolerance or process snapshot is needed or retained.
From the repository root run either command:

```sh
python3 docs/reports/erdos7-odd-covering/verify_h73.py
python3 -O docs/reports/erdos7-odd-covering/verify_h73.py
```

An optional positional certificate path is accepted; by default the JSON is
found beside the program, independently of the working directory. Python 3.8+
and its standard library suffice. Output includes exact rational `F` and `αF`,
the integer `Q`, family size and explicit integer `w`. Explicit failures remain
active with `-O`. The program checks the exceptional classes and the default
assignment rule; it does not enumerate all `5²⁰−1` full moduli. The passage from
the finite checks to all survivor probabilities is the counting and duality
proof above. Normal, optimized and isolated execution with spaced paths were
checked on macOS/Python 3.14; other platforms and Python 3.8 were not tested.

<a id="triage"></a>
## Triage

`wall`: user-selected third-tier core research. The unrestricted target remains
open. For the precise complete-star head assignment, arbitrary positive
head heights and completely unrestricted tails above 73 are excluded by
(US1)--(US12). The proof uses the actual broad-branch law, the published
conditional convex comparison, an exact positive-part certificate through
prime 2039 and a supported `Gamma<4331` seed for BBMST continuation.
It remains an ordinary mathematical proof with exact numerical premises,
not a complete Lean theorem. Other head assignments remain unresolved.
The results also include exact obstacles to earlier proof routes, a direct
joint-load transfer into the BBMST continuation, and a quantitative reduction
of the arbitrary-height sufficient condition to a finite exponent cap. A
uniform four-prime head bound additionally proves the restricted noncoverage
theorem (P1), allowing arbitrary prime support at or above 67. The star-family
pointwise layout certificate refutes Γ73 and every displayed universal
finite-base bound, while leaving the unrestricted conjecture open.
The block-saturation criterion gives further noncoverage theorems for
arbitrary `{3,5,7}` heads with sparse tail interactions, and for every
positive-height star head with matching tails. It also gives the actual
mixed-tail budgets (BS8)--(BS9) required of any full star completion.
The new graph arguments additionally permit arbitrary forest tails from
prime 19 for arbitrary three-prime heads,
arbitrary forest tails above 73 for full star heads, a degree-two core with
unrestricted pendant leaves from prime 37, and the stated hub-deletion
structures. The forest bound is independent of both depth and degree.
The feedback-vertex recurrence additionally permits one cycle-breaking
vertex per tail component from prime 23 for arbitrary three-prime heads,
and two per component above 73 for full star heads.
The local-parent capped-kernel criterion extends this to arbitrary
`20`-degenerate tails above 73 for full star heads, and to forests from 17,
`2`-degenerate graphs from 19 and planar graphs from 23 for arbitrary
three-prime heads. Its selective parent moment bound allows unbounded
feedback vertex number and treewidth. Arbitrary graph structure is also
allowed by (RK1)--(RK5) when each original modulus has at most two tail
primes for the full star or three-prime heads, or at most three for the
finite 315/945 heads, at the respective stated cutoffs. The finite
switch (RK6)--(RK8) already removes support restrictions above its cutoffs;
(PH1)--(PH7), sharpened by (AD1)--(AD5), further removes every tail support and graph restriction for
these head classes at the stated prime gaps. The head exponents for the
315/945 rows and the missing primes remain genuine hypotheses. The star
rows retain quantitative bounds, while (US1)--(US12) exclude all star
completions without those restrictions.
The finite supported-law bridge (FC4)--(FC5) sharpens the planar cutoff
to 17 for heads dividing 315 and to 19 for heads dividing 945, the two odd
parts in the frozen 5040 fibre.
The finite-height pure-coordinate CRT criterion and two-block refinement
give the independent finite exclusion `lcm > 11486474`: the verifier
discharges all 23758 odd abundant candidates in the interval from 1.
`TernaryRootLoadTail.root_load_tail_le` formalizes the finite-itinerary
component of the actual-layout improvement, and
`TwoRootEventMoment.two_root_event_moment_le` proves the bound for the
actual weighted event-load increment.
`ArbitraryRootEventMoment.arbitrary_root_event_moment_le` extends that
component to arbitrary root sets and geometric discounts, using an actual
event-chain induction;
`PrimeRectangleTransfer.prefix_weighted_rectangle_second_moment_le` formalizes
the weighted finite rectangle second-moment estimate underlying (W1),
with individual layer bounds retaining the shared zero layer.
`RestrictedSpineConstantPotential.restricted_spine_constant_potential`
formalizes the explicit constant-potential probability construction on arbitrary
finite restricted prefix trees, including its normalization and support.
`SequentialKernelCylinder.selected_cylinder_bound` formalizes the arbitrary
selected-coordinate cylinder bound for actual history-dependent Markov
kernels, directly reusing Mathlib's prefix-preservation result.
`HomogeneousCombCapacity.comb_le_actual_prefix_flow` formalizes the
all-height comparison between the actual forbidden-prefix flow recursion
and the extremal comb recursion, with arbitrary nonnegative capacities.
`PrefixCapacityRealization.exists_comb_capped_probability` constructs
an actual supported leaf probability from those capacities and derives
all prefix marginal caps after normalization.
No freeze or problem-resolution binding is supplied, and neither (P1) nor
(G1) is a complete Lean theorem.

<a id="assumed-unverified"></a>
## ASSUMED-UNVERIFIED

The external nine-prime result has no completed local kernel replay. The
three-factors-per-modulus theorem has the completed checks recorded in its
Library note, but `hThree` remains essential; its paper-only largest-prime-cutoff
extension is outside the Lean theorem. The joint-load transfer, exact finite
recurrence and restricted noncoverage theorem (P1) are proved above;
the universal Γ73 bound and the displayed sufficient finite-base bounds are
refuted by the complete star family.
These residue-level mathematical arguments have not been fully formalized
in Lean. The finite-itinerary and actual-event components are identified in (G2),
and the weighted finite rectangle second-moment component after (W1).
The nonuniform laws (N1)–(N10) and (NC1), sharp uniform bound (ZG1), shared-cofactor
improvement (P2), rectangular uniform-law obstruction and its nonuniform
repair (NR1) have ordinary mathematical proofs and exact rational checks,
not complete Lean proofs. The star-family refutation also has an ordinary
mathematical proof and exact certificate, not a complete Lean formalization;
its general restricted-tree probability construction is the Lean component
identified after (5) in the star-family proof.
H73 is refuted as a separate-cylinder claim. The random-tail layout certificate
additionally gives a true Gamma lower bound above 121.5478 for every law on
that family, below the sufficient threshold 138.877. Scalar-reweighting
optimality and the conditional conflict-graph query bridge also have ordinary
mathematical proofs, not complete Lean formalizations. Universal strict conflict-Shearer feasibility at charges `1/d` is false for
the star family; the conditional query theorem remains valid. No replacement
sufficient bound for unrestricted #7 is established here. These finite checks do not
establish literature priority or an unrestricted proof or covering counterexample.
The block-saturation criterion, its sparse-graph consequences for arbitrary
three-prime heads, and its all-positive-height star consequences also have
ordinary proofs and exact constant certificates, not complete Lean proofs.
The unrestricted-tail complete-star theorem (US1)--(US12) has the ordinary
actual-law, convex-comparison and stopping proof above and an exact directed
finite certificate. It does not extend the audited upstream Lean theorem
beyond its `hThree` hypothesis. The local selected-cylinder theorem proves
only the passage in (DG2); the changed star law, finite-height convex order,
original-label completion, positive-part computation and BBMST application
have not been combined into a Lean proof of the complete-star theorem.
The independent finite lcm exclusion through `11486474` likewise consists
of an ordinary CRT product-law proof and exact integer enumeration; no
local Lean formalization or duplicate declaration is claimed.

A [literal actual1575-source obstruction](../profile-notes/001-064/28-zero-local-losses-do-not-imply-a-common-maximizing-original-layout.md#zero-local-losses-do-not-imply-a-common-maximizing-original-layout)
shows that every central-unary star and every two-ended edge can have
zero separate loss while a common maximizing layout fails. The complete
triangle on original labels5/21/35 has exact loss9/382, retaining the
tradeoff of sacrificing one unary maximum. Pure11/13/17/19 extensions
preserve the example on all288 complete original labels of the actual
killed law. Both charges are zero; this is neither a positive-charge
classification nor a uniform numeric gain. Full support propagation
through the original period label does decide exact saturation; weighted
near-maximizing tradeoffs still require additional estimates.

A [proved density-domination bridge](../profile-notes/001-064/28-zero-local-losses-do-not-imply-a-common-maximizing-original-layout.md#dv-supported-probability-gives-lower-bounds-for-the-actual-ap-killed-law)
now transfers the DV supported probability to this actual AP13 killed
continuation. Under the substantive restriction that the entire original
357 part divides315, it proves `nu_* <= (38288250/4021271) nu13`, then
propagates the same actual17/19 kernels. For every inherited complete old
test, the actual surviving masses satisfy `eta(A<=8)>0.04294732385` and
`eta(A<=10)>0.05394558166`. Directly transferring the nonnegative
floor deficit gives `Delta81>1.97207505589` and `Delta121>4.78724716815`
in CT3, with all original11/13/17/19 heights and cofactors retained.
This uses domination in its proved direction, not substitution of the
auxiliary moments into actual-law upper bounds. It does not extend to
arbitrary original357 heights or complete the remaining frontier.

An [all-seven-height extension](../profile-notes/001-064/29-a-common-old-block-budget-strengthens-the-actual-mask-certificate.md#a-positive-actual-deficit-with-arbitrary-seven-heights)
now removes the seven-height restriction in that bridge: every original
357 part may divide `45*7^H`, for any finite H. The supported core is
lifted, all high-seven forbidden and complete test labels are paid, and
retained auxiliary mass is at least669289/869464. Hinge-based charges,
including the full17 comparison tail, total less than0.249864067.
Transporting capped nonnegative minorants gives, for every complete
final test on the same actual AP13/killed17/19 law,
`Delta81>1.721417864` and `Delta121>3.917246877`. The general formula
keeps distinct budgets for omitted forbidden labels and complete test
labels; absent forbidden moduli do not remove divisor-test labels.
All11/13/17/19 heights and cofactors remain arbitrary. Original3-exponents
above2,5-exponents above1, the unrestricted299.661 joint bound and the
later-prime continuation remain open. This is an ordinary proof with
exact rational verification, not a new Lean result.

A [common old-block budget](../profile-notes/001-064/29-a-common-old-block-budget-strengthens-the-actual-mask-certificate.md#a-common-old-block-budget-strengthens-the-actual-mask-certificate)
now strengthens the actual MW interface. Each positive-current old block
obeys the same G(g) square budget, giving a one-price joint integer
maximum with all current tails retained. If the original modulus19 class
is present, it reduces the G(g) coefficient by104976/811405621 and
retains a further nonnegative actual-mask integral. An actual all-divisor
unit family proves this coefficient sharp for that certificate form;
at current height3 it also refutes doubling the coefficient and gives a
strict integer-interface improvement3499529/10779402240.

A second, literal six-class family of period513 shows the scalar budget
strictly improves the full old parameter family: its continuous minimum
is3.7106583639706385, while price1/18 gives3.710034179714640. All729 original
old residue layouts and an endpoint supporting tangent are checked
exactly. Its old integer bound already equals its budgeted integer bound;
that distinct improvement is not claimed on this second family.

The actual subprobability constraint q<=1 also sharpens the complete MW
old-test error to less than0.000357927 at box16 and0.000005399757 at box20.
The budgeted integer bound pays its price term and preserves the full
original label ceiling inside its rounding optimization. These results
use the same actual xi and kernels; they do not bound changes to forbidden
masks, provide the remaining299.661 uniform frontier, or supply an
independent rebate to add to the stronger OBE profile.

An [actual threshold-deficit certificate](../profile-notes/001-064/30-actual-threshold-deficits-and-sharp-row-caps.md#actual-threshold-deficits-and-sharp-row-caps)
now retains the joint square observation `G(min(alpha19,7/17))`, the
assigned loss and explicit nonnegative row-curvature terms. Its general
all-height bound uses the actual killed17 input and full original old
test domain. A family with7+8H distinct odd moduli, of period3^7*19^H,
shows that all four BM15 pointwise row constants are limiting sharp
even for actual AP rows. At H=2 the new observation improves the
rectangular relaxation from5.34179178255 to4.89000232359; the more
informative exact MW bound is4.83872561480 and is not improved by this
relaxation.

For the D7 domain `357 part | 45*7^H`, the same supported-law bridge
forces the actual19 threshold deficit
`(7/17)G(1)-G(min(alpha19,7/17))>0.002509422159`.
The proof controls the actual union via complete old cofactor hinges,
then transports a bounded nonnegative shortfall through killed17;
every auxiliary17 comparison tail is paid. RC consequently improves
its rectangular endpoint envelope uniformly by more than0.000862026574
on this domain. This spends RC's own deficit and cannot be subtracted
again from BM/OBE. The unrestricted joint frontier and later-prime
continuation remain unproved; all these results are ordinary mathematics
with exact rational certificates, not new Lean declarations.
