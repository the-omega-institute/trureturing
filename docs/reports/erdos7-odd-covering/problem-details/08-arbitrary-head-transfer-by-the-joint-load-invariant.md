[Index](../../../../Problems/erdos-7-odd-covering-systems.md) · [Previous](07-ordered-local-kernels-unbounded-feedback-sets-and-treewidth.md) · [Next](09-quantitative-extension-of-the-old-prime-powers.md)

<a id="arbitrary-head-transfer-by-the-joint-load-invariant"></a>
### Arbitrary-head transfer by the joint-load invariant

Let `Q` be a positive integer, `p` a prime not dividing `Q`, and `H ≥ 1`.
A layout chooses one residue `b_d mod d` for each divisor `d | Q`, including
`d = 1`; write `L_b(x) = ∑_{d | Q} 1_{x ≡ b_d (mod d)}` and
`Γ_Q(μ) = max_b E_μ L_b²`. Different layout residues need not be compatible.
All probability spaces below are finite. No independence of the coordinates
of the old probability `μ` is assumed.

**One-prime estimate.** Put

\[
 S_p(H)=\sum_{e=1}^H p^{-e},\qquad
 A_p(H)=\sum_{e=1}^H(2e+1)p^{-e}.
\]

For `0 ≤ δ < 1`, let `K(y | x)` be a probability kernel from `Z/QZ` to
`Z/p^H Z` with

\[
 K(y\mid x)\le\frac{1}{(1-\delta)p^H}.
\]

The joint probability `ν(x,y) = μ(x)K(y | x)`, interpreted by CRT, satisfies

\[
 \boxed{\Gamma_{Qp^H}(\nu)
 \le\Gamma_Q(\mu)\left(1+\frac{A_p(H)}{1-\delta}\right).}
 \tag{T1}
\]

For any actual family with at most one forbidden residue for each new
modulus `dp^e`, `d | Q`, `1 ≤ e ≤ H`, let `α(x)` be the fraction of the
uniform new-prime fibre covered by these classes. Then

\[
 \boxed{\mathbb E_\mu\alpha^2\le\Gamma_Q(\mu)S_p(H)^2.}
 \tag{T2}
\]

**Proof.** Fix a full layout and group its moduli by `e = v_p(d)`.
Each group gives an old layout load `L_e(x)`, because the map `d ↦ dp^e`
is injective on divisors of `Q`. For any `e,f`, Cauchy–Schwarz gives

\[
 \mathbb E_\mu[L_eL_f]
 \le\sqrt{\mathbb E_\mu L_e^2\,\mathbb E_\mu L_f^2}
 \le\Gamma_Q(\mu).
 \tag{T3}
\]

Expand the full squared load into ordered pairs of classes. When `e=f=0`,
the new coordinate is unrestricted, so normalization of `K` leaves the old
expectation unchanged. Otherwise the intersection of the two new-prime
conditions is empty or a single cylinder modulo `p^{max(e,f)}`. Its conditional
probability is at most `p^{-max(e,f)}/(1−δ)`. This bound holds separately for
every pair, even when their new-prime residues depend on their old moduli.
After applying it, sum the old indicators and use (T3). There are exactly
`2t+1` ordered exponent pairs with maximum `t`. This proves (T1).

The weighted rectangle theorem described after (W1) supplies the more general
formal estimate. A constant prefix cap `M_t=p^{-t}/(1−δ)` recovers this
coefficient; Mathlib's modular interval count supplies that cap from the
pointwise bound on `K`. The divisor-layout embedding by CRT, the maximum
defining `Γ`, and construction of the capped kernel remain separate
formalization obligations.

For the actual forbidden classes, their old conditions give partial loads
`F_e`; distinct moduli ensure at most one class per old divisor in each group.
Complete these partial loads to layouts. A union bound in each uniform fibre
and (T3) then give

\[
 \alpha(x)\le\sum_{e=1}^H p^{-e}F_e(x),\qquad
 \mathbb E_\mu\alpha^2
 \le\sum_{e,f=1}^H p^{-e-f}\mathbb E_\mu[F_eF_f]
 \le S_p(H)^2\Gamma_Q(\mu).
\]

This proves (T2), with all old cofactors and arbitrary exponents retained.

**Capped deletion.** For `0 < δ ≤ 1/2`, use the BBMST kernel. In a fibre
with `α ≤ δ`, give zero weight to forbidden points and multiply uniform
weight at every other point by `1/(1−α)`. In a fibre with `α > δ`, multiply
uniform weight by `(α−δ)/(α(1−δ))` on forbidden points and by `1/(1−δ)`
on other points. Both cases are normalized and obey the cap in (T1).
The first case has `α < 1`, and the second has `α > 0`; no division by zero
is used. Completely forbidden fibres, where `α=1`, keep their original mass.

If `B` is the union of the new forbidden classes, then

\[
 \nu(B)=\frac{\mathbb E_\mu(\alpha-\delta)_+}{1-\delta}
 \le\frac{\mathbb E_\mu\alpha^2}{4\delta(1-\delta)}
 \le\frac{\Gamma_Q(\mu)S_p(H)^2}{4\delta(1-\delta)}.
 \tag{T4}
\]

Here `(t−δ)_+ ≤ t²/(4δ)` follows from `(t−2δ)² ≥ 0` when `t ≥ δ`;
it is immediate otherwise. If `R` denotes the complete old survivor set and
`R'=(R×Z/p^H Z)\B`, preservation of the old marginal gives

\[
 \nu(R')\ge\mu(R)-\nu(B).
 \tag{T5}
\]

The physical probability is **not** conditioned on complete survival at each
step. Its mass on previously forbidden points is permitted; (T5) separately
tracks the mass on the complete survivor set. Thus zero-survival fibres cause
no hidden positivity assumption and do not change the kernel cap.

**Iteration.** Start with any probability on complete head survivors having
`Γ ≤ C`, so its initial survivor mass is one. Index all subsequent primes in
increasing order, padding omitted primes by unused coordinates if needed. Put
`G_0=C`, `s_0=1`, and, at each subsequent prime `p`, define

\[
 a_p=\frac{3p-1}{(p-1)^2},\qquad
 G'=G\left(1+\frac{a_p}{1-\delta}\right),\qquad
 s'=s-\frac{G}{4\delta(1-\delta)(p-1)^2}.
\]

Since `S_p(H) ≤ 1/(p−1)` and `A_p(H) ≤ a_p`, induction using (T1), (T4)
and (T5) gives `Γ ≤ G` and complete survivor mass at least `s`.
If the next `s'` is positive, `F=G/s` obeys the exact scalar recurrence

\[
 \boxed{F'=\frac{(1+a_p/(1-\delta))F}
 {1-F/[4\delta(1-\delta)(p-1)^2]}.}
 \tag{T6}
\]

Every denominator must be strictly positive. This is BBMST's recurrence,
now with an arbitrary correlated head and `C=Γ_head(μ)` as its seed.
The kernel construction and scalar continuation are reused from
[BBMST, §2 and §6](../../../../Library/Arith/balister2018covering.md); (T1)–(T3)
justify using the joint-layout seed in place of a sum of separate cylinder maxima.
The searched project congruence declarations, pinned Mathlib probability and
combinatorics files, and these BBMST papers supplied the component inequalities,
but no exact joint-layout head theorem was identified. This bounded search does
not establish literature priority. The argument here is not a Lean formalization.

<a id="exact-feasibility-of-a-complete-survivor-kernel-with-cylinder-caps"></a>
### Exact feasibility of a complete-survivor kernel with cylinder caps

Let `X` be a finite old survivor carrier, `Y=Z/p^H Z` with prime `p` and
`H≥1`, and `U` its uniform law. Let `R⊆X×Y` be the actual complete survivor
relation and put `s(x)=U(R_x)`. Fix an old probability `μ` and `C≥1`.
There exists a law supported on `R`, with old marginal `μ` and conditional
cylinder masses at most `C p^{-e}` at every depth `1≤e≤H`, if and only if

\[
 s(x)\ge1/C\quad\text{for every }x\text{ with }\mu(x)>0.
\]

For necessity, sum the depth-`H` singleton caps over `R_x`. For sufficiency,
use the uniform conditional law on `R_x`; a depth-`e` cylinder has ambient
mass `p^{-e}`, and restriction followed by normalization costs at most `C`.
This is a condition on actual fibre survival, not just the new marginal.

If the old marginal may instead be any `μ'≤Dμ`, for `D≥1`, the exact
criterion becomes

\[
 \mu\{x:s(x)\ge1/C\}\ge1/D.
\]

Necessity follows because `μ'` is supported on this set and has total mass
one. For sufficiency, restrict `μ` to this set and normalize, then use the
same conditional construction. These are elementary finite deductions;
no new Lean declaration is required.

The positivity premise can fail in a complete legal `{3,5}` family.
At every common height `H≥4`, forbid residue zero at all pure powers.
For the four mixed moduli `3^i·5`, `1≤i≤4`, forbid the CRT class
`(1 mod 3^i, i mod 5)`; at every other mixed divisor forbid residue zero.
These rules assign one class to every nonunit divisor, without duplication.
The pure ternary survivor set `X` comprises roots `1,2 mod 3`. Above every
`x≡1 mod 81`, the pure-5 class removes root zero and the four special
mixed classes remove roots `1,2,3,4 mod 5`. Thus that entire fibre is empty.
Its uniform `X`-mass is exactly `(1/81)/(2/3)=1/54` at every `H≥4`.
Nevertheless `x≡2 mod 3`, `y≠0 mod 5` always survives, so the complete
family has survivors. Hence a complete-survivor extension preserving the
uniform old marginal need not exist, even without a cylinder cap.

The [exact finite verifier](../elementary-checks/verify_fibre_coupling_obstruction.py)
checks all 24 nonunit divisors at height four and all relevant pairs in the
period `81·625=50625`, yielding 22000 complete survivors and exactly one
empty old survivor fibre among 54. The all-height assertion follows from
the reductions modulo 81 and 5 above. This result explains why the capped
deletion route (T4) tracks complete survivor mass separately and why a
strict survivor kernel must sometimes change the old marginal. Neither
argument establishes the universal Γ73 bound.

<a id="transfer-retaining-the-actual-forbidden-fibre-geometry"></a>
### Transfer retaining the actual forbidden-fibre geometry

Extend `Γ_Q` homogeneously to finite positive measures. For an arbitrary
normalized kernel `K_x` on `Z/p^H Z`, set

\[
 M_t(x)=\max_{b\bmod p^t}K_x(y\equiv b\pmod{p^t}).
\]

The joint-load argument gives the stronger, measure-dependent estimate

\[
 \boxed{\Gamma_{Qp^H}(\mu K)
 \le\Gamma_Q(\mu)+\sum_{t=1}^H(2t+1)\Gamma_Q(M_t\mu).}
 \tag{W1}
\]

Indeed, for exponent groups `(e,f)` with `max(e,f)=t`, each nonempty current
intersection is a depth-`t` prefix and has conditional mass at most `M_t(x)`.
If `A_e,A_f` are their complete old loads, weighted Cauchy–Schwarz gives
`∫M_t A_e A_f dμ≤Γ_Q(M_t μ)`. There are `2t+1` such ordered groups.
The old-old contribution remains at most `Γ_Q(μ)`. All old cofactors,
including 1, remain in these loads.

The finite weighted rectangle estimate is formalized in
[PrimeRectangleTransfer.prefix_weighted_rectangle_second_moment_le](../../../../D5/S3/Arith/Congruence/PrimeRectangleTransfer.lean).
For arbitrary finite `X,I`, nonnegative old weights `μ(x)` and coefficients
`A(e,i,x)`, it takes a normalized nonnegative kernel `K(x,y)` and bounds
on each actual single-prefix mass by `M_t(x)`. If the zero layer has second
moment at most `G_0`, and each layer `e≤t` has its own second-moment bound `G(t,e)`
under the weighted measure `μ M_t`, then the actual modular rectangle load
has second moment at most

\[
 G_0+\sum_{t=1}^H\left[\sum_{e=0}^tG(t,e)+tG(t,t)\right].
\]

Taking `G(t,0)=D_t` and `G(t,e)=G_t` for positive `e` gives
`D_t+2tG_t` at depth `t`; setting all layer bounds equal recovers (W1).
Keeping the zero layer distinct is the formal ingredient used in (ZG2).

The theorem includes `H=0`, permits correlation between `x` and the kernel,
and does not require normalization of `μ`. It proves intersection bounds
from single-prefix bounds, derives nonnegativity of the prefix envelope,
and counts the exponent pairs by induction. Its compiled axiom closure
contains only `propext`, `Classical.choice` and `Quot.sound`.
It does not define the maximum `Γ`, construct `K`, or supply the CRT
embedding of a divisor layout; those are still outside this Lean theorem.

For the BBMST kernel take the current base law `U` to be uniform on
`Z/p^H Z`, with **all** new forbidden classes, including pure powers, in
the actual union `B_x`. Put

\[
 \alpha(x)=U(B_x),\quad \theta(x)=\min\{\alpha(x),\delta\},\quad
 m_t(x)=\min_{b\bmod p^t}U(B_x\cap\{y\equiv b\pmod{p^t}\}).
\]

The outside density is `1/(1−θ)` and the inside density is
`(α−δ)_+/(α(1−δ))`. Subtracting these densities and summing on a prefix
proves the exact formula

\[
 M_t(x)=\frac{p^{-t}-(\theta/\alpha)m_t(x)}{1-\theta},
 \tag{W2}
\]

where `(θ/α)m_t` is defined as zero at `α=0`. The formula also applies
at `α=1`. In particular, with `c_t=p^{-t}/(1−δ)`,

\[
 c_t-M_t=
 \frac{p^{-t}(\delta-\theta)}{(1-\delta)(1-\theta)}
 +\frac{\theta m_t}{\alpha(1-\theta)}\ge0.
 \tag{W3}
\]

Since every old layout has load at least one,
`Γ_Q(M_t μ)≤c_t Γ_Q(μ)−E_μ(c_t−M_t)`. Consequently

\[
 \Gamma_{Qp^H}(\mu K)
 \le\Gamma_Q(\mu)\left(1+\frac{A_p(H)}{1-\delta}\right)
       -\sum_{t=1}^H(2t+1)\mathbb E_\mu(c_t-M_t).
 \tag{W4}
\]

The second term of (W3) measures forbidden occupancy in every depth-`t`
prefix and can be positive even when `α≥δ`. The weighted estimate (W1)
additionally retains its correlation with the old test loads.
For the actual ending-event charge `b=(μK)(B)`, the first term alone gives
the joint inequality

\[
 \Gamma_{Qp^H}(\mu K)+A_p(H)b
 \le\Gamma_Q(\mu)\left(1+\frac{A_p(H)}{1-\delta}\right)
       +\frac{A_p(H)(\mathbb E_\mu\alpha-\delta)}{1-\delta}.
 \tag{W5}
\]

To obtain it use
`E(δ−α)_+=δ−Eα+(1−δ)b` in (W3)–(W4).

The geometry in (W2) can be computed without counting nested exclusions
twice. Write the actual union as `⋃_j A_j×J_j`, combining equal old
cylinders, and order proper old supersets before subsets. Replacing `J_j`
by `J_j\⋃_{i:A_j⊊A_i}J_i` preserves this union. A point removed from one
rectangle lies in a rectangle with a strictly larger old cylinder, and
this finite ascent terminates. For irredundant full congruence classes,
intersecting current prefixes from these ancestors lie strictly inside the
child prefix; their maximal members are disjoint, so their masses subtract
by finite additivity. This is the local prefix-packing calculation behind
the Kraft inequality.

Both `α` and `m_t` must refer to that same actual union. An upper bound
on `α` supplies no lower bound on `m_t`; a base already conditioned away
from pure-power classes cannot use the numerical `p^{-t}` factors unchanged.
The project’s `CompatibleResidueJointImage` and `FiniteCompatibleCrt`
provide the congruence compatibility statements, and pinned Mathlib's
`InformationTheory/Coding/KraftMcMillan.lean` supplies prefix packing.
The rectangle component of (W1) is formalized as stated above. The exact
clipped-kernel formula (W2), its consequences (W3)–(W5), and the full
divisor-layout embedding have not been formalized in Lean.
A uniform accumulated improvement yielding Γ73 is ruled out by the star family.

<a id="forced-loss-on-an-actual-pure-prime-forbidden-root"></a>
### Forced loss on an actual pure-prime forbidden root

Let Q=3^a M with a>=1 and gcd(3,M)=1. Let U be uniform on Z/QZ,
B the actual forbidden union, and s=U(B^c)>0. Suppose B contains an
actual class A=r mod 3. For every complete test layout L, let T be its
subload indexed by the divisors of M, including 1. Then L>=T>=1 and the
law of the M-coordinate conditional on A is uniform.

Write

    Z_M = sum_{d|M} 1/d = product_{p|M}(1+S_p),
    C_M = sum_{d,e|M, gcd(d,e)=1} 1/(de)
        = product_{p|M}(1+2S_p),
    S_p = sum_{j=1}^{v_p(M)} p^(-j).

Every diagonal term in E(T^2) has mass 1/d, and every pair of distinct
coprime test moduli intersects with mass 1/(de), independently of the
chosen residues. All remaining intersections have nonnegative mass.
Therefore every complete cofactor layout satisfies

    E_U(T^2) >= Z_M+C_M-1.                         (1)

This is a lower bound on all complete layouts, not the maximum Gamma.
Since L^2>=1 on B\A as well, the total forbidden loss obeys

    integral_B L^2 dU >= U(B)+(Z_M+C_M-2)/3.       (2)

The ordinary complete-layout uniform maximum is

    K_Q = product_{p|Q}[1+sum_{j=1}^{v_p(Q)}(2j+1)p^(-j)].

Combining (2) with this exact maximum gives a parameterized survivor bound

    Gamma(U conditioned on B^c)
      <= 1+[K_Q-1-(Z_M+C_M-2)/3]/s.               (3)

The extra loss is positive whenever M>1. It strengthens the bound using
only the total deleted mass. It is valid for arbitrary finite exponents
and all test cofactors, with no alignment assumption.

<a id="sharpness-of-the-cofactor-lower-bound"></a>
#### Sharpness of the cofactor lower bound

For P=prime support of M, suppose p-1>=2^(|P|-1) for every p in P.
This includes P contained in {5,7,11}. For each p, assign different nonzero
digits c_p(S) in {1,...,p-1} to the supports S contained in P with p in S.
For a divisor d with support S and exponent e>0 at p, choose by CRT

    a_d = c_p(S) p^(e-1) mod p^e.

Two such p-prefixes of different depths are disjoint; prefixes of the same
depth and different support labels are also disjoint. Thus distinct
divisors sharing a prime have disjoint test classes. Coprime pairs have
the forced intersection 1/(de). This constructs a complete layout attaining
(1), so its lower bound is exact for arbitrary heights on {5,7,11}.

<a id="comparison-with-the-current-head-estimates"></a>
#### Comparison with the current head estimates

The existing same-family density bounds imply

    s_357 >= 5/42,   s_35711 >= 1591/30240.

For example s_35>=1/4 follows from the two-root budget; subsequent factors
are (5/6)(1-(15/7)/5) and (9/10)(1-(1649/360)/9).

The numerator of (3) is increasing in every finite height: for an exponent
increment in M, K-local factors dominate both Z-local and C-local factors,
and the K increment has coefficient 2j+1>=3. Hence the infinite-height
values give valid bounds simultaneously, without mixing incompatible maxima.

For support {3,5,7}:

    K_Q <= 35/4, Z_M ->35/24, C_M ->2,
    extra loss ->35/72,
    resulting universal bound from (3): 3721/60.

For support {3,5,7,11}:

    K_Q <=231/20, Z_M ->77/48, C_M ->12/5,
    extra loss ->481/720,
    resulting universal bound from (3): 300421/1591.

These improve the bare deleted-mass bounds 661/10 and 320623/1591,
respectively. They do not improve the existing survivor bounds 481/12
and 4939031/47730. The absent-modulus-3 case uses the already stronger
existing unsplit branch. No new best head constant results.

<a id="why-this-does-not-automatically-improve-the-pure-survivor-base"></a>
#### Why this does not automatically improve the pure-survivor base

Suppose the actual family contains 0 mod p for each p in P, and let nu
be the product of the pure-prime survivor laws. Choose every nonunit test
residue to be 0. Every nonunit test cylinder then lies in an actual pure
forbidden root, so the complete test load is identically 1 on nu's support.
For any additional mixed forbidden union D of positive nu-mass,

    integral_D L^2 dnu = nu(D).

Thus no positive extra loss valid for every test layout can be imported
into this already conditioned base. A useful improvement there must
couple the extra loss to how close the test layout is to maximizing its
moment. Such a uniform high-load tradeoff is not established here.

These are ordinary mathematical proofs. No new Lean declaration is supplied.

<a id="actual-forbidden-class-projection-and-its-open-quantitative-input"></a>
### Actual forbidden-class projection and its open quantitative input

A second-moment projection retains the actual intersections supplied by CRT.
Let `rho` be any finite positive measure, `B` the union of actual forbidden
classes `A_i`, and `s=rho(B^c)>0`. For a complete test load `L`, define

\[
 G_{ij}=\rho(A_i\cap A_j),\qquad
 c_i=\int L\,1_{A_i}\,d\rho.
\]

For every real vector `z`, integrating
`(L−sum_i z_i 1_{A_i})²≥0` over `B` gives

\[
 \int L^2\,d(\rho|_{B^c}/s)
 \le\frac{\int L^2d\rho-2z^Tc+z^TGz}{s}.
\]

This is ordinary finite least-squares projection. It permits dependent
forbidden classes and either sign of `z`; there is no assumed alignment
between their residues and the test layout. Under a full uniform law,
CRT computes each Gram entry and each test/forbidden intersection as zero
or `1/lcm(d,e)`. Under a weighted root law, the actual weighted intersections
must be retained. The matrix is positive semidefinite because
`z^TGz=integral(sum_i z_i 1_Ai)²≥0`.

Using this identity as a quantitative upper estimate requires control of
the subtraction and the test load's deficit from the unconditioned maximum,
for the actual family and every complete test layout. The star family rules
out obtaining the proposed universal Γ73 bound by this method. These
projection identities are reused as tools; no new Lean wrapper is supplied.

<a id="exact-saturation-despite-actual-mixed-deletion"></a>
### Exact saturation despite actual mixed deletion

For every integer Q>1, prime p not dividing Q, and H>=1, put N=p^H.
Use the actual old forbidden class 1 mod Q and old survivor law mu=delta_0.
Use the single actual new forbidden mixed class 0 mod QN. These moduli are
distinct and the true combined least common multiple is QN. On the only
old point charged by mu, the forbidden fibre B is the singleton {0} in
Z/NZ. Thus alpha=1/N. Choose any 0<delta<alpha, and use the BBMST clipped
kernel K. Its mass at y is

    K(0)=(alpha-delta)/(1-delta),
    K(y)=1/[N(1-delta)] for y != 0.

The actual mixed ending charge is b=K(0)>0. For every 1<=t<=H a prefix
in root 1 avoids B, so m_t=0 and

    M_t=c_t=1/[p^t(1-delta)].

Consequently Gamma_Q(M_t mu)=c_t Gamma_Q(mu), with Gamma_Q(mu)=tau(Q)^2.
This already excludes a strictly positive universal rebate based only on
positive b, alpha>=delta, or positive distortion, without an additional
old-law or test/forbidden-overlap assumption.

The entire transfer inequality is also sharp. For every divisor d of Q,
choose the exponent-zero test residue to be 0 mod d. For every 1<=e<=H,
choose the residue at divisor d p^e by CRT to be 0 mod d and 1 mod p^e.
All old cofactors occur. On the support of mu the literal test load is

    L(y)=tau(Q) [1+sum_{e=1}^H 1_{y=1 mod p^e}].

The selected prefixes are nested, and their K-masses equal c_e. Expanding
the square assigns coefficient 2t+1 to pairs whose maximum exponent is t.
The concrete layout therefore gives

    Gamma_{QN}(mu K)
      >= tau(Q)^2 [1+sum_{t=1}^H (2t+1)c_t].

W1 gives the reverse inequality, hence equality. This is an ordinary
mathematical proof using the existing transfer theorem, not new Lean.

There is also strictly positive chi-square distortion energy:

    E_U[(dK/dU-1)^2]
      = delta^2(1-alpha)/[alpha(1-delta)^2] > 0.

Relative entropy D(K||U) is strictly positive because K differs from U.
Neither scalar energy nor entropy forces a test-layout penalty here.
The test load is small on the actual forbidden singleton and maximized
along a different p-adic path; alignment must not be assumed.

The old law is a Dirac law supported on actual survivors. It is not uniform
on all old survivors. Thus this does not refute stronger bounds restricted
to a uniform head law, nor bounds requiring quantitative regularity.

For any finite old layout family, c>=w>=0 also gives the exact identity

    c Gamma(mu)-Gamma(w mu)
      = min_lambda {c[Gamma(mu)-E_mu L_lambda^2]
                    +E_mu[(c-w)L_lambda^2]}.

This separates old-layout suboptimality from weighted loss. A positive
improvement needs a lower bound on their sum for every old layout. It is
an algebraic identity, not a proposed new Lean declaration.

<a id="verification"></a>
#### Verification

[The saturation verifier](../elementary-checks/verify_actual_union_saturation.py)
uses rational arithmetic and explicit exceptions. It verifies
the prefix masses, common nested layout, full transfer equality, positive
charge and energy for seven choices, with arbitrary old prime-power factors
among the examples. Three H=1 cases exhaust all 891 literal layouts in
total. Finite checks support the displayed construction; the proof above
covers arbitrary Q,p,H.

<a id="literature-boundary"></a>
#### Literature boundary

BBMST, arXiv:1811.03547, Lemma labelled lem:distortion, proves
E_i Delta_i <= 2 sum_{d in D_i} nu(d)/d for
Delta_i=max(0,log(Pr_i/Pr_0)). Its use is a lower bound on uniform uncovered
density. It does not prove positive correlation with arbitrary test loads.
BBMST, arXiv:1901.11465, subsection 'Constructing the measure Pr_5', optimizes
nonuniform survivor masses by linear programming in the squarefree setting.
It provides a route to optimize the old law, not a universal rebate for the
fixed arbitrary law in this example.

<a id="exact-continuation-from-the-conditional-73-head-seed"></a>
### Exact continuation from the conditional 73-head seed

[The finite continuation verifier](../verify_finite_continuation.py)
uses Python 3.9+ standard-library integer and rational arithmetic. It starts at
`p_21=73`, `F_21=138877/1000`, checks each rational choice `0<δ≤1/2`,
checks positivity of every denominator in (T6), and rounds each resulting `F`
upward to a grid of `10^−12`. It checks 13,141,979 successive prime steps and
obtains, at `k=13,142,000`, `p_k=239,622,407`,

\[
 F_k\le\frac{860976507525503444783}{250000000000}
 <\frac{430488883362679218496182453443671999019139}
 {125000000000000000000000000000000}
 \le k(\log k+\log\log k-3)^2.
\]

The second rational is a lower bound obtained from positive 24-term `atanh`
series for logarithms, with a checked positive bracket before squaring.
Every finite check is performed afresh; no checkpoint or resume data is used.
Reproduction from the repository root:

```sh
python3 docs/reports/erdos7-odd-covering/verify_finite_continuation.py
```

BBMST Theorem 6.1 continues (T6) from this stopping inequality with `δ=1/2`.
Its proof uses only that recurrence, the positive current survivor mass and the
published lower bound for the `k`th prime. These hypotheses have exactly the
same form here. For any finite number of further primes the survivor mass
therefore stays positive. If the given family ends before the displayed
endpoint, the already checked positive denominators suffice.

Consequently **Γ73 implies the unrestricted negative answer to Erdős #7**.
The finite arithmetic and the general-head transfer are established as stated;
the universal Γ73 existence bound is false by the star family. This conditional result
supplies no covering counterexample and no unrestricted proof by itself.
