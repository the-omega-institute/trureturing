[Index](../../marked_head_profile.md) · [Previous](01-survivor-reduction.md) · [Next](03-arbitrary-height-transfer-for-matching-kernels.md)

<a id="survivor-weighted-full-convex-comparison"></a>
## Survivor-weighted full convex comparison

Let p be prime, p∤Q, and H≥1. Let ρ be a finite nonnegative measure on Z/QZ, and let R_x be a nonnegative row measure on Z/pᴴZ with total mass r(x)∈[0,1]. Suppose every depth-e prefix has R_x-mass at most a_e(x), where a₁≥⋯≥a_H≥0. Put

\[
 \beta_0=r,\quad\beta_e=\min(r,a_e)\ (1\le e\le H),\quad
 \beta_{H+1}=0,\qquad w_k=\beta_k-\beta_{k+1}.
\]

For any complete enlarged layout write A_e for its complete old head layout at p-exponent e. All original pairs (old divisor,e) remain separate labels. Then every increasing convex h satisfies

\[
 \int h(L(x,y))\,dR_x(y)
 \le\sum_{k=0}^H w_k(x)h\!\left(\sum_{e=0}^kA_e(x)\right). \tag{C1}
\]

Here is a detailed verification of the comparison step. At fixed x retain only active positive-depth labels, each contributing a Bernoulli indicator, and order them by decreasing cap β_e(x). If their count is m and their indicators are I₁,…,I_m, then for every integer j≥0,

\[
 (\sum_iI_i-j)_+\le\sum_{i>j}I_i.
\]

Therefore the hinge integral is bounded by Σ_{i>j}β_i, which is exactly the hinge integral of nested indicators of those cap masses on an interval of total mass r. Every increasing convex function on the finitely many possible integer load values is a constant plus a nonnegative linear combination of the identity and these integer hinges. The constant is integrated against the same total mass r on both sides. The active labels of each depth have the same cap; grouping the nested comparison by depth gives (C1). This proves the inequality without any actual nestedness or identification of projected labels.

Jensen gives h(Σ_{e≤k}A_e)≤(k+1)⁻¹Σ_{e≤k}h((k+1)A_e). Extend Θ and Γ homogeneously to finite positive measures by maximizing, respectively, their hinge and square integrals over complete old layouts. Integrating (C1), then taking the maximum over enlarged layouts, yields

\[
 \Theta_{\rho R}(t)
 \le\sum_{k=0}^H(k+1)\Theta_{w_k\rho}(t/(k+1)), \tag{C2}
\]
\[
 \Gamma_{Qp^H}(\rho R)
 \le\sum_{k=0}^H(k+1)^2\Gamma_Q(w_k\rho). \tag{C3}
\]

These use the same physical finite measure. Empty rows contribute zero. No product structure of ρ, constant r, or preserved normalized prefix cap is assumed.

For a normalized distortion kernel relative to the actual pure-p survivor probability U_p, let B_x be the actual mixed union, α=U_p(B_x), and 0≤δ(x)<1. With θ=min(α,δ), its restriction to the good points is exactly

\[
 R_x(dy)=\frac{1_{B_x^c}(y)}{1-\theta(x)}U_p(dy),\qquad
 r(x)=1-\frac{(\alpha(x)-\delta(x))_+}{1-\delta(x)}.
\]

Its actual unnormalized prefix maxima may be used as a_e. Those maxima decrease with depth. Row-dependent thresholds are valid here because x is the entire previous history.

At a subsequent odd prime q, coprime to Qp, use one fixed threshold 0≤δ_q<1 and the actual pure-q base. Complete separately for each original q-exponent, with weights (q−1)q⁻ᶠ. Pure q classes are already absent, so completion subtracts exactly **one** unit cofactor. Jensen and the pure-q cylinder cap give the unnormalized assigned charge

\[
 b_q\le\frac{\Theta_{\rho R}(1+(q-2)\delta_q)}{(q-2)(1-\delta_q)}. \tag{C4}
\]

Combining with (C2) is valid. If the total surviving mass is s>0, normalized charges and moments divide by s. The comparison does not supply a fixed-dimensional closed recurrence.

<a id="relation-to-the-existing-square-transfer"></a>
### Relation to the existing square transfer

The dossier's W1 and `PrimeRectangleTransfer.prefix_weighted_rectangle_second_moment_le` already give, after normalizing each nonempty row and using old measure rρ,

\[
 \Gamma_{Qp^H}(\rho R)
 \le\Gamma_Q(r\rho)+\sum_{e=1}^H(2e+1)\Gamma_Q(\beta_e\rho). \tag{C5}
\]

For empty rows choose any normalized kernel; its old mass is zero. Since Γ is subadditive on positive measures, r=Σ_kw_k and β_e=Σ_{k≥e}w_k imply

\[
 \Gamma_Q(r\rho)+\sum_{e=1}^H(2e+1)\Gamma_Q(\beta_e\rho)
 \le\sum_k(k+1)^2\Gamma_Q(w_k\rho).
\]

Thus (C3) is **not** a stronger second-moment result than W1. The useful extension is the full convex/hinge formula (C2), together with its row-mass dependence and the following sharp obstruction. Existing full-label rearrangement is also present in `ConditionalComparison/CappedGainRearrangement.lean` (`finite_run_rearrangement`, `depth_rearrangement`) and the finite Abel formulas in `Runs.lean`; no claim of a new underlying rearrangement theorem is made.

<a id="sharp-geometric-cap-envelope"></a>
## Sharp geometric cap envelope

Fix a row and suppose a_e=c p⁻ᵉ. Feasibility requires r≤c (sum the leaf caps), in addition to 0≤r≤1; the usual c≥1 implies this. For head layers all having common value z≥0 at the selected point, the exact cap-only upper envelope is

\[
 C_r(h;z)=r h(z)+\sum_{e=1}^H\min(r,a_e)
                    [h(z(e+1))-h(ze)]. \tag{C6}
\]

To attain it, give a distinguished nested prefix chain masses β_e=min(r,a_e). At each branch distribute the excess β_e−β_{e+1} among the other p−1 children, and distribute each such off-chain mass uniformly below that child. The required capacity condition follows from β_e≤p a_{e+1}; the root uses r≤p a₁=c. Every deeper cap holds. Select all test p-prefixes along the chain, so (C1) is an equality and summation by parts gives (C6).

For feasible r₀≥r≥a₁, the entire reduction is (r₀−r)h(z). Hence every hinge with threshold T≥z is unchanged. For the square cost,

\[
 C_r(u^2;z)=z^2[r+\sum_{e=1}^H(2e+1)\min(r,a_e)].
\]

On a_{j+1}<r<a_j the derivative of the bracket is (j+1)²; above a₁ it is only1. Actual geometry may reduce a_e independently, but residual row-mass loss alone need not do so.

<a id="the-actual-45-class-family"></a>
## The actual 45-class family

The exact checker constructs all45 original `(modulus,residue)` pairs and independently evaluates the physical chain.

1. For every nonunit d|315, forbid0 mod d. The survivors are the144 units modulo315, carrying the uniform head law μ.
2. Forbid0 mod11. For d in the ordered list (3,5,7,15,21,35,105,9,45), assign distinct11 digits1,…,9 and head residue1 mod d. Use δ₁₁=2/5.
3. Forbid0 mod31. Let w=1891 mod3465, so w=1 mod315 and w=10 mod11. For the23 nonunit divisors d|3465 in increasing order assign31 digits1,…,23, and old residue w mod d. Use δ₃₁=2/5.

All45 moduli are distinct, nontrivial and odd; their lcm is107415. The largest modulus has five distinct prime factors. No three-factor hypothesis is used.

Let ℓ(x)=Σ_{d|315}1_{x=1 mod d}. Its only values exceeding6 occur at x=1,106,211, where they are12,8,8. The nine active11 labels have count n(x); its complete histogram is

| n | 0 | 1 | 2 | 3 | 4 | 5 | 7 | 9 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| count |45|54|15|19|3|5|2|1|

The pure11 law is uniform on ten digits. Thus α₁₁=n/10 and the exact conditional assigned charge is (n−4)₊/6. Averaging gives Pr(B₁₁)=1/54. At x=1,106,211, n=9,7,7, so the good-row masses are1/6,1/2,1/2. Digit10 is always good and has mass1/6 in every one of these rows, both before and after killing.

The coherent old load for the next prime is L(x,y)=ℓ(x)(1+1_{y=10}). Because all31 colours differ, the actual number of active mixed31 colours is L−1. There is one missing unit. The pure31 law has30 digits, so the exact conditional charge is (L−13)₊/18. It is positive only at y=10 above the three specified head points. Therefore

\[
 \Pr(B_{31})
 =\frac1{144}\frac16\left(\frac{11}{18}+\frac3{18}+\frac3{18}\right)
 =\frac{17}{15552}.
\]

Every B₁₁ point has y≠10, where the next charge is zero. Hence

\[
 \Pr(B_{11}\cap B_{31})=0,
 \qquad (\mu K_{11}|_{B_{11}^c})K_{31}(B_{31})=\frac{17}{15552}.
\]

Every head point carrying positive later charge was positively depleted at11, but the later unnormalized charge did not decrease. Normalizing the good restriction multiplies by54/53, giving

\[
 \frac{54}{53}\frac{17}{15552}=\frac{17}{15264}.
\]

This is a strict increase. The normalization is ν=(54/53)ρ for ρ=μK₁₁ restricted to B₁₁ᶜ.

At every finite11 height H, adding the pure classes0 mod11ᵉ for2≤e≤H changes no pure survivor root. Above x=1 the free root10 and every prefix inside it have mass1/[6·11ᵉ⁻¹], before and after killing. These are also the maximum actual depth-e prefix masses. The total row mass falls from1 to1/6. A complete test coherent with x=1 and that free11 root has load12 on every deleted point, so **all real hinge thresholds at least12** have unchanged unnormalized integrals. This proves the all-height statement. The checker additionally reconstructs all prefix maxima and every hinge segment endpoint for heights1,2,3.


The existing verifier and fixed certificate reconstruct all45 actual classes, their CRT unions, normalized kernels, total chain mass and all stated charge quantities using exact rational arithmetic. They also check the finite prefix instances at heights1 through3; the preceding argument supplies the all-height result. The comparison and obstruction are ordinary proofs, not end-to-end Lean verification or a new noncoverage cutoff.

<a id="a-block-transfer-retaining-row-column-and-cell-compatibility"></a>
## A block transfer retaining row, column and cell compatibility

This gives a universal finite two-coordinate transfer inequality and an
actual 11/13 example where it is strictly stronger than sequential scalar
prefix completion. It does not give a universal numerical head Gamma or
an odd-covering conclusion. All mathematical proof below is ordinary
finite convexity; the witness is checked by exact arithmetic, not Lean.

<a id="existing-results-and-the-retained-distinction"></a>
### Existing results and the retained distinction

The searched project already has the one-coordinate weighted-prefix
theorem PrimeRectangleTransfer.prefix_weighted_rectangle_second_moment_le,
the dossier's W 1--W 5, the full convex comparison C 1--C 5 in the marked-head
note, and the actual two-prime root estimates G 1/ZG 3. These retain old-point
weights or separate prefix caps. No two-coordinate surviving-grid maximum
was identified in the searched congruence files and odd-covering notes.
The distinction below is compatibility: maxima for a row, a column, and
their intersection cannot always be attained together on the actual grid.

<a id="universal-finite-height-statement"></a>
### Universal finite-height statement

Let S be an old supported finite set with a probability mu, and let q,r
be new coprime primes. Fix finite heights H,K. Remove the actual pure-q
and pure-r classes, giving coordinate sets P and R; their uniform product
is the new base. Keep every other original label (d,a,b), representing
old divisor d and new prime exponents a,b, distinct. At old point x define
T_x subset P times R by deleting exactly the new original rectangles
whose old congruence cylinder contains x. Thus a label containing both
new primes deletes a cell-prefix rectangle, an axis label deletes a strip,
and overlaps are counted as unions. Put

    N_x=|T_x|,   Z=sum_x mu(x) N_x.

Assume Z>0 and globally condition mu times the uniform product on these
actual survivors. The resulting law can change the old marginal.

For a complete test layout and exponent pair (a,b), let A_(a,b)(x) be
the complete old test load obtained by summing its old cofactor indicators.
Its individual labels can have different new prefixes. For nonnegative
numbers v_(a,b), define

    B_h(T;v)=max_(one prefix rectangle C_(a,b) for each pair)
               sum_(y,z in T) h(sum_(a,b) v_(a,b) 1_C_(a,b)(y,z)),

where C_(0,0) is the entire grid. Empty prefixes and prefixes outside the
pure survivor sets are permitted. Then for every increasing convex h,

    E_survivors h(L)
      <= Z^(-1) sum_x mu(x) B_h(T_x; (A_(a,b)(x))).                 (B 1)

The assertion is simultaneous for the one actual conditioned law. It
does not replace original labels by a family of projected distinct moduli.

Proof: at fixed x, group active old indicators by their selected new
prefix within each exponent pair. Their nonnegative amounts have total
A_(a,b)(x). The sum of h over T_x is convex in the allocation vector for
one pair while all other allocations are fixed. Allowing arbitrary
nonnegative allocations with this same total enlarges the feasible set:
individual labels need not be splittable, and the pointwise maximizing
allocation need not come from one common global test layout. Both facts
are harmless for this upper bound. A convex function on a
simplex is at most its maximum at a vertex, which places the whole amount
in one prefix. Apply this successively to the finitely many exponent pairs,
then integrate. Normalization is exactly Z; the pure-product size cancels.
This argument needs neither independence of the old test loads nor a
nonempty fibre at every old point.

Unlike replacing every rectangle by an independent prefix-mass cap, B 1
preserves the common actual grid until all cross terms are formed. The
operator can be expensive at large heights; no fixed-dimensional closure
or arbitrary-height numerical bound is claimed.

<a id="explicit-one-height-square-operator"></a>
### Explicit one-height square operator

For H=K=1 write A,B,C,D for the old test loads at exponent pairs
(0,0),(1,0),(0,1),(1,1). Let T be the actual surviving grid, N=|T|, and
let n_i,m_j be its row and column counts. If N=0 set F_T=0. Otherwise
the convex concentration above gives the explicit expression

    F_T(A,B,C,D)=N A^2 + max_(i in rows,j in columns,z in T) [
        n_i (2 AB+B^2) + m_j (2 AC+C^2)
        +2 BC 1_((i,j) in T) +2 AD+D^2
        +2 BD 1_(z_row=i) +2 CD 1_(z_col=j)].                       (B 2)

Here i is any row, j any column, and z any surviving cell; i,j need not
themselves form a surviving cell. The notation max means independent
choices of i,j and z with only z constrained to T. The D contribution may
be placed in T because h is increasing. Formula B 1 with h(t)=t^2 therefore
has right side Z^(-1)sum_x mu(x)F_(T_x)(A(x),B(x),C(x),D(x)).

This is an upper bound for each fixed four old test layouts. Taking the
maximum over those layouts gives a universal second-moment bound, but
that old-layout optimization has not been evaluated for arbitrary families.

Independent scalar intersection caps instead give

    G_T=N A^2+n_max(2 AB+B^2)+m_max(2 AC+C^2)
        +2 BC+2 AD+D^2+2 BD+2 CD.                                   (B 3)

Always F_T<=G_T. Equality can fail because the row and column maxima
and the three positive mixed intersections must share one grid.

<a id="strict-gain-in-a-complete-original-315-times-11-times-13-family"></a>
### Strict gain in a complete original 315 times 11 times 13 family

Use the 86-point old survivor family

    (3,0),(9,4),(5,0),(15,1),(45,37),(7,0),
    (21,1),(35,9),(63,52),(105,4),(315,142).

Let d run increasingly through

    1,3,5,7,9,15,21,35,45,63,105,315.

All new old cofactor conditions are x=2 mod d. For the 11 axis, use digit 0
for d=1 and for the last four nonunit cofactors; for the first seven
nonunit cofactors use digits 4,5,...,10. For the 13 axis, similarly use
digits 4,5,...,12 for the first nine nonunit cofactors and digit 0 otherwise.
For the 143 d cross labels, use respectively

    (1,1),(2,2),(2,3),(3,2),(3,3)

at the first five cofactors d=1,3,5,7,9, and use (0,0) for all others.
CRT defines one residue for each modulus. Together with the old classes,
these are exactly all 47 nonunit divisors of 45045, without duplication.

At old point x=2, the surviving grid is exactly

    T={(1,2),(1,3),(2,1),(3,1)}.

Its unique largest row and largest column both have size 2, but their
intersection (1,1) is forbidden. With A=B=C=D=1, the exact block maximum
is 22, attained for example by row 1, column 2, and cell(1,2). The independent
intersection-cap bound is 25.

For comparison with sequential W 1 scalar completion, let k be the number
of nonempty rows. Its marginal old square contribution is N+3 n_max.
Under the conditional-prefix weight, every nonempty row has mass 1; the
two completed old layouts each have maximum square k+3. The one-height
W 1 coefficient therefore gives

    N+3 n_max+3(k+3).

This is 28 on T. Reversing the prime order also gives 28. Thus the strict
gain persists even after using actual conditional row caps in sequential
scalar completion; it is not an improvement obtained by changing the law.

The exact verifier also checks all 86 old points of this one actual family.
There are 7128 complete survivors. Take every nonunit old test cofactor
in each of the four groups to be its original forbidden residue. Then
A=B=C=D=1 throughout the old survivor set, so the same comparison applies
to one legitimate set of old test blocks. Summed square numerators are

| Bound | Numerator | Divided by 7128 |
|---|---:|---:|
| Joint surviving-grid operator | 12618 | 701/396 |
| Independent row/column/intersection caps | 12621 | 4207/2376 |
| Sequential scalar completion, either order | 12624 | 526/297 |

The extra compatibility gain beyond independent intersection caps is
1/2376. The gain over sequential scalar completion is 1/1188. Directly
maximizing the three global unit-cofactor test choices gives square
numerator 12522, so the joint pointwise bound itself is not asserted sharp
after integration. In particular, these numbers are not a Gamma bound
for all old test layouts of the family.

<a id="exact-compatibility-rebate-for-a-two-prime-block"></a>
## Exact compatibility rebate for a two-prime block

For a nonempty finite grid T, let n_i,m_j be its row and column degrees,
with maxima n_max,m_max. For nonnegative real A,B,C,D, set

    a=B(2A+B),       b=C(2A+C),       e=2BC+2D min(B,C),
    P=a n_max+b m_max,
    E=max_((i,j) in T) (a n_i+b m_j).

The operators B 2 and B 3 satisfy the exact identity

    G_T-F_T = min(e,P-E)
            = min(e, min_((i,j) in T)
                         [a(n_max-n_i)+b(m_max-m_j)]).             (R1)

Thus degrees and one scan of T suffice to evaluate the joint operator.

To prove this, put u=2BD, v=2CD, c=2BC and
K=|T|A²+2AD+D². If the selected row and column intersect in T, place
the D-cell at that intersection. The maximum of these choices is
K+E+c+u+v. If their intersection is absent, a surviving D-cell can lie
in at most one of them, giving at most K+P+max(u,v). This second bound
is attained by a maximum-degree row and column whenever their intersection
is absent: both degrees are positive, so a D-cell can attain whichever
of u,v is larger. If their intersection survives, the first branch
already dominates. Consequently

    F_T=K+max(E+c+u+v, P+max(u,v)),
    G_T=K+P+c+u+v.

Subtracting proves R1, including zero coefficients and empty ambient
rows or columns. If B=0 or C=0, the rebate is zero. Otherwise a,b,e>0,
so strict gain occurs exactly when no surviving edge joins a
maximum-degree row to a maximum-degree column. This criterion is
independent of A and D.

For complete old test blocks A,B,C,D≥1, one has a,b≥3 and e≥4. Let
I(T) indicate that T is nonempty and has no such maximum-degree edge.
Integer degree deficits give

    G_T-F_T ≥ min(e,min(a,b)) I(T) ≥ 3 I(T).                      (R2)

Give empty grids zero contribution. With the same actual globally
conditioned law and Z from B 1,

    sum_x mu(x)F_(T_x)/Z
      ≤ sum_x mu(x)G_(T_x)/Z - 3 mu{x:I(T_x)=1}/Z.                (R3)

The event I(T_x) depends only on the actual surviving grid, so this
subtraction remains valid after maximizing over all complete old layouts.
No positive universal lower bound on its mass is asserted. For example,
put each new mixed original class inside an already forbidden pure class.
The distinct moduli remain present, but every surviving grid is a
rectangle and I(T_x)=0.

The exact verifier checks 77 targeted grid/coefficient cases against
literal allocation squares. They include both positive branches of the
minimum, their equality boundary, zero coefficients, rational coefficients,
empty ambient rows and columns, and the actual four-cell witness with
F=22,G=25. The preceding proof supplies the arbitrary nonnegative-real
scope. The final min/max subtraction reuses the standard order identity;
no standalone Lean wrapper is introduced.

<a id="a-nonuniform-law-for-a-block-with-zero-compatibility-rebate"></a>
## A nonuniform law for a block with zero compatibility rebate

There is a supported law that improves the complete second moment even
when the uniform grid's rebate R1 is zero. For every positive Q coprime
to143 and every probability mu on residues modulo Q, the explicit law rho
below satisfies the exact identity

    Gamma_(143Q)(mu × rho)
      = (6386411/3927000) Gamma_Q(mu).                            (NT1)

This allows every complete old test layout and arbitrary old prime-power
heights. The new prime heights at11 and13 are both one.

Use the actual new classes0 mod11,0 mod13 and1 mod143. Index the nonzero
11-residues by0,...,9 and the nonzero13-residues by0,...,11. The surviving
grid is

    T=({0,...,9} × {0,...,11}) minus {(0,0)}.

Its uniform law has exact factor194/119 in NT1. Every maximum-degree row
meets a maximum-degree column in a surviving cell, so R1 is zero for
all four nonnegative old loads. Instead assign

    rho(i,j)=a=2119/238000       if exactly one of i,j is zero,
             c=9781/1178100     if both i,j are positive.

Equivalently a=1/119+1/2000 and c=1/119−20/(99·2000). There are20adjacent
cells and99interior cells, so20a+99c=1. Both weights are positive and
the missing cell has mass zero. The improvement in the exact factor is

    194/119−6386411/3927000 = 131/33000 >0.                        (NT2)

<a id="a-common-quadratic-bound-for-all-four-old-layouts"></a>
### A common quadratic bound for all four old layouts

Let R_i and C_j be rho's row and column masses. For a selected row i,
column j and surviving cell z, the indicators1, row i, column j and
cell z have Gram matrix

    M=[[1,R_i,C_j,rho(z)],
       [R_i,R_i,rho(i,j),rho(z)·1[z_row=i]],
       [C_j,rho(i,j),C_j,rho(z)·1[z_col=j]],
       [rho(z),rho(z)·1[z_row=i],rho(z)·1[z_col=j],rho(z)]].

Choose the interior aligned configuration i=j=1,z=(1,1), and denote
its matrix by M*. Put R=a+11c and C=a+9c. The four row sums of M* are

    lambda=(1+R+C+c, 2R+2c, 2C+2c, 4c).

Simultaneously for every row, column and cell choice,

    M ≤ diag(lambda) in positive-semidefinite order.              (NT3)

The rational certificate proves NT3 by exact LDLᵀ factorizations of
its20distinct matrix differences. For each one the verifier reconstructs
every entry and checks every diagonal pivot is nonnegative, including
the remaining column at a zero pivot. All14280choices are accounted for;
no floating-point eigenvalue estimate is used. The coefficient sum is

    sum(lambda)=6386411/3927000.

Fix any complete test layout modulo143Q. At an old point x, let A_g(x)
be the complete old cofactor load in exponent group
 g=(0,0),(1,0),(0,1),(1,1). The new prefixes of individual old cofactors
may differ. The convex allocation argument of B 1 remains valid with
rho in place of counting measure: for an upper bound, concentrate each
group's nonnegative amount into one row, column or cell. Prefixes outside
support may be moved into support since the squared nonnegative load
is increasing. Thus, at this same old point,

    E_rho L(x,·)² ≤ max_(i,j,z) A(x)ᵀ M A(x)
                  ≤ sum_g lambda_g A_g(x)².

Every A_g is a complete Q-divisor layout. Integrating under mu gives
at most sum(lambda) Gamma_Q(mu), proving the upper bound of NT1 for
all old layouts simultaneously.

For equality, choose an old layout attaining Gamma_Q(mu); the finite
residue-choice set ensures it exists. Reuse that layout in all four
exponent groups with the fixed interior aligned new row, column and
cell. CRT gives one residue for every divisor of143Q. Its complete load
factors as the old load times(1+row indicator+column indicator+cell
indicator). The latter's square integral is the sum of entries of M*,
namely sum(lambda). This gives the reverse bound of NT1.

For the uniform law on T, the interior aligned Gram matrix dominates
all other Gram matrices entrywise. Its row-sum diagonal majorant follows
from the weighted square inequality, and the same coherent test attains
it. This proves its exact factor194/119. Hence NT2 compares two complete
supported laws for the same actual family, including the full old-layout
optimization.

<a id="actual-arithmetic-consumer-and-boundary"></a>
### Actual arithmetic consumer and boundary

Adjoin(11,0),(13,0),(143,1) to the sharp315head's eleven original classes.
These14moduli are distinct, nontrivial and odd, with lcm45045. The full
survivor set has86·119=10234points. Keeping its old uniform law and using
rho on the new block gives the exact value

    Gamma45045=(6386411/3927000)(1131/86)
              =2407676947/112574000,

compared with109707/5117 for the fully uniform survivor law. The verifier
uses the already computed sharp315result, reconstructs every actual
survivor in one full period, and checks the product support.

This supplies one positive case for handling zero compatibility rebate;
it does not show that every zero-rebate grid admits this improvement.
Additional actual classes involving the new primes need not preserve
this grid. No unrestricted tail cutoff or arbitrary-height11/13block
bound follows from NT1.

The repository's B 1 convex allocation proof is reused directly; the
new quantitative input is the common rational quadratic bound NT3.
[Hough–Nielsen, Lemmas5–6](https://arxiv.org/html/1703.02133) controls
moments by maximal biases and good-fibre proportions.
[BBMST, section5.3](https://arxiv.org/html/1901.11465) constructs nonuniform
survivor laws by optimizing actual configurations. These provide the
public precedents; neither cited passage supplies NT1. The result here
is an ordinary universal proof with an exact finite certificate, not
Lean certification.

<a id="rectangular-matching-holes-a-symbolic-common-quadratic-bound"></a>
## Rectangular matching holes: a symbolic common quadratic bound

The preceding finite construction extends to every m×n rectangle with
m,n≥3 and a matching of k deleted cells, where0≤k<min(m,n). Relabel the
holes as(0,0),…,(k−1,k−1), and call their rows and columns affected. Put

    S=m+n,  V=mn−k,  H=k(m+n−k−1),
    C=max(m+n+2k−1,2m,2n),  0≤epsilon≤1/(9C),
    c=1/(V+H epsilon),  a=(1+epsilon)c.

Assign mass zero to holes, mass a to every surviving cell touching an
affected row or column, and mass c elsewhere. There are H cells of the
first positive type and(m−k)(n−k) of the second; their masses sum to one.
Here epsilon is a ratio perturbation, distinct from NT1's additive
probability perturbation. The explicit interval is sufficient; it is
not sharp and does not recover NT1's larger specific perturbation.

Untouched rows have mass c(n+k epsilon), untouched columns have mass
c(m+k epsilon), and untouched cells have mass c. Define

    lambda=(1+c(S+1+2k epsilon),
            2c(n+1+k epsilon), 2c(m+1+k epsilon), 4c).

For every selected row i, column j and surviving cell z, its four
indicator Gram matrix M, as in NT3, satisfies

    M ≤ diag(lambda).                                           (MT1)

All four coefficients depend only on(m,n,k,epsilon), including when
m≠n. They do not depend on hole positions or selected coordinate labels.

<a id="a-uniform-laplacian-estimate"></a>
### A uniform Laplacian estimate

Divide by c and write D(epsilon)=(diag(lambda)−M)/c=D_0+epsilon Delta.
At epsilon=0, let h_i,h_j indicate whether the selected row and column
are affected; put u=1[(i,j) survives],v=1[z_row=i],t=1[z_col=j]. The
unnormalized row and column masses are n−h_i,m−h_j. Decompose D_0 into
the graph Laplacian whose off-diagonal edge weights are(M/c)_ab plus
the diagonal matrix of row-sum slacks. Those slacks are exactly

    h_i+h_j,  2+2h_i−u−v,  2+2h_j−u−t,  2−v−t.                 (MT2)

They are nonnegative integers, and all vanish exactly for an untouched
aligned row, column and intersection cell. In that exceptional case,
lambda is the row-sum vector of M at every epsilon, so D(epsilon) is
itself a nonnegative weighted graph Laplacian for every epsilon≥0.

Otherwise at least one slack is at least one. The three Laplacian edges
from coordinate0 have weights n−h_i,m−h_j,1, each at least one. For
some ell∈{0,1,2,3}, therefore,

    xᵀD_0x ≥ sum_(j=1)^3(x_0−x_j)²+x_ell² ≥ ||x||²/9.           (MT3)

For the last inequality, express x in coordinates
(x_ell,x_0−x_1,x_0−x_2,x_0−x_3). The inverse transformation has squared
Frobenius norm7 for ell=0 and9 otherwise; rowwise Cauchy–Schwarz proves
MT3. This bound is independent of the grid dimensions.

The unnormalized row derivative r_i' is n−1 on affected rows and k
otherwise; the column derivative q_j' is m−1 or k. Every cell-weight
derivative w' is zero or one. Consequently

    Delta_00=2k, Delta_01=−r_i', Delta_02=−q_j', Delta_03=−w_z',
    Delta_11=2k−r_i', Delta_22=2k−q_j', Delta_33=−w_z',
    Delta_12=−w_ij', Delta_13=−w_z'v, Delta_23=−w_z't.

Its absolute row sums are bounded respectively by
m+n+2k−1,2n,2m,4. For example, row1 is at most r_i'+|2k−r_i'|+2:
the cases r_i'=k and r_i'=n−1 give either2k+2 or2n−2k, both at most2n.
The other bounds follow directly from k≤min(m,n)−1. Thus every row sum
is at most C. Applying2|x_ax_b|≤x_a²+x_b² gives

    |xᵀDelta x|≤C||x||²,
    D(epsilon)≥(1/9−epsilon C)I≥0

for all nonexceptional configurations. Together with the aligned
Laplacian case, this proves MT1 symbolically, without a grid enumeration.

<a id="exact-factor-positive-gain-and-moving-fibres"></a>
### Exact factor, positive gain and moving fibres

The coefficient sum and its uniform-law counterpart are

    F_k=1+[3(S+3)+6k epsilon]/[V+H epsilon],
    U_k=1+3(S+3)/V.

Their exact difference is

    U_k−F_k=3k epsilon B/[V(V+H epsilon)],
    B=m²+n²+(2−k)(m+n)−k−3>0.                                  (MT4)

Indeed m=k+1+x,n=k+1+y with x,y≥0 gives
B=5k+3+(k+4)(x+y)+x²+y². Hence the gain is strict for k≥1,epsilon>0.
At epsilon=1/(9C), it is3kB/[V(9CV+H)]. For k=0 the law is uniform,
independent of epsilon, and F_0=U_0=(1+3/m)(1+3/n).

The B1 convex allocation argument and MT1 apply to all four complete
old-cofactor groups. For a fixed grid, the aligned untouched test
attains the upper bound by reusing one maximizing old layout in all
four groups, exactly as in NT1. Thus, for every old law mu,

    Gamma_new(mu×rho)=F_k Gamma_old(mu).                          (MT5)

This arithmetic statement uses a coprime pair of new height-one primes
with m,n actual available residue counts; old heights are unrestricted.
For the uniform punctured grid, the aligned untouched Gram matrix
entrywise dominates every other Gram matrix. The same allocation and
row-sum argument gives its exact factor U_k, proving that MT4 compares
complete laws on the same support, including the old-layout maximum.

If instead each old point x has available row and column sets of the
same sizes m,n and at most k matching holes, extend its matching to
exactly k by pairing unused rows and columns. Extra virtual holes only
restrict support. Construct rho_x after any fibrewise relabeling. Each
rho_x sums to one, so nu(x,y)=mu(x)rho_x(y) preserves the old marginal.
Because lambda is common to all fibres, integration of MT1 gives

    Gamma_new(nu)≤F_k Gamma_old(mu).                             (MT6)

The matching, row and column sets, and virtual holes may all move with
x. Equality is not asserted: one global test layout need not align in
every fibre. MT4 does not compare the padded law with each original
fibre's uniform law when it originally had fewer than k holes.

<a id="keeping-the-actual-hole-count-gives-an-additive-saving"></a>
### Keeping the actual hole count gives an additive saving

Fix1≤K<min(m,n) and one0≤epsilon≤1/(9C_K). If fibre x has exactly k_x
matching holes with0≤k_x≤K, use its own law without virtual holes. Put

    D_j=mn−j+epsilon j(S−j−1), N_j=3(S+3)+6epsilon j, F_j=1+N_j/D_j.

The positive denominators strictly decrease, since
delta_j=D_j−D_(j+1)=1−epsilon(S−2j−2)>0. Each lambda coordinate has a
nondecreasing positive numerator and this decreasing denominator, so
lambda_g(j) increases. Every complete old load A_g includes its unit
cofactor and is at least one. Therefore, pointwise,

    sum_g lambda_g(k_x)A_g²
      ≤sum_g lambda_g(K)A_g²−(F_K−F_(k_x)).

After integration this strengthens MT6 to

    Gamma_new≤F_K Gamma_old−E_mu[F_K−F_(k_x)].                   (MT7)

The successive differences F_(j+1)−F_j have numerator
T_j=6epsilon D_j+N_j delta_j and denominator D_jD_(j+1). Their
numerators increase by T_(j+1)−T_j=2epsilon N_(j+1)≥0 and their
denominators decrease. Thus every difference is at least

    gamma=F_1−F_0
      =[6epsilon mn+3(S+3)(1−epsilon(S−2))]
        /[mn(mn−1+(S−2)epsilon)]>0,

and

    Gamma_new≤F_K Gamma_old−gamma(K−E_mu k_x).                  (MT8)

This holds also at epsilon=0. K=0 uses the full-rectangle bound alone.

For actual mixed moduli qrd with distinct old cofactors d, each class
activates on one old residue. The number of distinct forbidden cells
k_x is at most this activation count, which is at most one complete
old test load L_cross(x), obtained by filling any missing cofactors.
Writing R_mu for the sum of nonunit old cylinder maxima gives
E_mu k_x≤E_mu L_cross≤1+R_mu. Hence, whenever the remaining holes are
a partial matching and their count is at most K, MT8 gives

    Gamma_new≤F_K Gamma_old−gamma(K−1−R_mu)_+.                  (MT9)

This uses actual cofactor labels. It does not assume globally distinct
new digits, and it retains the hypotheses of fixed available dimensions
and a matching within each fibre.

<a id="arbitrary-holes-via-fixed-row-and-column-deletion-budgets"></a>
### Arbitrary holes via fixed row and column deletion budgets

Suppose an ambient M×N fibre excludes at most a entire rows, b entire
columns and L individual cells. For L≥1 choose any fixed nonnegative
A,B with A+B≥L−1 and m=M−a−A≥3,n=N−b−B≥3. First pad the original
axis exclusions to exactly a,b. Of the remaining point holes, select
all but at most one; there are at most L−1 selected holes. Assign at
most A to their row endpoints and at most B to their column endpoints,
then delete those endpoints. Repeated endpoints save budget. Pad these
additional deletions to exactly A rows and B columns. The remaining
m×n rectangle has at most one hole. If necessary, add one virtual hole.

The k=1 law now has common lambda across all such fibres, is supported
on the original survivor set, and preserves the old marginal; MT6
applies. Endpoint choices and all padded deletions may vary with x.
For L=0, use the k=0 full rectangle after padding the original axis
exclusions. These are support constructions, not comparisons with the
uniform laws on the original irregular fibres.

The standard-library verifier checks10 sparse polynomial identities,
all32 abstract Boolean incidence/slack patterns in MT2, and the four
exact anchor transformations in MT3. It adds no concrete grid instances.
The universal inequalities and support arguments above are ordinary
proofs, independently reviewed; they are not Lean certification. Full
matchings k=min(m,n), higher new prime heights and varying dimensions
without fixed deletion budgets are outside the stated hypotheses. No
unrestricted tail cutoff follows from these bounds.
