# Structural three-row cone estimate

## Abstract

Ordered defects and bulk subtraction for the full three-row spectral cone.

These statements concern real scalar spectra and ordered step synthesis. Connecting the boundary inequalities to a physical APPT model, constructing an attaining state, and determining a purity supremum require additional results.

**Theorem 1.1 (Mass identity for disjoint boundary blocks).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/StructuralCone.boundary_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/StructuralCone.boundary_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N>=16, 6<=j<=N-10 and arbitrary real x:Fin 16 to Real, sum_k synth(positions N j,x)_k equals low(x)N+x5*j+H(head x)-D(tail x). This identity does not require feasibility or nonnegativity. It follows from mass_synth and finite-coordinate normalization. The actual_mass theorem applies it for N>=56; normalized_endpoint52_good, half_jump_endpoint52_good and bulk_endpoint52_good use it to express endpoint mass in boundary coordinates.

**Theorem 1.2 (Square identity for disjoint boundary blocks).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/StructuralCone.boundary_square`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/StructuralCone.boundary_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same N,j and arbitrary x, write S=low(x)N+x5*j+H-D. Then sum_k synth(positions N j,x)_k^2=(2 low(x)+x5)S-low(x)(low(x)+x5)N+E(x5,head x,tail x). It includes negative and infeasible x. The derivation uses square_synth, strict ordering of all sixteen slot positions and polynomial normalization. The actual_square theorem applies it for N>=56; normalized_endpoint52_good, half_jump_endpoint52_good and bulk_endpoint52_good use it to express endpoint energy in boundary coordinates.

**Theorem 1.3 (Unconditional fixed-cone estimate).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/StructuralCone.structural_fixed_good`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/StructuralCone.structural_fixed_good` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural N at least 67, natural j from 6 to N-10, and arbitrary real x on sixteen slots with x nonnegative and all three actual A rows nonnegative, the synthesized spectrum has Euclidean norm at most sqrt(target N) times its mass. The positions are 1,2,3,4,5,j,N-9 through N. The target uses the natural integer t=(3*N+4)/8. There is no additional cone or certificate success assumption.

**Theorem 1.4 (Quadratic endpoint control).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/StructuralCone.quadratic_interval_le_fun`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/StructuralCone.quadratic_interval_le_fun` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any real function f and real a,b,c,l,r,x,M, assume f(y)=a y^2+b y+c for every real y, a is nonnegative, l≤x≤r, and f(l)≤M and f(r)≤M. Then f(x)≤M. This original helper applies Mathlib convex interval control to the quadratic and is consumed by the structural cone estimates and the actual-PSD moment proof.

**Theorem 1.5 (Energy of two ordered blocks).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/StructuralCone.ordered_block_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/StructuralCone.ordered_block_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite types ι and κ, real upper:ι→R and lower:κ→R, and real m≥0, assume every upper coordinate is at least m and every lower coordinate lies in [0,m]. If k=card(ι)≥1 and card(κ)≤k(k-1), then sum upper_i^2+sum lower_i^2≤(sum upper_i)^2. Empty lower blocks and arbitrary finite upper types remain in scope. The proof decomposes upper coordinates as m plus nonnegative excess and uses the cardinality budget for the lower block. Both the original structural estimates and the actual-PSD tail envelope consume this helper.

## 1. Target and compression reduction

Let l_0 ≥ ... ≥ l_{N-1} ≥ 0, sum l_i = 1, and suppose

    l_0+l_1+l_2 ≤ l_{N-6}+...+l_{N-1},     l_0+...+l_5 ≤ l_{N-10}+...+l_{N-1},     l_0 ≤ l_{N-3}+l_{N-2}+l_{N-1}.

Put t=floor((3N+4)/8) and T_N=(9N+16t)/(3N+2t)^2. We prove sum l_i^2 ≤ T_N.

Full gap reconstruction and convex-mixture reduction reduce the problem to the following unconditional cone bound: for every integer 6≤j≤N-10 and every x≥0 with Ax≥0,

    Q(x) := sum_ab min(p_a,p_b)x_a x_b ≤ T_N S(x)^2,     S(x) := sum_a p_a x_a,     p=(1,2,3,4,5,j,N-9,...,N),     A_0=(-1,-2,-3,-3,-3,-3,-3,-3,-3,-3,-2,-1,0,1,2,3),     A_1=(-1,-2,-3,-4,-5,-6,-5,-4,-3,-2,-1,0,1,2,3,4),     A_2=(-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,0,1,2).

For clarity, f_i=sum_{a:p_a>i}x_a has S=sum_i f_i and Q=sum_i f_i^2. This identity also proves the positive-semidefinite min-kernel structure. For any fixed nonnegative C, the set Q≤C S^2, S≥0 is closed under nonnegative scaling and addition: apply the triangle inequality to f and its nonnegative mass. These are the same norm properties already used by the existing compression reduction.

## 2. Ordered-block energy

If y_1≥...≥y_n≥0 and 1≤k≤n≤k^2, then

    sum_{i=1}^n y_i^2 ≤ (y_1+...+y_k)^2.                 (2.1)

Indeed put m=y_k. Every one of the n-k remaining squares is at most m^2. Expanding the square of the first k-term sum gives its k squares and k(k-1) ordered cross products, each at least m^2. Since n-k≤k(k-1), (2.1) follows. This is a general order/energy argument, with arbitrary real input and arbitrary permitted block sizes. We will use (n,k)=(4,2) and (9,3). A more general two-block version holds with arbitrary finite index types and a separating level m.

## 3. Actual head and tail defects

For a compressed spectrum f, write u for its low middle level and v=x_5 for its middle jump. Its high middle level is u+v. The first five entries are u+v+h_0,...,u+v+h_4, with

    h_0≥h_1≥...≥h_4≥0.

The last nine entries are u-d_1,...,u-d_9, with

    0≤d_1≤...≤d_9≤u.

Let H=sum h_i, D=sum d_i, H2=sum h_i^2, D2=sum d_i^2, H3=h_0+h_1+h_2, D6=d_4+...+d_9, D3=d_7+d_8+d_9. Directly substituting into the three original rows gives exactly

    H3+D6 ≤ 3u-3v,     H+D   ≤ 4u-6v,     h_0+D3≤ 2u-v.                                      (3.1)

There are j high-middle baseline entries and N-j low-middle baseline entries, including their head/tail corrections. Therefore

    S=uN+vj+H-D,     Q=(2u+v)S-u(u+v)N+E,     E=v(H+D)+H2+D2.                                    (3.2)

If u=0, nonnegativity and the second inequality in (3.1) force v=H=D=0, so f=0. Otherwise divide the entire spectrum by u. From now on u=1 and write w=v/u, c=H-D, z=h_0. Then 0≤w≤2/3. Formula (3.2) becomes

    S=N+wj+c,     Q=(2+w)S-(1+w)N+E,     E=w(H+D)+H2+D2.                                    (3.3)

All following estimates are homogeneous, so normalization loses no cases.

## 4. Uniform small-jump bound

For every such spectrum with 0≤w≤1/2, every N≥67, and every allowed j, we prove

    Q ≤ B_N S^2,   B_N=16(15N-8)/(15N-4)^2.             (4.1)

This is the analytic bound that pays all four residual faces later.

If z≤1, all h_i and all d_i lie in [0,1], hence

    E ≤ (1+w)(H+D) ≤ (1+w)(4-6w)       =4-2w-6w^2.                                     (4.2)

If z≥1, put b=h_1+h_2 and r=D3. By (2.1),

    H2≤z^2+b^2,     D2≤r^2.

Also H≥z+b, D≤3r (partition the nine ordered d_i into three blocks), and D6≥r. The actual row budgets (3.1) imply

    1≤z≤2-w,   0≤r≤2-w-z,     0≤b≤3-3w-z-r,   H+D≤4-6w.                         (4.3)

The following **two analytic inequalities** result:

    E ≤ P(w):=5-4w-w^2,     4E-c ≤ 17-12w-4w^2.                               (4.4)

Here is a complete derivation, including the parameter boundaries. First,

    E ≤ w(4-6w)+z^2+b^2+r^2,     4E-c ≤ 4w(4-6w)+4z^2-z+4b^2-b+4r^2+3r.          (4.5)

Each right side is a convex quadratic in b. Its maximum over (4.3) is at b=0 or b=3-3w-z-r. After either substitution it is a convex quadratic in r, so its maximum is at r=0 or r=2-w-z. After either substitution it is a convex quadratic in z, so its maximum is at z=1 or z=2-w. Thus only the following algebraic endpoint differences must be nonnegative. These are values derived from arbitrary interval inputs, not preselected cone multipliers or a cone-success oracle:

| b endpoint | r endpoint | z endpoint | P minus first RHS of (4.5) | (17-12w-4w²) minus second RHS | |---|---|---|---|---| | 0 | 0 | 1 | 5w²-8w+4 | 20w²-28w+14 | | 0 | 0 | 2-w | (2w-1)² | 16w²-13w+3 | | 0 | upper | 1 | 4w²-6w+3 | 16w²-17w+7 | | 0 | upper | 2-w | (2w-1)² | 16w²-13w+3 | | upper | 0 | 1 | 4w(1-w) | w(17-16w) | | upper | 0 | 2-w | 0 | w | | upper | upper | 1 | 2(1-w) | 4-3w | | upper | upper | 2-w | 0 | w |

For 0≤w≤1/2 every entry is nonnegative. For the only entries not already manifest: 5w²-8w+4=5(w-4/5)^2+4/5; 4w²-6w+3=4(w-3/4)^2+3/4; 20w²-28w+14=20w²+14(1-2w); 16w²-13w+3=16(w-13/32)^2+23/64; 16w²-17w+7=16(w-17/32)^2+159/64. This proves (4.4).

A separate estimate, valid for all nonnegative defects, is

    E≤w(H+D)+(H+D)^2≤(4-6w)(4-5w).                    (4.6)

The second inequality uses H+D≤4-6w and w≥0. The reused homogeneous form total_energy_estimate retains arbitrary real u,w and DefectData u w h d with w>=0: E=w(H+D)+H2+D2<=(4u-6w)(4u-5w). It follows from H,D>=0, H2<=H^2, D2<=D^2 and H+D<=4u-6w. No PSD hypothesis is required. This homogeneous form is also used at a half-jump residual in ContinuousSpectrumAssembly; the N>=67 three-row theorem here is unchanged.

## 5. Scalar comparisons

Write theta=B_N and q=N-67≥0. Direct positive-denominator multiplication proves

    0<theta≤16/(15N)<1/24,     theta≥16/(15N+49),     theta≥(N+11)/(N+3)^2,     theta≥1/(N-4),     theta≥25/[24(N-1)],     theta≥256/(255N-1001),     theta≥36/(35N-81),     theta≥36/(35N-80).                                 (5.1)

For completeness the five nontrivial comparison numerators, using common factor (15N-4)^2 and the stated other denominator, are respectively

    (N+11)/(N+3)^2: 15q^3+1972q^2+64939q+8722,     25/[24(N-1)]:   135q^2+12258q+217943,     256/(255N-1001):3600q^2+240240q+59712,     36/(35N-81):    300q^2+20600q+43292,     36/(35N-80):    300q^2+20840q+59244.

The 1/(N-4) comparison follows from (N+11)(N-4)-(N+3)^2=N-53≥0 and the preceding boundary comparison. The upper estimate for theta uses (15N-4)^2-15N(15N-8)=16. The lower estimate uses (15N-8)(15N+49)-(15N-4)^2=735N-408>0. All denominators above are strictly positive at N≥67.

These scalar polynomial comparisons hold uniformly for every real N at least 67.

## 6. Completing squares and all intervals

For any upper bound E≤U(w), put K(w)=(1+w)N-U(w). If

    4 theta K(w)≥(2+w)^2,                              (6.1)

then (3.3) yields Q≤theta S^2, because

    4 theta [theta S^2-(2+w)S+K(w)]       =[2 theta S-(2+w)]^2+4 theta K(w)-(2+w)^2≥0.

For a concave quadratic, nonnegativity at both endpoints gives nonnegativity throughout the interval. We now use this fact only on ordinary real intervals, with all endpoint inequalities paid in (5.1).

* z≤1, 0≤w≤1/2: use U=4-2w-6w² from (4.2). The left side of   (6.1) minus its right side has w² coefficient 24theta-1<0.   Its endpoint requirements are exactly theta≥1/(N-4) and   theta≥25/[24(N-1)], already proved. * z≥1, 2/15≤w≤2/5: use U=P. The coefficient is 4theta-1<0.   The endpoint requirements are theta≥256/(255N-1001) and   theta≥36/(35N-81). * z≥1, 2/5≤w≤1/2: use U=(4-6w)(4-5w) from (4.6).   The coefficient is -120theta-1<0. The endpoint requirements are   theta≥36/(35N-80) and theta≥25/[24(N-1)].

It remains to pay z≥1 and 0≤w≤W=2/15. This is the part for which a continuous bulk upper bound alone would lose the exact original target. Both inequalities in (4.4) are essential here.

Set

    c*=3-4w,  L=N+3+2w,  e=w(j-6)≥0,     a=2theta L-(2+w),     F0(w)=theta L²-(N+11+3w+w²).

We first establish

    0≤a≤1/4.                                          (6.2)

The function a is affine and decreasing in w, since 4theta-1<0. At w=W, L=N+49/15, so theta≥16/(15N+49) gives a≥0. At w=0, theta≤16/(15N) gives

    a≤32(N+3)/(15N)-2≤1/4,

the last inequality being 384≤7N, true at N≥67.

Also F0(w) is concave in w (coefficient 4theta-1). Its value at 0 is nonnegative by theta≥(N+11)/(N+3)^2. Its value at W is nonnegative by (6.1) at W with U=P, proved above. Consequently F0(w)≥0 throughout [0,W]. The identity used at the endpoint, and below, is

    F0=theta L²-(2+w)L+(1+w)N-P(w).                   (6.3)

If c≥c*, put d=c-c*≥0. Then S=L+e+d and E≤P, hence

    theta S²-Q       ≥ F0 + theta(e+d)²+a(e+d) ≥0.                  (6.4)

If c≤c*, put d=c*-c≥0. The second bound in (4.4) says E≤P-d/4. Now S=L+e-d and

    theta S²-Q       ≥ F0 + theta(e-d)²+a e+(1/4-a)d ≥0.            (6.5)

This is a genuine mass-defect transfer identity for arbitrary e,d≥0; it is not a fixed-array checker. Equations (6.2)--(6.5) pay the last small-jump case, including w=0, d=0 and all interval endpoints. This completes (4.1) with no residual face assumed good.

## 7. Attained bulk subtraction and four faces

Let b=2e_5+3e_15 in gap coordinates. The actual rows give

    A b=(3,0,4).

For any feasible x define

    alpha=min(x_5/2, x_15/3, (A_0 x)/3, (A_2 x)/4),     y=x-alpha b.

Every argument of the minimum is nonnegative. The chosen alpha guarantees y≥0, A_0 y≥0, A_2 y≥0, and A_1 y=A_1 x≥0. A finite minimum is attained, so y lies on at least one of these four faces:

    y_5=0;   y_15=0;   A_0 y=0;   A_2 y=0.           (7.1)

Here is why **each** face is already covered by Section 6. If its low middle level u is zero, it is the zero spectrum as noted above. Otherwise normalize u=1 and use its actual defects:

* y_5=0 implies w=0. * y_15=0 implies d_9=1, so 1≤H+D≤4-6w and w≤1/2. * A_0 y=0 implies 3-3w=H3+D6≤H+D≤4-6w, so w≤1/3. * A_2 y=0 implies 2-w=z+D3≤H+D≤4-6w, so w≤2/5.

Thus Q(y)≤B_N S(y)^2. Each face therefore satisfies the same small-jump estimate.

The spectrum associated with b is 5 on its first j entries and 3 on the remaining N-j entries. Its mass and square mass are

    S(b)=3N+2j,    Q(b)=9N+16j.

Section 8 shows Q(b)≤T_N S(b)^2 and B_N≤T_N. Since x=y+alpha b, positivity, homogeneity and the min-kernel triangle inequality from Section 1 give Q(x)≤T_N S(x)^2. No success hypothesis remains.

## 8. Exact integer optimizer

The scalar rounding facts are `ScalarEnvelopes.common_le_integer_bulk` and `bulk_integer_maximum`. Here is their ordinary algebra, so this proof is independently readable. Let d=3N-8t. Natural division gives -4≤d≤3. For zeta=8t-3N=-d∈[-3,4],

    (9N+16t)(15N-4)^2       -16(15N-8)(3N+2t)^2       =(zeta+4)((15N-8)(4-zeta)+32)≥0.

This proves B_N≤T_N. Define

    R(j)=36N²-36N(t+j)-64tj.

For any natural j, the cross-multiplied difference between the bulk value at t and at j is

    (t-j)R(j).

R is decreasing, and

    R(t-1)=16+(d+4)(15N-(d+4))>0,     R(t+1)=16-(4-d)^2-15N(4-d)<0.

If j<t, integrality gives j≤t-1 and the product is positive; if j>t, j≥t+1 and both factors are negative. At j=t it is zero. This proves the bulk bound at exactly the original t, without replacing it by a continuous maximum. All denominators 3N+2j are positive. In particular the proof applies on the full required 6≤j≤N-10 range.

Section 7 now proves the unconditional fixed-cone statement in Section 1. Applying it through the **existing** full compression/convex-mixture bridge gives the asserted inequality for every original l. That bridge preserves the original full three rows, nonnegativity, antitonicity and mass; no truncated rows or extra hypothesis have been substituted. With sum l_i=1, the homogeneous bound is exactly sum l_i²≤T_N.

The analytic argument uses ordered nonnegative block energies, Mathlib convex and concave interval endpoint principles, the scalar envelope comparisons and exact integer optimizer, and the Euclidean norm-to-mass closure lemmas. The external theorem APPTReview.appt_rectangular_maximum_formula in mxym/math at immutable commit 479acd5d6269faf94433ad6b694c5b7979027c69, formalizations/appt-high-dimensional-review/APPTReview/RectangularMaximum.lean:78 (https://github.com/mxym/math/blob/479acd5d6269faf94433ad6b694c5b7979027c69/formalizations/appt-high-dimensional-review/APPTReview/RectangularMaximum.lean#L78), states the rounded plateau physical maximum for m at least 3 and n at least m^3-m-2, hence for four rows n at least 58. Its single four-row cut differs from the jointly imposed rank-two, rank-three and rank-four inequalities used here. The leading asymptotic does not give the exact finite target. At N=4n, the N>=67 three-row scalar estimate applies for n>=17. The n>=14 route uses actual_k1_l4_purity_bound in ContinuousSpectrumAssembly at N=4n>=56, with the actual APPT diagonal, its literal K1 and rank-four necessary row. A physical maximum also requires an attaining density, supplied by the coordinate-projector construction described in QuadbitQuintitMaximumPurity. The inner-polytope formulas, attainers and transition are published by Ahiable–Kothakonda–Winter. Neither scalar theorem alone constructs a physical density or proves an attained supremum. The dimension range 14 through 57 lies below the cited external theorem's four-row threshold; this comparison alone establishes no literature priority or global uniqueness.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/StructuralCone.boundary_mass`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/StructuralCone.boundary_square`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/StructuralCone.ordered_block_energy`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/StructuralCone.quadratic_interval_le_fun`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/StructuralCone.structural_fixed_good`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/HalfspaceConeTransfer](../HalfspaceConeTransfer.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/DefectScalarBounds](DefectScalarBounds.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ScalarEnvelopes](ScalarEnvelopes.md)
