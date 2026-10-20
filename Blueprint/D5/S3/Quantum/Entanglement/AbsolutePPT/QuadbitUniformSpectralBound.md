# Three-row scalar spectral bound

## Abstract

Three boundary inequalities bound the squared mass of every ordered probability spectrum in every dimension at least 67.

For l:Fin N to the reals, indices inside prefix and tail sums mean their natural values embedded in Fin N. Thus the three rows compare the first three entries with the last six, the first six with the last ten, and the first entry with the last three. N is arbitrary subject to N at least 67, with zero entries and repeated eigenvalues allowed.

**Theorem 1.1 (Nonnegative exact boundary packing).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.boundary_packed_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.boundary_packed_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For N>=16 and every nonnegative original gap vector g:Fin N to Real, boundaryPacked is nonnegative at all sixteen slots. The first five entries retain the original first five gaps, slot five is the sum of the middle gaps, and the remaining ten entries retain the original last ten gaps. Each retained entry and each summand in the middle slot is nonnegative. The concentration construction in ContinuousSpectrumAssembly uses this helper to preserve nonnegative boundary coefficients.

**Theorem 1.2 (Exact concentration of the original gap vector).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.boundary_lift_packed`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.boundary_lift_packed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For N>=16, every real gap vector g:Fin N to Real and every k with 5<=k.val<N-10, lifting boundaryPacked(g) at middle position k yields fixedGaps(g,k). All fifteen original boundary gaps remain unchanged, while the total middle mass is placed at k. The linear map boundaryLift places each of the sixteen coefficients at its original gap index and is zero elsewhere. The support partition and injective slot embedding establish equality of complete gap vectors, including the zero middle-mass case.

**Theorem 1.3 (Compatibility of packing and spectrum synthesis).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.boundary_synth_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.boundary_synth_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For N>=16 and 6<=j<=N-10, fullSynth applied to boundaryLift(x) equals synth(positions N j,x) as an entire real spectrum, for arbitrary real x:Fin 16 to Real. The construction uses the same step functions and their original indices. Index reconstruction and linear synthesis identify the full spectrum without a finite-valued spectral assumption. This identity connects the sixteen boundary coefficients to full-gap synthesis.

**Theorem 1.4 (Exact rows retained under boundary packing).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.boundary_packed_image`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.boundary_packed_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For N>=16, every real gap vector g:Fin N to Real and k with 5<=k.val<N-10, A times boundaryPacked(g) equals boundaryGapRows(g). The three rows remain exactly bottom-six minus top-three, bottom-ten minus top-six, and bottom-three minus the largest coordinate of fullSynth(g). The middle step has the same row image at every allowed position, so concentrating the middle gaps preserves all three row values. The equality holds for arbitrary real gaps without a nonnegativity premise.

**Theorem 1.5 (Arbitrary-dimension squared-mass estimate).**

$$\forall (N:\mathbb{N}), (67\leq N)\Rightarrow \forall (l:Fin\left(N\right)\to \mathbb{R}), ((Antitone\left(l\right))\land (\forall (i:Fin\left(N\right)), 0\leq l\left(i\right))\land (\sum_{i:Fin\left(N\right)} l\left(i\right)=1)\land (\sum_{i:Fin\left(3\right)} l\left(i\right)\leq \sum_{i:Fin\left(6\right)} l\left(N-6+i\right))\land (\sum_{i:Fin\left(6\right)} l\left(i\right)\leq \sum_{i:Fin\left(10\right)} l\left(N-10+i\right))\land (l\left(0\right)\leq \sum_{i:Fin\left(3\right)} l\left(N-3+i\right)))\Rightarrow \sum_{i:Fin\left(N\right)} (l\left(i\right))^{2}\leq \frac{9\cdot ((N:\mathbb{N}):\mathbb{R})+16\cdot ((\left\lfloor\frac{3\cdot N+4}{8}\right\rfloor:\mathbb{N}):\mathbb{R})}{(3\cdot ((N:\mathbb{N}):\mathbb{R})+2\cdot ((\left\lfloor\frac{3\cdot N+4}{8}\right\rfloor:\mathbb{N}):\mathbb{R}))^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.three_row_scalar_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integer t is natural-number division (3*N+4)/8, equivalently the displayed floor; its real coercion is taken only after that division. N-6, N-10 and N-3 are natural subtractions before indexing. All ratios in the bound are real divisions. The only hypotheses are the displayed ordering, nonnegativity, mass one and three boundary inequalities.

The proof first reconstructs the complete spectrum from its adjacent nonnegative gaps, including the final gap to zero. The middle gap mass is compressed to one step length j. Positive middle mass uses barycentric weights; zero middle mass uses a division-free reconstruction. Closure of the Euclidean norm-to-mass cone then transfers estimates for the fixed sixteen-slot boundary cone back to every original spectrum.

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

The second inequality uses H+D≤4-6w and w≥0.

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

The analytic argument uses ordered nonnegative block energies, Mathlib convex and concave interval endpoint principles, the scalar envelope comparisons and exact integer optimizer, and the Euclidean norm-to-mass closure lemmas. The external theorem APPTReview.appt_rectangular_maximum_formula in mxym/math at immutable commit 479acd5d6269faf94433ad6b694c5b7979027c69, formalizations/appt-high-dimensional-review/APPTReview/RectangularMaximum.lean:78 (https://github.com/mxym/math/blob/479acd5d6269faf94433ad6b694c5b7979027c69/formalizations/appt-high-dimensional-review/APPTReview/RectangularMaximum.lean#L78), states the rounded plateau physical maximum for m at least 3 and n at least m^3-m-2, hence for four rows n at least 58. Its single four-row cut differs from the jointly imposed rank-two, rank-three and rank-four inequalities used here. The leading asymptotic does not give the exact finite target. At N=4n, the N>=67 scalar estimate applies for n>=17, including the range 17 through 57 below the cited external theorem's threshold. A physical maximum also requires the necessary spectral inequalities and an attaining state; this scalar theorem alone supplies neither that state nor an equality classification. The threshold comparison alone establishes no literature priority or global uniqueness.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.boundary_lift_packed`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.boundary_packed_image`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.boundary_packed_nonneg`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.boundary_synth_lift`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.three_row_scalar_bound`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/StructuralCone](QuadbitUniform/StructuralCone.md)
