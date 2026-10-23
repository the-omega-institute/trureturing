# Zero-jump actual-PSD defect moment

## Abstract

Joint moments of ordered defects under the actual positive semidefinite constraint.

**Theorem 1.1 (Sharp two-ninths actual PSD moment).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ActualPSDMoment.actual_psd_zero_jump_two_ninths_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ActualPSDMoment.actual_psd_zero_jump_two_ninths_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let h:Fin 5 to Real be antitone and nonnegative and d:Fin 9 to Real be monotone with 0<=d_i<=1. Put H=sum h_i, D=sum d_i, H2=sum h_i^2 and D2=sum d_i^2. Assume H+D<=4 and the literal actual matrix K(h,d) is PSD: its diagonal is 2(1-d8),2(1-d6),2(1-d3), and upper off-diagonal entries are -(h0+d7),-(h1+d5),-(h2+d4). Then H2+D2-(2/9)(H-D)<=32/9. All fourteen defects are arbitrary real coordinates; ties, zeros and singular PSD matrices are included. The determinant bound on the first three heads combines with the ordered-tail energy estimate to control the joint moment. This does not assert APPT sufficiency or physical attainment.

**Theorem 1.2 (Middle energy down to two ninths).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ActualPSDMoment.actual_psd_nonflat_middle_energy_two_ninths`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ActualPSDMoment.actual_psd_nonflat_middle_energy_two_ninths` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same head ordering and tail caps, assume 2/9<=w<=1/2, H+D<=4-6w, and K(w+h,d) is PSD. Its diagonal entries are 2(1-d8),2(1-d6),2(1-d3), and upper off-diagonal entries are -(w+h0+d7),-(w+h1+d5),-(w+h2+d4). Then E=w(H+D)+H2+D2<=C(w)=4-2w-4w^2+w^3+w^4. For h0<=1 the small-head chord suffices. Otherwise flatten the tail into h0 using r=d6+d7+d8. The actual congruent Z-matrix proves PSD preservation and ordered-tail bounds pay the w(D-r) charge. For shifted heads a,b,e,x,y the determinant and pair-square estimates reduce to min(F(w,e),T(w,e)), where F=4-2w-4we+we^2+e^4 and T=4-2w+2e-5we+(w-4)e^2+e^3+e^4. For e<=3/5 the gap C-F=(e-w)[4w-(e+w)(e^2+w^2+w)] is nonnegative; for e>=3/5 the gap C-T is nonnegative. Both scalar comparisons follow from polynomial decompositions into nonnegative rational Bernstein monomials.

For the two-ninths moment, h0<=4/9 gives H2<=(4/9)H and the sharp tail bound D2<=9/4, hence the moment is at most 113/36<32/9. Otherwise r=d6+d7+d8 and the actual PSD flattening give hbar=(h0+r,h1,h2,h3,h4), with moment no smaller because D2<=r^2, D<=3r and h0>=4/9. After flattening, the five-head chord and a convex quadratic interval bound reduce the moment to scalar endpoint estimates. At c=2/9 the endpoints z=e, z=2-e^2 and the interior kink z=4-4e satisfy the required bounds by explicit rational polynomial identities; the kink obeys 9/16<=e<=4/5.

**Theorem 1.3 (Continuous joint moment bound).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ActualPSDMoment.actual_psd_zero_jump_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ActualPSDMoment.actual_psd_zero_jump_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real h on Fin 5 and d on Fin 9, assume h is antitone and nonnegative, d is monotone with every coordinate between zero and one, and H+D is at most four, where H and D are the respective coordinate sums. The literal symmetric matrix has diagonal entries 2(1-d8), 2(1-d6), 2(1-d3), and upper off-diagonal entries -(h0+d7), -(h1+d5), -(h2+d4). Its positive semidefiniteness implies sum h_i^2 + sum d_i^2 - (H-D)/4 is at most 7/2. All indices are zero based. The statement includes singular matrices and arbitrary ordered tail shapes.

Write r=d6+d7+d8 and u=d3. The original ordered-block energy theorem supplies sum d_i^2 at most r^2. The actual PSD matrix also supplies the coupled tail budget via a homogeneous quadratic-form evaluation in the full plus/minus congruence. Combining this budget with ordering gives two further square-sum envelopes. Rational polynomial case splits yield sum d_i^2 at most 9/4.

For h0 at most 1/2, the head chord estimate and H+D at most four give a joint moment at most 13/4. For h0 at least 1/2, replace the tail by zero and add r to h0. This preserves order and the total budget. In the full congruent Z-matrix it increases entries while keeping off-diagonal entries nonpositive, so it preserves actual positive semidefiniteness. The joint moment increases by 2r(h0-1/2)+(r^2-sum d_i^2)+(3r-D)/4.

For the resulting flat tail, the PSD determinant gives a^2+b^2+e^2+abe at most four for the first three heads. The other two heads are bounded by a chord and their remaining mass budget. Polynomial comparison reduces the first two heads to a scalar interval with one possible kink; the original quadratic interval theorem and rational endpoint factors give the bound 7/2. This is a statement about continuous real defect data; any physical realization or purity theorem requires its own connection to these hypotheses.

**Theorem 1.4 (Flat-tail middle energy).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ActualPSDMoment.actual_psd_flat_tail_middle_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ActualPSDMoment.actual_psd_flat_tail_middle_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let h be any antitone nonnegative real function on Fin 5, with H=sum h_i at most 4-6w and h0 at least one. Assume 1/4 is at most w and w is at most (5-sqrt(17))/2. The literal symmetric matrix has diagonal entries two and upper off-diagonal entries -(w+h0), -(w+h1), -(w+h2). Positive semidefiniteness of this matrix implies wH+sum h_i^2 is at most 4-2w-4w^2+w^3+w^4. Indices are zero based; arbitrary continuous ordered heads and singular PSD matrices are included. No determinant bound or auxiliary head or tail cap is a premise.

Set a=w+h0, b=w+h1, e=w+h2, x=w+h3 and y=w+h4. The shared literal determinant implication gives a^2+b^2+e^2+abe at most four. The shared ordered-head consequence gives e at most one. Put A=2-e^2. At the original point only, the tail chord bounds x(x-w)+y(y-w) by e times min(2(e-w),4-3w-a-b-e). The shared fixed-e square-sum comparison splits at a+b=A+e. In the lower branch put z=a+b-e; ordering, h0 at least one and this branch condition give 1+w at most z and z at most A. In the upper branch compare directly with A.

The scalar comparison is G(w,z,e)=min(z^2+4e^2-wz-4we,z^2-(w+e)z+(4-5w)e). Both entries increase from z to A when 1+w is at most z and z is at most A. This comparison remains valid if the replacement L4 remainder is negative: the chord was used only at the original point, and no replacement spectrum is asserted to be feasible or PSD. At A, the two entries are F(w,e)=4-2w-4we+we^2+e^4 and U(w,e)=4-2w+2e-5we+(w-4)e^2+e^3+e^4.

For w at most e at most 1/2, the exact full-polynomial secant and its nonnegative factor decomposition give F(w,e) at most F(w,w). For e at least 1/2, the exact truncated-polynomial secant gives U(w,e) at most U(w,1/2), which is at most F(w,1/2) and hence at most F(w,w). Finally F(w,w)=4-2w-4w^2+w^3+w^4. These scalar comparisons hold for 1/4<=w<=1/2; the flat-tail estimate above uses w<=(5-sqrt(17))/2. This dimension-independent middle estimate supplies an energy bound for the rounded-purity assembly; it asserts neither an all-dimension purity theorem nor a physical APPT characterization.

**Theorem 1.5 (Middle energy with arbitrary ordered tails).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ActualPSDMoment.actual_psd_nonflat_middle_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ActualPSDMoment.actual_psd_nonflat_middle_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real w, h:Fin 5 to Real and d:Fin 9 to Real, assume h is antitone and nonnegative, d is monotone with 0<=d_i<=1 for every i, H+D<=4-6w, and 1/4<=w<=1/2. Here H=sum h_i, D=sum d_i, H2=sum h_i^2, D2=sum d_i^2, and E=w(H+D)+H2+D2. All indices are zero based. The sole matrix premise is positive semidefiniteness of K_w, whose rows are [2(1-d8),-(w+h0+d7),-(w+h1+d5)], [-(w+h0+d7),2(1-d6),-(w+h2+d4)], [-(w+h1+d5),-(w+h2+d4),2(1-d3)]. Then E is at most 4-2w-4w^2+w^3+w^4 if w<=(5-sqrt(17))/2, and at most (4-6w)(4-5w) otherwise. The endpoint belongs to the first branch. No tail-transfer, energy or purity inequality is assumed; repeated defects, zero coordinates and singular PSD matrices remain in scope.

The quadratic forms at (1,1,1) and (1,1,0) derive H3+D6<=3-3w and h0+D3<=2-w, where H3=h0+h1+h2, D6=d3+...+d8 and D3=d6+d7+d8. These are the original StructuralCone defect rows with u=1 and v=w. For w at most (5-sqrt(17))/2 and h0<=1, the reused small_head_energy bound E<=4-2w-6w^2 implies the polynomial bound. For h0>=1 put r=D3 and replace h by (h0+r,h1,h2,h3,h4) and d by zero. The full plus/minus congruence proves PSD of the shifted flat matrix. The reused ordered-tail bounds D2<=r^2, r<=D and D<=3r give the energy difference w(r-D)+2h0*r+r^2-D2 >= 2r(h0-w)+(r^2-D2)>=0. Thus the wD charge is paid by the original ordering and h0>=1, w<=1/2. The replacement head mass is H+r<=H+D<=4-6w, so actual_psd_flat_tail_middle_energy applies with the same w. Above the branch point, the reused total_energy_estimate gives E<=(4-6w)(4-5w) directly from the defect rows.

**Theorem 1.6 (Small-jump mass and square bound).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ActualPSDMoment.actual_psd_small_jump_defect_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ActualPSDMoment.actual_psd_small_jump_defect_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N>=56 and arbitrary real j,w with j>=6 and 0<=w<=1/4, let h:Fin 5 to Real be antitone and nonnegative, and d:Fin 9 to Real be monotone with every entry in [0,1]. Assume H+D<=4-6w and the same literal K_w displayed above is PSD. There is no integrality or upper-bound premise on j. Set S=Real.ofNat(N)+w*j+H-D and E=w(H+D)+H2+D2. Then (2+w)S-(1+w)Real.ofNat(N)+E<=target(N)*S^2. Here target(N)=(9 Real.ofNat(N)+16 Real.ofNat(t))/(3 Real.ofNat(N)+2 Real.ofNat(t))^2 with natural t=(3*N+4)/8; division precedes coercion. These are all the source parameters and premises, including both closed endpoints of the w interval.

Apply actual_psd_zero_jump_moment to g_i=w+h_i for all five head coordinates and to the original d. The identities sum g_i=5w+H and sum g_i^2=H2+2wH+5w^2, together with 5w+H+D<=4-w<=4, retain its full hypotheses and literal matrix. Rearrangement gives E<=7/2+(1/4-w)(H-D)+5w/4-5w^2. Since w(1/4-w)>=0 and j>=6, the left side of the claimed bound is at most (9/4)S-(5N/4-7/2). The reused square_completion theorem bounds this by theta*S^2, with theta=16(15N-8)/(15N-4)^2; positivity and its discriminant follow for N>=56. The existing common_le_integer_bulk comparison then gives theta<=target(N), preserving natural rounding.

The two estimates are repository derivations from the existing actual-PSD moment, ordered-block, scalar-envelope and norm framework. Hildebrand's PPT-from-spectrum criterion supplies the spectral-matrix context; it is not an attribution of these defect-energy derivations. Their application to the original spectrum is given in ContinuousSpectrumAssembly with the full parameter correspondence. They assert bounds on the stated real data, without an APPT sufficiency or equality classification.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ActualPSDMoment.actual_psd_flat_tail_middle_energy`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ActualPSDMoment.actual_psd_nonflat_middle_energy`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ActualPSDMoment.actual_psd_nonflat_middle_energy_two_ninths`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ActualPSDMoment.actual_psd_small_jump_defect_bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ActualPSDMoment.actual_psd_zero_jump_moment`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ActualPSDMoment.actual_psd_zero_jump_two_ninths_moment`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/DefectScalarBounds](DefectScalarBounds.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/StructuralCone](StructuralCone.md)
