# SelectedRootCommonZero

## Abstract

Selected-root equations for the literal source minors

sourceJ, sourceN, sourceD and sourceC are the integer circuit of VI (2.3) over a commutative coefficient ring. sourceNumerator contains the three clock-five, clock-six and clock-seven numerators in this order. The third entry uses the row (-20,70,-84,35); it is distinct from the clock-eight numerator in the actual read pair.

sourceBt and sourceBb use formal polynomial differentiation in the independent t and b coordinates. sourceE0 and sourceE1 are polynomials in r, with the exact integer coefficient expansions of VI (3.2) for the ordered pairs (N0,N1) and (N0,N2). Their normalization is checked before specialization: 45 D(t,b) Ei(tb,b) equals b^7 times the corresponding formal Jacobian numerator. No leading coefficient is divided out.

literalRow and literalMatrix retain all twenty-eight shifts and all twenty-nine descending columns. The source normalization connects the formal source criticality equations to the fixed-minor linear relation. It does not prove that the chosen fixed 28-row minor is nonzero, nor that the stored candidate lift equals the normalized-minor lift.

**Theorem 1.1 (literal fixed-column common-root relation).**

Lean statement: `D5/S3/Observer/CubicGain/SelectedRootCommonZero.literal_fixed_minor_relation`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/SelectedRootCommonZero.literal_fixed_minor_relation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real b,z, if sourceE0(b) and sourceE1(b) both vanish at z, then z times the determinant of fixedMinorR(literalMatrix(b)) plus the determinant of fixedMinorC(literalMatrix(b)) equals zero. literalMatrix has all twenty-eight rows r^13 E0 through E0 followed by r^13 E1 through E1, in columns r^28 through 1.

**Theorem 1.2 (literal circuit to fixed-minor relation).**

Lean statement: `D5/S3/Observer/CubicGain/SelectedRootCommonZero.source_fixed_minor_relation`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/SelectedRootCommonZero.source_fixed_minor_relation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real t,b, with nonzero sourceD(t,b) and both formal source Jacobian numerators for (N0,N1) and (N0,N2) equal to zero, the same fixed determinants satisfy (tb) det(fixedMinorR)+det(fixedMinorC)=0. The normalization identities supply the two common-root equations. No leading coefficient is divided out, and no selected-root common-zero hypothesis is discharged by this statement.

**Theorem 1.3 (first exact normalized minor).**

Lean statement: `D5/S3/Observer/CubicGain/SelectedRootCommonZero.source_e0_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/SelectedRootCommonZero.source_e0_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real t,b, 45 sourceD(t,b) times sourceE0(b) evaluated at tb equals b^7 times (sourceBt(0) sourceBb(1) minus sourceBb(0) sourceBt(1)), with both partials evaluated at (t,b).

**Theorem 1.4 (second exact normalized minor).**

Lean statement: `D5/S3/Observer/CubicGain/SelectedRootCommonZero.source_e1_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/SelectedRootCommonZero.source_e1_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real t,b, 45 sourceD(t,b) times sourceE1(b) evaluated at tb equals b^7 times (sourceBt(0) sourceBb(2) minus sourceBb(0) sourceBt(2)), with both partials evaluated at (t,b).

The algebraic parameter is criticalRoot, the unique root of the literal degree-67 FC polynomial in the interval (12758053/100000000,12758054/100000000). Its candidate coefficient lift is r=-C(b)/A(b), using determinantalLiftNumerator and determinantalLiftDenominator. The denominator is nonzero at this selected root. The corresponding source point has coordinates t=r/b and b.

The two degree-15 polynomials sourceE0 and sourceE1 retain their 134 integer monomials and their original ordered clock-five/six and clock-five/seven pairs. Homogenizing their evaluations at r=-C/A gives degree-1802 integer polynomials divisible by FC. Each exact quotient has degree 1735. A coefficient-mass bound below 2^9000 makes evaluation at the integer base 2^9000 conclusive: if an integer polynomial of smaller coefficient mass vanishes there, every coefficient is zero. This yields polynomial identities before specializing to the selected algebraic root.

Integer coefficient lists are evaluated by Horner recursion. Their coefficient mass is the sum of the absolute values of their entries. Addition, multiplication and powers extend these operations to arithmetic circuits. The small_mass_zero and Circuit.zero_of_packed theorems establish soundness over every commutative ring. For identity0=h0_0-f*q0 and identity1=h1_0-f*q1, the exact bounds bound0 and bound1 are below 2^9000, and packed0 and packed1 establish zero integer evaluations at that base. The resulting identities homogeneous0 and homogeneous1 hold before real specialization. The equations homogeneous_eval0 and homogeneous_eval1 recover the literal source polynomial evaluations; eval_f, eval_a and eval_c identify the coefficient arrays. The nonzero candidate denominator follows from exactW3_parent. The value and mass functions also give the coefficient bounds used to prove selected-minor nonvanishing.

The exact source normalization then gives both original formal Jacobian numerators zero. The nonzero regular source denominator allows the fixed-minor relation for all twenty-eight shifted rows in columns r^28 through 1 to be applied at these coordinates. The clock-seven source read remains distinct from the absolute-clock-eight M read.

These equations do not identify the candidate A,C arrays with the actual primitive normalized fixed minors, prove that the chosen literal minor is nonzero, establish the common factor h at the selected root, or identify the full original W3 coefficient world and its response center. Those additional identities are separate conditions for the full W3 identification.

**Definition 1.5 (integer coefficient evaluation).**

Lean statement: `D5/S3/Observer/CubicGain/SelectedRootCommonZero.value`

*Formalization.* `D5/S3/Observer/CubicGain/SelectedRootCommonZero.value` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an arbitrary commutative ring R, an element x of R, and an ascending integer coefficient list, value evaluates the associated polynomial by Horner recursion. The empty list has value zero; a head coefficient c and tail cs have value c+x value(x,cs).

**Definition 1.6 (integer coefficient mass).**

Lean statement: `D5/S3/Observer/CubicGain/SelectedRootCommonZero.mass`

*Formalization.* `D5/S3/Observer/CubicGain/SelectedRootCommonZero.mass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mass of an integer coefficient list is the sum of the absolute values of its entries. It bounds the absolute value of polynomial evaluation on the real unit interval.

**Theorem 1.7 (literal selected-root equations and fixed-minor relation).**

Lean statement: `D5/S3/Observer/CubicGain/SelectedRootCommonZero.selected_root_common_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/SelectedRootCommonZero.selected_root_common_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At b=criticalRoot and t=liftedR(b)/b, the actual source denominator is nonzero, both literal sourceE polynomials vanish at liftedR(b), and both formal source Jacobian numerators for the ordered pairs (N0,N1) and (N0,N2) vanish. Consequently liftedR(b) times the determinant of fixedMinorR(literalMatrix(b)) plus the determinant of fixedMinorC(literalMatrix(b)) is zero. The common-zero equations and denominator conditions are conclusions, not added hypotheses.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/SelectedRootCommonZero.literal_fixed_minor_relation`
- Truth anchor: `D5/S3/Observer/CubicGain/SelectedRootCommonZero.mass`
- Truth anchor: `D5/S3/Observer/CubicGain/SelectedRootCommonZero.selected_root_common_zero`
- Truth anchor: `D5/S3/Observer/CubicGain/SelectedRootCommonZero.source_e0_normalization`
- Truth anchor: `D5/S3/Observer/CubicGain/SelectedRootCommonZero.source_e1_normalization`
- Truth anchor: `D5/S3/Observer/CubicGain/SelectedRootCommonZero.source_fixed_minor_relation`
- Truth anchor: `D5/S3/Observer/CubicGain/SelectedRootCommonZero.value`
- Dependency: [D5/S3/Observer/CubicGain/ExactW3Center](ExactW3Center.md)
