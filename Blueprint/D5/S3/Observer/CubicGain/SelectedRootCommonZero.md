# SelectedRootCommonZero

## Abstract

Selected-root equations for the literal source minors

The algebraic parameter is criticalRoot, the unique root of the literal degree-67 FC polynomial in the interval (12758053/100000000,12758054/100000000). Its candidate coefficient lift is r=-C(b)/A(b), using determinantalLiftNumerator and determinantalLiftDenominator. The denominator is nonzero at this selected root. The corresponding source point has coordinates t=r/b and b.

The two degree-15 polynomials sourceE0 and sourceE1 retain their 134 integer monomials and their original ordered clock-five/six and clock-five/seven pairs. Homogenizing their evaluations at r=-C/A gives degree-1802 integer polynomials divisible by FC. Each exact quotient has degree 1735. A coefficient-mass bound below 2^9000 makes evaluation at the integer base 2^9000 conclusive: if an integer polynomial of smaller coefficient mass vanishes there, every coefficient is zero. This yields polynomial identities before specializing to the selected algebraic root.

Computational utility: checker, consumed by selected_root_common_zero through selected_zeros and homogeneous0/1. The general small_mass_zero and Circuit.zero_of_packed soundness proofs apply over every commutative ring. The concrete inputs identity0=h0_0-f*q0 and identity1=h1_0-f*q1 use the original coefficient arrays. At the same base 2^9000, bound0/packed0 and bound1/packed1 prove both strict circuit-mass bounds and exact zero integer evaluations; homogeneous0/1 apply soundness to these checked inputs. The header instance packed0 names the first successful check, and packed1 supplies the second. All numerical premises are discharged. Evaluation transport and homogeneous_eval0/1 connect the identities to the literal source equations, with the candidate denominator proved nonzero from exactW3_parent. The finite certificates are consumed checker premises. The public value and mass definitions also support the bounds in SelectedMinorNonzero.

The exact source normalization then gives both original formal Jacobian numerators zero. The nonzero regular source denominator allows the fixed-minor relation for all twenty-eight shifted rows in columns r^28 through 1 to be applied at these coordinates. The clock-seven source read remains distinct from the absolute-clock-eight M read.

These equations do not identify the candidate A,C arrays with the actual primitive normalized fixed minors, prove that the chosen literal minor is nonzero, establish the common factor h at the selected root, or identify the full original W3 coefficient world and its response center. Those additional identities are separate conditions for the full W3 identification.

**Definition 1.1 (integer coefficient evaluation).**

Lean statement: `D5/S3/Observer/CubicGain/SelectedRootCommonZero.value`

*Formalization.* `D5/S3/Observer/CubicGain/SelectedRootCommonZero.value` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an arbitrary commutative ring R, an element x of R, and an ascending integer coefficient list, value evaluates the associated polynomial by Horner recursion. The empty list has value zero; a head coefficient c and tail cs have value c+x value(x,cs).

**Definition 1.2 (integer coefficient mass).**

Lean statement: `D5/S3/Observer/CubicGain/SelectedRootCommonZero.mass`

*Formalization.* `D5/S3/Observer/CubicGain/SelectedRootCommonZero.mass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mass of an integer coefficient list is the sum of the absolute values of its entries. It bounds the absolute value of polynomial evaluation on the real unit interval.

**Theorem 1.3 (literal selected-root equations and fixed-minor relation).**

Lean statement: `D5/S3/Observer/CubicGain/SelectedRootCommonZero.selected_root_common_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/SelectedRootCommonZero.selected_root_common_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At b=criticalRoot and t=liftedR(b)/b, the actual source denominator is nonzero, both literal sourceE polynomials vanish at liftedR(b), and both formal source Jacobian numerators for the ordered pairs (N0,N1) and (N0,N2) vanish. Consequently liftedR(b) times the determinant of fixedMinorR(literalMatrix(b)) plus the determinant of fixedMinorC(literalMatrix(b)) is zero. The common-zero equations and denominator conditions are conclusions, not added hypotheses.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/SelectedRootCommonZero.mass`
- Truth anchor: `D5/S3/Observer/CubicGain/SelectedRootCommonZero.selected_root_common_zero`
- Truth anchor: `D5/S3/Observer/CubicGain/SelectedRootCommonZero.value`
- Dependency: [D5/S3/Observer/CubicGain/SourceFixedMinor](SourceFixedMinor.md)
