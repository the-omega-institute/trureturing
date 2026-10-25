# Actual H6 Sources and the Complete Theta Transform

## Abstract

The original physical H6 condition supplies almost everywhere convergence of the complete physical theta series, preservation of H6 and control of the normalized sixth-moment excess for the same source.

**Theorem 1.1 (The full theta transform preserves H6 and bounds the sixth-moment excess).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiThetaExcess.actual_h6_fullTheta_excess_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiThetaExcess.actual_h6_fullTheta_excess_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original physical source F with originalPhysicalH6(F), the theorem proves all three clauses together: originalPhysicalH6(fullTheta(F)); genuine integrability on x>pi of ((x/pi)^6-1)*norm(fullTheta(F)(x))^2; and its integral at most C^2 times the same excess integral of F. Here C is the actual convergent series sum over j>=0 of (j+1)^(-3). The coefficient C is not replaced by a supplied finite constant. Since C=zeta(3)>1, this is a boundedness estimate; no strict contraction or optimality is claimed.

The predicate originalPhysicalH6 means MemLp 2 on the original half-line x>pi together with genuine integrability of (x/pi)^6*norm(F(x))^2 there. The full transform retains every mode n^4 F(n^2 x), n=j+1>=1. No cutoff, independent coefficient model, assumed theta convergence, assumed excess bound or Gamma form-domain premise occurs in this statement.

The proof uses the nonnegative densities (x/pi)^6-b for b=0 and b=1. Dilation by n^2 contributes the measure Jacobian n^(-2), and the sixth-moment scaling dominates the squared mode amplitude n^8. This yields the n^(-3) mode norm estimate in weighted L2. The b=0 estimate supplies H6 preservation, while b=1 gives the displayed excess bound. The L2 series is tied back to the literal fullTheta representative almost everywhere; a totalized sum alone does not serve as convergence evidence.

Its mirrored audit keeps the complete F,hF telescope and all three conclusion clauses. It observes only the source excess integral on the right of the last bound. Replacing that readout by -1 fails at the lawful zero H6 source because C>0. Actual dependence is witnessed by zero and the H6 indicator of (2*pi,3*pi], whose excess is finite and positive. Both audits retain the original source states.

**Theorem 1.2 (The actual mode series is summable almost everywhere).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiThetaExcess.actual_h6_physicalTerm_summable_ae`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiThetaExcess.actual_h6_physicalTerm_summable_ae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every F satisfying originalPhysicalH6(F), the theorem proves Summable(j -> physicalTerm(F,j,x)) for almost every x with respect to volume restricted to x>pi. It concerns the literal complex mode series, with the original F. It asserts no pointwise convergence on every x and supplies no convergence premise as an input.

The weighted-L2 mode estimate makes the sum of mode norms finite. A function-space series result then supplies almost everywhere summability. Strict positivity of the b=0 density transfers that property to the original restricted volume measure.

The mirrored law preserves the F,hF telescope, the original almost-everywhere filter and Summable. Its selected data operand is the entire partial application physicalTerm(F), a family indexed by j and x. The rejected constant-one mode family is nonsummable even at the lawful zero source; the half-line has nonzero measure. Actual dependence uses zero and the same H6 interval indicator, distinguished by mode j=0 at x=5*pi/2.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiThetaExcess.actual_h6_fullTheta_excess_bound`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiThetaExcess.actual_h6_physicalTerm_summable_ae`
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample](ActualSuzukiDomainCounterexample.md)
