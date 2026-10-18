# The strict middle-angle window

## Abstract

A short-axis response angle lies strictly between pi over three and pi over two.

Let h and Q be positive real parameters with 1<h and Q<=h. Let theta lie strictly between zero and pi, with tan(theta/2)<=1/2, and assume Q is larger than cot(theta/2) squared.

**Theorem 1.1 (Strict middle-angle window).**

Lean statement: `D5/S3/Geometry/Hyperideal/Section71AngleWindow.middle_angle_window`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/Section71AngleWindow.middle_angle_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The response angle is arctan of the product of cot(theta/2) and the square root of (h squared minus one) divided by (Q plus h squared). It lies strictly above pi/3 and strictly below pi/2.

The proof first bounds the square-root factor from below using Q<=h. The cotangent hypothesis and the half-angle bound then force the squared tangent of the response above three. Positivity and the principal arctangent branch give the two strict angle inequalities.

This is the local analytic angle-window component of the Section 71 low-axis transport obstruction. It does not by itself identify a global face pairing, prove the parity of actual occurrences, or establish a complete geometric realization.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/Section71AngleWindow.middle_angle_window`
