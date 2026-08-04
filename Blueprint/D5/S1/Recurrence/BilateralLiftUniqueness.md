# Bilateral Fibonacci Lift Uniqueness

## Abstract

Fibonacci solutions split into two golden eigenlines with a minimal cyclic carrier.

**Theorem 1.1 (Bilateral lift uniqueness).**

$$\operatorname{Sol}(F)=\langle e_{\varphi},e_{\psi}\rangle,\quad Se_{\lambda}=\lambda e_{\lambda},\quad F_{k+1}=\frac{\varphi^{k+1}-\psi^{k+1}}{\sqrt{5}},\quad \langle F\rangle_S=\langle e_{\varphi},e_{\psi}\rangle.$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/BilateralLiftUniqueness.bilateral_lift_uniqueness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The aggregate theorem packages the two-dimensional recurrence space, both shift eigenlines, Binet decomposition, cyclic minimality, and the exact contracting residual into one kernel-checked statement.

**Theorem 1.2 (Golden decomposition of the solution space).**

$$\operatorname{Sol}(u_{k+2}=u_{k+1}+u_k)=\operatorname{span}_{\mathbb{R}}\{e_{\varphi},e_{\psi}\}.$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/BilateralLiftUniqueness.fibonacci_solution_space_eq_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real solution space of the Fibonacci recurrence is exactly the span of the expanding and contracting golden eigensequences.

**Theorem 1.3 (Shift eigenlines).**

$$Se_{\varphi}=\varphi e_{\varphi},\qquad Se_{\psi}=\psi e_{\psi}.$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/BilateralLiftUniqueness.shift_golden_eigenvectors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Forward shift acts by the expanding golden ratio on one line and by its algebraic conjugate on the other.

**Theorem 1.4 (Shifted Binet formula).**

$$F_{k+1}=\frac{\varphi^{k+1}-\psi^{k+1}}{\sqrt{5}}.$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/BilateralLiftUniqueness.fibonacci_weight_binet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With Fibonacci weights indexed from F_1, both golden components have nonzero coefficient and their difference is normalized by sqrt(5).

**Theorem 1.5 (Minimal shift-invariant carrier).**

$$\langle F\rangle_{S}=\operatorname{span}_{\mathbb{R}}\{e_{\varphi},e_{\psi}\}.$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/BilateralLiftUniqueness.fibonacci_cyclic_span_minimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The golden two-line span contains the Fibonacci weight sequence, is shift-invariant, and lies in every shift-invariant real submodule that contains that sequence. This is the formal uniqueness carrier.

**Theorem 1.6 (Exact contracting residual).**

$$F_{k+2}-\varphi F_{k+1}=\psi^{k+1}.$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/BilateralLiftUniqueness.fibonacci_weight_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting the expanding golden component from the shifted Fibonacci weight leaves the contracting eigensequence exactly.
