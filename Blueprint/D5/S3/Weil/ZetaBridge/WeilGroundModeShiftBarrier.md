# Weil Ground-Mode Shift Barrier

## Abstract

Symmetric translations give an exact correlation identity and a necessary residual cost for a complement gap of the arithmetic Weil form.

C(f,g) denotes the existing Zeta23.EF.weilTest correlation. W(f,g) denotes Zeta23.EF.literatureRHS applied to C(f,g), including the canonical prime-power, pole-pair and Gamma terms. M(h) is the Lebesgue integral of Complex.normSq(h(x)). B abbreviates symmetricShiftDefect(t,c); t and c are real. Nonzero is the predicate that a function is not identically zero.

**Definition 1.1 (The explicit symmetric translation probe).**

$$\operatorname{B}(f)(x)= f(x-t)+f(x+t)-c f(x)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilGroundModeShiftBarrier.symmetricShiftDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The input function is arbitrary on the real line with complex values. This probe uses two translations and a real scalar. It makes no reference to an unknown eigenfunction.

**Theorem 1.2 (Transfer through the complete correlation function).**

$$\operatorname{Continuous}(f)\land \operatorname{Continuous}(g)\land \operatorname{HasCompactSupport}(f) \Rightarrow \operatorname{C}(\operatorname{B}(f), g)= \operatorname{C}(f, \operatorname{B}(g))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilGroundModeShiftBarrier.weil_symmetric_shift_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is equality of functions at every correlation displacement. Only f needs compact support. The proof justifies the integral splittings and translates the integration variable. Substitution g=B(f) gives C(B(f),B(f))=C(f,B(B(f))). Applying the existing arithmetic functional transfers every prime sample and both analytic contributions simultaneously.

**Theorem 1.3 (The compactly supported probe cannot vanish).**

$$\operatorname{HasCompactSupport}(f)\land \operatorname{Nonzero}(f)\land \operatorname{Positive}(t) \Rightarrow \operatorname{Nonzero}(\operatorname{B}(f))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilGroundModeShiftBarrier.symmetric_shift_defect_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive(t) means 0<t. No continuity assumption is needed here. If B(f) vanished, the values of f on each arithmetic progression would satisfy a second-order recurrence. Compact support supplies two consecutive terminal zeros, and backward induction gives f=0. For continuous nonzero f, this also implies positive L2 mass of B(f); the public conclusion itself is function nonvanishing.

**Theorem 1.4 (A complement gap requires a definite arithmetic residual).**

$$\operatorname{ContDiff}(2, f)\land \operatorname{HasCompactSupport}(f)\land 0\leq delta\land {{mu+delta} \operatorname{M}(\operatorname{B}(f))\leq \Re(\operatorname{W}(\operatorname{B}(f), \operatorname{B}(f)))}\land {{\Re(\operatorname{W}(f, \operatorname{B}(\operatorname{B}(f)))-mu \operatorname{C}(f, \operatorname{B}(\operatorname{B}(f)))(0))}^{2}\leq {r}^{2} \operatorname{M}(\operatorname{B}(\operatorname{B}(f)))} \Rightarrow {delta}^{2} \operatorname{M}(\operatorname{B}(f))\leq 3{2+{c}^{2}} {r}^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilGroundModeShiftBarrier.weil_symmetric_shift_residual_barrier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ContDiff(2,f) means ContDiff real 2 f. All five parameters t,c,mu,delta,r are real. The gap premise is tested on the single explicit direction B(f); it is not a theorem establishing a gap for the Weil operator. The residual premise is its squared real directional bound on B(B(f)), written with the exact arithmetic functional and zero-displacement correlation. Cauchy-Schwarz supplies this premise from an operator residual only after domain compatibility has been established. The proof combines the transfer identity with M(B(h)) <= 3(2+c^2)M(h), and treats zero mass separately. For a fixed support window, both translated tests must be admissible. Candidates with nontrivial boundary leakage are outside that interior application. No simplicity, evenness of the lowest mode, all-scale coercivity, or convergence to Xi is asserted.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilGroundModeShiftBarrier.symmetricShiftDefect`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilGroundModeShiftBarrier.symmetric_shift_defect_ne_zero`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilGroundModeShiftBarrier.weil_symmetric_shift_residual_barrier`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilGroundModeShiftBarrier.weil_symmetric_shift_transfer`
