# Partial-Quotient Extraction

## Abstract

Extract a rational continued-fraction maximum and instantiate the exact twelve-scale floor.

This module makes the normalization denominator endogenous. Its finite partial-quotient tail is computed from the rational input itself by Mathlib's Euclidean continued-fraction algorithm, then placed in the odd-tail terminal convention before taking its maximum. No independent scale parameter remains. The sample-to-rational provenance remains open, and the moat, envelope, and diffusion residuals remain open.

**Definition 1.1 (A rational mechanically determines its finite partial-quotient tail).**

$$C(q)=\operatorname{OddTail}\!\left(\operatorname{toList}(\operatorname{partDens}(\operatorname{GenContFract.of}(q)))\right)$$

*Formalization.* `D5/S1/Depth/PartialQuotientExtraction.partialQuotients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

GenContFract.of separates the integer head from its positive denominator stream. Rational termination turns that stream into a list of natural partial quotients, and an even nonempty tail receives the terminal n to n - 1, 1 rewrite. Integral inputs have an empty tail.

**Definition 1.2 (The normalization denominator is the extracted maximum).**

$$A(q)=\max C(q)$$

*Formalization.* `D5/S1/Depth/PartialQuotientExtraction.aMax` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The maximum is folded directly over C(q), with zero reserved for the empty integral tail. Neither a caller-supplied finite set nor a separately quantified rational scale participates in the definition.

**Theorem 1.3 (A nonintegral rational has a nonempty extracted tail).**

$$\forall q\in\mathbb{Q}\setminus\mathbb{Z},\ C(q)\neq\varnothing$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/PartialQuotientExtraction.partialQuotients_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero fractional part makes the first denominator of GenContFract.of present. Stream-to-list conversion and the terminal normalization preserve nonemptiness.

**Theorem 1.4 (The extracted maximum is positive off the integers).**

$$\forall q\in\mathbb{Q}\setminus\mathbb{Z},\ A(q)>0$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/PartialQuotientExtraction.aMax_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib proves every present denominator of GenContFract.of is at least one. A positive member therefore lies below the list maximum, including after the odd-tail terminal rewrite.

**Theorem 1.5 (The finite-sample floor uses the extracted maximum partial quotient).**

$$\forall q\in\mathbb{Q}\setminus\mathbb{Z},\ \forall S\subset_{\mathrm{fin}}\mathbb{Z},\ (\forall\psi\in S,\ 12\mid\psi\land\psi\neq0)\land(\exists\psi_0\in S,\ |\psi_0|=12)\Rightarrow\min\left\{\frac{|\psi|}{A(q)}:\psi\in S\right\}=\frac{12}{A(q)},\qquad A(q)=\max C(q)$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/PartialQuotientExtraction.twelve_scale_is_extracted_normalized_sample_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonintegral rational q, every normalized sample member lies above twelve divided by A(q), and an absolute-value-twelve witness attains it. The theorem instantiates the frozen generic twelve-scale lemma at the extracted value; it does not identify which rational belongs to a historical sample.
