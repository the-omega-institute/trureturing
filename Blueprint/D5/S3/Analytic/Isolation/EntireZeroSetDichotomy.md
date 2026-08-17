# The Isolated-Zero Dichotomy

## Abstract

An entire function is identically zero or has a discrete zero set.

**Theorem 1.1 (Entire functions are zero or have discrete zero sets).**

$$\forall f:\mathbb{C}\to\mathbb{C},\\\operatorname{AnalyticOnNhd}_{\mathbb{C}}(f,\mathbb{C}) \Rightarrow f=0 \lor \operatorname{IsDiscrete}(\{z\in\mathbb{C} \mid f(z)=0\})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Isolation/EntireZeroSetDichotomy.entire_zero_set_dichotomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a complex function analytic on the whole plane, there are exactly two possibilities relevant here. It may vanish everywhere. Otherwise each zero is isolated, equivalently its zero set is discrete.

Mathlib was searched before proving. The pinned library provides `AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected`, which gives the global isolated-zero dichotomy on a connected set. The Lean proof applies it to the complex plane and uses `compl_mem_codiscrete_iff` to translate the codiscrete complement into an explicitly discrete zero set.

This formalization closes only the analytic mechanism stated in remark 27.746, clause 2. It does not formalize the four motivating moduli-space examples, and it makes no claim about non-analytic relations, which the source explicitly places outside the scope of the isolation law.

## References

- Truth anchor: `D5/S3/Analytic/Isolation/EntireZeroSetDichotomy.entire_zero_set_dichotomy`
