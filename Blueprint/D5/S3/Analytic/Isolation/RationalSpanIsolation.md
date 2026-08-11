# Isolation of Fixed Rational-Span Levels

## Abstract

Fixed rational-span levels of a nonconstant real-analytic family are isolated.

**Theorem 1.1 (Fixed rational-span levels are isolated).**

$$\begin{gathered}\forall \iota [\operatorname{Fintype}(\iota)],\\P\subseteq\mathbb{R}, F:\mathbb{R}\to\mathbb{R},\\q:\iota\to\mathbb{Q}, b:\iota\to\mathbb{R},\\\operatorname{IsConnected}(P) \land \operatorname{AnalyticOnNhd}(F,P),\\x\in P \land F(x)\neq\sum_{i\in \iota}q_ib_i \Rightarrow \\F^{-1}(\{\sum_{i\in \iota}q_ib_i\}^{c})\in \operatorname{codiscreteWithin}(P).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Isolation/RationalSpanIsolation.rational_span_level_set_codiscrete` (`✓ std3`). ∎

*Citation.* Steven G. Krantz and Harold R. Parks (2002). *A Primer of Real Analytic Functions*. DOI: [10.1007/978-0-8176-8134-0](https://doi.org/10.1007/978-0-8176-8134-0).

*Commentary.*

Fix a finite family of real values and one rational coefficient for each value. If a real-analytic function on a connected parameter set differs from their weighted sum at one point, the complement of that level set is codiscrete within the parameter set. On the real line, connected sets are intervals, and this is Mathlib's filter formulation of the level set being isolated.

The source assumes that membership in the whole rational span is not identically true on any subinterval. For each fixed coefficient tuple, that hypothesis supplies the one unequal witness required by the formal theorem. The indexed family may contain repeated values; finiteness, rather than a duplicate-free enumeration, is the only property used by the displayed rational sum.

Mathlib was searched before proving. The pinned library already provides `AnalyticOnNhd.preimage_zero_mem_codiscreteWithin`. The Lean proof is therefore a thin honest wrapper: it subtracts the fixed rational linear combination, applies that theorem, and rewrites the zero set as the original level set. Krantz and Parks supply the literature anchor for the classical one-variable real-analytic identity and isolated-zero principle; no new analytic proof is claimed here.

## References

- Truth anchor: `D5/S3/Analytic/Isolation/RationalSpanIsolation.rational_span_level_set_codiscrete`
