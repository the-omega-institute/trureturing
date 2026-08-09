# Chain Rule for Finite Classical KL Divergence

## Abstract

Finite real-valued classical KL divergence decomposes into marginal and conditional terms.

**Theorem 1.1 (Finite classical KL divergence obeys the chain rule).**

$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] [\operatorname{Fintype}(\kappa)],\\\forall p, q: \iota\times\kappa\to \mathbb{R},\\p_{\iota}(i):=\sum_{j}p(i,j),\quad q_{\iota}(i):=\sum_{j}q(i,j),\\p_{\kappa\mid i}(j):=\frac{p(i,j)}{p_{\iota}(i)},\quad q_{\kappa\mid i}(j):=\frac{q(i,j)}{q_{\iota}(i)};\\(\forall i, j, 0<p(i, j) \land 0<q(i, j)) \Rightarrow\\D(p\Vert\Vert q)=D(p_{\iota}\Vert\Vert q_{\iota})+\\\sum_{i}p_{\iota}(i)D(p_{\kappa\mid i}\Vert\Vert q_{\kappa\mid i}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/ChainRule.kl_divergence_chain_rule` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let iota and kappa be finite types, and let p and q be strictly positive real functions on their product. Only strict positivity is assumed; neither p nor q is assumed normalized. The in-file definitions are marginal r i = sum_j r(i,j) and conditional r i j = r(i,j) / marginal r i, so the conditional is the genuine quotient.

The empty second coordinate is handled explicitly in the Lean proof, so the theorem carries no Nonempty hypothesis and claims no normalization for an empty family. When kappa is nonempty, strict positivity makes every marginal positive, and sum_j conditional p i j = 1 is proved from these definitions and strict positivity, not assumed. The factorization p(i,j) = marginal p i * conditional p i j and Real.log_mul then split the finite joint sum into its marginal and marginal-weighted conditional terms.

This is the finite real-valued klDivergence of ClassicalDPI, the repository's single source for the definition, not a measure-theoretic divergence. Mathlib's measure-valued InformationTheory.klDiv_compProd_eq_add is not used, and no bridge between the ENNReal measure divergence and this finite real sum is established here. The declaration therefore does not identify this finite divergence with any measure-valued KL divergence. The ninth-wave theorem D5/S3/Divergence/ProductAdditivity is the special case in which the conditionals do not depend on the first coordinate.

## References

- Truth anchor: `D5/S3/Divergence/ChainRule.kl_divergence_chain_rule`
- Dependency: [D5/S3/Divergence/ClassicalDPI](ClassicalDPI.md)
