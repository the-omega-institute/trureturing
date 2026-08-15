# Quotient Contraction Rigidity

## Abstract

A strict contraction on a closed-subspace quotient has no nonzero fixed class.

**Theorem 1.1 (A strict quotient contraction has no nonzero fixed class).**

$$\forall k, H: \operatorname{Type},\ [\operatorname{NontriviallyNormedField}(k)],\ [\operatorname{NormedAddCommGroup}(H)],\ [\operatorname{NormedSpace}_{k}(H)],\ M: \operatorname{Submodule}_{k}(H),\ [\operatorname{IsClosed}(M)],\ R: H \to H,\ h: R(M) \subseteq M,\ x: H,\ (R(x) - x \in M \land \operatorname{norm}\left(\operatorname{inducedQuotientMap}\left(M, R, h\right)\right) < 1) \Rightarrow x \in M.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/QuotientContractionRigidity.quotient_contraction_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be a nontrivially normed field, H a normed space over k, M a closed subspace, and R a continuous linear endomorphism preserving M. If R fixes x modulo M and the induced operator on H modulo M has norm strictly less than one, then x lies in M.

The invariant-subspace hypothesis constructs the quotient operator via the canonical continuous quotient map and its continuous lift. The class of x is fixed because R x minus x belongs to M. Its norm is therefore at most the operator norm times itself; strict contraction forces that quotient norm to vanish, and closedness identifies the zero quotient class with membership in M.

Repository and pinned-Mathlib searches found no exact rigidity theorem. Pinned Mathlib supplies Submodule.mkQL, Submodule.liftQL, ContinuousLinearMap.le_opNorm, and the quotient zero-class lemma, which are composed directly. Loogle returned no exact match, and three GitHub Lean-code searches returned no hits. The LeanSearch API request failed, so it is not counted as a negative result.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/QuotientContractionRigidity.quotient_contraction_rigidity`
