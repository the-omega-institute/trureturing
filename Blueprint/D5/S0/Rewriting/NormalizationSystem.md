# Certified Normalization Systems

## Abstract

Terminating locally confluent rewrite systems expose one canonical certified normalizer.

**Theorem 1.1 (Certified normalizers are unique).**

$$\forall N, M: \operatorname{CertifiedNormalizer}(S), N.run = M.run.$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/NormalizationSystem.certified_normalizer_run_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A normalization system packages a rewrite step together with well-founded termination and local confluence.

The existing Newman and normal-form nodes supply a canonical endpoint, reachability, irreducibility, idempotence, and invariance under generated equivalence.

A certified normalizer must return a reachable irreducible endpoint. Confluence identifies that endpoint with the canonical normal form, so any two certified normalizers agree as functions.

## References

- Truth anchor: `D5/S0/Rewriting/NormalizationSystem.certified_normalizer_run_unique`
- Dependency: [D5/S0/Rewriting/NormalFormFunction](NormalFormFunction.md)
