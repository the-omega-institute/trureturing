# Structural Completion Signatures

## Abstract

A structural completion signature is the one-orbit quotient of the constrained zero-defect carrier, and a gauge-fixed completion constant is its sole value.

**Theorem 1.1 (Completion points, signatures, and constants).**

$$\forall G, A, D, \operatorname{Group}\left(G\right) \land \operatorname{MulAction}\left(G, A\right) \land (\forall g: G, a: A, a\in \operatorname{K}\left(\mathcal{N}, \Delta, 0_{D}\right) \Rightarrow \operatorname{smul}\left(g, a\right)\in \operatorname{K}\left(\mathcal{N}, \Delta, 0_{D}\right)) \Rightarrow\\(\forall a: A, a\in \operatorname{K}\left(\mathcal{N}, \Delta, 0_{D}\right) \iff (a\in \mathcal{N} \land \operatorname{Delta}\left(a\right) = 0_{D})) \land\\(\operatorname{HasStructuralCompletionSignature}\left(\mathcal{N}, \Delta, 0_{D}\right) \iff \operatorname{Nonempty}\left(\operatorname{Unique}\left(\operatorname{CompletionSignature}\left(\operatorname{K}\left(\mathcal{N}, \Delta, 0_{D}\right), G\right)\right)\right)) \land\\(\forall R, S: \operatorname{Set}\left(R\right), \kappa: R, \operatorname{IsCompletionConstant}\left(S, \kappa\right) \iff S = \{\kappa\}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Completion/StructuralCompletionSignature.completion_vocabulary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N be the supplied normalization constraint, Delta the structural defect, and zero_D its distinguished zero. The completion carrier K consists exactly of the parameters in N with zero defect. It is implemented as Mathlib's SubMulAction, so the displayed gauge stability premise is the closure needed to act on K.

The signature Sigma is Mathlib's canonical orbitRel quotient K/G. The source's one-orbit naming condition is represented by nonemptiness of K together with IsPretransitive G K. Mathlib's exact pretransitive_iff_unique_quotient_of_nonempty theorem identifies that condition with Sigma carrying a Unique instance.

The completion-constant predicate contains both halves of uniqueness: kappa belongs to the gauge-fixed value set and every value in that set equals kappa. It is therefore equivalent to the fixed value set being the singleton containing kappa; an empty set cannot satisfy the predicate vacuously.

The unconditioned quotient is not forced to collapse: the Lean probes construct a two-point, gauge-stable completion carrier with two distinct orbit classes. Collapse occurs exactly after the nonempty pretransitive naming condition is supplied.

## References

- Truth anchor: `D5/S3/Observer/Completion/StructuralCompletionSignature.completion_vocabulary`
