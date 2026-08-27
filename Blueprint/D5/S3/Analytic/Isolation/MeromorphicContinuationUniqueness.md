# Uniqueness of Meromorphic Continuation

## Abstract

Normal-form meromorphic continuations are fixed by their values on a nonempty open set.

**Theorem 1.1 (Meromorphic continuations agreeing on an open set are unique).**

$$\begin{gathered}\forall Omega, D\subseteq \mathbb{C},\\\forall f, g:\mathbb{C}\to\mathbb{C},\\\operatorname{IsOpen}(Omega) \land \operatorname{IsPreconnected}(Omega) \land \\\operatorname{IsOpen}(D) \land D\neq\emptyset \land D\subseteq Omega \land \\\operatorname{MeromorphicNFOn}(f,Omega) \land \operatorname{MeromorphicNFOn}(g,Omega) \land \\\operatorname{EqOn}(f,g,D) \Rightarrow \\\operatorname{EqOn}(f,g,Omega).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Isolation/MeromorphicContinuationUniqueness.meromorphic_continuation_unique` (`✓ std3`). ∎

*Citation.* Pintoo R. Jaiswar (2021). *Identity Theorem in Complex Analysis*. DOI: [10.37398/JSR.2021.650210](https://doi.org/10.37398/JSR.2021.650210).

*Commentary.*

Let Omega be an open preconnected complex domain and let D be a nonempty open subset of Omega. If f and g are meromorphic in normal form on Omega and agree pointwise on D, then they agree pointwise throughout Omega. Every premise displayed here occurs in the Lean type; in particular, D cannot be empty and the conclusion includes the canonical values at poles.

Normal form is the faithful Mathlib representation needed for the source's sphere-valued meromorphic functions. Bare `MeromorphicOn` allows a function to be changed arbitrarily at discrete pole points, so pointwise uniqueness would be false for that predicate. `MeromorphicNFOn` fixes every pole to one canonical default value; it does not assert that the functions are analytic or pole-free.

The proof delegates the analytic content to Mathlib's local identity principles `MeromorphicAt.frequently_eq_iff_eventuallyEq` and `MeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds`. The repository wrapper only proves that local agreement and local disagreement form an open separation, then invokes preconnectedness. No Laurent-series identity argument is reproved.

Repository search found the related theorem `D5/S3/Zeros/CompletedZeta.analytic_continuation_unique`, but that declaration assumes both continuations are analytic and therefore does not cover this meromorphic atom. This theorem proves uniqueness only: it constructs no continuation and assumes no Euler-product, functional equation, or absence of poles.

## References

- Truth anchor: `D5/S3/Analytic/Isolation/MeromorphicContinuationUniqueness.meromorphic_continuation_unique`
