# Measurable selection and compact metric quotient sections

## Abstract

Weak-measurable nonempty closed fibers admit measurable selectors; continuous compact metric quotients have Borel right inverses.

All carrier universes are independent. BorelSpace means that the specified measurable structure equals the Borel structure. Hit(Phi,U) is exactly the set of a with nonempty Phi(a) intersect U. No carrier is assumed nonempty. The first theorem has an arbitrary measurable source and a complete separable metric Borel target.

**Theorem 1.1 (Kuratowski–Ryll-Nardzewski measurable selection).**

$$\begin{aligned}\forall A: \operatorname{Type}\left(u\right), \forall Y: \operatorname{Type}\left(v\right), \\\operatorname{MeasurableSpace}\left(A\right) \land \operatorname{CompleteSeparableMetricBorelSpace}\left(Y\right) \Rightarrow\\\forall Phi: A \to \operatorname{Set}\left(Y\right), \\{\forall a: A, \operatorname{Nonempty}\left(\operatorname{Phi}\left(a\right)\right) \land \operatorname{IsClosed}\left(\operatorname{Phi}\left(a\right)\right)} \Rightarrow\\{\forall U: \operatorname{Set}\left(Y\right), \operatorname{IsOpen}\left(U\right) \Rightarrow \operatorname{MeasurableSet}\left(\operatorname{Hit}\left(Phi, U\right)\right)} \Rightarrow\\\exists f: A \to Y, \operatorname{Measurable}\left(f\right) \land {\forall a: A, \operatorname{f}\left(a\right) \in \operatorname{Phi}\left(a\right)}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Selection/Measurable.exists_measurable_selection` (`✓ std3`). ∎

*Citation.* KT. Wu (2026). *The Kuratowski–Ryll-Nardzewski measurable selection theorem*. URL: <https://github.com/LeanPool/lean-pool/blob/7d5e94f7172d47c78cac7f23c0dd01cef1665e42/LeanPool/BicausalOT/BicausalOT/DescriptiveSetTheory/MeasurableSelection.lean>.

*Commentary.*

The actual KT. Wu / LeanPool proof is ported from commit 7d5e94f7172d47c78cac7f23c0dd01cef1665e42 under Apache 2.0. At stage n the selector takes values in a dense sequence and is the least index whose ball, intersected with the previous ball, meets the current fiber. The predicate splits over the countably many measurable fibers of the previous index. Geometric bounds give a Cauchy sequence; its pointwise limit is measurable and belongs to each closed fiber. The empty-source case uses the empty function. The source identity and license are recorded in the cited Library note; no originality is claimed.

**Theorem 1.2 (Borel section of a compact metric quotient).**

$$\begin{aligned}\forall K: \operatorname{Type}\left(u\right), \forall L: \operatorname{Type}\left(v\right), \\\operatorname{CompactMetricBorelSpace}\left(K\right) \land \operatorname{HausdorffBorelSpace}\left(L\right) \Rightarrow\\\forall p: K \to L, \operatorname{Continuous}\left(p\right) \land \operatorname{Surjective}\left(p\right) \Rightarrow\\\exists q: L \to K, \operatorname{Measurable}\left(q\right) \land {\forall y: L, \operatorname{p}\left(\operatorname{q}\left(y\right)\right) = y}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Selection/Measurable.exists_measurable_right_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* KT. Wu (2026). *The Kuratowski–Ryll-Nardzewski measurable selection theorem*. URL: <https://github.com/LeanPool/lean-pool/blob/7d5e94f7172d47c78cac7f23c0dd01cef1665e42/LeanPool/BicausalOT/BicausalOT/DescriptiveSetTheory/MeasurableSelection.lean>.

*Commentary.*

For every continuous surjection p from compact metric K to Hausdorff Borel L, put Phi(y)=p-preimage({y}). Surjectivity gives nonempty fibers and continuity gives closed fibers. An open U in K is locally compact and second countable as a subspace, hence sigma-compact. Its continuous image p[U] is a countable union of compact sets. Each compact set is closed in Hausdorff L, so this union is Borel. This image equals the hit set of U. The selector theorem gives measurable q with p(q(y))=y. No zero-dimensionality, positivity or metrizability assumption on L is imposed; empty carriers remain included.

## References

- Truth anchor: `D5/S3/Topology/Selection/Measurable.exists_measurable_right_inverse`
- Truth anchor: `D5/S3/Topology/Selection/Measurable.exists_measurable_selection`
