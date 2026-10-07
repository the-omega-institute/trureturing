# ConditionalNikolovSegal

## Abstract

Strong completeness conditional on two explicit finite-group propositions.

**Theorem 1.1 (Conditional strong completeness).**

$${\forall (d: \mathbb{N}), \forall (m: \mathbb{N}), {0 < m} \Rightarrow {\exists (w: \mathbb{N}), \operatorname{FinitePowerWidth}(d, m, w)}} \Rightarrow {{\forall (d: \mathbb{N}), \forall (m: \mathbb{N}), {0 < m} \Rightarrow {\exists (B: \mathbb{N}), \operatorname{FiniteExponentBound}(d, m, B)}} \Rightarrow {\forall (G: Type), {\operatorname{CompactTotallyDisconnectedTopologicalGroup}(G)} \Rightarrow {{\exists (S: \operatorname{Finset}(G)), \operatorname{TopologicalClosure}(\operatorname{SubgroupClosure}(S)) = \operatorname{TopSubgroup}(G)} \Rightarrow {\forall (H: \operatorname{Subgroup}(G)), {\operatorname{FiniteIndex}(H)} \Rightarrow {\operatorname{IsOpen}(H)}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/ConditionalNikolovSegal.conditional_nikolov_segal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume, for every d and positive m, an ordered mth-power width bound for every finite d-generated group, and a finite order bound for every such group of exponent dividing m. Then every finite-index subgroup of an arbitrary compact totally disconnected topological group generated densely by some finite set is open. Both deep finite-group propositions are premises. This is the full strong-completeness conclusion conditional on those premises; neither deep theorem is proved here. The power-width input is the Nikolov and Segal result Powers in finite groups (2011), DOI 10.4171/GGD/136. The order-bound input is the restricted Burnside theorem of Zelmanov. The unconditional strong-completeness theorem is Nikolov and Segal (2007), DOI 10.4007/annals.2007.165.171.

## References

- Truth anchor: `D5/S3/Factorization/Galois/ConditionalNikolovSegal.conditional_nikolov_segal`
- Dependency: [D5/S3/Factorization/Galois/ProfiniteQuotientBound](ProfiniteQuotientBound.md)
