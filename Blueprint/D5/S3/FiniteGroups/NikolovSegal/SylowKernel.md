# Simple Sections of Sylow Normalizers

## Abstract

The normalizer of a Sylow p-subgroup excludes simple sections with p-divisible order that are not p-groups.

**Theorem 1.1 (The Sylow-normalizer obstruction).**

$$\forall A \in Typeu,\; Group\left(A\right) \Rightarrow \left(\forall G \in Typev,\; Group\left(G\right) \Rightarrow \left(\left(Finite\left(G\right) \land Simple\left(A\right)\right) \Rightarrow \left(\forall p \in Nat,\; Prime\left(p\right) \Rightarrow \left(\forall P \in Sylow\left(p, G\right),\; \left(\left(\neg IsPGroup\left(p, A\right)\right) \land p \mid card\left(A\right)\right) \Rightarrow \left(\neg Involves\left(A, normalizer\left(P\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/SylowKernel.not_involves_sylow_normalizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here P is a Sylow p-subgroup of finite G and normalizer(P) is its normalizer in G. Inside that normalizer, P is normal and is a p-group, while the quotient order is not divisible by p. A simple section must occur in the kernel or quotient. The p-group obstruction excludes the kernel branch; divisibility excludes the quotient branch.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/SylowKernel.not_involves_sylow_normalizer`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/Sections](Sections.md)
