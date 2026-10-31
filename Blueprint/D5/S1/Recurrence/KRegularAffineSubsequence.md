# Affine subsequences of integer k-regular sequences

## Abstract

Every positive-step affine subsequence of an integer k-regular sequence is k-regular.

Sequences have domain the natural numbers, including zero, and values in the integers. Write K_k(s) for the set of all sequences n ↦ s(k^e n+r), where e and r are natural numbers and r<k^e. The sequence s is k-regular exactly when the integer span of K_k(s) is finitely generated; denote this property by Regular(k,s). Neither the values nor the kernel are required to be finite.

**Theorem 1.1 (Uniform transport of kernel spans).**

$$\forall k \in \mathrm{Nat},\; \forall a \in \mathrm{Nat},\; \forall b \in \mathrm{Nat},\; \forall s \in (\mathrm{Nat} \to \mathbb{Z}),\; 2 \le k \Rightarrow \left(1 \le a \Rightarrow \left(\forall G \in \operatorname{Finset}\left((\mathrm{Nat} \to \mathbb{Z})\right),\; \operatorname{span}_{\mathbb{Z}}(G) = \operatorname{span}_{\mathbb{Z}}(K_{k}(s)) \Rightarrow \operatorname{span}_{\mathbb{Z}}(K_{k}((n: \mathrm{Nat} \mapsto \operatorname{s}\left(a \cdot n + b\right)))) \subseteq \operatorname{span}_{\mathbb{Z}}(\{f: (\mathrm{Nat} \to \mathbb{Z}) \mid \exists g \in (\mathrm{Nat} \to \mathbb{Z}),\; g \in G \land \left(\exists c \in \mathrm{Nat},\; c < a + b \land f = (n: \mathrm{Nat} \mapsto \operatorname{g}\left(a \cdot n + c\right))\right) \})\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KRegularAffineSubsequence.affine_kernel_span_le` (`✓ std3`). ∎

*Citation.* Jean-Paul Allouche and Jeffrey Shallit (1992). *The Ring of k-Regular Sequences*. URL: <https://cs.uwaterloo.ca/~shallit/Papers/as0.pdf>.

*Commentary.*

For every base k≥2, positive natural step a, natural offset b, and finite family G whose integer span equals the span of K_k(s), the entire sampled kernel span lies in the span of the displayed family. To see this, fix any e and r with r<k^e and write ar+b=c k^e+d with d<k^e. Then c<a+b and s(a(k^e n+r)+b)=s(k^e(an+c)+d). The sequence m ↦ s(k^e m+d) belongs to K_k(s) and hence to the integer span of G. Substitution m=an+c is linear, so the sampled kernel element belongs to the span of n ↦ g(an+c), g∈G. The same fixed family, with all c<a+b, works for every e and r. This is the containment used in the proof of Allouche and Shallit's preprint Theorem 2.6, PDF page 7.

**Theorem 1.2 (Affine-subsequence closure).**

$$\forall k \in \mathrm{Nat},\; \forall a \in \mathrm{Nat},\; \forall b \in \mathrm{Nat},\; \forall s \in (\mathrm{Nat} \to \mathbb{Z}),\; 2 \le k \Rightarrow \left(1 \le a \Rightarrow \left(\operatorname{Regular}\left(k, s\right) \Rightarrow \operatorname{Regular}\left(k, (n: \mathrm{Nat} \mapsto \operatorname{s}\left(a \cdot n + b\right))\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KRegularAffineSubsequence.is_k_regular_affine_subsequence` (`✓ std3`). ∎

*Citation.* Jean-Paul Allouche and Jeffrey Shallit (1992). *The Ring of k-Regular Sequences*. URL: <https://cs.uwaterloo.ca/~shallit/Papers/as0.pdf>.

*Commentary.*

For every k≥2, every natural a≥1 and b, and every integer-valued k-regular sequence s, the sequence n ↦ s(an+b) is k-regular in the same base. Extract a finite generating family G for the original kernel span. The family of affine observations above is finite, being the image of G times the natural offsets c<a+b. The uniform containment places the sampled kernel span inside its finitely generated integer span. Since the integers form a Noetherian ring, that submodule is finitely generated. This is the integer-coefficient case of the cited preprint theorem; its coefficient convention and regularity definition appear on PDF page 3. The offset is nonnegative because it is natural. No finite-range, finite-kernel, periodicity, recurrence, or base-two hypothesis occurs. The mathematical assertion ranges over every base k≥2; its integer-valued sequence space is the one fixed here.

## References

- Truth anchor: `D5/S1/Recurrence/KRegularAffineSubsequence.affine_kernel_span_le`
- Truth anchor: `D5/S1/Recurrence/KRegularAffineSubsequence.is_k_regular_affine_subsequence`
- Dependency: [D5/S1/Recurrence/MetaFibonacci/SobolewskiUlasParityPositions](MetaFibonacci/SobolewskiUlasParityPositions.md)
