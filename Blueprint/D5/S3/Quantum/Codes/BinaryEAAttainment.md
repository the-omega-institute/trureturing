# Coordinate kernels and support for binary Singleton attainment

## Abstract

Conditional counts of binary words vanishing on sets of sites control radical projection ranks and bound the size of the radical support.

**Definition 1.1 (A single coordinate pair).**

$$\forall (n: \mathbb{N}), \forall (i: \operatorname{Fin}\left(n\right)), \forall (v: ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))), \operatorname{site}\left(i, v\right) = (v.fst\left(i\right), v.snd\left(i\right))$$

*Formalization.* `D5/S3/Quantum/Codes/BinaryEAAttainment.site` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two entries are the position and momentum bits at the same site.

**Definition 1.2 (Restriction to a finite set of sites).**

$$\forall (n: \mathbb{N}), \forall (I: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), \forall (v: ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))), \forall (i: I), \operatorname{restrictSites}\left(I\right)\left(v, i\right) = \operatorname{site}\left(i.val, v\right)$$

*Formalization.* `D5/S3/Quantum/Codes/BinaryEAAttainment.restrictSites` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The codomain is indexed by the subtype of sites in the prescribed set.

**Definition 1.3 (Radical of the restricted symplectic form).**

$$\forall (n: \mathbb{N}), \forall (U: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))\right)), \operatorname{radical}\left(U\right) = \operatorname{inf}\left(U, \operatorname{orthogonal}\left(\operatorname{spForm}\left(n\right), U\right)\right)$$

*Formalization.* `D5/S3/Quantum/Codes/BinaryEAAttainment.radical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The orthogonal complement uses the ambient binary symplectic form.

**Definition 1.4 (Number of zero coordinate pairs).**

$$\forall (n: \mathbb{N}), \forall (v: ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))), \operatorname{zeroCount}\left(v\right) = \operatorname{card}\left(\operatorname{filter}\left(\operatorname{univ}, i \mapsto (\operatorname{site}\left(i, v\right) = 0)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Codes/BinaryEAAttainment.zeroCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A site contributes exactly when both bits vanish.

**Definition 1.5 (Exact binary attainment).**

$$(\operatorname{Attainment}) \Leftrightarrow (\exists (n: \mathbb{N}), (6 \le n) \land (\exists (U: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))\right)), (\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), U\right) = 8) \land ((\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), \operatorname{radical}\left(U\right)\right) = 4) \land ((\forall (v: ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))), (v \in U) \Rightarrow \left((\neg (v \in \operatorname{radical}\left(U\right))) \Rightarrow n - 3 \le n - \operatorname{zeroCount}\left(v\right)\right)) \land (\exists (v: ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))), (v \in U) \land ((\neg (v \in \operatorname{radical}\left(U\right))) \land (n - \operatorname{zeroCount}\left(v\right) = n - 3)))))))$$

*Formalization.* `D5/S3/Quantum/Codes/BinaryEAAttainment.Attainment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Weight counts nonzero coordinate pairs. The universal lower bound and an attaining nonradical word together specify the exact minimum.

**Definition 1.6 (At most three zero sites outside the radical).**

$$\forall (n: \mathbb{N}), \forall (U: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))\right)), (\operatorname{ZeroBound}\left(U\right)) \Leftrightarrow (\forall (v: ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))), (v \in U) \Rightarrow \left((\neg (v \in \operatorname{radical}\left(U\right))) \Rightarrow \operatorname{zeroCount}\left(v\right) \le 3\right))$$

*Formalization.* `D5/S3/Quantum/Codes/BinaryEAAttainment.ZeroBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Radical words are unrestricted by this predicate.

**Theorem 1.7 (Weight lower bound implies the zero-site bound).**

$$\forall (n: \mathbb{N}), \forall (U: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))\right)), (6 \le n) \Rightarrow \left((\forall (v: ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))), (v \in U) \Rightarrow \left((\neg (v \in \operatorname{radical}\left(U\right))) \Rightarrow n - 3 \le n - \operatorname{zeroCount}\left(v\right)\right)) \Rightarrow \operatorname{ZeroBound}\left(U\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/BinaryEAAttainment.zeroBound_of_weight_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero count is bounded by the ambient length, so the weight subtraction is exact.

**Definition 1.8 (Subspace vanishing on a site set).**

$$\forall (n: \mathbb{N}), \forall (W: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))\right)), \forall (I: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), \operatorname{siteKernel}\left(W, I\right) = \operatorname{inf}\left(W, \operatorname{ker}\left(\operatorname{restrictSites}\left(I\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Codes/BinaryEAAttainment.siteKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The intersection keeps the kernel in the ambient word space.

**Definition 1.9 (Cardinality of a coordinate kernel).**

$$\forall (n: \mathbb{N}), \forall (W: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))\right)), \forall (I: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), \operatorname{kernelCount}\left(W, I\right) = 2^{\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), \operatorname{siteKernel}\left(W, I\right)\right)}$$

*Formalization.* `D5/S3/Quantum/Codes/BinaryEAAttainment.kernelCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The base is two because the kernel is a binary vector space.

**Theorem 1.10 (Rank and nullity of the restricted site map).**

$$\forall (n: \mathbb{N}), \forall (W: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))\right)), \forall (I: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), \operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), \operatorname{siteKernel}\left(W, I\right)\right) + \operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), \operatorname{range}\left(\operatorname{domRestrict}\left(\operatorname{restrictSites}\left(I\right), W\right)\right)\right) = \operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), W\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/BinaryEAAttainment.dim_kernel_add_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ambient kernel and the kernel with domain restricted to W have equal dimension.

**Theorem 1.11 (Conditional coordinate-kernel count).**

$$\forall (n: \mathbb{N}), \forall (U: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))\right)), (\operatorname{ZeroBound}\left(U\right)) \Rightarrow \forall (I: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), (n - \operatorname{card}\left(I\right)) \cdot \operatorname{kernelCount}\left(U, I\right) + 4 \cdot (3 - \operatorname{card}\left(I\right)) \cdot \operatorname{kernelCount}\left(\operatorname{radical}\left(U\right), I\right) \le 4 \cdot (3 - \operatorname{card}\left(I\right)) \cdot \operatorname{kernelCount}\left(U, I\right) + 4 \cdot (\sum_{j \in I^{c}} \operatorname{kernelCount}\left(\operatorname{radical}\left(U\right), \operatorname{insert}\left(j, I\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/BinaryEAAttainment.kernelCount_inequality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each word outside the radical that vanishes on the prescribed set can vanish at at most three sites in total. Adding one site decreases the dimension of a kernel by at most two.

**Theorem 1.12 (Two-site radical kernels at length at least nine).**

$$\forall (n: \mathbb{N}), \forall (U: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))\right)), (\operatorname{ZeroBound}\left(U\right)) \Rightarrow \left((\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), U\right) = 8) \Rightarrow \left((9 \le n) \Rightarrow \forall (I: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), (\operatorname{card}\left(I\right) = 2) \Rightarrow 2 \le \operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), \operatorname{siteKernel}\left(\operatorname{radical}\left(U\right), I\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/BinaryEAAttainment.pair_kernel_dim_ge_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The count over extensions of a pair forces at least four radical words in the pair kernel.

**Theorem 1.13 (Positive two-site radical kernel at length eight).**

$$\forall (U: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(8\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(8\right) \to \operatorname{ZMod}\left(2\right)))\right)), (\operatorname{ZeroBound}\left(U\right)) \Rightarrow \left((\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), U\right) = 8) \Rightarrow \forall (I: \operatorname{Finset}\left(\operatorname{Fin}\left(8\right)\right)), (\operatorname{card}\left(I\right) = 2) \Rightarrow 0 < \operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), \operatorname{siteKernel}\left(\operatorname{radical}\left(U\right), I\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/BinaryEAAttainment.pair_kernel_dim_pos_at_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each pair shares at least one nonzero radical word that vanishes on it.

**Theorem 1.14 (Radical site rank at length at least nine).**

$$\forall (n: \mathbb{N}), \forall (U: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))\right)), (\operatorname{ZeroBound}\left(U\right)) \Rightarrow \left((\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), U\right) = 8) \Rightarrow \left((\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), \operatorname{radical}\left(U\right)\right) = 4) \Rightarrow \left((9 \le n) \Rightarrow \forall (i: \operatorname{Fin}\left(n\right)), \operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), \operatorname{range}\left(\operatorname{domRestrict}\left(\operatorname{restrictSites}\left(\{i\}\right), \operatorname{radical}\left(U\right)\right)\right)\right) \le 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/BinaryEAAttainment.radical_site_rank_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A rank-two site would have the same radical kernel as every pair containing it. The common kernel would then vanish at every site.

**Definition 1.15 (Union of occupied sites).**

$$\forall (n: \mathbb{N}), \forall (W: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))\right)), \operatorname{support}\left(W\right) = \operatorname{filter}\left(\operatorname{univ}, i \mapsto (\exists (v: ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))), (v \in W) \land (\operatorname{site}\left(i, v\right) \ne 0))\right)$$

*Formalization.* `D5/S3/Quantum/Codes/BinaryEAAttainment.support` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The support is taken across all words of the subspace.

**Theorem 1.16 (Membership in the radical-support construction).**

$$\forall (n: \mathbb{N}), \forall (W: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))\right)), \forall (i: \operatorname{Fin}\left(n\right)), (i \in \operatorname{support}\left(W\right)) \Leftrightarrow (\exists (v: ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))), (v \in W) \land (\operatorname{site}\left(i, v\right) \ne 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/BinaryEAAttainment.mem_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A single word with a nonzero pair witnesses membership.

**Definition 1.17 (Words supported on a specified site set).**

$$\forall (n: \mathbb{N}), \forall (I: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), \operatorname{supportedOn}\left(I\right) = \operatorname{siteKernel}\left(\operatorname{top}, I^{c}\right)$$

*Formalization.* `D5/S3/Quantum/Codes/BinaryEAAttainment.supportedOn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The site kernel is imposed on the complement of the prescribed sites.

**Definition 1.18 (Projection that zeroes sites outside a prescribed set).**

$$\forall (n: \mathbb{N}), \forall (I: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), \forall (v: ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))), \forall (i: \operatorname{Fin}\left(n\right)), ((i \in I) \Rightarrow \operatorname{site}\left(i, \operatorname{mask}\left(I\right)\left(v\right)\right) = \operatorname{site}\left(i, v\right)) \land ((\neg (i \in I)) \Rightarrow \operatorname{site}\left(i, \operatorname{mask}\left(I\right)\left(v\right)\right) = 0)$$

*Formalization.* `D5/S3/Quantum/Codes/BinaryEAAttainment.mask` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two implications give the coordinate pair of the projected word at every site.

**Theorem 1.19 (Injectivity of projection to the radical support).**

$$\forall (n: \mathbb{N}), \forall (U: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))\right)), (\operatorname{ZeroBound}\left(U\right)) \Rightarrow \left((4 \le \operatorname{card}\left(\operatorname{support}\left(\operatorname{radical}\left(U\right)\right)\right)) \Rightarrow \operatorname{Injective}\left(\operatorname{domRestrict}\left(\operatorname{mask}\left(\operatorname{support}\left(\operatorname{radical}\left(U\right)\right)\right), U\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/BinaryEAAttainment.core_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A kernel word already vanishes on the radical support. With at least four such sites it lies in the radical, where it also vanishes at all other sites.

**Theorem 1.20 (The projected code is supported and orthogonal to the radical).**

$$\forall (n: \mathbb{N}), \forall (U: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))\right)), \operatorname{map}\left(\operatorname{mask}\left(\operatorname{support}\left(\operatorname{radical}\left(U\right)\right)\right), U\right) \le \operatorname{inf}\left(\operatorname{orthogonal}\left(\operatorname{spForm}\left(n\right), \operatorname{radical}\left(U\right)\right), \operatorname{supportedOn}\left(\operatorname{support}\left(\operatorname{radical}\left(U\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/BinaryEAAttainment.core_le_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Masking outside the radical support preserves the pairing with every radical word.

**Theorem 1.21 (At least seven radical support sites).**

$$\forall (n: \mathbb{N}), \forall (U: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))\right)), (\operatorname{ZeroBound}\left(U\right)) \Rightarrow \left((\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), U\right) = 8) \Rightarrow \left((\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), \operatorname{radical}\left(U\right)\right) = 4) \Rightarrow 7 \le \operatorname{card}\left(\operatorname{support}\left(\operatorname{radical}\left(U\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/BinaryEAAttainment.seven_le_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At six support sites the masked code fills the supported orthogonal complement. Zero and the eighteen single-site errors would require nineteen distinct four-bit syndromes.

**Theorem 1.22 (Upper bounds on the radical support at length at least nine).**

$$\forall (n: \mathbb{N}), \forall (U: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))\right)), (\operatorname{ZeroBound}\left(U\right)) \Rightarrow \left((\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), U\right) = 8) \Rightarrow \left((\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), \operatorname{radical}\left(U\right)\right) = 4) \Rightarrow \left((9 \le n) \Rightarrow \left((8 \cdot n + 3 \cdot \operatorname{card}\left(\operatorname{support}\left(\operatorname{radical}\left(U\right)\right)\right) \le 120) \land (\operatorname{card}\left(\operatorname{support}\left(\operatorname{radical}\left(U\right)\right)\right) \le 10)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/BinaryEAAttainment.radical_support_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At length at least nine all occupied radical sites project to lines. The one-site conditional count across four independent types gives the joint length and support bound.

## References

- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainment.Attainment`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainment.ZeroBound`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainment.core_injective`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainment.core_le_orthogonal`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainment.dim_kernel_add_rank`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainment.kernelCount`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainment.kernelCount_inequality`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainment.mask`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainment.mem_support`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainment.pair_kernel_dim_ge_two`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainment.pair_kernel_dim_pos_at_eight`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainment.radical`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainment.radical_site_rank_le_one`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainment.radical_support_upper_bound`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainment.restrictSites`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainment.seven_le_support`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainment.site`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainment.siteKernel`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainment.support`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainment.supportedOn`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainment.zeroBound_of_weight_bound`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAAttainment.zeroCount`
- Dependency: [D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm](../Information/BinaryStabilizerGraphNormalForm.md)
