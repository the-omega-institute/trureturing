# Rank-two shortening for binary symplectic codes

## Abstract

Surjective radical projections allow binary symplectic shortening. The spread and six-site Gram arguments rule out a rank-two radical site at length seven. A conditional count rules out a rank-two radical site at length eight under the two-site rank bound.

**Theorem 1.1 (Shortening on a set of radical sites).**

$$\forall (n: \mathbb{N}), \forall (I: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), \forall (H: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))\right)), \forall (U: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))\right)), (H \le U) \Rightarrow \left((\forall (h: ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))), (h \in H) \Rightarrow \forall (u: ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))), (u \in U) \Rightarrow \operatorname{spForm}\left(n, h, u\right) = 0) \Rightarrow \left((\operatorname{Surjective}\left(\operatorname{domRestrict}\left(\operatorname{restrictSites}\left(I\right), H\right)\right)) \Rightarrow \left((\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), \operatorname{shortened}\left(I, H\right)\right) + 2 \times \operatorname{card}\left(I\right) = \operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), H\right)) \land ((\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), \operatorname{shortened}\left(I, U\right)\right) + 2 \times \operatorname{card}\left(I\right) = \operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), U\right)) \land (\forall (x: ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))), (x \in U) \Rightarrow \exists (y: ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))), (y \in \operatorname{shortened}\left(I, U\right)) \land ((x - y \in H) \land (\forall (u: ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))), (u \in U) \Rightarrow \operatorname{spForm}\left(n, y, u\right) = \operatorname{spForm}\left(n, x, u\right)))))\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/BinaryEAShortening.shorten_of_radical_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The site map reads the position and momentum bits. The map π sends a word to all its symbols on I, and shortened(I,S) is the subspace of S whose symbols on I vanish. Subtract a word of H with the same symbols on I to get a representative of each class. Orthogonality to H preserves the pairing, and surjectivity gives the two dimension drops.

**Theorem 1.2 (The Gram of a five-site spread).**

$$\forall (n: \mathbb{N}), \forall (J: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), \forall (G: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))\right)), (\operatorname{card}\left(J\right) = 5) \Rightarrow \left((\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), G\right) = 4) \Rightarrow \left((\forall (x: ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))), (x \in G) \Rightarrow \left((x \ne 0) \Rightarrow \operatorname{card}\left(\operatorname{zeroSites}\left(J, x\right)\right) \le 1\right)) \Rightarrow \forall (x: ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))), (x \in G) \Rightarrow \forall (y: ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))), (y \in G) \Rightarrow \sum_{i \in J} ((x).fst\left(i\right) \cdot (y).snd\left(i\right) + (x).snd\left(i\right) \cdot (y).fst\left(i\right)) = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/BinaryEAShortening.five_site_gram_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each coordinate kernel has at least three nonzero words. The five kernels have disjoint nonzero parts, so those parts exhaust the fifteen nonzero words. At a site the binary pairing equals one plus the zero indicators of x, y, and x+y. For distinct nonzero x and y the five constants and the three zero indicators sum to zero in the binary field.

**Theorem 1.3 (Exclusion of two rank-two shortenings at length seven).**

$$\forall (H: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)))\right)), \forall (U: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)))\right)), (H \le U) \Rightarrow \left((\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), H\right) = 4) \Rightarrow \left((\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), U\right) = 8) \Rightarrow \left((\forall (h: ((\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)))), (h \in H) \Rightarrow \forall (u: ((\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)))), (u \in U) \Rightarrow \operatorname{spForm}\left(7, h, u\right) = 0) \Rightarrow \left((\forall (x: ((\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)))), (x \in U) \Rightarrow \left((\neg (x \in H)) \Rightarrow \operatorname{card}\left(\operatorname{zeroSites}\left(univ, x\right)\right) \le 3\right)) \Rightarrow \forall (I: \operatorname{Finset}\left(\operatorname{Fin}\left(7\right)\right)), (\operatorname{card}\left(I\right) = 2) \Rightarrow \left((\operatorname{Surjective}\left(\operatorname{domRestrict}\left(\operatorname{restrictSites}\left(I\right), H\right)\right)) \Rightarrow False\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/BinaryEAShortening.length_seven_no_surjective_radical_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shortened radical is zero and the shortened code has dimension four on five surviving sites. Its pairing vanishes by the spread argument, so the original code is isotropic by the radical lifts. An isotropic subspace in the nondegenerate length-seven ambient space has dimension at most seven.

**Theorem 1.4 (Exclusion with seven surviving sites and a rank-one radical projection bound).**

$$\forall (n: \mathbb{N}), \forall (J: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), \forall (H: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))\right)), \forall (U: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))\right)), (H \le U) \Rightarrow \left((\operatorname{card}\left(J\right) = 7) \Rightarrow \left((\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), H\right) = 2) \Rightarrow \left((\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), U\right) = 6) \Rightarrow \left((\forall (h: ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))), (h \in H) \Rightarrow \forall (u: ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))), (u \in U) \Rightarrow \operatorname{spForm}\left(n, h, u\right) = 0) \Rightarrow \left((\forall (h: ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))), (h \in H) \Rightarrow \forall (i: \operatorname{Fin}\left(n\right)), (\neg (i \in J)) \Rightarrow \operatorname{site}\left(i\right)\left(h\right) = 0) \Rightarrow \left((\forall (i: \operatorname{Fin}\left(n\right)), (i \in J) \Rightarrow \left(\neg (\operatorname{Surjective}\left(\operatorname{domRestrict}\left(\operatorname{site}\left(i\right), H\right)\right))\right)) \Rightarrow \left((\forall (x: ((\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(n\right) \to \operatorname{ZMod}\left(2\right)))), (x \in U) \Rightarrow \left((\neg (x \in H)) \Rightarrow \operatorname{card}\left(\operatorname{zeroSites}\left(J, x\right)\right) \le 2\right)) \Rightarrow False\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/BinaryEAShortening.seven_surviving_sites_no_rank_one_radical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an occupied radical site, where the kernel in H consists of zero and a single nonzero word h. Outside H, words vanishing there and at distinct second sites belong to disjoint sets. Rank-nullity and the cardinality of each pair kernel force h to be supported on at most two sites. A triple containing that support and the fixed site is injective on H and then on U. Its restriction on U is surjective by dimension, which contradicts orthogonality to h.

**Theorem 1.5 (The remaining length-seven case after one shortening).**

$$\forall (H: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)))\right)), \forall (U: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)))\right)), (H \le U) \Rightarrow \left((\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), H\right) = 4) \Rightarrow \left((\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), U\right) = 8) \Rightarrow \left((\forall (h: ((\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)))), (h \in H) \Rightarrow \forall (u: ((\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)))), (u \in U) \Rightarrow \operatorname{spForm}\left(7, h, u\right) = 0) \Rightarrow \left((\forall (x: ((\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)))), (x \in U) \Rightarrow \left((\neg (x \in H)) \Rightarrow \operatorname{card}\left(\operatorname{zeroSites}\left(univ, x\right)\right) \le 3\right)) \Rightarrow \forall (i: \operatorname{Fin}\left(7\right)), (\operatorname{Surjective}\left(\operatorname{domRestrict}\left(\operatorname{site}\left(i\right), H\right)\right)) \Rightarrow \mathrm{let} I := \{i\} , (\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), \operatorname{shortened}\left(I, H\right)\right) = 2) \land ((\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), \operatorname{shortened}\left(I, U\right)\right) = 6) \land ((\forall (j: \operatorname{Fin}\left(7\right)), (j \in I^{c}) \Rightarrow \left(\neg (\operatorname{Surjective}\left(\operatorname{domRestrict}\left(\operatorname{site}\left(j\right), \operatorname{shortened}\left(I, H\right)\right)\right))\right)) \land (\forall (x: ((\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)))), (x \in \operatorname{shortened}\left(I, U\right)) \Rightarrow \left((\neg (x \in \operatorname{shortened}\left(I, H\right))) \Rightarrow \operatorname{card}\left(\operatorname{zeroSites}\left(I^{c}, x\right)\right) \le 2\right))))\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/BinaryEAShortening.length_seven_rank_two_shortens_to_rank_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A rank-two radical site leaves dimensions two and six and a bound of two zeros outside the shortened radical. Any second surjective radical site would lift to a surjective joint projection on the two original sites, contradicting the length-seven spread obstruction.

**Theorem 1.6 (Exclusion of a rank-two radical site at length eight).**

$$\forall (H: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(8\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(8\right) \to \operatorname{ZMod}\left(2\right)))\right)), \forall (U: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(8\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(8\right) \to \operatorname{ZMod}\left(2\right)))\right)), (H \le U) \Rightarrow \left((\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), H\right) = 4) \Rightarrow \left((\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), U\right) = 8) \Rightarrow \left((\forall (h: ((\operatorname{Fin}\left(8\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(8\right) \to \operatorname{ZMod}\left(2\right)))), (h \in H) \Rightarrow \forall (u: ((\operatorname{Fin}\left(8\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(8\right) \to \operatorname{ZMod}\left(2\right)))), (u \in U) \Rightarrow \operatorname{spForm}\left(8, h, u\right) = 0) \Rightarrow \left((\forall (x: ((\operatorname{Fin}\left(8\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(8\right) \to \operatorname{ZMod}\left(2\right)))), (x \in U) \Rightarrow \left((\neg (x \in H)) \Rightarrow \operatorname{card}\left(\operatorname{zeroSites}\left(univ, x\right)\right) \le 3\right)) \Rightarrow \forall (i: \operatorname{Fin}\left(8\right)), (\operatorname{Surjective}\left(\operatorname{domRestrict}\left(\operatorname{site}\left(i\right), H\right)\right)) \Rightarrow \left((\forall (j: \operatorname{Fin}\left(8\right)), (j \ne i) \Rightarrow \operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), \operatorname{range}\left(\operatorname{domRestrict}\left(\operatorname{restrictSites}\left(\{i, j\}\right), H\right)\right)\right) \le 3) \Rightarrow False\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/BinaryEAShortening.length_eight_no_rank_two_site` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Surjectivity at a second site of the shortened radical would lift to joint rank four on the corresponding original pair. The rank bound of three therefore leaves at most rank one at each of the seven surviving sites, where the conditional count gives the contradiction.

## References

- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAShortening.five_site_gram_zero`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAShortening.length_eight_no_rank_two_site`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAShortening.length_seven_no_surjective_radical_pair`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAShortening.length_seven_rank_two_shortens_to_rank_one`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAShortening.seven_surviving_sites_no_rank_one_radical`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAShortening.shorten_of_radical_surjective`
- Dependency: [D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm](../Information/BinaryStabilizerGraphNormalForm.md)
