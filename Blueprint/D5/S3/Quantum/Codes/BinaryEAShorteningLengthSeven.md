# Length-seven residual obstruction for binary symplectic codes

## Abstract

The six-site residual Gram argument rules out the remaining rank-two radical case at length seven.

**Theorem 1.1 (Exclusion of a rank-two radical site at length seven).**

$$\forall (H: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)))\right)), \forall (U: \operatorname{Submodule}\left(\operatorname{ZMod}\left(2\right), ((\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)))\right)), (H \le U) \Rightarrow \left((\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), H\right) = 4) \Rightarrow \left((\operatorname{finrank}\left(\operatorname{ZMod}\left(2\right), U\right) = 8) \Rightarrow \left((\forall (h: ((\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)))), (h \in H) \Rightarrow \forall (u: ((\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)))), (u \in U) \Rightarrow \operatorname{spForm}\left(7, h, u\right) = 0) \Rightarrow \left((\forall (x: ((\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)) \times (\operatorname{Fin}\left(7\right) \to \operatorname{ZMod}\left(2\right)))), (x \in U) \Rightarrow \left((\neg (x \in H)) \Rightarrow \operatorname{card}\left(\operatorname{zeroSites}\left(univ, x\right)\right) \le 3\right)) \Rightarrow \forall (i: \operatorname{Fin}\left(7\right)), (\operatorname{Surjective}\left(\operatorname{domRestrict}\left(\operatorname{site}\left(i\right), H\right)\right)) \Rightarrow False\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/BinaryEAShorteningLengthSeven.length_seven_no_rank_two_site` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After shortening, a three-site projection excludes radical words of weight at most two and weight-three words supported on mixed radical types. Local symplectic coordinates leave either two triples or three pairs of types. In both profiles the Z projection has kernel equal to the radical and image equal to its annihilator. A weight-two Z vector in the two-triple profile permits three zeros after a radical shift. In the three-pair profile, shifts enforce pair mismatches and parity equations on the four Z-basis lifts. These equations make the symplectic Gram vanish. Lifting through the shortening then makes the original eight-dimensional code isotropic in dimension fourteen.

## References

- Truth anchor: `D5/S3/Quantum/Codes/BinaryEAShorteningLengthSeven.length_seven_no_rank_two_site`
- Dependency: [D5/S3/Quantum/Codes/BinaryEAShortening](BinaryEAShortening.md)
