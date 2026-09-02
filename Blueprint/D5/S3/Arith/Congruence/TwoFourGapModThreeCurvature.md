# Two-Four-Gap Modulo-Three Curvature

## Abstract

Two-four-gap constellations omit a residue modulo three exactly when every adjacent curvature is nonzero.

**Theorem 1.1 (Modulo-three admissibility is equivalent to nonzero gap curvature).**

$$\begin{gathered}\forall H \in \operatorname{List}(\mathbb{Z}),\\{}(\forall i \in \mathbb{N}, i + 1 < \operatorname{length}(H) \Rightarrow (H_{i + 1} - H_{i} = 2 \lor H_{i + 1} - H_{i} = 4)) \Rightarrow\\{}(((\exists r \in \operatorname{ZMod}(3), \forall i \in \mathbb{N}, i < \operatorname{length}(H) \Rightarrow \operatorname{residue}(3, H_{i}) \neq r) \Leftrightarrow \forall i \in \mathbb{N}, i + 2 < \operatorname{length}(H) \Rightarrow (\frac{H_{i + 1 + 1} - H_{i + 1}}{2} - 1) - (\frac{H_{i + 1} - H_{i}}{2} - 1) \neq 0) \land\\{}\forall i \in \mathbb{N}, i + 2 < \operatorname{length}(H) \Rightarrow\\{}(((\frac{H_{i + 1 + 1} - H_{i + 1}}{2} - 1) - (\frac{H_{i + 1} - H_{i}}{2} - 1) = 0 \Leftrightarrow (H_{i + 1} - H_{i} = H_{i + 1 + 1} - H_{i + 1} \land \forall r \in \operatorname{ZMod}(3), \operatorname{residue}(3, H_{i}) = r \lor \operatorname{residue}(3, H_{i + 1}) = r \lor \operatorname{residue}(3, H_{i + 2}) = r)) \land\\{}((\frac{H_{i + 1 + 1} - H_{i + 1}}{2} - 1) - (\frac{H_{i + 1} - H_{i}}{2} - 1) = 1 \Leftrightarrow (H_{i + 1} - H_{i} = 2 \land H_{i + 1 + 1} - H_{i + 1} = 4 \land \exists r \in \operatorname{ZMod}(3), \operatorname{residue}(3, H_{i}) \neq r \land \operatorname{residue}(3, H_{i + 1}) \neq r \land \operatorname{residue}(3, H_{i + 2}) \neq r)) \land\\{}((\frac{H_{i + 1 + 1} - H_{i + 1}}{2} - 1) - (\frac{H_{i + 1} - H_{i}}{2} - 1) = -1 \Leftrightarrow (H_{i + 1} - H_{i} = 4 \land H_{i + 1 + 1} - H_{i + 1} = 2 \land \exists r \in \operatorname{ZMod}(3), \operatorname{residue}(3, H_{i}) \neq r \land \operatorname{residue}(3, H_{i + 1}) \neq r \land \operatorname{residue}(3, H_{i + 2}) \neq r)))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/TwoFourGapModThreeCurvature.two_four_gap_mod_three_admissible_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be a finite integer constellation whose consecutive gaps are all two or four. Its normalized curvature at a triple is the second gap bit minus the first gap bit.

The constellation omits a residue modulo three exactly when every adjacent curvature is nonzero. Equal gaps have zero curvature and their three points cover all residues.

A two-then-four turn has curvature one, while a four-then-two turn has curvature minus one. Each unequal turn visits only two residues and therefore has an explicitly omitted residue.

Repository and pinned-library searches found no exact theorem. The proof constructs the residue trajectory from the integer gaps, proves its two-step repetition, and classifies all four local gap pairs.

## References

- Truth anchor: `D5/S3/Arith/Congruence/TwoFourGapModThreeCurvature.two_four_gap_mod_three_admissible_iff`
