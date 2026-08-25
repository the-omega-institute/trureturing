# Binary Character Redundancy Criterion

## Abstract

A binary character is redundant exactly when it lies in the existing span.

**Theorem 1.1 (Kernel preservation, span membership, and output recovery are equivalent).**

$$\begin{gathered}\forall G, I: \operatorname{Type},\\{}[\operatorname{AddCommGroup}(G)], [\operatorname{Finite}(I)],\\{}chi: I \to \operatorname{Dual}(\operatorname{ZMod}(2), \operatorname{ModN}(G, 2)),\\{}eta: \operatorname{Dual}(\operatorname{ZMod}(2), \operatorname{ModN}(G, 2)),\\{}\operatorname{ListTFAE}({[\forall g \in G, (\forall i \in I, chi(i)(\operatorname{mkQ}(2, g)) = 0) \Rightarrow eta(\operatorname{mkQ}(2, g)) = 0, eta \in \operatorname{span}(\operatorname{ZMod}(2), \operatorname{range}(chi)), \exists a: \operatorname{Finsupp}(I, \operatorname{ZMod}(2)), \forall g \in G, \operatorname{ofAdd}(eta(\operatorname{mkQ}(2, g))) = \prod_{i \in \operatorname{support}(a)} \operatorname{ofAdd}(a(i) \cdot chi(i)(\operatorname{mkQ}(2, g)))]}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/BinaryCharacterRedundancyCriterion.binary_character_redundancy_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be an abelian group and let I be a finite role-index type. Every binary character is a linear functional on the canonical quotient of G by doubles, evaluated on G through the quotient map.

The first public clause says that the new character vanishes whenever all existing characters vanish. The second says directly that it belongs to the binary-field span of the existing character range.

The third clause exposes finite coefficients. At every group element, the multiplicative output of the new character is recovered as the finite product of the corresponding weighted existing outputs.

The proof applies the pinned library kernel-span criterion and finite-span coefficient theorem, then uses ofAdd_sum for the product formula.

## References

- Truth anchor: `D5/S3/Fourier/BinaryCharacterRedundancyCriterion.binary_character_redundancy_criterion`
- Dependency: [D5/S3/Fourier/BinaryCharacterBasisMinimality](BinaryCharacterBasisMinimality.md)
