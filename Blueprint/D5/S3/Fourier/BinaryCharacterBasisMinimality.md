# Binary Character Basis Minimality

## Abstract

Binary-character bases are exactly minimum complete observation families.

**Theorem 1.1 (Character-span bases are minimum complete observation families).**

$$\begin{gathered}\forall G, I, J, B,\\{}[\operatorname{AddCommGroup}(G)], [\operatorname{Finite}(G)], [\operatorname{Finite}(I)],\\{}[\operatorname{Fintype}(J)], [\operatorname{Fintype}(B)],\\{}chi: I \to \operatorname{Dual}(\operatorname{ZMod}(2), \operatorname{ModN}(G, 2)), psi: J \to \operatorname{Dual}(\operatorname{ZMod}(2), \operatorname{ModN}(G, 2)),\\{}H := \operatorname{span}(\operatorname{ZMod}(2), \operatorname{range}(chi)), r := \operatorname{finrank}(\operatorname{ZMod}(2), H),\\{}beta: \operatorname{Basis}(B, \operatorname{ZMod}(2), H),\\{}(\forall g \in G, (\forall i \in I, chi(i)(\operatorname{mkQ}(2, g)) = 0) \iff (\forall j \in J, psi(j)(\operatorname{mkQ}(2, g)) = 0)) \Rightarrow\\{}\operatorname{IsLeast}(\{kappa \mid \exists S, S \subseteq \operatorname{range}(chi) \land \operatorname{span}(\operatorname{ZMod}(2), S) = H \land \operatorname{card}(S) = kappa\}, \operatorname{rank}(\operatorname{ZMod}(2), H)) \land r \leq \operatorname{card}(J) \land\\{}(\exists sigma: \operatorname{Fin}(r) \to \operatorname{Dual}(\operatorname{ZMod}(2), \operatorname{ModN}(G, 2)), (\forall k \in \operatorname{Fin}(r), sigma(k) \in \operatorname{range}(chi)) \land \operatorname{LinearIndependent}(\operatorname{ZMod}(2), sigma) \land\\{}\operatorname{span}(\operatorname{ZMod}(2), \operatorname{range}(sigma)) = H \land \forall g \in G, (\forall k \in \operatorname{Fin}(r), sigma(k)(\operatorname{mkQ}(2, g)) = 0) \iff (\forall i \in I, chi(i)(\operatorname{mkQ}(2, g)) = 0)) \land\\{}((\forall g \in G, (\forall j \in B, beta(j)(\operatorname{mkQ}(2, g)) = 0) \iff (\forall i \in I, chi(i)(\operatorname{mkQ}(2, g)) = 0)) \land \operatorname{card}(B) \leq \operatorname{card}(J)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/BinaryCharacterBasisMinimality.binary_character_basis_minimality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be a finite abelian group. Binary characters are represented additively as linear functionals on the canonical quotient of G by doubles, so evaluation remains on the original group through the canonical quotient map.

The character space H is constructed as the binary-field span of the given character family, and r is its finite dimension. The displayed same-kernel premise is pointwise on G, not an abstract replacement definition of sufficiency.

The minimum same-span cardinality is inherited from the frozen binary role theorem. Equality of actual joint kernels forces the competitor span to equal H, giving the lower bound r.

A linearly independent Fin(r)-indexed family is extracted from the original characters, spans H, and has their joint kernel. The last public clause quantifies over an arbitrary supplied basis of H and proves both kernel sufficiency and minimum cardinality.

## References

- Truth anchor: `D5/S3/Fourier/BinaryCharacterBasisMinimality.binary_character_basis_minimality`
- Dependency: [D5/S3/ConceptDynamics/LinearSufficiency/BinaryRoleMinimumCardinality](../ConceptDynamics/LinearSufficiency/BinaryRoleMinimumCardinality.md)
