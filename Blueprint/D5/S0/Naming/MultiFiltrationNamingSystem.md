# Multi-Filtration Naming System

## Abstract

A primary naming filtration remains finite after a secondary budget is imposed.

**Lemma 1.1 (Joint budget layers remain finite).**

$$\begin{gathered}\forall X: \operatorname{Type},\\{}[\operatorname{MeasureSpace}\left(X\right)],\\{}\forall M: \operatorname{MultiFiltrationNamingSystem}\left(X\right),\\{}\forall QK, QC: \mathbb{N},\\{}\operatorname{Finite}\left(\operatorname{jointLayer}\left(M, QK, QC\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/MultiFiltrationNamingSystem.joint_budget_layer_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The structure wraps the canonical NamingSystem as its primary field and adds one secondary height on exactly the same name carrier.

Every joint budget layer is a subset of the corresponding primary layer. Its finiteness therefore uses only the primary owner's finite-layer law and imposes no filtration law on the secondary height.

## References

- Truth anchor: `D5/S0/Naming/MultiFiltrationNamingSystem.joint_budget_layer_finite`
- Dependency: [D5/S0/Naming/NamingSystem](NamingSystem.md)
