# No Invisible Register

## Abstract

Total-code-preserving transformations cannot hide object changes.

**Theorem 1.1 (Preserving the total code preserves the object).**

$$\left(\forall x3 \in \left(\forall x3 \in \mathrm{TotalCode},\; \mathrm{TotalCode}\right),\; \left(\forall x4 \in \mathrm{TotalCode},\; \mathrm{TotalCodedata}\left(\mathit{x3}\left(\mathit{x4}\right)\right) = \mathrm{TotalCodedata}\left(\mathit{x4}\right)\right) \Rightarrow \left(\left(\forall x5 \in \mathrm{TotalCode},\; \mathrm{TotalCoderules}\left(\mathit{x3}\left(\mathit{x5}\right)\right) = \mathrm{TotalCoderules}\left(\mathit{x5}\right)\right) \Rightarrow \left(\left(\forall x6 \in \mathrm{TotalCode},\; \mathrm{TotalCodeledger}\left(\mathit{x3}\left(\mathit{x6}\right)\right) = \mathrm{TotalCodeledger}\left(\mathit{x6}\right)\right) \Rightarrow \left(\forall x7 \in \mathrm{TotalCode},\; \mathit{x3}\left(\mathit{x7}\right) = \mathit{x7}\right)\right)\right)\right) \land \left(\forall x3 \in \left(\forall x3 \in \mathrm{TotalCode},\; \mathrm{TotalCode}\right),\; \forall x4 \in \mathrm{TotalCode},\; \mathit{x3}\left(\mathit{x4}\right) \ne \mathit{x4} \Rightarrow \left(\mathrm{TotalCodedata}\left(\mathit{x3}\left(\mathit{x4}\right)\right) \ne \mathrm{TotalCodedata}\left(\mathit{x4}\right) \lor \left(\mathrm{TotalCoderules}\left(\mathit{x3}\left(\mathit{x4}\right)\right) \ne \mathrm{TotalCoderules}\left(\mathit{x4}\right) \lor \mathrm{TotalCodeledger}\left(\mathit{x3}\left(\mathit{x4}\right)\right) \ne \mathrm{TotalCodeledger}\left(\mathit{x4}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Conventions/TotalCode.no_hidden_register` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The semantic kernel-identity criterion is represented here by Lean structure equality, not claimed as a proof of an ontological identity criterion. Extensionality proves both the preservation clause and its componentwise dual. This is the C3a identity pillar announced for use in 23.4.
