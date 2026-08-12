# The Exact Heat-Entropy-Information Identity

## Abstract

Reservoir and unitary entropy balances determine the exact heat-entropy-information identity.

**Theorem 1.1 (The two entropy balances imply the exact identity).**

$$\begin{gathered}\forall beta, heat, systemEntropyChange, reservoirEntropyChange, mutualInformation, reservoirDivergence \in \mathbb{R},\\beta \cdot heat = reservoirEntropyChange + reservoirDivergence \Rightarrow\\mutualInformation = systemEntropyChange + reservoirEntropyChange \Rightarrow\\beta \cdot heat = -systemEntropyChange + mutualInformation + reservoirDivergence.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/DivergenceSupport/LandauerIdentity.landauer_identity_from_balances` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reservoir balance expresses inverse temperature times released heat as the reservoir entropy change plus its divergence remainder. The unitary entropy balance expresses final mutual information as the sum of the system and reservoir entropy changes.

Eliminating the shared reservoir entropy change gives the displayed exact identity. No sign assumption is used and no remainder is discarded. The formal module also checks concrete witnesses showing that both balance hypotheses are satisfiable and that each is necessary for this derivation.

## References

- Truth anchor: `D5/S3/DivergenceSupport/LandauerIdentity.landauer_identity_from_balances`
