# Finite-stage Fourier separation of profinite integers

## Abstract

Finite additive characters separate compatible profinite residue families.

ProfiniteIntegers is the compatible family of residues in ZMod (m+1) for all natural stages m. At each stage, coordinateCharacter m k is the additive character x ↦ toAddCircle(k · x(m)); it is continuous because each finite residue space is discrete and coordinate evaluation is continuous. The use of m+1 indexes all positive finite moduli, including ZMod 1 at m=0. The displayed sum is over the complete finite residue group and uses the standard primitive additive character.

**Definition 1.1 (Continuous finite-stage character).**

$$\left(\forall m \in Nat,\; \forall k \in ZMod\left(succ\left(m\right)\right),\; \forall x \in ProfiniteIntegers,\; ContinuousAddChar\left(coordinateCharacter\left(m, k, x\right)\right)\right) \land \left(\left(\forall m \in Nat,\; finiteCorrelation\left(m, x, y\right) = if\left(coordinate\left(m, x\right) = coordinate\left(m, y\right), card\left(ZMod\left(succ\left(m\right)\right)\right), zero\left(\right)\right)\right) \land \left(\left(x = y \Leftrightarrow \left(\forall m \in Nat,\; finiteCorrelation\left(m, x, y\right) \ne zero\left(\right)\right)\right) \land \left(x \ne y \Rightarrow \left(\exists m \in Nat,\; \exists k \in ZMod\left(succ\left(m\right)\right),\; coordinateCharacter\left(m, k, x\right) \ne coordinateCharacter\left(m, k, y\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Topology/InverseLimit/ProfiniteStageFourierSeparation.coordinateCharacter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

coordinateCharacter packages one finite residue character as a continuous additive homomorphism from the profinite inverse-limit space to UnitAddCircle. The proof supplies the additive laws through ZMod.toAddCircle and continuity through the discrete finite coordinate followed by the product-coordinate projection.

**Theorem 1.2 (Complete finite Fourier correlation).**

$$\left(\forall m \in Nat,\; \forall k \in ZMod\left(succ\left(m\right)\right),\; \forall x \in ProfiniteIntegers,\; ContinuousAddChar\left(coordinateCharacter\left(m, k, x\right)\right)\right) \land \left(\left(\forall m \in Nat,\; finiteCorrelation\left(m, x, y\right) = if\left(coordinate\left(m, x\right) = coordinate\left(m, y\right), card\left(ZMod\left(succ\left(m\right)\right)\right), zero\left(\right)\right)\right) \land \left(\left(x = y \Leftrightarrow \left(\forall m \in Nat,\; finiteCorrelation\left(m, x, y\right) \ne zero\left(\right)\right)\right) \land \left(x \ne y \Rightarrow \left(\exists m \in Nat,\; \exists k \in ZMod\left(succ\left(m\right)\right),\; coordinateCharacter\left(m, k, x\right) \ne coordinateCharacter\left(m, k, y\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/ProfiniteStageFourierSeparation.stage_correlation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a fixed stage m, the complete standard-character sum of the difference x(m)-y(m) is the cardinality m+1 when the two residues agree and is zero otherwise. This is Mathlib's AddChar.sum_mulShift specialized to ZMod (m+1) and its primitive standard character.

**Theorem 1.3 (A separating stage has zero correlation).**

$$\left(\forall m \in Nat,\; \forall k \in ZMod\left(succ\left(m\right)\right),\; \forall x \in ProfiniteIntegers,\; ContinuousAddChar\left(coordinateCharacter\left(m, k, x\right)\right)\right) \land \left(\left(\forall m \in Nat,\; finiteCorrelation\left(m, x, y\right) = if\left(coordinate\left(m, x\right) = coordinate\left(m, y\right), card\left(ZMod\left(succ\left(m\right)\right)\right), zero\left(\right)\right)\right) \land \left(\left(x = y \Leftrightarrow \left(\forall m \in Nat,\; finiteCorrelation\left(m, x, y\right) \ne zero\left(\right)\right)\right) \land \left(x \ne y \Rightarrow \left(\exists m \in Nat,\; \exists k \in ZMod\left(succ\left(m\right)\right),\; coordinateCharacter\left(m, k, x\right) \ne coordinateCharacter\left(m, k, y\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/ProfiniteStageFourierSeparation.profinite_fourier_separates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two compatible residue families differ, their underlying functions differ at some finite natural stage. The stage-correlation formula then gives a zero complete Fourier correlation at that stage.

**Theorem 1.4 (All-stage nonzero correlations reflect equality).**

$$\left(\forall m \in Nat,\; \forall k \in ZMod\left(succ\left(m\right)\right),\; \forall x \in ProfiniteIntegers,\; ContinuousAddChar\left(coordinateCharacter\left(m, k, x\right)\right)\right) \land \left(\left(\forall m \in Nat,\; finiteCorrelation\left(m, x, y\right) = if\left(coordinate\left(m, x\right) = coordinate\left(m, y\right), card\left(ZMod\left(succ\left(m\right)\right)\right), zero\left(\right)\right)\right) \land \left(\left(x = y \Leftrightarrow \left(\forall m \in Nat,\; finiteCorrelation\left(m, x, y\right) \ne zero\left(\right)\right)\right) \land \left(x \ne y \Rightarrow \left(\exists m \in Nat,\; \exists k \in ZMod\left(succ\left(m\right)\right),\; coordinateCharacter\left(m, k, x\right) \ne coordinateCharacter\left(m, k, y\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/ProfiniteStageFourierSeparation.profinite_fourier_reflects` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality implies every stage difference is zero, so every complete correlation is the nonzero cardinality m+1. Conversely, a distinct pair has the zero correlation supplied by profinite_fourier_separates, contradicting the all-stage nonzero hypothesis.

**Theorem 1.5 (Continuous characters separate points).**

$$\left(\forall m \in Nat,\; \forall k \in ZMod\left(succ\left(m\right)\right),\; \forall x \in ProfiniteIntegers,\; ContinuousAddChar\left(coordinateCharacter\left(m, k, x\right)\right)\right) \land \left(\left(\forall m \in Nat,\; finiteCorrelation\left(m, x, y\right) = if\left(coordinate\left(m, x\right) = coordinate\left(m, y\right), card\left(ZMod\left(succ\left(m\right)\right)\right), zero\left(\right)\right)\right) \land \left(\left(x = y \Leftrightarrow \left(\forall m \in Nat,\; finiteCorrelation\left(m, x, y\right) \ne zero\left(\right)\right)\right) \land \left(x \ne y \Rightarrow \left(\exists m \in Nat,\; \exists k \in ZMod\left(succ\left(m\right)\right),\; coordinateCharacter\left(m, k, x\right) \ne coordinateCharacter\left(m, k, y\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/ProfiniteStageFourierSeparation.continuous_character_separates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A differing finite coordinate is detected already by the coefficient k=1 character. Injectivity of ZMod.toAddCircle turns equality of the character values into equality of the finite residues, yielding a contradiction.

## References

- Truth anchor: `D5/S3/Topology/InverseLimit/ProfiniteStageFourierSeparation.continuous_character_separates`
- Truth anchor: `D5/S3/Topology/InverseLimit/ProfiniteStageFourierSeparation.coordinateCharacter`
- Truth anchor: `D5/S3/Topology/InverseLimit/ProfiniteStageFourierSeparation.profinite_fourier_reflects`
- Truth anchor: `D5/S3/Topology/InverseLimit/ProfiniteStageFourierSeparation.profinite_fourier_separates`
- Truth anchor: `D5/S3/Topology/InverseLimit/ProfiniteStageFourierSeparation.stage_correlation`
- Dependency: [D5/S1/Dynamics/ProfiniteIntegers](../../../S1/Dynamics/ProfiniteIntegers.md)
