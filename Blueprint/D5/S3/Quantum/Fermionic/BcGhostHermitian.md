# Original bc Hermitian and relative ghost metric

## Abstract

Native signed Hermitian and literal c0-relative pairings on the original finite-support bc occupation Fock space.

**Theorem 1.1 (Finite-support signed coefficient expansion).**

$$\operatorname{Hg}\left(x, y\right) = \operatorname{FinsuppSum}\left(x, starCoeffTimesSignedRow\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hg_signed_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ambient pairing is the actual finite Finsupp sum over the support of x, with the derived epsilon sign and involutive partner.

**Theorem 1.2 (Ordinary Hermitian symmetry).**

$$(\forall x: Fock, (\forall y: Fock, \operatorname{Hg}\left(x, y\right) = \operatorname{star}\left(\operatorname{Hg}\left(y, x\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hg_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Hermitian symmetry is proved from the vacuum base, creator and annihilator adjoints, and the finite occupation induction.

**Theorem 1.3 (Zero left radical).**

$$(\forall x: Fock, \operatorname{forallZeroRight}\left(x\right) \implies x = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hg_left_radical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The involutive partner row and nonzero derived epsilon force every coefficient of a left-radical vector to vanish.

**Theorem 1.4 (Zero right radical).**

$$(\forall y: Fock, \operatorname{forallZeroLeft}\left(y\right) \implies y = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hg_right_radical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same finite-support coefficient argument proves the right radical is zero.

**Theorem 1.5 (Literal reversed dagger word).**

$$(\forall S: FinsetNatFock, (\forall y: FinsetNatFock, \operatorname{Hg}\left(\operatorname{ket}\left(S\right), y\right) = \operatorname{rho}\left(\operatorname{daggerWord}\left(S, y\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hg_literal_dagger` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The row is represented by the literal reverse-ordered dagger word on the original occupation ket.

**Theorem 1.6 (All-integer b adjoint).**

$$(\forall m: Int, (\forall x: Fock, (\forall y: Fock, \operatorname{Hg}\left(\operatorname{b}\left(m, x\right), y\right) = \operatorname{Hg}\left(x, \operatorname{b}\left(\operatorname{neg}\left(m\right), y\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hg_b` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both b cuts and every exceptional and bulk integer mode are covered by one derived theorem.

**Theorem 1.7 (All-integer c adjoint).**

$$(\forall n: Int, (\forall x: Fock, (\forall y: Fock, \operatorname{Hg}\left(\operatorname{c}\left(n, x\right), y\right) = \operatorname{Hg}\left(x, \operatorname{c}\left(\operatorname{neg}\left(n\right), y\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hg_c` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original c vacuum cut and all integer branches use the same native signed pairing.

**Theorem 1.8 (Partner charge sum).**

$$(\forall S: FinsetNat, \operatorname{add}\left(\operatorname{charge}\left(S\right), \operatorname{charge}\left(\operatorname{partner}\left(S\right)\right)\right) = 3)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostHermitian.charge_partner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact original signed charge is contragredient under the derived partner involution.

**Theorem 1.9 (Ambient charge selection).**

$$ambientChargeSelection$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hg_charge_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Selection is derived from the coefficient support and the exact partner charge identity.

**Theorem 1.10 (Literal c0-relative Hermitian symmetry).**

$$(\forall x: Relative, (\forall y: Relative, \operatorname{Hrel}\left(x, y\right) = \operatorname{star}\left(\operatorname{Hrel}\left(y, x\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hrel_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The relative form is Hg(x,c0 y) on the actual kernel of b0; its symmetry follows from the derived c0 adjoint.

**Theorem 1.11 (Relative finite-support signed expansion).**

$$\operatorname{Hrel}\left(x, y\right) = \operatorname{FinsuppSum}\left(x, relativeSignedCoefficient\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hrel_signed_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The c0 insertion produces the exact relative partner and lowerCount sign on every arbitrary finite support.

**Theorem 1.12 (Zero relative left radical).**

$$(\forall x: Relative, \operatorname{forallZeroRightRelative}\left(x\right) \implies x = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hrel_left_radical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The relative pairing has no left radical on the actual ker(b0) carrier.

**Theorem 1.13 (Zero relative right radical).**

$$(\forall y: Relative, \operatorname{forallZeroLeftRelative}\left(y\right) \implies y = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hrel_right_radical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The relative partner involution and nonzero relative epsilon give the right radical proof.

**Theorem 1.14 (Relative partner charge sum).**

$$(\forall S: FinsetNat, \operatorname{notMem}\left(3, S\right) \implies \operatorname{add}\left(\operatorname{charge}\left(S\right), \operatorname{charge}\left(\operatorname{relativePartner}\left(S\right)\right)\right) = 2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostHermitian.charge_relativePartner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Removing the forced c0 site changes the exact charge selection from three to two.

**Theorem 1.15 (Relative charge selection).**

$$relativeChargeSelection$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hrel_charge_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The relative selection rule is obtained by the actual c0 charge shift and the ambient theorem.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hg_b`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hg_c`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hg_charge_selection`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hg_hermitian`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hg_left_radical`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hg_literal_dagger`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hg_right_radical`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hg_signed_coefficient`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hrel_charge_selection`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hrel_hermitian`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hrel_left_radical`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hrel_right_radical`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostHermitian.Hrel_signed_coefficient`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostHermitian.charge_partner`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostHermitian.charge_relativePartner`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostCharge](BcGhostCharge.md)
