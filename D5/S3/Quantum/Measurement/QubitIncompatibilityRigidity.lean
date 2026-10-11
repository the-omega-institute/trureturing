/- GID: D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/QubitIncompatibilityRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Restricted-state compatibility determines incompatible unbiased qubit pairs. -/

import D5.S3.Quantum.FiniteDimensional
noncomputable section
open D5.S3.Quantum.FiniteDimensional
open scoped ComplexOrder
namespace D5.S3.Quantum.ToriiTakakuraImamuraRigidity
abbrev V := EuclideanSpace ℝ (Fin 3)
abbrev Density := {ρ : QubitMatrix // ρ.PosSemidef ∧ Matrix.trace ρ = 1}
def pauliY : QubitMatrix := !![0, -Complex.I; Complex.I, 0]
def pauli (v : V) : QubitMatrix := (v 0 : ℂ) • qubitX + (v 1 : ℂ) • pauliY + (v 2 : ℂ) • qubitZ
def effect (v : V) (s : Fin 2) : QubitMatrix :=
  (1 / 2 : ℂ) • ((1 : QubitMatrix) + (if s = 0 then (1 : ℂ) else -1) • pauli v)
def IsPOVM (G : Fin 2 × Fin 2 → QubitMatrix) : Prop :=
  (∀ q, (G q).PosSemidef) ∧ (∑ s : Fin 2, ∑ t : Fin 2, G (s, t)) = 1
def marginal (G : Fin 2 × Fin 2 → QubitMatrix) (i s : Fin 2) : QubitMatrix :=
  if i = 0 then ∑ t : Fin 2, G (s, t) else ∑ t : Fin 2, G (t, s)
def SCompatible (S : Set Density) (a : Fin 2 → V) : Prop :=
  ∃ G : Fin 2 × Fin 2 → QubitMatrix, IsPOVM G ∧ ∀ ρ ∈ S, ∀ i s : Fin 2,
    bornProbability ρ.1 (marginal G i s) = bornProbability ρ.1 (effect (a i) s)
def Incompatible (a : Fin 2 → V) : Prop := ¬ SCompatible Set.univ a
def SignedPermutation (a b : Fin 2 → V) : Prop :=
  ∃ (π : Equiv.Perm (Fin 2)) (ε : Fin 2 → ℝ),
    (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∀ i, b i = ε i • a (π i)
def claim : Prop :=
  ∀ a b : Fin 2 → V,
    (∀ i, ‖a i‖ ≤ 1) →
    (∀ i, ‖b i‖ ≤ 1) →
    Incompatible a →
    Incompatible b →
    ((∀ S : Set Density, SCompatible S a ↔ SCompatible S b) ↔
      SignedPermutation a b)

end D5.S3.Quantum.ToriiTakakuraImamuraRigidity
