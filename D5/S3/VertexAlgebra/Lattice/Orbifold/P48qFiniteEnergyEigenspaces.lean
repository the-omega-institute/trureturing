/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFiniteEnergyEigenspaces
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every P48q twisted energy eigenspace is finite-dimensional. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedStateEnergy
import D5.S3.VertexAlgebra.LatticeChargeCoercivity
import Mathlib.Data.Fin.Embedding
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
Finite-dimensional eigenspaces for the actual P48q twisted zero mode, as
required by the grading condition in Bakalov–Kac, Definition 2.2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFiniteEnergyEigenspaces

open LatticeGeneratingFieldLocality (Charge Index bilinear)
open LatticePositiveEnergy (Exponent chargeEnergy two_chargeEnergy chargeSublevel_finite
  oscillatorEnergy oscillatorLeFinite)
open P48qThirdTwistedField (Mode State frequency)
open P48qTwistedChargeAction (Momentum lattice)
open P48qTwistedStateEnergy (Occupation momentumWeight momentumWeight_nonneg
  occupationFrequency totalWeight totalLZero totalLZero_coeff)

noncomputable section

private theorem momentumWeight_eq_chargeEnergy (p : Momentum) :
    momentumWeight p = (chargeEnergy lattice p.1 : ℝ) / 9 := by
  have h : (2 : ℝ) * (chargeEnergy lattice p.1 : ℝ) = (bilinear lattice p.1 p.1 : ℝ) := by
    exact_mod_cast two_chargeEnergy lattice p.1
  rw [momentumWeight, ← h]
  ring

private def modeEmbedding : Mode ↪ Index lattice :=
  (Fin.castLEEmb (by decide : 16 ≤ 48)).prodMap (Function.Embedding.refl ℕ)

private theorem oscillatorEnergy_mapDomain (d : Occupation) :
    oscillatorEnergy (D := lattice) (d.mapDomain modeEmbedding) = occupationFrequency d := by
  rw [oscillatorEnergy, Finsupp.weight_apply]
  simp only [Nat.nsmul_eq_mul]
  calc
    _ = d.sum (fun j e => e * frequency j) :=
      Finsupp.sum_mapDomain_index (s := d) (f := modeEmbedding)
        (h := fun (j : Index lattice) (e : ℕ) => e * (j.2 + 1))
        (fun j => Nat.zero_mul (j.2 + 1))
        (fun j a b => Nat.add_mul a b (j.2 + 1))
    _ = occupationFrequency d := by simp only [occupationFrequency, Nat.mul_comm]

private theorem occupationSublevel_finite (N : ℕ) :
    Finite {d : Occupation // occupationFrequency d ≤ N} := by
  let : Finite {e : Exponent lattice // oscillatorEnergy (D := lattice) e ≤ N} :=
    oscillatorLeFinite lattice N
  let encode (d : {d : Occupation // occupationFrequency d ≤ N}) :
      {e : Exponent lattice // oscillatorEnergy (D := lattice) e ≤ N} :=
    ⟨d.1.mapDomain modeEmbedding, by
      rw [oscillatorEnergy_mapDomain]
      exact d.2⟩
  refine Finite.of_injective encode ?_
  intro d e h
  apply Subtype.ext
  exact Finsupp.mapDomain_injective modeEmbedding.injective (congrArg Subtype.val h)

/-- Every real joint weight sublevel contains finitely many monomial labels. -/
theorem totalWeight_sublevel_finite (B : ℝ) :
    Set.Finite {x : Momentum × Occupation | totalWeight x.1 x.2 ≤ B} := by
  obtain ⟨M, hM⟩ := exists_nat_gt (9 * B)
  obtain ⟨N, hN⟩ := exists_nat_gt (3 * B)
  let : Finite {p : Charge lattice // chargeEnergy lattice p ≤ (M : ℤ)} :=
    (chargeSublevel_finite lattice P48qGramPositivity.nebeGram_posDef M).to_subtype
  let : Finite {d : Occupation // occupationFrequency d ≤ N} :=
    occupationSublevel_finite N
  let encode (x : {x : Momentum × Occupation // totalWeight x.1 x.2 ≤ B}) :
      {p : Charge lattice // chargeEnergy lattice p ≤ (M : ℤ)} ×
        {d : Occupation // occupationFrequency d ≤ N} := by
    have h : totalWeight x.1.1 x.1.2 ≤ B := x.2
    unfold totalWeight at h
    have hp := momentumWeight_nonneg x.1.1
    have hd : 0 ≤ (occupationFrequency x.1.2 : ℝ) := Nat.cast_nonneg _
    have hcharge : (chargeEnergy lattice x.1.1.1 : ℝ) ≤ (M : ℝ) := by
      rw [momentumWeight_eq_chargeEnergy] at h
      linarith only [h, hd, hM]
    have hoccupation : (occupationFrequency x.1.2 : ℝ) ≤ (N : ℝ) := by
      linarith only [h, hp, hN]
    exact ⟨⟨x.1.1.1, by exact_mod_cast hcharge⟩, ⟨x.1.2, by exact_mod_cast hoccupation⟩⟩
  have hinj : Function.Injective encode := by
    intro x y h
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun z => z.1.1) h
    · exact congrArg (fun z => z.2.1) h
  let finiteSublevel : Finite {x : Momentum × Occupation // totalWeight x.1 x.2 ≤ B} :=
    Finite.of_injective encode hinj
  exact @Set.toFinite (Momentum × Occupation) {x | totalWeight x.1 x.2 ≤ B} finiteSublevel

/-- Each complex weight fiber lies in the joint sublevel at its real part. -/
theorem totalWeight_fiber_finite (a : ℂ) :
    Set.Finite {x : Momentum × Occupation | (totalWeight x.1 x.2 : ℂ) = a} := by
  refine (totalWeight_sublevel_finite a.re).subset ?_
  intro x hx
  change (totalWeight x.1 x.2 : ℂ) = a at hx
  have hreal : totalWeight x.1 x.2 = a.re := by
    simpa only [Complex.ofReal_re] using congrArg Complex.re hx
  exact hreal.le

private def stateCoeffEquiv : State ≃ₗ[ℂ] ((Momentum × Occupation) →₀ ℂ) :=
  (Finsupp.mapRange.linearEquiv (MvPolynomial.basisMonomials Mode ℂ).repr).trans
    (Finsupp.curryLinearEquiv ℂ).symm

private theorem stateCoeffEquiv_apply (v : State) (x : Momentum × Occupation) :
    stateCoeffEquiv v x = (v x.1).coeff x.2 := rfl

/-- The actual eigenspace has precisely the coefficients on its weight fiber. -/
def totalLZeroEigenspaceCoeffEquiv (a : ℂ) :
    totalLZero.eigenspace a ≃ₗ[ℂ]
      ({x : Momentum × Occupation // (totalWeight x.1 x.2 : ℂ) = a} →₀ ℂ) := by
  let S : Set (Momentum × Occupation) := {x | (totalWeight x.1 x.2 : ℂ) = a}
  have he : totalLZero.eigenspace a =
      (Finsupp.supported ℂ ℂ S).comap stateCoeffEquiv.toLinearMap := by
    ext v
    change v ∈ totalLZero.eigenspace a ↔ stateCoeffEquiv v ∈ Finsupp.supported ℂ ℂ S
    rw [Module.End.mem_eigenspace_iff, Finsupp.mem_supported']
    simp only [stateCoeffEquiv_apply]
    constructor
    · intro hv x hx
      have h := congrArg (fun w : State => (w x.1).coeff x.2) hv
      change (totalLZero v x.1).coeff x.2 = ((a • v) x.1).coeff x.2 at h
      rw [totalLZero_coeff, Finsupp.smul_apply, MvPolynomial.coeff_smul, smul_eq_mul] at h
      by_contra hn
      exact hx (mul_right_cancel₀ hn h)
    · intro hv
      apply Finsupp.ext
      intro p
      apply MvPolynomial.ext
      intro d
      change (totalLZero v p).coeff d = ((a • v) p).coeff d
      rw [totalLZero_coeff, Finsupp.smul_apply, MvPolynomial.coeff_smul, smul_eq_mul]
      by_cases h : (p, d) ∈ S
      · change (totalWeight p d : ℂ) = a at h
        rw [h]
      · have hz := hv (p, d) h
        change (v p).coeff d = 0 at hz
        simp only [hz, mul_zero]
  exact (LinearEquiv.ofEq _ _ he).trans
    ((LinearEquiv.ofSubmodule' stateCoeffEquiv (Finsupp.supported ℂ ℂ S)).trans
      (Finsupp.supportedEquivFinsupp S))

/-- Bakalov–Kac finite dimensionality for every eigenspace of the actual `totalLZero`. -/
theorem totalLZero_eigenspace_finiteDimensional (a : ℂ) :
    FiniteDimensional ℂ (totalLZero.eigenspace a) := by
  let finiteFiber : Finite {x : Momentum × Occupation // (totalWeight x.1 x.2 : ℂ) = a} :=
    (totalWeight_fiber_finite a).to_subtype
  exact @Module.Finite.of_basis ℂ (totalLZero.eigenspace a) _
    inferInstance inferInstance inferInstance finiteFiber
    (Module.Basis.ofRepr (totalLZeroEigenspaceCoeffEquiv a))

end

#print axioms totalWeight_sublevel_finite
#print axioms totalWeight_fiber_finite
#print axioms totalLZeroEigenspaceCoeffEquiv
#print axioms totalLZero_eigenspace_finiteDimensional

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFiniteEnergyEigenspaces
