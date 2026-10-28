/- GID: D5/S3/VertexAlgebra/HalfFock/ActualFieldIrreducible
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/ActualFieldIrreducible
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Production corrected-field coefficients act irreducibly on the actual tensor. -/

/- proof_shape: correctedField_irreducible: content
admission_basis: escape-witness
escape_witness: Coefficient stability is transported to the actual ground intersection,
including every quotient representative through its central sign; irreducible ground
stability and actual negative-current polynomial induction then fill the tensor module.
Literature status: classical twisted lattice module irreducibility; no novelty claim.
-/
import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.ActualTensorGroundIntersection
import D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds
import D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation

/-! Extraction of ground stability and oscillator generation from raw field coefficients. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped TensorProduct

namespace D5.S3.VertexAlgebra.HalfFock.ActualFieldIrreducible
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockChargedCoefficients LatticeAllStateField
open LatticeTwistedGroundRealization LatticeTwistedGroundRealization.SignQuotient
open MvPolynomial

open private current_coeff from D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds
open private creation_zero from D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients

private theorem currents_mem (D : LatticeData) (hu : IsUnit D.G.det)
    (S : Submodule ℂ (ActualTensor D hu))
    (stable : ∀ (source : Carrier D) (e : ℤ) (x : ActualTensor D hu),
      x ∈ S → (correctedField D hu source).coeff e x ∈ S)
    (i : Fin D.rank) (k : ℤ) (x : ActualTensor D hu) (hx : x ∈ S) :
    LatticeHalfFock.tensorCurrent D (ActualGround D hu) i k x ∈ S := by
  rw [← current_coeff D hu i k x]
  exact stable _ _ _ hx

private def groundIntersection (D : LatticeData) (hu : IsUnit D.G.det)
    (S : Submodule ℂ (ActualTensor D hu)) : Submodule ℂ (ActualGround D hu) :=
  S.comap (TensorProduct.mk ℂ (Oscillator D) (ActualGround D hu) 1)

private theorem groundAction_mem (D : LatticeData) (hu : IsUnit D.G.det)
    (S : Submodule ℂ (ActualTensor D hu))
    (stable : ∀ (source : Carrier D) (e : ℤ) (x : ActualTensor D hu),
      x ∈ S → (correctedField D hu source).coeff e x ∈ S)
    (charge : Charge D) (g : ActualGround D hu)
    (hg : g ∈ groundIntersection D hu S) :
    groundAction D hu charge g ∈ groundIntersection D hu S := by
  have member := stable (Finsupp.single charge 1) (-chargeNorm D charge)
    ((1 : Oscillator D) ⊗ₜ[ℂ] g) hg
  rw [corrected_singleton_coeff_charged] at member
  change chargedCoefficient D hu charge (-chargeNorm D charge)
    ((1 : Oscillator D) ⊗ₜ[ℂ] g) ∈ S at member
  rw [charged_vacuum_coefficient, neg_add_cancel, creation_zero] at member
  have hn : chargeScalar D charge ≠ 0 := zpow_ne_zero _ (by norm_num)
  have scaled := S.smul_mem (chargeScalar D charge)⁻¹ member
  change ((1 : Oscillator D) ⊗ₜ[ℂ] groundAction D hu charge g) ∈ S
  simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using scaled

private def groundSubrepresentation (D : LatticeData) (hu : IsUnit D.G.det)
    (S : Submodule ℂ (ActualTensor D hu))
    (stable : ∀ (source : Carrier D) (e : ℤ) (x : ActualTensor D hu),
      x ∈ S → (correctedField D hu source).coeff e x ∈ S) :
    Subrepresentation (groundRepresentation D hu) where
  toSubmodule := groundIntersection D hu S
  apply_mem_toSubmodule element g hg := by
    induction element using Quotient.inductionOn with
    | h representative =>
      obtain ⟨sign, charge⟩ := representative
      have decompose : (⟨sign, charge⟩ : Extension D) =
          (⟨sign, 0⟩ : Extension D) * ⟨0, charge⟩ := by
        apply SignExtension.ext <;> simp [HMul.hMul, Mul.mul]
      change groundRepresentation D hu
        ((QuotientGroup.mk' (K D)) (⟨sign, charge⟩ : Extension D)) g ∈
          groundIntersection D hu S
      rw [decompose, map_mul, map_mul, Module.End.mul_apply]
      have hc := groundAction_mem D hu S stable charge g hg
      change groundRepresentation D hu (QuotientGroup.mk (⟨sign, 0⟩ : Extension D))
        (groundAction D hu charge g) ∈ groundIntersection D hu S
      have signs : sign = 0 ∨ sign = 1 := by fin_cases sign <;> simp
      rcases signs with hzero | hone
      · rw [hzero]
        change groundRepresentation D hu (QuotientGroup.mk' (K D) 1)
          (groundAction D hu charge g) ∈ groundIntersection D hu S
        simpa only [map_one, Module.End.one_apply] using hc
      · rw [hone]
        have central : groundRepresentation D hu
            (QuotientGroup.mk (⟨1, 0⟩ : Extension D)) =
              -(1 : Module.End ℂ (ActualGround D hu)) :=
          (Classical.choose_spec
            (Classical.choose_spec (actual_twisted_ground_representation D hu))).2.2.1
        simpa only [central, LinearMap.neg_apply, Module.End.one_apply] using
          (groundIntersection D hu S).neg_mem hc

private theorem all_ground_mem (D : LatticeData) (hu : IsUnit D.G.det)
    (S : Submodule ℂ (ActualTensor D hu)) (hS : S ≠ ⊥)
    (stable : ∀ (source : Carrier D) (e : ℤ) (x : ActualTensor D hu),
      x ∈ S → (correctedField D hu source).coeff e x ∈ S)
    (g : ActualGround D hu) : ((1 : Oscillator D) ⊗ₜ[ℂ] g) ∈ S := by
  obtain ⟨v, hv, hmember⟩ :=
    ActualTensorGroundIntersection.nonzero_current_stable_submodule_meets_ground D hu S hS
      (fun i k x hx => currents_mem D hu S stable i (k : ℤ) x hx)
  let : (groundRepresentation D hu).IsIrreducible :=
    (Classical.choose_spec
      (Classical.choose_spec (actual_twisted_ground_representation D hu))).2.1
  rcases eq_bot_or_eq_top (groundSubrepresentation D hu S stable) with bottom | top
  · have member : v ∈ groundSubrepresentation D hu S stable := hmember
    rw [bottom] at member
    exact False.elim (hv member)
  · have member : g ∈ groundSubrepresentation D hu S stable := by rw [top]; trivial
    exact member

/-- The complete actual tensor module has no proper nonzero submodule stable
under every integer raw coefficient of every production corrected-field source. -/
theorem correctedField_irreducible (D : LatticeData) (hu : IsUnit D.G.det)
    (S : Submodule ℂ (ActualTensor D hu))
    (stable : ∀ (source : Carrier D) (e : ℤ) (x : ActualTensor D hu),
      x ∈ S → (correctedField D hu source).coeff e x ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  classical
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  have ground := all_ground_mem D hu S hS stable
  have polynomial (p : Oscillator D) (g : ActualGround D hu) : p ⊗ₜ[ℂ] g ∈ S := by
    induction p using MvPolynomial.induction_on with
    | C c =>
      have constant : (C c : Oscillator D) ⊗ₜ[ℂ] g =
          c • ((1 : Oscillator D) ⊗ₜ[ℂ] g) := by
        rw [TensorProduct.smul_tmul', MvPolynomial.smul_eq_C_mul, mul_one]
      rw [constant]
      exact S.smul_mem c (ground g)
    | add p q hp hq => simpa only [TensorProduct.add_tmul] using S.add_mem hp hq
    | mul_X p index hp =>
      have hm := currents_mem D hu S stable index.1 (-(index.2 : ℤ) - 1)
        (p ⊗ₜ[ℂ] g) hp
      simpa only [LatticeHalfFock.tensorCurrent, LatticeHalfFock.tensorEnd,
        TensorProduct.map_tmul, LinearMap.id_apply, LatticeHalfFock.current_negative,
        LinearMap.mulLeft_apply, mul_comm] using hm
  apply top_unique
  intro x hx
  clear hx
  induction x using TensorProduct.inductionOn with
  | tmul p g => exact polynomial p g
  | add x y hx hy => exact S.add_mem hx hy

end D5.S3.VertexAlgebra.HalfFock.ActualFieldIrreducible
