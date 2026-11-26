import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.CommutantQuaternionCoordinates
import Reg.Support.DependentFamily

/-! Source-bound audit of quaternionic coordinates from a noncommutative commutant.

The audited observation is the left multiplication `q * Φ v` in the conclusion. The model used
for the rejected law is Euclidean four-space indexed by `ULift (Fin 4)`, identified with `ℍ` by
an orthonormal frame; right multiplications by unit quaternions act irreducibly, left
multiplications by unit quaternions commute with them, and left multiplications by `i` and `j`
do not commute, so the model satisfies every hypothesis of the theorem. -/

namespace Reg.D5.S3.Quantum.AURICOmega.CommutantQuaternionCoordinates

open _root_.D5.S3.Quantum.AURICOmega.CommutantQuaternionCoordinates
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped Quaternion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u

/-- Left multiplication by a unit quaternion, as a linear isometry of `ℍ`. -/
def lmul (q : unitary ℍ[ℝ]) : ℍ[ℝ] ≃ₗᵢ[ℝ] ℍ[ℝ] where
  toFun v := (q : ℍ[ℝ]) * v
  invFun v := star (q : ℍ[ℝ]) * v
  map_add' a b := mul_add _ _ _
  map_smul' c a := by simp
  left_inv v := by
    change star (q : ℍ[ℝ]) * ((q : ℍ[ℝ]) * v) = v
    rw [← mul_assoc, Unitary.star_mul_self_of_mem q.prop, one_mul]
  right_inv v := by
    change (q : ℍ[ℝ]) * (star (q : ℍ[ℝ]) * v) = v
    rw [← mul_assoc, Unitary.mul_star_self_of_mem q.prop, one_mul]
  norm_map' v := by
    change ‖(q : ℍ[ℝ]) * v‖ = ‖v‖
    rw [norm_mul, CStarRing.norm_coe_unitary, one_mul]

/-- Right multiplication by a unit quaternion, as a linear isometry of `ℍ`. -/
def rmul (p : unitary ℍ[ℝ]) : ℍ[ℝ] ≃ₗᵢ[ℝ] ℍ[ℝ] where
  toFun v := v * (p : ℍ[ℝ])
  invFun v := v * star (p : ℍ[ℝ])
  map_add' a b := add_mul _ _ _
  map_smul' c a := by simp
  left_inv v := by
    change v * (p : ℍ[ℝ]) * star (p : ℍ[ℝ]) = v
    rw [mul_assoc, Unitary.mul_star_self_of_mem p.prop, mul_one]
  right_inv v := by
    change v * star (p : ℍ[ℝ]) * (p : ℍ[ℝ]) = v
    rw [mul_assoc, Unitary.star_mul_self_of_mem p.prop, mul_one]
  norm_map' v := by
    change ‖v * (p : ℍ[ℝ])‖ = ‖v‖
    rw [norm_mul, CStarRing.norm_coe_unitary, mul_one]

/-- Euclidean four-space in universe `u`. -/
abbrev Space : Type u := EuclideanSpace ℝ (ULift.{u} (Fin 4))

/-- An orthonormal frame identifying `ℍ` with `Space`. -/
def frame : ℍ[ℝ] ≃ₗᵢ[ℝ] Space.{u} :=
  ((stdOrthonormalBasis ℝ ℍ[ℝ]).reindex
    ((finCongr Quaternion.finrank_eq_four).trans Equiv.ulift.symm)).repr

/-- A linear isometry of `ℍ`, read in the frame. -/
def conj (f : ℍ[ℝ] ≃ₗᵢ[ℝ] ℍ[ℝ]) : Space.{u} ≃ₗᵢ[ℝ] Space.{u} :=
  frame.symm.trans (f.trans frame)

theorem conj_apply (f : ℍ[ℝ] ≃ₗᵢ[ℝ] ℍ[ℝ]) (v : Space.{u}) :
    conj f v = frame (f (frame.symm v)) := rfl

theorem lmul_apply (q : unitary ℍ[ℝ]) (v : ℍ[ℝ]) : lmul q v = (q : ℍ[ℝ]) * v := rfl

theorem rmul_apply (p : unitary ℍ[ℝ]) (v : ℍ[ℝ]) : rmul p v = v * (p : ℍ[ℝ]) := rfl

theorem mul_apply (S T : Space.{u} ≃ₗᵢ[ℝ] Space.{u}) (v : Space.{u}) :
    (S * T) v = S (T v) := rfl

/-- Right multiplications by unit quaternions, read in the frame. -/
def rightSet : Set (Space.{u} ≃ₗᵢ[ℝ] Space.{u}) := Set.range fun p => conj (rmul p)

/-- Left multiplications by unit quaternions, read in the frame. -/
def leftSet : Set (Space.{u} ≃ₗᵢ[ℝ] Space.{u}) := Set.range fun q => conj (lmul q)

/-- The unit quaternion `i`. -/
def uI : unitary ℍ[ℝ] :=
  ⟨⟨0, 1, 0, 0⟩, Unitary.mem_iff.mpr ⟨by ext <;> simp, by ext <;> simp⟩⟩

/-- The unit quaternion `j`. -/
def uJ : unitary ℍ[ℝ] :=
  ⟨⟨0, 0, 1, 0⟩, Unitary.mem_iff.mpr ⟨by ext <;> simp, by ext <;> simp⟩⟩

theorem mem_unitary_of_norm (q : ℍ[ℝ]) (hq : ‖q‖ = 1) : q ∈ unitary ℍ[ℝ] := by
  have h : ((Quaternion.normSq q : ℝ) : ℍ[ℝ]) = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, hq, mul_one, Quaternion.coe_one]
  exact Unitary.mem_iff.mpr ⟨(Quaternion.star_mul_self q).trans h,
    (Quaternion.self_mul_star q).trans h⟩

theorem frame_one_ne_zero : frame.{u} 1 ≠ 0 := by
  intro h
  exact one_ne_zero (frame.{u}.map_eq_zero_iff.mp h)

theorem norm_frame_one : ‖frame.{u} 1‖ = 1 := by
  rw [LinearIsometryEquiv.norm_map, norm_one]

theorem model_finrank : Module.finrank ℝ Space.{u} ≤ 4 := by
  simp [Space, finrank_euclideanSpace]

theorem model_irreducible : ∀ X : Submodule ℝ Space.{u},
    (∀ T ∈ rightSet.{u}, ∀ x ∈ X, T x ∈ X) → X = ⊥ ∨ X = ⊤ := by
  intro X hX
  by_cases hb : X = ⊥
  · exact Or.inl hb
  right
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  rw [eq_top_iff]
  intro y _
  set a : ℍ[ℝ] := frame.symm x
  have ha : a ≠ 0 := fun h => hx0 (by rw [← frame.apply_symm_apply x]; simp only [a] at h; rw [h, map_zero])
  set w : ℍ[ℝ] := a⁻¹ * frame.symm y
  have hy : y = frame (a * w) := by
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul, LinearIsometryEquiv.apply_symm_apply]
  by_cases hw : w = 0
  · rw [hy, hw, mul_zero, map_zero]
    exact X.zero_mem
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  set p : ℍ[ℝ] := ‖w‖⁻¹ • w
  have hp : ‖p‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  have hmem : frame (a * p) ∈ X := by
    have := hX (conj (rmul ⟨p, mem_unitary_of_norm p hp⟩)) ⟨_, rfl⟩ x hx
    rwa [conj_apply] at this
  have : y = ‖w‖ • frame (a * p) := by
    rw [hy, ← map_smul, mul_smul_comm, smul_inv_smul₀ hn]
  rw [this]
  exact X.smul_mem _ hmem

theorem model_commute : ∀ S ∈ rightSet.{u}, ∀ T ∈ leftSet.{u}, S * T = T * S := by
  rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
  refine LinearIsometryEquiv.ext fun v => ?_
  rw [mul_apply, mul_apply, conj_apply, conj_apply, conj_apply, conj_apply, rmul_apply,
    lmul_apply, LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply,
    rmul_apply, lmul_apply, mul_assoc]

theorem model_noncommutative : ∃ S ∈ leftSet.{u}, ∃ T ∈ leftSet.{u}, S * T ≠ T * S := by
  refine ⟨conj (lmul uI), ⟨uI, rfl⟩, conj (lmul uJ), ⟨uJ, rfl⟩, fun h => ?_⟩
  have h1 := DFunLike.congr_fun h (frame.{u} 1)
  rw [mul_apply, mul_apply, conj_apply, conj_apply, conj_apply, conj_apply,
    LinearIsometryEquiv.symm_apply_apply, lmul_apply, lmul_apply,
    LinearIsometryEquiv.symm_apply_apply, lmul_apply, lmul_apply, mul_one, mul_one] at h1
  have h2 := congrArg (fun z : Space.{u} => (frame.{u}.symm z).imK) h1
  simp only [LinearIsometryEquiv.symm_apply_apply] at h2
  simp [uI, uJ] at h2
  norm_num at h2

/-! The left multiplication `q * Φ v` in the conclusion, against the coordinates `Φ` and `q`. -/
namespace LeftAction

abbrev signature : Signature where
  Params := Σ E : Type u, Σ _ : NormedAddCommGroup E, Σ _ : InnerProductSpace ℝ E,
    Σ _ : E ≃ₗᵢ[ℝ] ℍ[ℝ], ℍ[ℝ]
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℍ[ℝ]
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p s => p.2.2.2.2 * p.2.2.2.1 s) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the complete space, isometry sets, hypotheses and both conjuncts of
`exists_quaternion_coordinates`. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law rd := ∀ {E : Type u} [i₁ : NormedAddCommGroup E] [i₂ : InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (𝒰 𝒱 : Set (E ≃ₗᵢ[ℝ] E)),
    Module.finrank ℝ E ≤ 4 →
    (∀ X : Submodule ℝ E, (∀ T ∈ 𝒰, ∀ x ∈ X, T x ∈ X) → X = ⊥ ∨ X = ⊤) →
    (∀ S ∈ 𝒰, ∀ T ∈ 𝒱, S * T = T * S) →
    (∃ S ∈ 𝒱, ∃ T ∈ 𝒱, S * T ≠ T * S) →
    Module.finrank ℝ E = 4 ∧
      ∀ e : E, ‖e‖ = 1 →
        ∃ Φ : E ≃ₗᵢ[ℝ] ℍ[ℝ], Φ e = 1 ∧
          (∀ T ∈ 𝒱, ∃ q : ℍ[ℝ], ‖q‖ = 1 ∧ ∀ v : E, Φ (T v) = rd.readout () ⟨E, i₁, i₂, Φ, q⟩ v) ∧
          (∀ S ∈ 𝒰, ∃ p : ℍ[ℝ], ‖p‖ = 1 ∧ ∀ v : E, Φ (S v) = Φ v * p)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨-, h2⟩ := h rightSet.{u} leftSet.{u} model_finrank model_irreducible model_commute
    model_noncommutative
  obtain ⟨Φ, -, hV, -⟩ := h2 (frame 1) norm_frame_one
  obtain ⟨q, -, hq⟩ := hV (conj (lmul 1)) ⟨1, rfl⟩
  have h0 : Φ (conj (lmul 1) (frame 1)) = 0 := hq (frame 1)
  exact frame_one_ne_zero ((conj (lmul 1)).map_eq_zero_iff.mp (Φ.map_eq_zero_iff.mp h0))

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨⟨Space.{u}, inferInstance, inferInstance, frame.{u}.symm, 1⟩, 0, frame.{u} 1, ?_⟩
  change (1 : ℍ[ℝ]) * frame.{u}.symm (0 : Space.{u}) ≠ 1 * frame.{u}.symm (frame.{u} 1)
  rw [map_zero, LinearIsometryEquiv.symm_apply_apply, mul_zero, mul_one]
  exact zero_ne_one

def source_registration :
    Registration arena.{u} (type_of% @exists_quaternion_coordinates.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_quaternion_coordinates.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end LeftAction

def exists_quaternion_coordinates_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_quaternion_coordinates.{u}) (Realization LeftAction.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.CommutantQuaternionCoordinates.exists_quaternion_coordinates_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.CommutantQuaternionCoordinates.LeftAction.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨LeftAction.arena.{u}⟩
  objectArena := .source ⟨LeftAction.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source LeftAction.arena.{u} ⟨LeftAction.source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize LeftAction.signature.{u}
    (fun _ p s => p.2.2.2.2 * p.2.2.2.1 s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.CommutantQuaternionCoordinates
    definition := none
    coordinates := #[0, 12, 15]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "body", "arg", "body", "arg", "fn", "arg", "body", "body", "arg", "body",
        "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Quantum.AURICOmega.CommutantQuaternionCoordinates
