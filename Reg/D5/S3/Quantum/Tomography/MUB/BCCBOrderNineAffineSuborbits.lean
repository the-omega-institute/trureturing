import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Tomography.MUB.BCCBOrderNineAffineSuborbits
import Reg.Support.DependentFamily

/-! Source-bound audit of the parameter comparison detecting a nonconstant affine suborbit. -/

namespace Reg.D5.S3.Quantum.Tomography.MUB.BCCBOrderNineAffineSuborbits

open _root_.D5.S3.Quantum.Tomography.MUB.BCCBOrderNineAffineSuborbits
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

local notation "omega" => _root_.D5.S3.Observer.WindowRegister.windowRoot 3

/-- Observe the parameter tuple at the first point of the nonconstancy comparison. -/
abbrev signature : Signature where
  Params := Σ p : ℕ, Σ _x : (Fin p → ℝ) → ℂ, Σ _y : (Fin p → ℝ) → ℂ,
    Σ _u : (Fin p → ℝ) → ℂ, (Fin p → ℝ) → ℂ
  State q := Fin q.1 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 4 → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ q t => params q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 t)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Preserve every hypothesis and both classification families. -/
abbrev arena : Arena where
  signature := signature
  Law r :=
    ∀ (p : ℕ) (U : Set (Fin p → ℝ)), IsOpen U → U.Nonempty →
      ∀ x y u w : (Fin p → ℝ) → ℂ,
        (∀ t ∈ U, ‖x t‖ = 1 ∧ ‖y t‖ = 1 ∧ ‖u t‖ = 1 ∧ ‖w t‖ = 1 ∧
          x t + y t + u t + w t = 1) →
        IsAffineOn U (fun t => dephase (bccb (x t) (y t) (u t) (w t))) →
        (∃ t₁ ∈ U, ∃ t₂ ∈ U,
          r.readout () ⟨p, x, y, u, w⟩ t₁ ≠ params x y u w t₂) →
        ∃ π : Equiv.Perm (Fin 4),
          (∃ μ : (Fin p → ℝ) → ℂ, ∀ t ∈ U,
            params x y u w t ∘ π = ![μ t, -μ t, -omega, -omega ^ 2]) ∨
          (∃ ξ : (Fin p → ℝ) → ℂ, ∀ t ∈ U,
            params x y u w t ∘ π = ![1, ξ t, omega * ξ t, omega ^ 2 * ξ t])

private def z : ℂ := ⟨1 / 4, Real.sqrt 15 / 4⟩

private theorem norm_z : ‖z‖ = 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)
  have hn : Complex.normSq z = 1 := by
    norm_num [z, Complex.normSq_apply]
    nlinarith
  rw [Complex.norm_def, hn, Real.sqrt_one]

private theorem tuple_re (t : Fin 0 → ℝ) (j : Fin 4) :
    (params (fun _ => z) (fun _ => z) (fun _ => star z) (fun _ => star z) t j).re =
      1 / 4 := by
  fin_cases j <;> norm_num [params, z]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hn : ∀ t ∈ (Set.univ : Set (Fin 0 → ℝ)),
      ‖z‖ = 1 ∧ ‖z‖ = 1 ∧ ‖star z‖ = 1 ∧ ‖star z‖ = 1 ∧
        z + z + star z + star z = 1 := by
    intro t ht
    refine ⟨norm_z, norm_z, ?_, ?_, ?_⟩
    · simpa using norm_z
    · simpa using norm_z
    · apply Complex.ext <;> norm_num [z]
  have ha : IsAffineOn (Set.univ : Set (Fin 0 → ℝ))
      (fun _ => dephase (bccb z z (star z) (star z))) := by
    intro a b
    exact ⟨dephase (bccb z z (star z) (star z)) a b, 0, by simp⟩
  have hnon : ∃ t₁ ∈ (Set.univ : Set (Fin 0 → ℝ)),
      ∃ t₂ ∈ (Set.univ : Set (Fin 0 → ℝ)),
      rejected.readout () ⟨0, (fun _ => z), (fun _ => z),
        (fun _ => star z), (fun _ => star z)⟩ t₁ ≠
          params (fun _ => z) (fun _ => z) (fun _ => star z) (fun _ => star z) t₂ := by
    refine ⟨0, Set.mem_univ _, 0, Set.mem_univ _, ?_⟩
    intro he
    have hh := congrArg (fun v : Fin 4 → ℂ => (v 0).re) he
    change (0 : ℝ) = 1 / 4 at hh
    norm_num at hh
  obtain ⟨π, hpair | htriple⟩ := h 0 Set.univ isOpen_univ Set.univ_nonempty
    (fun _ => z) (fun _ => z) (fun _ => star z) (fun _ => star z) hn ha hnon
  · obtain ⟨μ, hμ⟩ := hpair
    have h0 := congrArg Complex.re (congrFun (hμ 0 (Set.mem_univ _)) 0)
    have h1 := congrArg Complex.re (congrFun (hμ 0 (Set.mem_univ _)) 1)
    simp only [Function.comp_apply, tuple_re, Matrix.cons_val_zero,
      Matrix.cons_val_one, Complex.neg_re] at h0 h1
    linarith
  · obtain ⟨ξ, hξ⟩ := htriple
    have h0 := congrArg Complex.re (congrFun (hξ 0 (Set.mem_univ _)) 0)
    norm_num only [Function.comp_apply, tuple_re, Matrix.cons_val_zero, Complex.one_re] at h0

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, (fun t => (t 0 : ℂ)), (fun _ => 0), (fun _ => 0), (fun _ => 0)⟩,
    0, 1, ?_⟩
  intro he
  have hh := congrArg (fun v : Fin 4 → ℂ => (v 0).re) he
  change (0 : ℝ) = 1 at hh
  exact zero_ne_one hh

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Tomography.MUB.BCCBOrderNineAffineSuborbits.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Tomography.MUB.BCCBOrderNineAffineSuborbits.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Tomography.MUB.BCCBOrderNineAffineSuborbits.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ q t => params q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 t)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Tomography.MUB.BCCBOrderNineAffineSuborbits
    definition := some {
      owner := `D5.S3.Quantum.Tomography.MUB.BCCBOrderNineAffineSuborbits
      name := `D5.S3.Quantum.Tomography.MUB.BCCBOrderNineAffineSuborbits.claim
      path := #[] }
    coordinates := #[0, 4, 5, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "domain", "arg", "body", "arg", "arg", "body", "arg",
        "fn", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Tomography.MUB.BCCBOrderNineAffineSuborbits
