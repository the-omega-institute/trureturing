import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Dynamics.Symbolic.LatticeGardenOfEden

/-! Source-bound audits for lattice equivalence and strict actual-image loss. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.Symbolic.LatticeGardenOfEden
open CondensedMatter.Crystal Set Function

namespace Reg.D5.S1.Dynamics.Symbolic.LatticeGardenOfEden

noncomputable section
universe u

private def collisionX : (Fin 1 → ℤ) → ULift.{u} Bool := fun _ => ⟨false⟩
private def collisionY : (Fin 1 → ℤ) → ULift.{u} Bool :=
  Function.update collisionX 0 ⟨true⟩

private theorem collision_finite : Set.Finite {z | collisionX.{u} z ≠ collisionY.{u} z} := by
  apply (Set.finite_singleton 0).subset
  intro z hz
  by_contra hn
  have hne : z ≠ 0 := by simpa only [Set.mem_singleton_iff] using hn
  exact hz (by simp [collisionY, Function.update_of_ne hne])

private theorem collision_ne : collisionX.{u} ≠ collisionY.{u} := by
  intro he
  have hc := congrArg ULift.down (congrFun he 0)
  simp [collisionX, collisionY] at hc

private theorem constant_not_preinjective :
    ¬ Preinjective (∅ : Finset (Fin 1 → ℤ)) (fun _ => (ULift.up false : ULift.{u} Bool)) := by
  intro hp
  exact collision_ne (hp collisionX collisionY collision_finite rfl)

abbrev CodeInputs := Σ A : Type u, Σ d : ℕ, Σ S : Finset (Fin d → ℤ), (S → A) → A

abbrev codeSignature : Signature where
  Params := CodeInputs.{u}
  State P := (Fin P.2.1 → ℤ) → P.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := (Fin P.2.1 → ℤ) → P.1
  Anchor := Empty
  finiteAnchor := inferInstance

def codeActual : Realization codeSignature.{u} :=
  realize codeSignature (fun _ P => localMap P.2.2.1 P.2.2.2) (fun e => nomatch e)

def codeRejected : Realization codeSignature.{u} :=
  realize codeSignature (fun _ _ => id) (fun e => nomatch e)

def codeArena : Arena where
  signature := codeSignature.{u}
  Law R := ∀ {A : Type u} [Finite A] (d : ℕ) (S : Finset (Fin d → ℤ)) (φ : (S → A) → A),
    Surjective (R.readout () ⟨A, d, S, φ⟩) ↔ Preinjective S φ

private theorem codeRejected_law : ¬ codeArena.{u}.Law codeRejected := by
  intro hlaw
  have hh := @hlaw (ULift.{u} Bool) inferInstance 1 ∅ (fun _ => ULift.up false)
  exact constant_not_preinjective (hh.mp Function.surjective_id)

def codeFamily : Registration codeArena.{u}
    (type_of% (@_root_.D5.S1.Dynamics.Symbolic.LatticeGardenOfEden.garden_of_eden.{u})) where
  actual := codeActual
  bridge := Iff.rfl
  variation := ⟨@garden_of_eden.{u}, codeRejected, codeRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨codeRejected, ?_, rfl, codeRejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    let S : Finset (Fin 1 → ℤ) := {0}
    let P : CodeInputs.{u} := ⟨ULift.{u} Bool, 1, S, fun w => w ⟨0, by simp [S]⟩⟩
    refine ⟨P, (fun _ => ⟨false⟩), (fun _ => ⟨true⟩), ?_⟩
    intro he
    have hc := congrArg ULift.down (congrFun he 0)
    cases hc

abbrev CountInputs := Σ _A : Type u, Σ d : ℕ, Σ _S : Finset (Fin d → ℤ), ℕ

abbrev countSignature : Signature where
  Params := CountInputs.{u}
  State P := (P.2.2.1 → P.1) → P.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def countActual : Realization countSignature.{u} :=
  realize countSignature (fun _ P => imagePatternCount (box P.2.1 (P.2.2.2 + 1)) P.2.2.1)
    (fun e => nomatch e)

def countRejected : Realization countSignature.{u} :=
  realize countSignature (fun _ P _ => Nat.card P.1 ^ ((P.2.2.2 + 1) ^ P.2.1))
    (fun e => nomatch e)

def countArena : Arena where
  signature := countSignature.{u}
  Law R := ∀ {A : Type u} [Finite A] (d : ℕ) (_hd : 1 ≤ d)
    (S : Finset (Fin d → ℤ)) (φ : (S → A) → A) (_ha : 2 ≤ Nat.card A)
    (x y : (Fin d → ℤ) → A) (_hf : Set.Finite {z | x z ≠ y z})
    (_hi : localMap S φ x = localMap S φ y) (_hne : x ≠ y),
    ∃ c : ℝ, c < Real.log (Nat.card A : ℝ) ∧ ∃ N : ℕ, ∀ n ≥ N,
      Real.log (R.readout () ⟨A, d, S, n⟩ φ : ℝ) / ((n + 1 : ℕ) : ℝ) ^ d ≤ c

private theorem countRejected_law : ¬ countArena.{u}.Law countRejected := by
  intro hlaw
  obtain ⟨c, hc, N, hN⟩ := @hlaw (ULift.{u} Bool) inferInstance 1 (by omega) ∅
    (fun _ => ULift.up false) (by simp) collisionX collisionY collision_finite rfl collision_ne
  have hh := hN N le_rfl
  change Real.log ((Nat.card (ULift.{u} Bool) ^ ((N + 1) ^ 1) : ℕ) : ℝ) /
    ((N + 1 : ℕ) : ℝ) ^ 1 ≤ c at hh
  rw [Nat.cast_pow, Real.log_pow, Nat.cast_pow] at hh
  have hv : ((N + 1 : ℕ) : ℝ) ^ 1 ≠ 0 := by positivity
  rw [mul_div_cancel_left₀ _ hv] at hh
  exact (not_le_of_gt hc) hh

private theorem constant_count (d n : ℕ) :
    imagePatternCount (box d (n + 1)) ({0} : Finset (Fin d → ℤ))
      (fun _ => (ULift.up false : ULift.{u} Bool)) = 1 := by
  classical
  simp [imagePatternCount, ImagePatterns, localMap]

private theorem projection_count_lower :
    2 ≤ imagePatternCount (box 1 1) ({0} : Finset (Fin 1 → ℤ))
      (fun w : ({0} : Finset (Fin 1 → ℤ)) → ULift.{u} Bool => w ⟨0, by simp⟩) := by
  classical
  let S : Finset (Fin 1 → ℤ) := {0}
  let φ : (S → ULift.{u} Bool) → ULift.{u} Bool := fun w => w ⟨0, by simp [S]⟩
  let key : ULift.{u} Bool → ImagePatterns S φ (box 1 1) := fun a =>
    ⟨fun _ => a, (fun _ => a), rfl⟩
  have hk : Injective key := by
    intro a b he
    let z : box 1 1 := ⟨0, by simp [box, Fintype.mem_piFinset]⟩
    exact congrFun (congrArg Subtype.val he) z
  have hc := Nat.card_le_card_of_injective key hk
  simpa [imagePatternCount, S, φ, Nat.card_eq_fintype_card] using hc

def countFamily : Registration countArena.{u}
    (type_of% (@_root_.D5.S1.Dynamics.Symbolic.LatticeGardenOfEden.strict_image_box_loss.{u})) where
  actual := countActual
  bridge := Iff.rfl
  variation := ⟨@strict_image_box_loss.{u}, countRejected, countRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨countRejected, ?_, rfl, countRejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    let S : Finset (Fin 1 → ℤ) := {0}
    let P : CountInputs.{u} := ⟨ULift.{u} Bool, 1, S, 0⟩
    let φc : (S → ULift.{u} Bool) → ULift.{u} Bool := fun _ => ⟨false⟩
    let φp : (S → ULift.{u} Bool) → ULift.{u} Bool := fun w => w ⟨0, by simp [S]⟩
    refine ⟨P, φc, φp, ?_⟩
    intro he
    change imagePatternCount (box 1 1) S (fun _ => (ULift.up false : ULift.{u} Bool)) =
      imagePatternCount (box 1 1) S (fun w => w ⟨0, by simp [S]⟩) at he
    have hc := constant_count.{u} 1 0
    have hl := projection_count_lower.{u}
    dsimp [S] at he
    rw [he] at hc
    exact (by decide : ¬ (2 ≤ (1 : ℕ))) (hl.trans_eq hc)

def registration_code : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Dynamics.Symbolic.LatticeGardenOfEden.garden_of_eden.{u})
    (Realization codeSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.LatticeGardenOfEden.code
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.LatticeGardenOfEden.codeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨codeArena.{u}⟩
  objectArena := .source ⟨codeArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source codeArena.{u} ⟨codeFamily.{u}⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize codeSignature.{u}
    (fun _ P => localMap P.2.2.1 P.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.LatticeGardenOfEden
    definition := none
    coordinates := #[0, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def registration_count : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Dynamics.Symbolic.LatticeGardenOfEden.strict_image_box_loss.{u})
    (Realization countSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.LatticeGardenOfEden.count
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.LatticeGardenOfEden.countFamily
  realizationSource := none
  generated := false
  arena := .source ⟨countArena.{u}⟩
  objectArena := .source ⟨countArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source countArena.{u} ⟨countFamily.{u}⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize countSignature.{u}
    (fun _ P => imagePatternCount (box P.2.1 (P.2.2.2 + 1)) P.2.2.1)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.LatticeGardenOfEden
    definition := none
    coordinates := #[0, 2, 4, 14]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "body", "arg", "arg", "body",
        "body", "body", "fn", "arg", "fn", "arg", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev logSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def logActual : Realization logSignature :=
  realize logSignature (fun _ _ => Real.log) (fun e => nomatch e)

def logRejected : Realization logSignature :=
  realize logSignature (fun _ _ _ => 1) (fun e => nomatch e)

def logArena : Arena where
  signature := logSignature
  Law R := ∀ {a b k u v f : ℕ},
    2 ≤ a → 0 < b → 0 < v → 0 < f → v ≤ k * b ^ 2 → k * b ≤ u →
    f ≤ (a ^ b - 1) ^ k * a ^ (u - k * b) →
    0 < ((b : ℝ) * Real.log (a : ℝ) - Real.log (a ^ b - 1 : ℕ)) / (b : ℝ) ^ 2 ∧
    R.readout () () (f : ℝ) / v ≤ (u : ℝ) / v * Real.log (a : ℝ) -
      ((b : ℝ) * Real.log (a : ℝ) - Real.log (a ^ b - 1 : ℕ)) / (b : ℝ) ^ 2

private theorem logRejected_law : ¬ logArena.Law logRejected := by
  intro h
  have hh := (@h 2 1 1 1 1 1 (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num) (by norm_num)).2
  norm_num [logRejected, realize] at hh

def logFamily : Registration logArena
    (type_of% (@_root_.D5.S1.Dynamics.Symbolic.LatticeGardenOfEden.logarithmic_packing_bound)) where
  actual := logActual
  bridge := Iff.rfl
  variation := ⟨@logarithmic_packing_bound, logRejected, logRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨logRejected, ?_, rfl, logRejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (1 : ℝ), (2 : ℝ), ?_⟩
    change Real.log (1 : ℝ) ≠ Real.log (2 : ℝ)
    rw [Real.log_one]
    exact (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))).symm

def registration_log : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Dynamics.Symbolic.LatticeGardenOfEden.logarithmic_packing_bound)
    (Realization logSignature) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.LatticeGardenOfEden.log
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.LatticeGardenOfEden.logFamily
  realizationSource := none
  generated := false
  arena := .source ⟨logArena⟩
  objectArena := .source ⟨logArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source logArena ⟨logFamily⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize logSignature (fun _ _ => Real.log) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.LatticeGardenOfEden
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Dynamics.Symbolic.LatticeGardenOfEden
