import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Dynamics.Symbolic.GardenOfEden

/-! Complete source families for the native code and actual prefix counts. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.Symbolic.GardenOfEden
open _root_.D5.S1.Dynamics.Symbolic.PermutativeLifts.BipermutativeLift
open _root_.D5.S1.Dynamics.Symbolic.PermutativeLifts.BipermutativePreinjectivity
open _root_.D5.S1.Dynamics.Symbolic
open Set Function Filter

namespace Reg.D5.S1.Dynamics.Symbolic.GardenOfEden

noncomputable section
universe u

private theorem constant_not_preinjective :
    ¬ Preinjective (fun _ : Fin 2 → ULift.{u} Bool => ULift.up false) := by
  intro hp
  let x : ℤ → ULift.{u} Bool := fun _ => ⟨false⟩
  let y := Function.update x 0 ⟨true⟩
  have hf : FiniteDifference x y := by
    apply (Set.finite_singleton 0).subset
    intro i hi
    by_contra hn
    have hin : i ≠ 0 := by simpa using hn
    exact hi (by simp [x, y, Function.update_of_ne hin])
  have he := hp hf rfl
  have hc := congrArg ULift.down (congrFun he 0)
  simp [x, y] at hc

abbrev CodeInputs := Σ A : Type u, Σ k : ℕ, (Fin (k + 2) → A) → A

abbrev codeSignature : Signature where
  Params := CodeInputs.{u}
  State P := ℤ → P.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := ℤ → P.1
  Anchor := Empty
  finiteAnchor := inferInstance

def codeRejected : Realization codeSignature.{u} :=
  realize codeSignature (fun _ _ => id) (fun e => Empty.elim e)

def codeArena : Arena where
  signature := codeSignature.{u}
  Law R := ∀ {A : Type u} [Finite A] (k : ℕ) (h : (Fin (k + 2) → A) → A),
    Surjective (R.readout () ⟨A, k, h⟩) ↔ Preinjective h

private theorem codeRejected_law : ¬ codeArena.{u}.Law codeRejected := by
  intro hlaw
  have hh := @hlaw (ULift.{u} Bool) inferInstance 0 (fun _ => ULift.up false)
  exact constant_not_preinjective (hh.mp Function.surjective_id)

def codeFamily : Registration codeArena.{u}
    (type_of% (@_root_.D5.S1.Dynamics.Symbolic.GardenOfEden.garden_of_eden.{u})) where
  actual := realize codeSignature (fun _ P => code P.2.2) (fun e => Empty.elim e)
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
    let P : CodeInputs.{u} := ⟨ULift.{u} Bool, 0, fun w => w 0⟩
    refine ⟨P, (fun _ => ⟨false⟩), (fun _ => ⟨true⟩), ?_⟩
    intro he
    have hc := congrArg ULift.down (congrFun he 0)
    cases hc

abbrev countSignature : Signature where
  Params := Type u
  State A := Set (ℕ → A)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def countRejected : Realization countSignature.{u} :=
  realize countSignature (fun _ A _ n => Nat.card A ^ n) (fun e => Empty.elim e)

def countArena : Arena where
  signature := countSignature.{u}
  Law R := ∀ {A : Type u} {k : ℕ} {h : (Fin (k + 2) → A) → A} [Finite A]
    (_hq : 2 ≤ Nat.card A) (_hnot : ¬ Preinjective h),
    ∃ r : ℝ, r < Real.log (Nat.card A : ℝ) ∧
      Tendsto (fun n : ℕ => Real.log (R.readout () A (imageRay h) n : ℝ) / n)
        atTop (nhds r)

private theorem countRejected_law : ¬ countArena.{u}.Law countRejected := by
  intro hlaw
  obtain ⟨r, hr, hlim⟩ := @hlaw (ULift.{u} Bool) 0 (fun _ => ULift.up false)
    inferInstance (by simp) constant_not_preinjective
  have hfull : Tendsto (fun n : ℕ => Real.log ((Nat.card (ULift.{u} Bool) ^ n : ℕ) : ℝ) / n)
      atTop (nhds (Real.log (Nat.card (ULift.{u} Bool) : ℝ))) := by
    refine (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => Real.log (Nat.card (ULift.{u} Bool) : ℝ)) atTop _).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Nat.cast_pow, Real.log_pow]
    exact (mul_div_cancel_left₀ (Real.log (Nat.card (ULift.{u} Bool) : ℝ))
      (by exact_mod_cast (show n ≠ 0 by omega))).symm
  exact (ne_of_lt hr) (tendsto_nhds_unique hlim hfull)

def countFamily : Registration countArena.{u}
    (type_of% (@_root_.D5.S1.Dynamics.Symbolic.GardenOfEden.strict_image_prefix_loss.{u})) where
  actual := realize countSignature
    (fun _ A => @PrefixGrowthEntropy.prefixCount A) (fun e => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨@strict_image_prefix_loss.{u}, countRejected, countRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨countRejected, ?_, rfl, countRejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    let A := ULift.{u} Bool
    refine ⟨A, (∅ : Set (ℕ → A)), (Set.univ : Set (ℕ → A)), ?_⟩
    intro he
    have hc := congrFun he 0
    have hzero : PrefixGrowthEntropy.prefixCount (∅ : Set (ℕ → A)) 0 = 0 := by
      simp [PrefixGrowthEntropy.prefixCount]
    have hone : PrefixGrowthEntropy.prefixCount (Set.univ : Set (ℕ → A)) 0 = 1 := by
      unfold PrefixGrowthEntropy.prefixCount
      have : Nonempty (range fun x : (Set.univ : Set (ℕ → A)) =>
          fun i : Fin 0 => (x : ℕ → A) i.val) :=
        ⟨⟨fun i => Fin.elim0 i, ⟨⟨fun _ => ⟨false⟩, trivial⟩, by ext i; exact Fin.elim0 i⟩⟩⟩
      exact Nat.card_unique
    change PrefixGrowthEntropy.prefixCount (∅ : Set (ℕ → A)) 0 =
      PrefixGrowthEntropy.prefixCount (Set.univ : Set (ℕ → A)) 0 at hc
    rw [hzero, hone] at hc
    cases hc

def erasableArena : Arena where
  signature := codeSignature.{u}
  Law R := ∀ {A : Type u} {k : ℕ} {h : (Fin (k + 2) → A) → A}
    (_hnot : ¬ Preinjective h),
    ∃ n : ℕ, 0 < n ∧ ∃ p q : Fin n → A, p ≠ q ∧
      ∀ (t : ℤ) (z : ℤ → A), (∀ j : Fin n, z (t + (j : ℕ)) = p j) →
        R.readout () ⟨A, k, h⟩ (writeWord q t z) = code h z

private theorem erasableRejected_law : ¬ erasableArena.{u}.Law codeRejected := by
  intro hlaw
  obtain ⟨n, hn, p, q, _hpq, hreplace⟩ :=
    @hlaw (ULift.{u} Bool) 0 (fun _ => ULift.up false) constant_not_preinjective
  let z : ℤ → ULift.{u} Bool :=
    fun i => if hi : i.toNat < n then p ⟨i.toNat, hi⟩ else ⟨true⟩
  have hz : ∀ j : Fin n, z (0 + (j : ℕ)) = p j := by
    intro j
    dsimp only [z]
    simp only [zero_add, Int.toNat_natCast]
    rw [dite_eq_left j.isLt]
  have he := hreplace 0 z hz
  have hc := congrArg (fun w : ℤ → ULift.{u} Bool => (w (n : ℤ)).down) he
  simp [codeRejected, realize, writeWord, z, code] at hc

def erasableFamily : Registration erasableArena.{u}
    (type_of% (@_root_.D5.S1.Dynamics.Symbolic.GardenOfEden.exists_erasable_words.{u})) where
  actual := realize codeSignature (fun _ P => code P.2.2) (fun e => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨@exists_erasable_words.{u}, codeRejected, erasableRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨codeRejected, ?_, rfl, erasableRejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := codeFamily.dependence

noncomputable def registration_code : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Dynamics.Symbolic.GardenOfEden.garden_of_eden.{u})
    (Realization codeSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.GardenOfEden.code
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.GardenOfEden.codeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨codeArena.{u}⟩
  objectArena := .source ⟨codeArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source codeArena.{u} ⟨codeFamily.{u}⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize codeSignature.{u} (fun _ P => code P.2.2) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.GardenOfEden
    definition := none
    coordinates := #[0, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def registration_count : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Dynamics.Symbolic.GardenOfEden.strict_image_prefix_loss.{u})
    (Realization countSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.GardenOfEden.prefixCount
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.GardenOfEden.countFamily
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
    (fun _ A => @PrefixGrowthEntropy.prefixCount A) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.GardenOfEden
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg",
        "fn", "fn", "arg", "body", "fn", "arg", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def registration_erasable : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Dynamics.Symbolic.GardenOfEden.exists_erasable_words.{u})
    (Realization codeSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.GardenOfEden.erasable
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.GardenOfEden.erasableFamily
  realizationSource := none
  generated := false
  arena := .source ⟨erasableArena.{u}⟩
  objectArena := .source ⟨erasableArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source erasableArena.{u} ⟨erasableFamily.{u}⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize codeSignature.{u} (fun _ P => code P.2.2) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.GardenOfEden
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "arg", "body",
        "arg", "body", "arg", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Dynamics.Symbolic.GardenOfEden
