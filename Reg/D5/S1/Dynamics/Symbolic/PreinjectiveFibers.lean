import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Dynamics.Symbolic.PreinjectiveFibers

/-! Source-bound families retain all alphabets, rules, configurations and fibers. -/

set_option autoImplicit false
noncomputable section
universe u

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.Symbolic.PreinjectiveFibers
open _root_.D5.S1.Dynamics.Symbolic.PermutativeLifts.BipermutativeLift
open _root_.D5.S1.Dynamics.Symbolic.PermutativeLifts.BipermutativePreinjectivity
open Set Function

namespace Reg.D5.S1.Dynamics.Symbolic.PreinjectiveFibers

abbrev Inputs := Σ A : Type u, Σ k : ℕ, (Fin (k + 2) → A) → A

abbrev signature : Signature where
  Params := Inputs.{u}
  State P := ℤ → P.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := ℤ → P.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ P => code P.2.2) (fun e => Empty.elim e)

def repeatedOrigin : Realization signature.{u} :=
  realize signature (fun _ _ x _ => x 0) (fun e => Empty.elim e)

private theorem projection_preinjective {A : Type u} :
    Preinjective (fun w : Fin 2 → A => w 0) := by
  intro x z _ he
  funext i
  have hi := congrFun he i
  change x (i + 0) = z (i + 0) at hi
  simpa only [add_zero] using hi

private def pulse (n : ℕ) : ℤ → ULift.{u} Bool :=
  fun i => ⟨decide (i = (n + 1 : ℕ))⟩

private theorem pulse_injective : Injective pulse.{u} := by
  intro m n he
  have hc := congrArg ULift.down (congrFun he (m + 1 : ℕ))
  simp [pulse] at hc
  omega

private theorem pulse_origin (n : ℕ) : pulse.{u} n 0 = ⟨false⟩ := by
  simp [pulse]
  omega

def collarArena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} {k : ℕ} {h : (Fin (k + 2) → A) → A},
    Preinjective h → ∀ (y : ℤ → A) (F : Finset (ℤ → A)),
      (∀ x ∈ F, R.readout () ⟨A, k, h⟩ x = y) →
        ∃ a b : ℤ, a ≤ b ∧ (F : Set (ℤ → A)).InjOn (collarPair k a b)

private theorem collar_rejected : ¬ collarArena.{u}.Law repeatedOrigin := by
  classical
  intro hlaw
  let F := (Finset.range 5).image pulse.{u}
  have hF : ∀ x ∈ F,
      repeatedOrigin.readout () ⟨ULift.{u} Bool, 0, fun w => w 0⟩ x = fun _ => ⟨false⟩ := by
    intro x hx
    obtain ⟨n, _hn, rfl⟩ := Finset.mem_image.mp hx
    funext i
    exact pulse_origin n
  obtain ⟨a, b, _hab, hinj⟩ := hlaw projection_preinjective (fun _ => ⟨false⟩) F hF
  have hc := Fintype.card_le_of_injective
    (fun n : Fin 5 => collarPair 0 a b (pulse.{u} n)) (by
      intro m n he
      apply Fin.ext
      apply pulse_injective
      exact hinj (Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr m.isLt, rfl⟩)
        (Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr n.isLt, rfl⟩) he)
  norm_num [Fintype.card_prod, Fintype.card_fun] at hc

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let P : Inputs.{u} := ⟨ULift.{u} Bool, 0, fun w => w 0⟩
  refine ⟨P, (fun _ => ⟨false⟩), (fun _ => ⟨true⟩), ?_⟩
  intro he
  have hc := congrArg ULift.down (congrFun he 0)
  cases hc

def collarFamily : Registration collarArena.{u}
    (type_of% (@finite_family_two_collar_encoding.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_family_two_collar_encoding.{u}, repeatedOrigin, collar_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨repeatedOrigin, ?_, rfl, collar_rejected⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := actual_dependence

def fiberArena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} {k : ℕ} {h : (Fin (k + 2) → A) → A} [Finite A],
    Preinjective h → ∀ y : ℤ → A,
      Set.Finite {x : ℤ → A | R.readout () ⟨A, k, h⟩ x = y} ∧
        Set.ncard {x : ℤ → A | code h x = y} ≤ (Nat.card A) ^ (2 * (k + 1))

private theorem fiber_rejected : ¬ fiberArena.{u}.Law repeatedOrigin := by
  intro hlaw
  have hh := hlaw (A := ULift.{u} Bool) projection_preinjective (fun _ => ⟨false⟩)
  apply (Set.infinite_range_of_injective pulse_injective) (hh.1.subset ?_)
  rintro x ⟨n, rfl⟩
  funext i
  exact pulse_origin n

def fiberFamily : Registration fiberArena.{u}
    (type_of% (@_root_.D5.S1.Dynamics.Symbolic.PreinjectiveFibers.finite_fiber_ncard_le.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_fiber_ncard_le.{u}, repeatedOrigin, fiber_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨repeatedOrigin, ?_, rfl, fiber_rejected⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := actual_dependence

def registration_collar : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Dynamics.Symbolic.PreinjectiveFibers.finite_family_two_collar_encoding.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.PreinjectiveFibers.collar
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.PreinjectiveFibers.collarFamily
  realizationSource := none
  generated := false
  arena := .source ⟨collarArena.{u}⟩
  objectArena := .source ⟨collarArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source collarArena.{u} ⟨collarFamily.{u}⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ P => code P.2.2) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.PreinjectiveFibers
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain",
        "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def registration_fiber : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Dynamics.Symbolic.PreinjectiveFibers.finite_fiber_ncard_le.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.PreinjectiveFibers.fiber
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.PreinjectiveFibers.fiberFamily
  realizationSource := none
  generated := false
  arena := .source ⟨fiberArena.{u}⟩
  objectArena := .source ⟨fiberArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fiberArena.{u} ⟨fiberFamily.{u}⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ P => code P.2.2) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.PreinjectiveFibers
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg",
        "arg", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Dynamics.Symbolic.PreinjectiveFibers
