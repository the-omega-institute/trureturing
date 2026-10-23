import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SubstochasticEscape
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SubstochasticEscape
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SubstochasticEscape
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Filter Topology Finset
open scoped BigOperators
noncomputable section
universe u
abbrev Params := Σ X : Type u, Fintype X × DecidableEq X
abbrev signature : Signature where
  Params := Params.{u}
  State p := Matrix p.1 p.1 ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.1 p.1 ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun (_ : Unit) (_ : Params.{u}) A => A) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun (_ : Unit) (p : Params.{u}) _ =>
    by letI := p.2.2; exact (1 : Matrix p.1 p.1 ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ (X : Type u) [Fintype X] [DecidableEq X] (A : Matrix X X ℝ),
    IsSubstochastic A → ∀ (N : ℕ), 0 < N → ∀ (c : ℝ), c < 1 →
    (∀ k, rowSum A N k ≤ c) → ∀ i j,
    let B := R.readout () ⟨X, inferInstance, inferInstance⟩ A
    HasSum (fun t : ℕ => (B ^ t) i j) ((1 - B)⁻¹ i j)

private theorem actual_law : arena.Law actual.{u} := by
  intro X fs ds A hA N hN c hc hb i j
  exact hA.hasSum_pow_entry hN hc hb i j

private theorem rejected_law : ¬ arena.Law rejected.{u} := by
  intro h
  let X := ULift.{u} Unit
  let a : X := ⟨()⟩
  have hA : IsSubstochastic (0 : Matrix X X ℝ) :=
    ⟨by intro i j; simp, by intro i; simp⟩
  have hb : ∀ k : X, rowSum (0 : Matrix X X ℝ) 1 k ≤ 0 := by
    intro k; simp [rowSum]
  have hs := h X 0 hA 1 (by norm_num) 0 (by norm_num) hb a a
  have hf : Summable (fun _ : ℕ => (1 : ℝ)) := by
    simpa [rejected, realize, Matrix.diagonal_one] using hs.summable
  have hz := hf.tendsto_atTop_zero
  have he : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hz
  exact one_ne_zero he

def evidence : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    change ∀ i : Unit, ∃ p x y, actual.readout i p x ≠ actual.readout i p y
    intro i
    let X := ULift.{u} Unit
    refine ⟨⟨X, inferInstance, inferInstance⟩, (0 : Matrix X X ℝ), 1, ?_⟩
    intro he
    have hh := congrArg (fun M => M ⟨()⟩ ⟨()⟩) he
    change (0 : ℝ) = 1 at hh
    exact zero_ne_one hh

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SubstochasticEscape.IsSubstochastic.hasSum_pow_entry.{u})
    (type_of% (actual.{u})) (Type u → Type u → Type → Type u) Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SubstochasticEscape.hasSum_pow_entry,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SubstochasticEscape.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} (fun (_ : Unit) (_ : Params.{u}) A => A)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some (Matrix),
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SubstochasticEscape,
    definition := none,
    coordinates := #[0, 1, 2],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "arg", "body", "fn", "fn", "fn", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "arg", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SubstochasticEscape
