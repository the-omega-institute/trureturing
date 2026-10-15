import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteStochasticMixing
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteStochasticMixing
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteStochasticMixing
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Filter Topology
open scoped BigOperators
noncomputable section
universe u

abbrev Params := Σ S : Type u, Fintype S × DecidableEq S
abbrev signature : Signature where
  Params := Params.{u}
  State p := Matrix p.1 p.1 ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℕ → Matrix p.1 p.1 ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun (_ : Unit) (p : Params.{u}) P =>
    letI := p.2.1
    letI := p.2.2
    fun n : ℕ => P ^ n) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun (_ : Unit) (_ : Params.{u}) _ => fun _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ (S : Type u) [Fintype S] [DecidableEq S] [Nonempty S]
    (P : Matrix S S ℝ), P ∈ Matrix.rowStochastic ℝ S → P.IsPrimitive →
    ∃ μ : S → ℝ, (∀ j, 0 ≤ μ j) ∧ (∑ j, μ j = 1) ∧ μ ᵥ* P = μ ∧
      (∀ ν : S → ℝ, (∀ j, 0 ≤ ν j) → (∑ j, ν j = 1) → ν ᵥ* P = ν → ν = μ) ∧
      Tendsto (R.readout () ⟨S, inferInstance, inferInstance⟩ P) atTop
        (𝓝 (fun _ j => μ j))

private theorem rejected_law : ¬ arena.Law rejected.{u} := by
  intro h
  let S := ULift.{u} Unit
  let P : Matrix S S ℝ := 1
  have hP : P ∈ Matrix.rowStochastic ℝ S := (Matrix.rowStochastic ℝ S).one_mem
  have hp : P.IsPrimitive := by
    refine ⟨fun i j => ?_, 1, by omega, ?_⟩
    · simp [P, Matrix.one_apply, Subsingleton.elim i j]
    · intro i j
      simp [P, Matrix.one_apply, Subsingleton.elim i j]
  obtain ⟨μ, _, hs, _, _, ht⟩ := h S P hP hp
  change Tendsto (fun _ : ℕ => (0 : Matrix S S ℝ)) atTop (𝓝 (fun _ j => μ j)) at ht
  have he : (0 : Matrix S S ℝ) = fun _ j => μ j :=
    tendsto_nhds_unique (by exact tendsto_const_nhds) ht
  have hz : ∀ j, μ j = 0 := fun j => (congrFun (congrFun he ⟨()⟩) j).symm
  simp [hz] at hs

private theorem actual_law : arena.Law actual.{u} := by
  intro S fs ds ns P hP hp
  exact primitive_convergence P hP hp

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
    let S := ULift.{u} Unit
    refine ⟨⟨S, inferInstance, inferInstance⟩, (0 : Matrix S S ℝ), (1 : Matrix S S ℝ), ?_⟩
    intro he
    have hh := congrArg (fun f => f 1 ⟨()⟩ ⟨()⟩) he
    simp only [actual, realize, pow_one] at hh
    change (0 : ℝ) = 1 at hh
    exact zero_ne_one hh

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteStochasticMixing.primitive_convergence.{u})
    (type_of% (actual.{u})) (Type u → Type u → Type → Type u) Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteStochasticMixing.primitive_convergence,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteStochasticMixing.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨evidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} (fun (_ : Unit) (p : Params.{u}) P =>
    letI := p.2.1
    letI := p.2.2
    fun n : ℕ => P ^ n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some (Matrix),
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteStochasticMixing,
    definition := none,
    coordinates := #[0, 1, 2],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "arg", "arg", "fn", "fn", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteStochasticMixing
