import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset MeasureTheory Preorder ProbabilityTheory
open ProbabilityTheory.Kernel
noncomputable section
universe u v

/-- Coordinates retain the sample type, every dependent time type, and the process. -/
abbrev signature : Signature where
  Params := (Ω : Type v) × (X : ℕ → Type u) × ((n : ℕ) → Ω → X n)
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (n : ℕ) → p.2.1 n
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {Ω : Type v} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : ℕ → Type u} [∀ n, MeasurableSpace (X n)]
    {κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))}
    [∀ n, IsMarkovKernel (κ n)] {μ₀ : Measure (X 0)} [IsProbabilityMeasure μ₀]
    [IsFiniteMeasure P] {Y : (n : ℕ) → Ω → X n}
    (hY_meas : ∀ n, Measurable (Y n)) (h0 : HasLaw (Y 0) μ₀ P)
    (h_condDistrib : ∀ n, HasCondDistrib (Y (n + 1))
      (fun ω ↦ fun i : Iic n ↦ Y i ω) (κ n) P),
    HasLaw (R.readout () ⟨Ω, X, Y⟩) (trajMeasure μ₀ κ) P

def actual : Realization signature.{u,v} :=
  realize signature (fun (_ : Unit)
    (p : (Ω : Type v) × (X : ℕ → Type u) × ((n : ℕ) → Ω → X n))
    (ω : p.1) (n : ℕ) => p.2.2 n ω) (fun e => nomatch e)

/-- This intervention erases the sample while preserving all dependent output types. -/
def rejected : Realization signature.{u,v} :=
  realize signature (fun (_ : Unit)
    (p : (Ω : Type v) × (X : ℕ → Type u) × ((n : ℕ) → Ω → X n))
    (ω : p.1) (n : ℕ) => Classical.choice (show Nonempty (p.2.1 n) from ⟨p.2.2 n ω⟩))
    (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected.{u,v} := by
  intro h
  let Ω := ULift.{v} Unit
  let B := ULift.{u} Bool
  let b : B := Classical.choice (inferInstance : Nonempty B)
  let c : B := ⟨!b.down⟩
  let P : Measure Ω := Measure.dirac ⟨()⟩
  let Y : (n : ℕ) → Ω → B := fun _ _ => c
  let κ : (n : ℕ) → Kernel (Iic n → B) B :=
    fun _ => Kernel.const _ (Measure.dirac c)
  have hc : b ≠ c := by
    intro heq
    have hh := congrArg ULift.down heq
    change b.down = !b.down at hh
    have hn : ∀ z : Bool, z ≠ !z := by decide
    exact hn b.down hh
  have hY : ∀ n, Measurable (Y n) := by intro n; exact measurable_const
  have h0 : HasLaw (Y 0) (Measure.dirac c) P := hasLaw_dirac_of_ae_eq (Filter.Eventually.of_forall fun _ => rfl)
  have hcond : ∀ n, HasCondDistrib (Y (n + 1))
      (fun ω => fun i : Iic n => Y i ω) (κ n) P := by
    intro n
    constructor
    · change AEMeasurable (fun _ : Ω => ((fun _ : Iic n => c), c)) P
      exact measurable_const.aemeasurable
    · simp [Y, P, κ, Measure.map_const, Measure.compProd_const, Measure.dirac_prod_dirac]
  have hbad := h hY h0 hcond
  have hgood := has_law_traj_measure hY h0 hcond
  have heq := hbad.map_eq.trans hgood.map_eq.symm
  change P.map (fun _ : Ω => fun _ : ℕ => b) =
    P.map (fun _ : Ω => fun _ : ℕ => c) at heq
  have hmass := congrArg (fun μ : Measure (ℕ → B) => μ {fun _ => c}) heq
  have hpath : (fun _ : ℕ => b) ≠ (fun _ : ℕ => c) := fun h => hc (congrFun h 0)
  simpa [P, Measure.map_const, hpath, Ne.symm hpath] using hmass

def registration : Registration arena.{u,v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨has_law_traj_measure,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨ULift.{v} Bool, (fun _ => ULift.{u} Bool),
      (fun _ ω => ⟨ω.down⟩)⟩, ⟨false⟩, ⟨true⟩, ?_⟩
    intro h
    have hh := congrArg (fun f => (f 0).down) h
    cases hh

register_information_theorem has_law_traj_measure in arena
  readout via (realize signature.{u,v}
    (fun (_ : Unit)
      (p : (Ω : Type v) × (X : ℕ → Type u) × ((n : ℕ) → Ω → X n))
      (ω : p.1) (n : ℕ) => p.2.2 n ω) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory
    coordinates := #[0, 3, 10]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "fn", "fn", "arg", "body"], stateBinder := 14 }] })
  escape continues (open)

#print axioms registration
end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HasLawTrajectory
