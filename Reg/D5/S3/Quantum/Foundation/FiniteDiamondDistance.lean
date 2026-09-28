import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.Quantum.Foundation.FiniteDiamondDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped CStarAlgebra ComplexOrder MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance
universe u v

abbrev signature : Signature where
  Params := Unit
  State := fun _ => Set ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ states => sSup states) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law observation := ∀ {a b : Type u}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (first second : QuantumChannel a b),
    (∀ {R : Type v} [Fintype R] [DecidableEq R] (rho : DensityState (R × a)),
      ∃ tau : DensityState (R × a),
        IsPure tau ∧ referenceError first second rho ≤ referenceError first second tau) ∧
    (∀ {R : Type v} [Fintype R] [DecidableEq R] (rho : DensityState (R × a)),
      ∃ tau : DensityState (Fin (Fintype.card a) × a),
        IsPure tau ∧ referenceError first second rho ≤ referenceError first second tau) ∧
    diamondDistance first second =
      observation.readout () ()
        ({0} ∪ {x : ℝ | ∃ tau : DensityState (Fin (Fintype.card a) × a),
          IsPure tau ∧ x = referenceError first second tau})

theorem actual_law : arena.{u, v}.Law actual := by
  intro a b _ _ _ _ first second
  exact _root_.D5.S3.Quantum.Foundation.FiniteDiamondDistance.result first second

theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  let q := ULift.{u} Unit
  let channel : QuantumChannel q q := {
    toCompletelyPositiveMap := {
      toLinearMap := LinearMap.id
      map_cstarMatrix_nonneg' := by
        intro k X hX
        change 0 ≤ X.map id
        simpa only [CStarMatrix.map_id] using hX }
    trace_preserving := by intro X; rfl }
  have hd : 0 ≤ diamondDistance channel channel := by
    apply Real.sSup_nonneg'
    exact ⟨0, Or.inl (Set.mem_singleton 0), le_rfl⟩
  have hbad := (h channel channel).2.2
  change diamondDistance channel channel = (-1 : ℝ) at hbad
  rw [hbad] at hd
  norm_num at hd

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), {0}, {1}, ?_⟩
  change sSup ({0} : Set ℝ) ≠ sSup ({1} : Set ℝ)
  rw [csSup_singleton, csSup_singleton]
  norm_num

def registration : Registration arena.{u, v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

register_information_theorem _root_.D5.S3.Quantum.Foundation.FiniteDiamondDistance.result
  in arena
  readout via (realize signature (fun _ _ states => sSup states) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Foundation.FiniteDiamondDistance
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg"]
      stateOperand := some #["arg"] }] })
  escape continues (open)

#print axioms registration
end Reg.D5.S3.Quantum.Foundation.FiniteDiamondDistance
