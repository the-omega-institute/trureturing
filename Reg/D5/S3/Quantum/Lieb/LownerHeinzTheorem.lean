import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Lieb.LownerHeinzTheorem
import Reg.Support.DependentFamily
import Mathlib.Analysis.InnerProductSpace.PiL2

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LownerHeinzTheorem
open LeanInformationAudit
open scoped Topology

noncomputable section
namespace Reg.D5.S3.Quantum.Lieb.LownerHeinzTheorem
universe u

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro x; cases x⟩

def actual : Realization signature :=
  realize signature (fun _ p x => x ^ p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => x ^ (2 : ℕ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ] [Nontrivial ℋ], ∀ p ∈ Set.Icc (0 : ℝ) 1,
      OperatorConcaveOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun x => r.readout () p x)

theorem actual_law : arena.{u}.Law actual := by
  intro ℋ _ _ _ _ p hp
  exact power_Icc_zero_one_operatorConcaveOn_Ici p hp

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hall
  let H := EuclideanSpace ℂ (ULift.{u} (Fin 1))
  have hconc := hall (ℋ := H) 0 (by constructor <;> norm_num)
  have h := hconc (A := (0 : H →L[ℂ] H)) (B := 1) (t := (1/2 : ℝ))
    (IsSelfAdjoint.zero _) (IsSelfAdjoint.one _) (by norm_num) (by norm_num)
    (by simp [spectrum.zero_eq]) (by simp [spectrum.one_eq])
  have heq : (1 - (1/2 : ℝ)) • (0 : H →L[ℂ] H) + (1/2 : ℝ) • 1 =
      algebraMap ℝ (H →L[ℂ] H) (1/2) := by simp [Algebra.algebraMap_eq_smul_one]
  change cfc (fun x : ℝ => -(x ^ (2 : ℕ)))
      ((1 - (1/2 : ℝ)) • (0 : H →L[ℂ] H) + (1/2 : ℝ) • 1) ≤
    (1 - (1/2 : ℝ)) • cfc (fun x : ℝ => -(x ^ (2 : ℕ))) (0 : H →L[ℂ] H) +
      (1/2 : ℝ) • cfc (fun x : ℝ => -(x ^ (2 : ℕ))) (1 : H →L[ℂ] H) at h
  rw [heq, cfc_algebraMap, cfc_apply_zero, cfc_apply_one] at h
  norm_num [Algebra.algebraMap_eq_smul_one, smul_smul] at h

def mathematicalRegistration : Registration arena.{u}
    (∀ {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
      [CompleteSpace ℋ] [Nontrivial ℋ], ∀ p ∈ Set.Icc (0 : ℝ) 1,
        OperatorConcaveOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun x => x ^ p)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      cases i; cases j
      exact (h rfl).elim
    · intro e; exact nomatch e
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), ?_⟩
    change (0 : ℝ) ^ (1 : ℝ) ≠ (1 : ℝ) ^ (1 : ℝ)
    norm_num

/- The exact source function operand is the final argument of
`OperatorConcaveOn`; all quantified Hilbert spaces are retained in the law.
Only the real exponent p is a readout parameter, and x is its real state. -/
noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.LownerHeinzTheorem.power_Icc_zero_one_operatorConcaveOn_Ici.{u})
    (Realization signature) (Type) (Unit) where
  unitName := `Reg.D5.S3.Quantum.Lieb.LownerHeinzTheorem.powerConcavity
  realizationName := `Reg.D5.S3.Quantum.Lieb.LownerHeinzTheorem.mathematicalRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨mathematicalRegistration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => x ^ p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Lieb.LownerHeinzTheorem
    definition := none
    coordinates := #[5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms mathematicalRegistration
#print axioms registration_1
end Reg.D5.S3.Quantum.Lieb.LownerHeinzTheorem
