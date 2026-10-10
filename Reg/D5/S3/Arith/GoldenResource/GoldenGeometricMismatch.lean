import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.GoldenResource.GoldenGeometricMismatch
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.GoldenResource.GoldenGeometricMismatch

open _root_.D5.S3.Arith.GoldenResource.GoldenGeometricMismatch
open _root_.D5.S3.Arith.GoldenLocalThreshold
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := ℝ × ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p : ℕ}, p.Prime → ∀ (lambda : ℝ) (a m : ℕ),
    geometricMismatchBudget lambda p a m ≤
      R.readout () (lambda, p) m - R.readout () (lambda, p) a

def actual : Realization signature :=
  realize signature (fun _ q a => goldenPrimeLocalObjective q.1 q.2 a)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ q a => goldenPrimeLocalObjective q.1 q.2 a + a)
    (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (p := 2) (by decide) 0 1 0
  have hd := golden_prime_local_objective_diff (by decide : Nat.Prime 2) 0 0
  norm_num [rejected, realize, geometricMismatchBudget, Finset.sum_range_succ] at hh
  norm_num at hd
  nlinarith

def familyRegistration : Registration arena
    (∀ {p : ℕ}, p.Prime → ∀ (lambda : ℝ) (a m : ℕ),
      geometricMismatchBudget lambda p a m ≤
        goldenPrimeLocalObjective lambda p m - goldenPrimeLocalObjective lambda p a) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prime_power_objective_gap_ge_geometric_mismatch, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(0, 2), 0, 1, ?_⟩
    change goldenPrimeLocalObjective 0 2 0 ≠ goldenPrimeLocalObjective 0 2 1
    norm_num [goldenPrimeLocalObjective]
    exact (Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2)).ne

/-- Faithful family proof; source-coordinate binding remains unfinished under issue5214.
`sourceSelection := none` is deliberately disclosed and is not declared_validated.
The coercive/global targets and newly exposed original suppliers also need their
own exact source reconstruction and four-slot evidence; this record covers only
the actual local-objective comparison. -/
def registration : LeanInformationAudit.Contract.Registration
    (@prime_power_objective_gap_ge_geometric_mismatch) (Realization signature) Unit Unit where
  unitName := `GoldenGeometricMismatch.localGap
  realizationName := `Reg.D5.S3.Arith.GoldenResource.GoldenGeometricMismatch.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ q a => goldenPrimeLocalObjective q.1 q.2 a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms signature
#print axioms arena
#print axioms actual
#print axioms rejected
#print axioms rejected_law
#print axioms familyRegistration
#print axioms registration

end
end Reg.D5.S3.Arith.GoldenResource.GoldenGeometricMismatch
