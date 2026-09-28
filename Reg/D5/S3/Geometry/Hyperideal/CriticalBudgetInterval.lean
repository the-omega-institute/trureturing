import D5.S3.Geometry.Hyperideal.CriticalBudgetInterval
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Hyperideal.CriticalBudgetInterval
open _root_.D5.S3.Geometry.Hyperideal.CriticalTransitionStar
open _root_.D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open LeanInformationAudit

namespace Reg.D5.S3.Geometry.Hyperideal.CriticalBudgetInterval

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ _ a => cosine 2 (5/4) (5/4) a (5/4) (5/4))
    (fun e => nomatch e)

def rejectedLeft : Realization signature :=
  realize signature
    (fun role _ a => if role then cosine 2 (5/4) (5/4) a (5/4) (5/4) else 0)
    (fun e => nomatch e)

def rejectedRight : Realization signature :=
  realize signature
    (fun role _ a => if role then 1 else cosine 2 (5/4) (5/4) a (5/4) (5/4))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a : ℝ), 1 < a → a < 7 / 5 →
    R.readout false () a = (25-8*a)/33 ∧
    ((0 < 2*Real.pi - 6*Real.arccos (2*(2-a)/(a+1)) ∧
      0 < 4*Real.arccos (R.readout true () a) + 2*beta - 2*Real.pi) ↔
    oppositeThreshold < a ∧ a < 7 / 5)

theorem actual_law : arena.Law actual := by
  intro a ha hb
  exact exact_budget_interval a ha hb

theorem rejected_left_law : ¬ arena.Law rejectedLeft := by
  intro h
  have hh := (h (4/3) (by norm_num) (by norm_num)).1
  norm_num [rejectedLeft, realize] at hh

private theorem threshold_lt_four_thirds : oppositeThreshold < (4/3:ℝ) := by
  let q : ℝ := 49 / Real.sqrt 6534
  let r : ℝ := Real.sqrt ((1-q)/2)
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hqsq : q^2 = (2401:ℝ)/6534 := by
    dsimp [q]
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6534)]
    norm_num
  have hqbound : q < (6103:ℝ)/9801 := by nlinarith
  have hrnonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r^2 = (1-q)/2 := by
    dsimp [r]
    exact Real.sq_sqrt (by linarith)
  have hrbound : (43:ℝ)/99 < r := by nlinarith
  change (25-33*r)/8 < 4/3
  linarith

theorem rejected_right_law : ¬ arena.Law rejectedRight := by
  intro h
  have hh := (h (4/3) (by norm_num) (by norm_num)).2
  have hinterval : oppositeThreshold < (4/3:ℝ) ∧ (4/3:ℝ) < 7/5 :=
    ⟨threshold_lt_four_thirds, by norm_num⟩
  have hu := (hh.mpr hinterval).2
  change 0 < 4*Real.arccos (1:ℝ) + 2*beta - 2*Real.pi at hu
  rw [Real.arccos_one] at hu
  have hbeta : beta ≤ Real.pi := Real.arccos_le_pi _
  linarith

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (4/3 : ℝ), (13/10 : ℝ), ?_⟩
  intro h
  change cosine 2 (5/4) (5/4) (4/3) (5/4) (5/4) =
    cosine 2 (5/4) (5/4) (13/10) (5/4) (5/4) at h
  rw [(exact_budget_interval (4/3) (by norm_num) (by norm_num)).1,
    (exact_budget_interval (13/10) (by norm_num) (by norm_num)).1] at h
  norm_num at h

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejectedLeft, rejected_left_law⟩
  sensitivity := by
    constructor
    · intro i
      cases i
      · refine ⟨rejectedLeft, ?_, rfl, rejected_left_law⟩
        intro j h
        cases j
        · exact (h rfl).elim
        · rfl
      · refine ⟨rejectedRight, ?_, rfl, rejected_right_law⟩
        intro j h
        cases j
        · rfl
        · exact (h rfl).elim
    · intro i
      exact nomatch i
  dependence := dependence

register_information_theorem exact_budget_interval in arena
  readout via (realize signature
    (fun _ _ a => cosine 2 (5/4) (5/4) a (5/4) (5/4))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Geometry.Hyperideal.CriticalBudgetInterval
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "body", "fn", "arg", "fn", "arg"],
        stateBinder := 0 },
      { path := #["body", "body", "body", "arg", "fn", "arg", "arg",
          "arg", "fn", "arg", "fn", "arg", "arg", "arg"],
        stateBinder := 0 }] })
  escape continues (open)

open Lean in
run_meta do
  let env ← getEnv
  let sourceName : Lean.Name :=
    `D5.S3.Geometry.Hyperideal.CriticalBudgetInterval.exact_budget_interval
  let some row := TemplateBinding.records env |>.find? (fun row =>
      row.occurrence.key.theoremName == sourceName &&
      row.occurrence.key.registrationModule == env.header.mainModule)
    | throwError "Budget interval registration evidence is missing"
  match row.result with
  | .declaredValidated certificate =>
      unless row.escape.fromObject.isSome &&
          row.escape.continuation.any (fun continuation => continuation.kind == "open") &&
          row.escape.bridgeKind == "source-equivalence" &&
          certificate.sourceBinding.isSome do
        throwError "Budget interval lacks validated source-bound four-slot evidence"
  | .declaredUnresolved diagnostic =>
      throwError "Budget interval registration is unresolved: {diagnostic}"
  | .undeclared =>
      throwError "Budget interval registration is undeclared"

#print axioms registration

end

end Reg.D5.S3.Geometry.Hyperideal.CriticalBudgetInterval
