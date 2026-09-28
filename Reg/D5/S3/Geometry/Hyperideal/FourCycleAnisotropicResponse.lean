import D5.S3.Geometry.Hyperideal.FourCycleAnisotropicResponse
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open _root_.D5.S3.Geometry.Hyperideal.FourCycleAnisotropicResponse
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Geometry.Hyperideal.FourCycleAnisotropicResponse

abbrev signature : Signature.{0, 0, 0, 0, 0} where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => x / 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

/-- The full original telescope, with only its half-angle readout varied. -/
def arena : Arena.{0, 0, 0, 0, 0} where
  signature := signature
  Law ρ := ∀
    (r a b o : ℝ)
    (_hr : 1 < r) (_ha : 1 < a) (_hb : 1 < b) (_ho : 1 < o)
    (_ht : -1 < cosine r a b o a b ∧ cosine r a b o a b < 1)
    (_hbeta : -1 < cosine a b r a b o ∧ cosine a b r a b o < 1)
    (_hdelta : -1 < cosine b a r b a o ∧ cosine b a r b a o < 1),
    ρ.readout () () (Real.arccos (cosine a b r a b o) -
      Real.arccos (cosine b a r b a o)) =
      Real.arctan (((Real.sqrt (a^2 - 1) - Real.sqrt (b^2 - 1)) / (a + b)) *
        Real.sqrt ((r - 1) / (r + 1)) *
          Real.cot (Real.arccos (cosine r a b o a b) / 2))

private theorem all_two_cosine : cosine 2 2 2 2 2 2 = (2 : ℝ) / 3 := by
  norm_num [cosine, numerator, rad]
  rw [div_div, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 27)]
  norm_num

private theorem all_two_range :
    -1 < cosine 2 2 2 2 2 2 ∧ cosine 2 2 2 2 2 2 < 1 := by
  rw [all_two_cosine]
  norm_num

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 2 2 2 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) all_two_range all_two_range all_two_range
  change (1 : ℝ) = _ at hb
  norm_num at hb

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (2 : ℝ), ?_⟩
  norm_num [actual, realize]

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@paired_angle_half_difference, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

register_information_theorem
  _root_.D5.S3.Geometry.Hyperideal.FourCycleAnisotropicResponse.paired_angle_half_difference
  in arena
  readout via (realize signature (fun _ _ x => x / 2) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Geometry.Hyperideal.FourCycleAnisotropicResponse
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn",
        "arg"]
      stateBinder := 0
      stateOperand := some #["fn", "arg"] }] })
  escape continues (open)

open Lean in
run_meta do
  let env ← getEnv
  let target := `D5.S3.Geometry.Hyperideal.FourCycleAnisotropicResponse.paired_angle_half_difference
  let some row := TemplateBinding.records env |>.find? (fun row =>
      row.occurrence.key.theoremName == target &&
      row.occurrence.key.registrationModule == env.header.mainModule)
    | throwError "Missing original CFMP registration"
  match row.result with
  | .declaredValidated certificate =>
      unless row.escape.fromObject.isSome && certificate.sourceBinding.isSome &&
          row.escape.bridgeKind == "source-equivalence" &&
          row.escape.continuation.any (·.kind == "open") do
        throwError "Original CFMP registration lacks four-slot source evidence"
  | .declaredUnresolved diagnostic => throwError "Original CFMP unresolved: {diagnostic}"
  | .undeclared => throwError "Original CFMP registration is undeclared"

#print axioms registration

end Reg.D5.S3.Geometry.Hyperideal.FourCycleAnisotropicResponse
