import D5.S3.Geometry.Hyperideal.FourCycleGramRadius
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Hyperideal.FourCycleGramRadius
open LeanInformationAudit

namespace Reg.D5.S3.Geometry.Hyperideal.FourCycleGramRadius

noncomputable section

abbrev signature : Signature where
  Params := Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, ℝ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p d =>
    Matrix.det (gram p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 d))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (r a b o c d : ℝ),
    1 < r → 1 < a → 1 < b → 1 < o → 1 < c → 1 < d →
    0 < ((a + c) / 2 + (b + d) / 2) ^ 2 - (r - 1) * (o - 1) →
    0 < (r + 1) * (o + 1) - ((a + c) / 2 - (b + d) / 2) ^ 2 →
    (((a - c) / 2) ^ 2 + ((b - d) / 2) ^ 2) ^ 2 +
      2 * (r * o - 1 + Real.sqrt ((((a + c) / 2) ^ 2 - ((b + d) / 2) ^ 2) ^ 2 +
        (r - o) ^ 2)) * (((a - c) / 2) ^ 2 + ((b - d) / 2) ^ 2) <
      (((a + c) / 2 + (b + d) / 2) ^ 2 - (r - 1) * (o - 1)) *
        ((r + 1) * (o + 1) - ((a + c) / 2 - (b + d) / 2) ^ 2) →
    R.readout () ⟨r, a, b, o, c⟩ d < 0

theorem actual_law : arena.Law actual := by
  intro r a b o c d hr ha hb ho hc hd hL hM hbound
  exact gram_det_radius r a b o c d hr ha hb ho hc hd hL hM hbound

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 2 2 2 2 2 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hh

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨(2 : ℝ), 2, 2, 2, 2⟩, (2 : ℝ), (3 : ℝ), ?_⟩
  intro h
  have hh := h
  norm_num [actual, realize, gram, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_one,
    Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at hh
  simp only [show Fin.succAbove (1 : Fin 4) (2 : Fin 3) = (3 : Fin 4) by decide,
    show Fin.succAbove (2 : Fin 4) (2 : Fin 3) = (3 : Fin 4) by decide,
    show Fin.castSucc (2 : Fin 3) = (2 : Fin 4) by decide] at hh
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead,
    Matrix.vecTail] at hh

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := dependence

register_information_theorem
  _root_.D5.S3.Geometry.Hyperideal.FourCycleGramRadius.gram_det_radius
  in arena
  readout via (realize signature (fun _ p d =>
    Matrix.det (gram p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 d))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Geometry.Hyperideal.FourCycleGramRadius
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5 }] })
  escape continues (open)

open Lean in
run_meta do
  let env ← getEnv
  let sourceName : Lean.Name :=
    `D5.S3.Geometry.Hyperideal.FourCycleGramRadius.gram_det_radius
  let some row := TemplateBinding.records env |>.find? (fun row =>
      row.occurrence.key.theoremName == sourceName &&
      row.occurrence.key.registrationModule == env.header.mainModule)
    | throwError "Gram radius registration evidence is missing"
  match row.result with
  | .declaredValidated certificate =>
      unless row.escape.fromObject.isSome &&
          row.escape.continuation.any (fun continuation => continuation.kind == "open") &&
          row.escape.bridgeKind == "source-equivalence" &&
          certificate.sourceBinding.isSome do
        throwError "Gram radius lacks validated source-bound four-slot evidence"
  | .declaredUnresolved diagnostic =>
      throwError "Gram radius registration is unresolved: {diagnostic}"
  | .undeclared =>
      throwError "Gram radius registration is undeclared"

#print axioms registration

end

end Reg.D5.S3.Geometry.Hyperideal.FourCycleGramRadius
