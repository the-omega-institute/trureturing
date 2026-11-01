import Reg.D5.S3.Quantum.Algebra.BornJaccardTracialClassification
import D5.S3.Quantum.Algebra.BornJaccardFixedOverlap

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.BornJaccardTracialClassification
open _root_.D5.S3.Quantum.Algebra.BornJaccardFixedOverlap
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Algebra.BornJaccardFixedOverlap

abbrev signature := Reg.D5.S3.Quantum.Algebra.BornJaccardTracialClassification.signature
abbrev actual := Reg.D5.S3.Quantum.Algebra.BornJaccardTracialClassification.actual
abbrev rejected := Reg.D5.S3.Quantum.Algebra.BornJaccardTracialClassification.rejected

abbrev arena : Arena where
  signature := signature
  Law A := ∀ {n : ℕ} (_hn : 2 ≤ n)
    (rho : Matrix (Fin n) (Fin n) ℂ) (hp : rho.PosDef) (_ht : Matrix.trace rho = 1)
    (c : ℝ) (_hc : 0 ≤ c) (R T : Submodule ℂ (H n))
    (_hTR : T ≤ R.orthogonal) (hT : Module.finrank ℂ T = 2)
    (r : ℝ) (_hr : 0 ≤ r) (_hr1 : r < 1),
    let lam := intervalEigenvalues rho hp T hT
    IsGreatest {d : ℝ | ∃ L N : Submodule ℂ T,
      Module.finrank ℂ L = 1 ∧ Module.finrank ℂ N = 1 ∧
      ∃ u v : T, u ∈ L ∧ v ∈ N ∧ ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ ‖inner ℂ u v‖ = r ∧
        d = A.readout () ⟨n, rho⟩ c (R ⊔ L.map T.subtype) (R ⊔ N.map T.subtype) -
          A.readout () ⟨n, rho⟩ c (R ⊔ L.map T.subtype) (R ⊔ T) -
          A.readout () ⟨n, rho⟩ c (R ⊔ T) (R ⊔ N.map T.subtype)}
      (r * (lam 0 - lam 1) / (c + weight rho.toEuclideanLin R + (lam 0 + lam 1)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let rho : Matrix (Fin 2) (Fin 2) ℂ := (2 : ℂ)⁻¹ • 1
  have hp : rho.PosDef := by
    convert (Matrix.PosDef.one (R := ℂ) (n := Fin 2)).smul
      (show (0 : ℝ) < (2 : ℝ)⁻¹ by norm_num) using 1
    ext i j
    simp [rho, Matrix.smul_apply, Complex.real_smul]
  have ht : Matrix.trace rho = 1 := by
    norm_num [rho, Matrix.trace, Matrix.smul_apply]
  have hm := h (by omega) rho hp ht 0 (by norm_num) ⊥ ⊤ (by simp)
    (by simp [H]) 0 (by norm_num) (by norm_num)
  obtain ⟨L, N, _, _, u, v, _, _, _, _, _, heq⟩ := hm.1
  norm_num [rejected, Reg.D5.S3.Quantum.Algebra.BornJaccardTracialClassification.rejected,
    realize] at heq

def family : Registration arena (type_of% (@fixed_overlap_maximum)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fixed_overlap_maximum, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := Reg.D5.S3.Quantum.Algebra.BornJaccardTracialClassification.dependence

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@fixed_overlap_maximum) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Algebra.BornJaccardFixedOverlap.fixed_overlap_maximum.information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.BornJaccardFixedOverlap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p c => distance p.2.toEuclideanLin c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.BornJaccardFixedOverlap
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration
end Reg.D5.S3.Quantum.Algebra.BornJaccardFixedOverlap
