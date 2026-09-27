import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
open MeasureTheory Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

-- Source coordinates c and t retain their order; x is the lambda-bound state.
abbrev signature : Signature where
  Params := (_ : ℝ) × ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature
  Law R := ∀ {c t : ℝ}, 0 < c →
    (∫ x in Ioi (0 : ℝ), (R.readout () ⟨c, t⟩ x : ℝ)) = c / (c ^ 2 + t ^ 2)

def actual : Realization signature :=
  realize signature
    (fun (_ : Unit) (p : (_ : ℝ) × ℝ) (x : ℝ) =>
      Real.exp (-p.1 * x) * Real.cos (p.2 * x))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) (_ : (_ : ℝ) × ℝ) (_ : ℝ) => (0 : ℝ)) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := h (c := 1) (t := 0) (by norm_num)
  norm_num [rejected, realize] at hzero

def registration : Registration arena (∀ {c t : ℝ}, 0 < c →
    (∫ x in Ioi (0 : ℝ), Real.exp (-c * x) * Real.cos (t * x)) =
      c / (c ^ 2 + t ^ 2)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.integral_exp_neg_mul_cos,
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
    refine ⟨⟨(1 : ℝ), (0 : ℝ)⟩, (1 : ℝ), (2 : ℝ), ?_⟩
    change Real.exp (-1 * 1) * Real.cos (0 * 1) ≠
      Real.exp (-1 * 2) * Real.cos (0 * 2)
    simp only [zero_mul, mul_one, Real.cos_zero]
    intro h
    have harg := Real.exp_injective h
    norm_num at harg

register_information_theorem
    _root_.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.integral_exp_neg_mul_cos in arena
  readout via (realize signature
    (fun (_ : Unit) (p : (_ : ℝ) × ℝ) (x : ℝ) =>
      Real.exp (-p.1 * x) * Real.cos (p.2 * x))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "body"]
      stateBinder := 3 }] })
  escape continues (open)

#print axioms registration
end
end Reg.D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
