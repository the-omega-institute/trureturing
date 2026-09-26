import D5.S3.Arith.Lattices.GoldenCubicIndexForm
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Lattices.GoldenCubicIndexForm

open scoped Matrix
open _root_.D5.S1.Scale
open _root_.D5.S3.Arith.Lattices.GoldenCubicIndexForm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ j => -3 * blockB j ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ j => -3 * blockB j ^ 2 + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law readout := ∀ (j : ℕ) (hj : 1 ≤ j) (r b c : ℤ),
    Matrix.det (traceGram (blockA j)) = readout.readout () () j ∧
      Matrix.det (indexMatrix (blockA j) r b c) =
        3 * b ^ 3 + 3 * b ^ 2 * c + b * c ^ 2 - blockA j * c ^ 3 ∧
      9 * Matrix.det (indexMatrix (blockA j) r b c) =
        (3 * b + c) ^ 3 - blockB j * c ^ 3

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hgood := (golden_cubic_discriminant_index_form 1 (by omega) 0 0 0).1
  have hbad := (h 1 (by omega) 0 0 0).1
  change Matrix.det (traceGram (blockA 1)) = -3 * blockB 1 ^ 2 + 1 at hbad
  rw [hgood] at hbad
  omega

def registration : Registration arena
    (∀ (j : ℕ) (hj : 1 ≤ j) (r b c : ℤ),
      Matrix.det (traceGram (blockA j)) = -3 * blockB j ^ 2 ∧
        Matrix.det (indexMatrix (blockA j) r b c) =
          3 * b ^ 3 + 3 * b ^ 2 * c + b * c ^ 2 - blockA j * c ^ 3 ∧
        9 * Matrix.det (indexMatrix (blockA j) r b c) =
          (3 * b + c) ^ 3 - blockB j * c ^ 3) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨golden_cubic_discriminant_index_form, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    change (-3 * blockB 0 ^ 2 : ℤ) ≠ -3 * blockB 1 ^ 2
    norm_num [blockB, goldenLucas, D5.S0.Carrier.trace,
      D5.S0.Carrier.phi, pow_succ]

register_information_theorem
  _root_.D5.S3.Arith.Lattices.GoldenCubicIndexForm.golden_cubic_discriminant_index_form
  in arena
  readout via (realize signature
    (fun _ _ j => -3 * blockB j ^ 2) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Lattices.GoldenCubicIndexForm
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

end Reg.D5.S3.Arith.Lattices.GoldenCubicIndexForm
