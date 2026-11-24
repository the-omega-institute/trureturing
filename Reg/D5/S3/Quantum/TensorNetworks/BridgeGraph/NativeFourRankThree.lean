import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourRankThree
import Reg.Support.SingleDependentReadout

/-! Dependent readout of the right dimension inequality. -/

namespace Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourRankThree

open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourRankThree
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourKernel (compression)
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeRectangularBound (stackK_compression)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped BigOperators Kronecker

noncomputable section

abbrev dimensionSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def dimensionLe : Realization dimensionSignature :=
  realize dimensionSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def dimensionFalse : Realization dimensionSignature :=
  realize dimensionSignature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dimensionDependence : ObservationalDependence dimensionSignature dimensionLe := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  norm_num [dimensionLe, realize] at he

abbrev rankThreeArena : Arena where
  signature := dimensionSignature
  Law R := ∀ {a b c d : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (lam : ℝ) (_hlam : 0 < lam) (_hab : a < b)
    (_hF : (∑ i, kronecker (X i) (Y i))ᴴ * (∑ i, kronecker (X i) (Y i)) =
      (lam : ℂ) • (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ))
    (_hK : ∃ T : Matrix (Fin 4) (Fin 4) ℂ, T.IsHermitian ∧ compression X T = 0 ∧
      T.rank = 3),
    R.readout () () (6 * c) (5 * d) ∧ (a * d - b * c < 2 * c - d → 4 * c ≤ 3 * d)

private def witnessX : Fin 4 → Matrix (Fin 2) (Fin 3) ℂ :=
  ![!![0, 0, 1; 0, 0, 0], !![0, 0, 0; 0, 0, 1],
    !![0, 0, 1; 0, 0, 0], !![1, 0, 0; 0, 1, 0]]

private def witnessY : Fin 4 → Matrix (Fin 3) (Fin 2) ℂ :=
  ![!![0, 0; 0, 0; 1, 0], !![0, 0; 0, 0; 0, 1], 0, !![1, 0; 0, 1; 0, 0]]

private theorem witnessGram :
    (∑ i, kronecker (witnessX i) (witnessY i))ᴴ *
      (∑ i, kronecker (witnessX i) (witnessY i)) =
      (1 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [witnessX, witnessY, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sum_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
      Fin.sum_univ_four, Matrix.one_apply]

private theorem witnessRankThree :
    ∃ T : Matrix (Fin 4) (Fin 4) ℂ, T.IsHermitian ∧ compression witnessX T = 0 ∧
      T.rank = 3 := by
  classical
  refine ⟨diagonal ![(2 : ℂ), -1, -1, 0], ?_, ?_, ?_⟩
  · change (diagonal ![(2 : ℂ), -1, -1, 0])ᴴ = diagonal ![(2 : ℂ), -1, -1, 0]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  · rw [compression, stackK_compression]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [witnessX, Matrix.diagonal_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.sum_apply, Matrix.smul_apply, Fin.sum_univ_two, Fin.sum_univ_four]
  · rw [Matrix.rank_diagonal, Fintype.card_subtype]
    rw [show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} by decide]
    norm_num

private theorem rankThreeRejected : ¬ rankThreeArena.Law dimensionFalse := by
  intro h
  exact (h witnessX witnessY 1 (by norm_num) (by decide)
    (by simpa using witnessGram) witnessRankThree).1

example : 2 * 3 - 3 * 2 < 2 * 2 - 3 := by decide

def rankThreeFamily : Registration rankThreeArena (type_of% @rank_three_small_defect_four_bound) where
  actual := dimensionLe
  bridge := Iff.rfl
  variation := ⟨@rank_three_small_defect_four_bound, dimensionFalse, rankThreeRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    rankThreeArena.Law dimensionLe dimensionFalse rankThreeRejected
  dependence := dimensionDependence

def rankThreeRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rank_three_small_defect_four_bound) (Realization dimensionSignature) Unit Unit where
  unitName := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourRankThree.rank_three_small_defect_four_bound.information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourRankThree.rankThreeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨rankThreeArena⟩
  objectArena := .source ⟨rankThreeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rankThreeArena ⟨rankThreeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some dimensionLe
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourRankThree
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

example {a b c d : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (lam : ℝ) (hlam : 0 < lam)
    (hF : (∑ i, kronecker (X i) (Y i))ᴴ * (∑ i, kronecker (X i) (Y i)) =
      (lam : ℂ) • (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ))
    (hSize : (a = 4 ∧ b = 5 ∧ c = 4 ∧ d = 5) ∨
      (a = 5 ∧ b = 6 ∧ c = 4 ∧ d = 5) ∨ (a = 5 ∧ b = 6 ∧ c = 5 ∧ d = 6)) :
    ¬ ∃ T : Matrix (Fin 4) (Fin 4) ℂ, T.IsHermitian ∧ compression X T = 0 ∧ T.rank = 3 := by
  have hdim : a < b ∧ a * d - b * c < 2 * c - d ∧ 3 * d < 4 * c := by
    rcases hSize with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
      decide
  intro hK
  exact (not_le_of_gt hdim.2.2) ((rank_three_small_defect_four_bound X Y lam hlam hdim.1 hF hK).2 hdim.2.1)

end
end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourRankThree
