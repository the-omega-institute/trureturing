import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourCliffordRankThree
import Reg.Support.SingleDependentReadout

/-! Dependent readout of the right dimension inequality. -/

namespace Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourCliffordRankThree

open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourCliffordRankThree
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

abbrev cliffordArena : Arena where
  signature := dimensionSignature
  Law R := ∀ {a b c d : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (lam : ℝ) (_hlam : 0 < lam) (_hab : a < b)
    (_hF : (∑ i, kronecker (X i) (Y i))ᴴ * (∑ i, kronecker (X i) (Y i)) =
      (lam : ℂ) • (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ))
    (_hK : ∃ P : Matrix (Fin 4) (Fin 4) ℂ, IsUnit P ∧
      ∀ T : Matrix (Fin 4) (Fin 4) ℂ, T.IsHermitian → compression X T = 0 →
        Pᴴ * T * P ∈ Submodule.span ℝ (Set.range pauliClifford)),
    R.readout () () (4 * c) (3 * d)

private def coordinateRow (i : Fin 4) : Matrix (Fin 1) (Fin 4) ℂ :=
  fun _ j => if i = j then 1 else 0

private theorem coordinate_compression (T : Matrix (Fin 4) (Fin 4) ℂ) :
    compression coordinateRow T = T := by
  rw [compression, stackK_compression]
  ext i j
  simp [coordinateRow, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
    Matrix.smul_apply, Fin.sum_univ_one, mul_ite, ite_mul, eq_comm]

private theorem coordinate_gram :
    (∑ i, kronecker (coordinateRow i) (coordinateRow i)ᴴ)ᴴ *
      (∑ i, kronecker (coordinateRow i) (coordinateRow i)ᴴ) =
      (1 : Matrix (Fin 4 × Fin 1) (Fin 4 × Fin 1) ℂ) := by
  let F : Matrix (Fin 1 × Fin 4) (Fin 4 × Fin 1) ℂ :=
    ∑ i, kronecker (coordinateRow i) (coordinateRow i)ᴴ
  have hF : F = (1 : Matrix (Fin 4 × Fin 1) (Fin 4 × Fin 1) ℂ).submatrix
      (Equiv.prodComm _ _) id := by
    ext ⟨i, j⟩ ⟨k, l⟩
    have hil : i = l := Subsingleton.elim _ _
    simp [F, hil, coordinateRow, Matrix.sum_apply, Matrix.submatrix_apply, Matrix.one_apply,
      Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Prod.mk.injEq, ite_mul, mul_ite]
  change Fᴴ * F = 1
  rw [hF]
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
  let I : Matrix (Fin 4 × Fin 1) (Fin 4 × Fin 1) ℂ := 1
  let swap := Equiv.prodComm (Fin 1) (Fin 4)
  let stay := Equiv.refl (Fin 4 × Fin 1)
  change I.submatrix stay swap * I.submatrix swap stay = I
  rw [Matrix.submatrix_mul_equiv I I stay swap stay, show I * I = I from Matrix.one_mul I] <;> rfl

private theorem cliffordRejected : ¬ cliffordArena.Law dimensionFalse := by
  intro h
  exact h coordinateRow (fun i => (coordinateRow i)ᴴ) 1 (by norm_num) (by decide)
    (by simpa using coordinate_gram)
    ⟨1, isUnit_one, fun T _ hT => by
      have hzero := (coordinate_compression T).symm.trans hT
      simp [hzero]⟩

def cliffordFamily : Registration cliffordArena (type_of% @clifford_kernel_four_bound) where
  actual := dimensionLe
  bridge := Iff.rfl
  variation := ⟨@clifford_kernel_four_bound, dimensionFalse, cliffordRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    cliffordArena.Law dimensionLe dimensionFalse cliffordRejected
  dependence := dimensionDependence

def cliffordRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@clifford_kernel_four_bound) (Realization dimensionSignature) Unit Unit where
  unitName := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourCliffordRankThree.clifford_kernel_four_bound.information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourCliffordRankThree.cliffordFamily
  realizationSource := none
  generated := false
  arena := .source ⟨cliffordArena⟩
  objectArena := .source ⟨cliffordArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cliffordArena ⟨cliffordFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some dimensionLe
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourCliffordRankThree
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourCliffordRankThree
