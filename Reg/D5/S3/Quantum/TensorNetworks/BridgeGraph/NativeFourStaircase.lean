import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourStaircase
import Reg.Support.SingleDependentReadout

/-! Dependent readouts on the dimension thresholds and the column Gram. -/

namespace Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourStaircase

open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourStaircase
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph (NativeRectangularBound)
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourKernel (compression)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped BigOperators

noncomputable section

abbrev natSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def natLe : Realization natSignature :=
  realize natSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def natEq : Realization natSignature :=
  realize natSignature (fun _ _ x y => x = y) (fun e => nomatch e)

def natFalse : Realization natSignature :=
  realize natSignature (fun _ _ _ _ => False) (fun e => nomatch e)

def natTrue : Realization natSignature :=
  realize natSignature (fun _ _ _ _ => True) (fun e => nomatch e)

private theorem leDependence : ObservationalDependence natSignature natLe := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  norm_num [natLe, realize] at he

private theorem eqDependence : ObservationalDependence natSignature natEq := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  norm_num [natEq, realize] at he

abbrev cornerMatrix := Matrix (Fin 4 × Fin 3) (Fin 4 × Fin 3) ℂ

abbrev cornerSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => cornerMatrix)
    (fun _ => cornerMatrix → Prop)

def cornerEq : Realization cornerSignature :=
  realize cornerSignature (fun _ _ x y => x = y) (fun e => nomatch e)

def cornerTrue : Realization cornerSignature :=
  realize cornerSignature (fun _ _ _ _ => True) (fun e => nomatch e)

private theorem cornerDependence : ObservationalDependence cornerSignature cornerEq := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : cornerMatrix) = 0) = ((1 : cornerMatrix) = 0) at he
  have hone := Eq.mp he rfl
  have hentry := congrArg (fun A : cornerMatrix => A (0, 0) (0, 0)) hone
  norm_num at hentry

private def probeLeft (i : Fin 4) : Matrix (Fin 1) (Fin 4) ℂ := fun _ j => if i = j then 1 else 0

private theorem probeIndependent : LinearIndependent ℂ probeLeft := by
  rw [Fintype.linearIndependent_iff]
  intro g h i
  have he := congrArg (fun A : Matrix (Fin 1) (Fin 4) ℂ => A 0 i) h
  simpa [probeLeft, Matrix.sum_apply, Matrix.smul_apply, mul_ite] using he

private theorem probeLeftGram : (∑ i, (probeLeft i)ᴴ * probeLeft i) = 1 := by
  ext i j
  by_cases h : i = j <;>
    simp [probeLeft, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, h] <;> aesop

private theorem probeCompression (T : Matrix (Fin 4) (Fin 4) ℂ) :
    compression probeLeft T = T := by
  ext i j
  simp [compression, NativeRectangularBound.stackK, probeLeft, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, mul_ite, ite_mul]

abbrev staircaseArena : Arena where
  signature := natSignature
  Law R := ∀ (a b c d : ℕ) (lam : ℝ) (_hlam : 0 < lam)
    (_h : R.readout () () b 0 ∨ c = 0 ∨ Staircase a b c d ∨ Staircase d c b a),
    FourScalarGram a b c d lam

private theorem staircaseRejected : ¬ staircaseArena.Law natTrue := by
  intro h
  have h0 := h 0 1 1 0 1 (by norm_num) (Or.inl trivial)
  have hw := (native_four_scalar_gram_iff 0 1 1 0 1 (by norm_num) (by decide) (by decide)).mp h0
  omega

def staircaseFamily : Registration staircaseArena (type_of% @staircase_sufficient) where
  actual := natEq
  bridge := Iff.rfl
  variation := ⟨@staircase_sufficient, natTrue, staircaseRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    staircaseArena.Law natEq natTrue staircaseRejected
  dependence := eqDependence

def staircaseRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@staircase_sufficient) (Realization natSignature) Unit Unit where
  unitName := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourStaircase.staircase_sufficient.information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourStaircase.staircaseFamily
  realizationSource := none
  generated := false
  arena := .source ⟨staircaseArena⟩
  objectArena := .source ⟨staircaseArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source staircaseArena ⟨staircaseFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourStaircase
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev cornerArena : Arena where
  signature := cornerSignature
  Law R := ∀ (lam : ℝ) (_hlam : 0 < lam),
    FourScalarGram 3 4 3 4 lam ∧
    ¬ ∃ (X : Fin 3 → Matrix (Fin 3) (Fin 4) ℂ) (Y : Fin 3 → Matrix (Fin 4) (Fin 3) ℂ),
      R.readout () () ((∑ i, kronecker (X i) (Y i))ᴴ * (∑ i, kronecker (X i) (Y i)))
        ((lam : ℂ) • (1 : cornerMatrix))

private theorem cornerRejected : ¬ cornerArena.Law cornerTrue := by
  intro h
  exact (h 1 (by norm_num)).2 ⟨0, 0, trivial⟩

def cornerFamily : Registration cornerArena (type_of% @exact_width_four_at_three_four) where
  actual := cornerEq
  bridge := Iff.rfl
  variation := ⟨@exact_width_four_at_three_four, cornerTrue, cornerRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    cornerArena.Law cornerEq cornerTrue cornerRejected
  dependence := cornerDependence

def cornerRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exact_width_four_at_three_four) (Realization cornerSignature) Unit Unit where
  unitName := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourStaircase.exact_width_four_at_three_four.information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourStaircase.cornerFamily
  realizationSource := none
  generated := false
  arena := .source ⟨cornerArena⟩
  objectArena := .source ⟨cornerArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cornerArena ⟨cornerFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cornerSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourStaircase
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "body", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev pureRankTwoArena : Arena where
  signature := natSignature
  Law R := ∀ {a b c d : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (_hab : a < b) (_hLI : LinearIndependent ℂ X)
    (_hF : (∑ i, kronecker (X i) (Y i))ᴴ * (∑ i, kronecker (X i) (Y i)) = 1)
    (_hX : ∑ i, (X i)ᴴ * X i = 1)
    (_hK : ∀ T, T.IsHermitian → compression X T = 0 → T ≠ 0 → T.rank = 2),
    R.readout () () (4 * c) (3 * d)

private theorem pureRankTwoRejected : ¬ pureRankTwoArena.Law natFalse := by
  intro h
  exact h probeLeft (0 : Fin 4 → Matrix (Fin 0) (Fin 0) ℂ) (by decide)
    probeIndependent (Subsingleton.elim _ _) probeLeftGram
    (fun T _ hT hn => (hn ((probeCompression T).symm.trans hT)).elim)

def pureRankTwoFamily : Registration pureRankTwoArena (type_of% @pure_rank_two_kernel_bound) where
  actual := natLe
  bridge := Iff.rfl
  variation := ⟨@pure_rank_two_kernel_bound, natFalse, pureRankTwoRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    pureRankTwoArena.Law natLe natFalse pureRankTwoRejected
  dependence := leDependence

def pureRankTwoRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@pure_rank_two_kernel_bound) (Realization natSignature) Unit Unit where
  unitName := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourStaircase.pure_rank_two_kernel_bound.information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourStaircase.pureRankTwoFamily
  realizationSource := none
  generated := false
  arena := .source ⟨pureRankTwoArena⟩
  objectArena := .source ⟨pureRankTwoArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pureRankTwoArena ⟨pureRankTwoFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourStaircase
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev leftArena : Arena where
  signature := natSignature
  Law R := ∀ (a b c d : ℕ) (lam : ℝ)
    (_hlam : 0 < lam) (_hc : 0 < c) (_hab : 2 * a < b),
    FourScalarGram a b c d lam ↔
      (2 * a < b ∧ R.readout () () (2 * b) (5 * a) ∧ 5 * c ≤ 2 * d) ∨
      (5 * a < 2 * b ∧ b ≤ 3 * a ∧ 3 * c ≤ d) ∨
      (3 * a < b ∧ b ≤ 4 * a ∧ 4 * c ≤ d)

private theorem leftRejected : ¬ leftArena.Law natFalse := by
  intro h
  have hw := (native_four_scalar_gram_iff 2 5 2 5 1 (by norm_num) (by decide) (by decide)).mpr
    (Or.inl ⟨by decide, by decide, by decide⟩)
  have hbad := (h 2 5 2 5 1 (by norm_num) (by decide) (by decide)).mp hw
  change (4 < 5 ∧ False ∧ 10 ≤ 10) ∨ (10 < 10 ∧ 5 ≤ 6 ∧ 6 ≤ 5) ∨
    (6 < 5 ∧ 5 ≤ 8 ∧ 8 ≤ 5) at hbad
  omega

def leftFamily : Registration leftArena (type_of% @native_four_scalar_gram_iff) where
  actual := natLe
  bridge := Iff.rfl
  variation := ⟨@native_four_scalar_gram_iff, natFalse, leftRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    leftArena.Law natLe natFalse leftRejected
  dependence := leDependence

def leftRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@native_four_scalar_gram_iff) (Realization natSignature) Unit Unit where
  unitName := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourStaircase.native_four_scalar_gram_iff.information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourStaircase.leftFamily
  realizationSource := none
  generated := false
  arena := .source ⟨leftArena⟩
  objectArena := .source ⟨leftArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source leftArena ⟨leftFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourStaircase
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev rightArena : Arena where
  signature := natSignature
  Law R := ∀ (a b c d : ℕ) (lam : ℝ)
    (_hlam : 0 < lam) (_hb : 0 < b) (_hdc : 2 * d < c),
    FourScalarGram a b c d lam ↔
      (2 * d < c ∧ R.readout () () (2 * c) (5 * d) ∧ 5 * b ≤ 2 * a) ∨
      (5 * d < 2 * c ∧ c ≤ 3 * d ∧ 3 * b ≤ a) ∨
      (3 * d < c ∧ c ≤ 4 * d ∧ 4 * b ≤ a)

private theorem rightRejected : ¬ rightArena.Law natFalse := by
  intro h
  have hw := (native_four_scalar_gram_swap_iff 5 2 5 2 1 (by norm_num) (by decide) (by decide)).mpr
    (Or.inl ⟨by decide, by decide, by decide⟩)
  have hbad := (h 5 2 5 2 1 (by norm_num) (by decide) (by decide)).mp hw
  change (4 < 5 ∧ False ∧ 10 ≤ 10) ∨ (10 < 10 ∧ 5 ≤ 6 ∧ 6 ≤ 5) ∨
    (6 < 5 ∧ 5 ≤ 8 ∧ 8 ≤ 5) at hbad
  omega

def rightFamily : Registration rightArena (type_of% @native_four_scalar_gram_swap_iff) where
  actual := natLe
  bridge := Iff.rfl
  variation := ⟨@native_four_scalar_gram_swap_iff, natFalse, rightRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    rightArena.Law natLe natFalse rightRejected
  dependence := leDependence

def rightRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@native_four_scalar_gram_swap_iff) (Realization natSignature) Unit Unit where
  unitName := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourStaircase.native_four_scalar_gram_swap_iff.information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourStaircase.rightFamily
  realizationSource := none
  generated := false
  arena := .source ⟨rightArena⟩
  objectArena := .source ⟨rightArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rightArena ⟨rightFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourStaircase
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourStaircase
