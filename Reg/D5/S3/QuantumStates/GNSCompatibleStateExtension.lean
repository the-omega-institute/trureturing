import D5.S3.QuantumStates.GNSCompatibleStateExtension
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

noncomputable section
open scoped CStarAlgebra ComplexOrder InnerProductSpace MatrixOrder
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.QuantumStates.GNSCompatibleStateExtension
namespace Reg.D5.S3.QuantumStates.GNSCompatibleStateExtension
universe u
abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (S : ℕ → StarSubalgebra ℂ A) (hS : Monotone S)
    [∀ n, IsClosed (S n : Set A)] [∀ n, PartialOrder (S n)] [∀ n, StarOrderedRing (S n)]
    (ω : ∀ n, (S n) →ₚ[ℂ] ℂ) (hω : ∀ n, ω n 1 = 1)
    (hcompat : ∀ n m (hnm : n ≤ m) (a : S n),
      ω m (StarSubalgebra.inclusion (hS hnm) a) = ω n a)
    (hdense : Dense (⋃ n, (S n : Set A))),
    ∃! f : A →ₚ[ℂ] ℂ, f 1 = 1 ∧
      (∀ n (a : S n), R.readout () () (f a) (ω n a)) ∧ (∀ a : A, ‖f a‖ ≤ ‖a‖) ∧
      ‖cyclicVector f‖ = 1 ∧
      (∀ a : A, inner ℂ (cyclicVector f) (f.gnsStarAlgHom a (cyclicVector f)) = f a) ∧
      DenseRange (fun a : A => f.gnsStarAlgHom a (cyclicVector f))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let A := CStarMatrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ
  let S : ℕ → StarSubalgebra ℂ A := fun _ => ⊤
  letI hclosed : ∀ n, IsClosed (S n : Set A) := fun _ => by simp [S]
  letI hstar : ∀ n, StarOrderedRing (S n) := fun n =>
    StarOrderedRing.of_nonneg_iff' (fun hab c => by simpa only [add_comm] using add_le_add_left hab c)
      (fun a => by
      change 0 ≤ (a : A) ↔ ∃ b : S n, a = star b * b
      constructor
      · intro ha
        have hM := map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ha
        obtain ⟨b,hb⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM
        refine ⟨⟨CStarMatrix.ofMatrixStarAlgEquiv b,by simp [S]⟩,?_⟩
        apply Subtype.ext
        apply CStarMatrix.ofMatrixStarAlgEquiv.symm.injective
        change CStarMatrix.ofMatrix.symm (a : A) = star b * b
        exact hb
      · rintro ⟨b,hb⟩
        rw [congrArg Subtype.val hb]
        exact star_mul_self_nonneg (b : A))
  let k : ULift.{u} Unit := ULift.up ()
  let eval : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ →ₗ[ℂ] ℂ := {
    toFun := fun X => X k k
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  let ω : ∀ n, (S n) →ₚ[ℂ] ℂ := fun n => {
    toLinearMap := eval.comp (CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
      (S n).toSubalgebra.val.toLinearMap)
    monotone' := by
      intro a b hab
      have hp : 0 ≤ (b : A) - (a : A) := sub_nonneg.mpr hab
      have hM := map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hp
      have hh := (Matrix.nonneg_iff_posSemidef.mp hM).diag_nonneg (i := k)
      exact sub_nonneg.mp hh }
  have hs : Monotone S := fun _ _ _ => le_rfl
  have hc : Dense (⋃ n, (S n : Set A)) := by
    rw [show (⋃ n, (S n : Set A)) = Set.univ by ext a; simp [S]]
    exact dense_univ
  obtain ⟨f,hf,_⟩ := @h A inferInstance inferInstance inferInstance S hs
    hclosed (fun n => inferInstance) hstar ω (fun n => by
      change (CStarMatrix.ofMatrix.symm (1 : A)) k k = 1
      change (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) k k = 1
      simp)
    (fun _ _ _ _ => rfl) hc
  exact hf.2.1 0 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  intro h
  have : (0 : ℂ) = 1 := (congrFun h 1).mpr rfl
  exact zero_ne_one this

def family : Registration arena.{u} (type_of% (@compatible_state_extension.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@compatible_state_extension, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@compatible_state_extension.{u})
    (type_of% (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.QuantumStates.GNSCompatibleStateExtension.compatible_state_extension.__information_unit
  realizationName := `Reg.D5.S3.QuantumStates.GNSCompatibleStateExtension.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumStates.GNSCompatibleStateExtension
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","arg","arg","fn","arg","body","body","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
end Reg.D5.S3.QuantumStates.GNSCompatibleStateExtension
