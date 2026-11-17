import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.CommonCoefficientPlane
import Reg.Support.DependentFamily

/-! A source-bound audit of the simultaneous native complex pairing. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.CommonCoefficientPlane
open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction
open Matrix Module
open scoped ComplexOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Algebra.CommonCoefficientPlane

abbrev signature : Signature where
  Params := Matrix (Fin 3) (Fin 3) ℂ
  State _ := Fin 3 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 3 → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ T v => T *ᵥ v) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ v => v) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (X : Fin 3 → Matrix (Fin 3) (Fin 5) ℂ)
    (_hX : LinearIndependent ℂ X)
    (_hinj : Function.Injective (stack X).mulVecLin),
    ∃ L : Submodule ℂ (Fin 3 → ℂ), finrank ℂ L = 2 ∧
      ∀ T : Matrix (Fin 3) (Fin 3) ℂ, T.IsHermitian →
        (stack X)ᴴ * Matrix.kronecker T (1 : Matrix (Fin 3) (Fin 3) ℂ) * stack X = 0 →
        ∀ u ∈ L, ∀ v ∈ L, star u ⬝ᵥ R.readout () T v = 0

private def sparse : Fin 3 → Matrix (Fin 3) (Fin 5) ℂ :=
  ![![![1,0,0,0,0], ![0,1,0,0,0], ![0,0,1,0,0]],
    ![![0,0,0,1,0], ![0,0,0,0,1], ![0,0,0,0,0]],
    ![![0,0,0,0,0], ![0,0,0,0,0], ![1,0,0,0,0]]]

private theorem sparse_independent : LinearIndependent ℂ sparse := by
  rw [Fintype.linearIndependent_iff]
  intro z hz r
  have he (i : Fin 3) (j : Fin 5) : ∑ s, z s * sparse s i j = 0 := by
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] using
      congrArg (fun M : Matrix (Fin 3) (Fin 5) ℂ => M i j) hz
  fin_cases r
  · simpa [sparse, Fin.sum_univ_three] using he 0 0
  · simpa [sparse, Fin.sum_univ_three] using he 0 3
  · simpa [sparse, Fin.sum_univ_three] using he 2 0

private theorem sparse_injective : Function.Injective (stack sparse).mulVecLin := by
  intro x y h
  have h0 := congrFun h (0,0)
  have h1 := congrFun h (0,1)
  have h2 := congrFun h (0,2)
  have h3 := congrFun h (1,0)
  have h4 := congrFun h (1,1)
  funext j
  fin_cases j
  · simpa [stack, sparse, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h0
  · simpa [stack, sparse, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h1
  · simpa [stack, sparse, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h2
  · simpa [stack, sparse, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h3
  · simpa [stack, sparse, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h4

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨L, hdim, hL⟩ := h sparse sparse_independent sparse_injective
  have hne : L ≠ ⊥ := by
    intro he
    rw [he] at hdim
    simp at hdim
  obtain ⟨u, hu, hnu⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hz := hL 0 (by simp) (by simp) u hu u hu
  exact hnu (dotProduct_star_self_eq_zero.mp (by simpa [rejected, realize] using hz))

def family : Registration arena (type_of% (@common_plane)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨common_plane, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, 0, ![1,0,0], ?_⟩
    intro he
    have hh := congrFun he 0
    norm_num [actual, realize] at hh

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@common_plane) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Algebra.CommonCoefficientPlane.common_plane.information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.CommonCoefficientPlane.family
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
    (fun _ T v => T *ᵥ v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.CommonCoefficientPlane
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg",
        "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Quantum.Algebra.CommonCoefficientPlane
