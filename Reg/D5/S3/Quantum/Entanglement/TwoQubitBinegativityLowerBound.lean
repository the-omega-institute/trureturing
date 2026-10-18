import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.TwoQubitBinegativityLowerBound
import Reg.Support.DependentFamily

/-! Source-bound audit of the two-qubit binegativity lower bound. -/

namespace Reg.D5.S3.Quantum.Entanglement.TwoQubitBinegativityLowerBound

open _root_.D5.S3.Quantum.Entanglement.TwoQubitBinegativityLowerBound
open _root_.D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation
  (partialTransposeB IsDensity)
open _root_.D5.S3.Quantum.Entanglement.TwoQubitBinegativityUpperBoundRefutation
  (binegativity vec4)
open _root_.D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the binegativity as the two-qubit matrix varies. -/
abbrev signature : Signature where
  Params := Unit
  State _ := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ σ => binegativity σ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

/-- Retain the density hypothesis and the complete fixed-negativity bound. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, IsDensity σ →
    let ν := 2 * ((partialTransposeB σ)⁻).trace.re
    let c := Real.sqrt (2 * ν * (ν + 1)) - ν
    ν / 2 * (1 + c / Real.sqrt ((1 - c) ^ 2 + c ^ 2)) ≤ r.readout () () σ

private def productState : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  rankOneDensity (vec4 1 0 0 0)

private theorem productState_density : IsDensity productState := by
  constructor
  · exact posSemidef_vecMulVec_self_star _
  · norm_num [productState, rankOneDensity, vec4, Matrix.trace,
      Matrix.vecMulVec_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

private theorem productState_partialTranspose :
    partialTransposeB productState = productState := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [partialTransposeB.eq_1, productState, rankOneDensity, vec4, Matrix.vecMulVec_apply]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hneg : (partialTransposeB productState)⁻ = 0 := by
    rw [productState_partialTranspose]
    exact (CFC.negPart_eq_zero_iff productState productState_density.1.isHermitian).mpr
      productState_density.1.nonneg
  have hbad := h productState productState_density
  dsimp only at hbad
  norm_num [hneg, rejected, realize] at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, -1, ?_⟩
  have hpt0 : partialTransposeB
      (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) = 0 := rfl
  have hpt1 : partialTransposeB
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) = 1 := by
    ext ⟨a, b⟩ ⟨c, d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [partialTransposeB.eq_1]
  have hptneg : partialTransposeB
      (-1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) = -1 := by
    change -(partialTransposeB
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) = -1
    rw [hpt1]
  change binegativity 0 ≠ binegativity (-1)
  norm_num [binegativity, hpt0, hpt1, hptneg, CFC.negPart_neg]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.TwoQubitBinegativityLowerBound.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.TwoQubitBinegativityLowerBound.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.TwoQubitBinegativityLowerBound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ σ => binegativity σ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.TwoQubitBinegativityLowerBound
    definition := some {
      owner := `D5.S3.Quantum.Entanglement.TwoQubitBinegativityLowerBound
      name := `D5.S3.Quantum.Entanglement.TwoQubitBinegativityLowerBound.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.TwoQubitBinegativityLowerBound
