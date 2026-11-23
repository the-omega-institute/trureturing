import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.FibonacciQutritSingularSupport
import D5.S3.Quantum.Subentropy.StrongSubadditivityRefutation

/-! Source-bound registration of the null-class equality test. -/

set_option autoImplicit false

noncomputable section

open Matrix LeanInformationAudit
open scoped CStarAlgebra ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open _root_.D5.S3.Quantum.Divergence.FibonacciQutritSingularSupport (singular_support_reduction)
open _root_.D5.S3.Quantum.Subentropy.StrongSubadditivityRefutation (diagonalState)
open private matrix from D5.S3.Quantum.Divergence.FibonacciQutritSingularSupport

namespace Reg.D5.S3.Quantum.Divergence.FibonacciQutritSingularSupport

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

universe u

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι]
    (X : ι → DensityState (Fin 3)) (X₀ : DensityState (Fin 3)) (p q : ι → ℝ) (e : ℝ)
    (_ : ∀ i, 0 < q i)
    (_ : ∀ i, (4 / 3 : ℝ) * q i ≤ p i ∧ p i ≤ (7 / 3 : ℝ) * q i) (_ : 0 < e),
    let C := ∑ i, q i • matrix (X i)
    let A := ∑ i, p i • matrix (X i)
    let B := C + e • matrix X₀
    let Δ := (A * (CFC.log B - CFC.log C)).trace.re
    (¬ C.PosDef ∨ C.rank ≤ 2) →
    ∃ Y : ι → DensityState (Fin 2),
      let C₂ := ∑ i, q i • matrix (Y i)
      let A₂ := ∑ i, p i • matrix (Y i)
      (A * (CFC.log A - CFC.log B)).trace.re =
        (A₂ * (CFC.log A₂ - CFC.log C₂)).trace.re - Δ ∧
      0 ≤ Δ ∧ (R.readout () () Δ 0 ↔ C * matrix X₀ = 0) ∧
      ∀ i j, (matrix (Y i) * matrix (Y j)).trace.re =
        (matrix (X i) * matrix (X j)).trace.re

private def ray (j : Fin 3) : DensityState (Fin 3) :=
  diagonalState (fun i => if i = j then 1 else 0)
    (fun i => by split <;> norm_num) (by simp)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hbad
  have hs : ¬ (matrix (ray 0)).PosDef := by
    change ¬ (diagonal fun i : Fin 3 => ((if i = 0 then 1 else 0 : ℝ) : ℂ)).PosDef
    rw [Matrix.posDef_diagonal_iff]
    intro h
    simpa using h 1
  have horth : matrix (ray 0) * matrix (ray 1) = 0 := by
    change diagonal (fun i : Fin 3 => ((if i = 0 then 1 else 0 : ℝ) : ℂ)) *
      diagonal (fun i : Fin 3 => ((if i = 1 then 1 else 0 : ℝ) : ℂ)) = 0
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
    congr 1
    funext i
    fin_cases i <;> simp
  obtain ⟨Y, hY⟩ := @hbad (ULift.{u} Unit) _ (fun _ => ray 0) (ray 1) (fun _ => 4 / 3)
    (fun _ => 1) 1 (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by simpa using hs))
  exact hY.2.2.1.mpr (by simpa using horth)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, fun h => ?_⟩
  have hz := congrFun h 0
  change ((0 : ℝ) = 0) = ((1 : ℝ) = 0) at hz
  exact one_ne_zero (hz ▸ rfl)

def family : Registration arena.{u} (type_of% @singular_support_reduction.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@singular_support_reduction.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

set_option linter.style.longLine false in
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@singular_support_reduction.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.FibonacciQutritSingularSupport.singular_support_reduction.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.FibonacciQutritSingularSupport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.FibonacciQutritSingularSupport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "body",
        "arg", "arg", "fn", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Divergence.FibonacciQutritSingularSupport
