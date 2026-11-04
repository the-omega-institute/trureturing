import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.PrefixKernelSigns
import Reg.Support.SingleDependentReadout

/-! The original full telescope, with the generator trace as its dependent readout. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.CubicGain
open _root_.D5.S3.Observer.CubicGain.CommonWordSensitivity
open _root_.D5.S3.Observer.CubicGain.PrefixKernelSigns
open scoped Matrix

noncomputable section
namespace Reg.D5.S3.Observer.CubicGain.PrefixKernelSigns

private def exampleWords : Fin 3 → List Bool := ![[false,true], [true,false], [true]]
private def E : Mat := !![1,0;0,0]

private theorem example_endpoints :
    prefixMatrix exampleWords = ![1, !![1,1;0,1], !![1,1;1,2], !![1,2;1,1]] := by
  ext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [prefixMatrix, prefixWord, exampleWords, List.ofFn_succ,
      futureProduct, actionJ, actionM, Matrix.mul_apply, Fin.sum_univ_two]

private theorem example_generator : OrientedKernelGenerator exampleWords E := by
  constructor
  · intro hz
    have hh := congrArg (fun X : Mat => X 0 0) hz
    norm_num [E] at hh
  · have he : E = Matrix.vecMulVec (![1,0] : Fin 2 → ℝ) (![1,0] : Fin 2 → ℝ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [E, Matrix.vecMulVec]
    have hle : E.rank ≤ 1 := by rw [he]; exact Matrix.rank_vecMulVec_le _ _
    have hs : E.submatrix (fun _ : Fin 1 => (0 : Fin 2))
        (fun _ : Fin 1 => (0 : Fin 2)) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [E, Matrix.submatrix]
    have hge := Matrix.rank_submatrix_le E (fun _ : Fin 1 => (0 : Fin 2))
      (fun _ : Fin 1 => (0 : Fin 2))
    rw [hs, Matrix.rank_one] at hge
    norm_num at hge
    omega
  · intro X
    constructor
    · intro hx
      have h0 := congrFun hx 0
      have h1 := congrFun hx 1
      have h2 := congrFun hx 2
      change Matrix.trace (prefixMatrix exampleWords _ * X) - Matrix.trace X = 0 at h0 h1 h2
      rw [example_endpoints] at h0 h1 h2
      norm_num [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two] at h0 h1 h2
      refine ⟨X 0 0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [E] <;> linarith
    · rintro ⟨v, rfl⟩
      ext i
      change Matrix.trace (prefixMatrix exampleWords i.succ * (v • E)) -
        Matrix.trace (v • E) = 0
      rw [example_endpoints]
      fin_cases i <;> norm_num [E, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
  · intro S hS
    have hh := hS.1 1 1
    simp [determinantPolar, E, Matrix.det_fin_two]
    nlinarith

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Mat) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ N => Matrix.trace N) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (w : Fin 3 → List Bool) (N : Mat), OrientedKernelGenerator w N →
    (0 ≤ N 0 0 ∧ 0 ≤ N 1 1 ∧ N 0 1 ≤ 0 ∧ N 1 0 ≤ 0) ∧
      0 < R.readout () () N ∧ Function.Bijective (prefixTrace w)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h exampleWords E example_generator).2.1
  norm_num [rejected, realize] at hh

def family : Registration arena (type_of% @kernel_signs_positive_trace_invertible) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨kernel_signs_positive_trace_invertible, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, E, ?_⟩
    change Matrix.trace (0 : Mat) ≠ Matrix.trace E
    norm_num [E, Matrix.trace, Matrix.diag, Fin.sum_univ_two, Pi.zero_apply]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kernel_signs_positive_trace_invertible) (Realization signature) Unit Unit := {
  unitName :=
    `D5.S3.Observer.CubicGain.PrefixKernelSigns.kernel_signs_positive_trace_invertible.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.PrefixKernelSigns.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => Matrix.trace N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.PrefixKernelSigns
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.Observer.CubicGain.PrefixKernelSigns
