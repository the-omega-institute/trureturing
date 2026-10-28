import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.PhaseRigidity
import Reg.Support.SingleDependentReadout

/-! Complete source telescopes for the chronological signed-phase statements. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.CubicGain
open _root_.D5.S3.Observer.CubicGain.CommonWordSensitivity
open _root_.D5.S3.Observer.CubicGain.PrefixKernelSigns
open _root_.D5.S3.Observer.CubicGain.PrimitiveKernelLattice
open _root_.D5.S3.Observer.CubicGain.PhaseRigidity
open scoped Matrix

noncomputable section
namespace Reg.D5.S3.Observer.CubicGain.PhaseRigidity.MixedLevel

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => List Bool) (fun _ => Mat)

def actual : Realization signature :=
  realize signature (fun _ _ u => futureProduct u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : Mat)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (u : List Bool) (p : PrimitiveCoordinates),
    0 < p.a → 0 < p.b → 0 < p.c → 0 < p.d →
    Mixed (futureProduct u *ᵥ p.column) →
    (p.c:ℝ)*(futureProduct u *ᵥ p.column) 0 -
      (p.d:ℝ)*(futureProduct u *ᵥ p.column) 1 = (p.a:ℝ)*p.c+(p.b:ℝ)*p.d →
    R.readout () () u = 1

private def p : PrimitiveCoordinates := ⟨1,1,1,1,by norm_num,by norm_num,by norm_num⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h [] p (by norm_num [p]) (by norm_num [p])
    (by norm_num [p]) (by norm_num [p])
    (by left; norm_num [p,PrimitiveCoordinates.column,futureProduct])
    (by norm_num [p,PrimitiveCoordinates.column,futureProduct])
  change (0 : Mat) = 1 at hh
  exact zero_ne_one hh

def family : Registration arena (type_of% @mixed_level_identity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨mixed_level_identity,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(),[],[false],?_⟩
    intro h
    have he := congrArg (fun A : Mat => A 0 0) h
    norm_num [actual,realize,futureProduct,actionM] at he

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mixed_level_identity) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.PhaseRigidity.mixed_level_identity.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.PhaseRigidity.MixedLevel.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => futureProduct u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.PhaseRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.Observer.CubicGain.PhaseRigidity.MixedLevel

namespace Reg.D5.S3.Observer.CubicGain.PhaseRigidity.WholeClass

private def exampleWords : Fin 3 → List Bool :=
  ![[true,false,true,false,true,false,true,false,true,false,true,false,false,true],
    [false,true,true,false,true,false],
    [true,true,false,true,false,true,false,true,false]]

private def p : PrimitiveCoordinates := ⟨1,5,6,1,by norm_num,by norm_num,by norm_num⟩

private theorem example_endpoints : prefixMatrix exampleWords =
    ![1, !![7,1;6,1], !![13,2;32,5], !![32,5;141,22]] := by
  ext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [prefixMatrix,prefixWord,exampleWords,List.ofFn_succ,
      futureProduct,actionJ,actionM,Matrix.mul_apply,Fin.sum_univ_two]

private theorem example_rank :
    Module.finrank ℝ (LinearMap.range (prefixDifference exampleWords)) = 3 := by
  have hsur : Function.Surjective (prefixDifference exampleWords) := by
    intro y
    let q := (y 1-2*y 0)/20
    let x := y 2-5*y 0-111*q
    let r := y 0-6*x-6*q
    refine ⟨!![x,q;r,0],?_⟩
    ext i
    change Matrix.trace (prefixMatrix exampleWords i.succ * _) - Matrix.trace _ = y i
    rw [example_endpoints]
    fin_cases i <;>
      norm_num [Matrix.trace,Matrix.diag,Matrix.mul_apply,Fin.sum_univ_two,x,q,r] <;> ring
  rw [LinearMap.range_eq_top.mpr hsur]
  simp

private theorem example_generator : OrientedKernelGenerator exampleWords p.matrix := by
  apply whole_class_primitive_lattice.2 exampleWords p (![0,1,2,6] : Fin 4 → ℤ) rfl
  · intro i
    rw [example_endpoints]
    ext j
    fin_cases i <;> fin_cases j <;>
      norm_num [p,PrimitiveCoordinates.column,PrimitiveCoordinates.direction,
        Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  · exact example_rank

private theorem example_nonzero : ∀ i j, p.matrix i j ≠ 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [p,PrimitiveCoordinates.matrix,PrimitiveCoordinates.column,
      PrimitiveCoordinates.row,Matrix.vecMulVec]

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Mat) (fun _ => Mat)

def actual : Realization signature := realize signature (fun _ _ N => N) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : Mat)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (w : Fin 3 → List Bool) (N : Mat),
    OrientedKernelGenerator w N → (∀ i j, N i j ≠ 0) →
    ∃ (p : PrimitiveCoordinates) (scale : ℝ) (m : Fin 4 → ℤ),
      0 < scale ∧ R.readout () () N = scale • p.matrix ∧
      (0 < p.a ∧ 0 < p.b ∧ 0 < p.c ∧ 0 < p.d) ∧
      m 0 = 0 ∧
      (∀ i, prefixMatrix w i *ᵥ p.column = p.column+(m i:ℝ) • p.direction) ∧
      (∀ i, prefixMatrix (conjugateHistory w) i = actionJ * prefixMatrix w i * actionJ) ∧
      actionJ * N * actionJ = scale • (swapCoordinates p).matrix ∧
      (StrictPhase w p m ∨
        StrictPhase (conjugateHistory w) (swapCoordinates p) (fun i => -m i))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨q,scale,m,hs,heq,-⟩ := h exampleWords p.matrix example_generator example_nonzero
  have hh := congrArg Matrix.trace heq
  have ht : (0:ℝ) < (q.a:ℝ)*q.c+(q.b:ℝ)*q.d := by exact_mod_cast q.trace_pos
  have hp := mul_pos hs ht
  simp [rejected,realize,PrimitiveCoordinates.matrix,PrimitiveCoordinates.column,
    PrimitiveCoordinates.row,Matrix.vecMulVec,Matrix.trace,Matrix.diag,Fin.sum_univ_two] at hh
  nlinarith

def family : Registration arena (type_of% @phase_rigidity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨phase_rigidity,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    change (0:Mat) ≠ 1
    exact zero_ne_one

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@phase_rigidity) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.PhaseRigidity.phase_rigidity.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.PhaseRigidity.WholeClass.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.PhaseRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","arg","body","arg","body",
        "arg","body","arg","fn","arg","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.Observer.CubicGain.PhaseRigidity.WholeClass
