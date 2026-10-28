import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.InteriorPrefixClassification
import Reg.D5.S3.Observer.CubicGain.PhaseRigidity
import Reg.Support.SingleDependentReadout

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.CubicGain
open _root_.D5.S3.Observer.CubicGain.CommonWordSensitivity
open _root_.D5.S3.Observer.CubicGain.PrefixKernelSigns
open _root_.D5.S3.Observer.CubicGain.PrimitiveKernelLattice
open _root_.D5.S3.Observer.CubicGain.PhaseRigidity
open _root_.D5.S3.Observer.CubicGain.InteriorPrefixClassification
open scoped Matrix
noncomputable section

namespace Reg.D5.S3.Observer.CubicGain.InteriorPrefixClassification.WholeClass
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (-1:ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (w : Fin 3 → List Bool) (N : Mat)
    (hG : OrientedKernelGenerator w N) (hn : ∀ i j, N i j ≠ 0),
    ∃ (p : PrimitiveCoordinates) (scale : ℝ) (m : Fin 4 → ℤ),
      0 < R.readout () () scale ∧ N = scale • p.matrix ∧ m 0 = 0 ∧
      (∀ i, prefixMatrix w i *ᵥ p.column = p.column+(m i:ℝ) • p.direction) ∧
      (∀ i, prefixMatrix (conjugateHistory w) i = actionJ*prefixMatrix w i*actionJ) ∧
      actionJ*N*actionJ = scale • (swapCoordinates p).matrix ∧
      ((∃ A : ZMat, (∀ i j, 0 ≤ A i j) ∧ (A.det = 1 ∨ A.det = -1) ∧
          real A = prefixMatrix w 1) ∧
        (∃ A : ZMat, (∀ i j, 0 ≤ A i j) ∧ (A.det = 1 ∨ A.det = -1) ∧
          real A = prefixMatrix (conjugateHistory w) 1)) ∧
      (ParameterForm w p m ∨
        ParameterForm (conjugateHistory w) (swapCoordinates p) (fun i => -m i))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  open _root_.Reg.D5.S3.Observer.CubicGain.PhaseRigidity.WholeClass in
    obtain ⟨q,s,m,hs,_⟩ := h exampleWords p.matrix example_generator example_nonzero
  change (0:ℝ) < -1 at hs
  norm_num at hs
def family : Registration arena (type_of% @interior_necessity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨interior_necessity,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    norm_num [actual,realize]
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@interior_necessity) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.InteriorPrefixClassification.interior_necessity.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.InteriorPrefixClassification.WholeClass.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.InteriorPrefixClassification
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","arg","body","arg","body","arg","body","fn","arg","arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


#print axioms family
#print axioms registration
end Reg.D5.S3.Observer.CubicGain.InteriorPrefixClassification.WholeClass

namespace Reg.D5.S3.Observer.CubicGain.InteriorPrefixClassification.Multipliers
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ZMat) (fun _ => ZMat)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (0:ZMat)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (K H : ZMat) (x y d c j h : ℤ)
    (hK : ∀ i k, 0 ≤ K i k) (hH : ∀ i k, 0 ≤ H i k)
    (hdK : K.det = 1 ∨ K.det = -1) (hdH : H.det = 1 ∨ H.det = -1)
    (hx : d < x) (hy : 0 < y) (hd : 0 < d) (hc : 0 < c)
    (hxy : IsCoprime x y) (hcd : IsCoprime d c)
    (ht : 0 < x*c-y*d) (hj : 1 ≤ j) (hh : 1 ≤ h)
    (hvK : K *ᵥ ![x,y] = ![x+j*d,y+j*c])
    (hvH : H *ᵥ ![x+j*d,y+j*c] = ![x+(j+h)*d,y+(j+h)*c])
    (hind : H*K ≠ (2:ℤ) • K - 1),
    j = 1 ∧ y = d ∧ IsCoprime x d ∧ ∃ n σ : ℤ,
      1 ≤ n ∧ (σ = 1 ∨ σ = -1) ∧
      h = n*(x+d)+σ ∧ c = x+h*d ∧
      2 ≤ 1+n*d ∧ K = !![1,1;1+n*d,1+n*d+σ] ∧ R.readout () () H = !![0,1;1,h]
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_,_,_,n,s,_,_,_,_,_,_,hh⟩ := h
    (!![1,1;2,3]) (!![0,1;1,4]) 2 1 1 6 1 4
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num)
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num)
    (by left; norm_num [Matrix.det_fin_two])
    (by right; norm_num [Matrix.det_fin_two])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one])
    (by norm_num [Int.isCoprime_iff_gcd_eq_one])
    (by norm_num) (by norm_num) (by norm_num)
    (by ext i; fin_cases i <;> norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_two])
    (by ext i; fin_cases i <;> norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_two])
    (by intro he; have hi := congrArg (fun A : ZMat => A 0 0) he
        norm_num [Matrix.mul_apply,Fin.sum_univ_two,Matrix.ofNat_apply] at hi)
  have he := congrArg (fun A : ZMat => A 0 1) hh
  norm_num [rejected,realize] at he
def family : Registration arena (type_of% @two_transition_parameters) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨two_transition_parameters,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    norm_num [actual,realize]
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@two_transition_parameters) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.InteriorPrefixClassification.two_transition_parameters.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.InteriorPrefixClassification.Multipliers.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.InteriorPrefixClassification
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","arg","arg","arg","arg","body","arg","body","arg","arg","arg","arg","arg","arg","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


#print axioms family
#print axioms registration
end Reg.D5.S3.Observer.CubicGain.InteriorPrefixClassification.Multipliers

