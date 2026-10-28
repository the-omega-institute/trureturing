import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.InteriorNormalForm
import Reg.Support.SingleDependentReadout

/-! Complete dependent source telescopes for primitive integer transitions. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.CubicGain
open _root_.D5.S3.Observer.CubicGain.InteriorNormalForm
open scoped Matrix

noncomputable section

namespace Reg.D5.S3.Observer.CubicGain.InteriorNormalForm.Coefficient

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℤ) (fun _ => ℤ)

def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (12:ℤ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A : ZMat) (x y d c j : ℤ)
    (hA : ∀ i k, 0 ≤ A i k) (hdet : A.det = 1 ∨ A.det = -1)
    (hx : 0 < x) (hy : 0 < y) (hd : 0 < d) (hc : 0 < c)
    (hxy : IsCoprime x y) (_hcd : IsCoprime d c)
    (ht : 0 < x*c-y*d) (hj : 1 ≤ j)
    (hv : A *ᵥ ![x,y] = ![x+j*d,y+j*c]),
    ∃ l : ℤ, 1 ≤ l ∧
      A *ᵥ ![d,c] = A.det • ![d,c] + l • ![x+j*d,y+j*c] ∧
      (x*c-y*d)*A 1 0 = c*(y+j*c-A.det*y)-l*y*(y+j*c) ∧
      (x*c-y*d)*A 0 0 = c*(x+j*d)-A.det*d*y-l*y*(x+j*d) ∧
      (A.det = 1 → (l:ℝ) ≤ (j:ℝ)*c^2/((y:ℝ)*(y+j*c))) ∧
      (A.det = -1 → (l:ℝ) ≤ (c:ℝ)*(1/(y:ℝ)+1/(y+j*c))) ∧
      (A.det = 1 → y < c) ∧ R.readout () () y < 2*c 

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨l,_,_,_,_,_,_,_,hh⟩ := h
    (!![1,1;2,3]) 2 1 1 6 1
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num)
    (by left; norm_num [Matrix.det_fin_two])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one])
    (by norm_num [Int.isCoprime_iff_gcd_eq_one])
    (by norm_num) (by norm_num)
    (by ext i; fin_cases i <;> norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_two])
  change (12:ℤ) < 2*6 at hh
  norm_num at hh

def family : Registration arena (type_of% @transition_certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨transition_certificate,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    norm_num [actual,realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@transition_certificate) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.InteriorNormalForm.transition_certificate.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.InteriorNormalForm.Coefficient.family
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
    owner := `D5.S3.Observer.CubicGain.InteriorNormalForm
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","arg","body","arg","arg","arg","arg","arg","arg","arg","fn","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration
end Reg.D5.S3.Observer.CubicGain.InteriorNormalForm.Coefficient

namespace Reg.D5.S3.Observer.CubicGain.InteriorNormalForm.Last

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
    (hvH : H *ᵥ ![x+j*d,y+j*c] = ![x+(j+h)*d,y+(j+h)*c]),
    j = 1 ∧ y = d ∧ c = x+h*d ∧ R.readout () () H = !![0,1;1,h] 

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h
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
  have he := congrArg (fun A : ZMat => A 0 1) hh.2.2.2
  norm_num [rejected,realize] at he

def family : Registration arena (type_of% @last_transition_rigidity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨last_transition_rigidity,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    change (0:ZMat) ≠ 1
    exact zero_ne_one

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@last_transition_rigidity) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.InteriorNormalForm.last_transition_rigidity.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.InteriorNormalForm.Last.family
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
    owner := `D5.S3.Observer.CubicGain.InteriorNormalForm
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","arg","arg","arg","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration
end Reg.D5.S3.Observer.CubicGain.InteriorNormalForm.Last
