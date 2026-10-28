import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.InteriorForwardRealization
import Reg.D5.S3.Observer.CubicGain.PhaseRigidity
import Reg.Support.SingleDependentReadout

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.CubicGain
open _root_.D5.S3.Observer.CubicGain.CommonWordSensitivity
open _root_.D5.S3.Observer.CubicGain.PrefixKernelSigns
open _root_.D5.S3.Observer.CubicGain.PrimitiveKernelLattice
open _root_.D5.S3.Observer.CubicGain.PhaseRigidity
open _root_.D5.S3.Observer.CubicGain.InteriorNormalForm
open _root_.D5.S3.Observer.CubicGain.InteriorPrefixClassification
open _root_.D5.S3.Observer.CubicGain.InteriorForwardRealization
open scoped Matrix
noncomputable section
namespace Reg.D5.S3.Observer.CubicGain.InteriorForwardRealization
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℤ) (fun _ => ℤ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (0:ℤ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x d m n σ : ℤ) (A : ZMat)
    (hd : 1 ≤ d) (hx : d < x) (hxd : IsCoprime x d)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hσ : σ = 1 ∨ σ = -1)
    (ha : 1 ≤ x-m*d)
    (hab : IsCoprime (x-m*d) (m*(x+(n*(x+d)+σ)*d)-d))
    (hA : ∀ i j, 0 ≤ A i j) (hdet : A.det = 1 ∨ A.det = -1)
    (hfirst : A *ᵥ ![x-m*d,-(m*(x+(n*(x+d)+σ)*d)-d)] = ![x,d])
    (hrank : Module.finrank ℝ (LinearMap.range
      (endpointDifference (real A) (!![1,1;((1+n*d:ℤ):ℝ),((1+n*d+σ:ℤ):ℝ)])
        (!![0,1;1,((n*(x+d)+σ:ℤ):ℝ)]))) = 3),
    let a := x-m*d
    let h := n*(x+d)+σ
    let c := x+h*d
    let b := m*c-d
    let Q := 1+n*d
    ∃ (w : Fin 3 → List Bool) (p : PrimitiveCoordinates),
      (p.a:ℤ) = a ∧ (p.b:ℤ) = b ∧ (p.c:ℤ) = c ∧ (p.d:ℤ) = d ∧
      0 < R.readout () () a ∧ 0 < b ∧ 0 < c ∧ 0 < h ∧ 2 ≤ Q ∧
      prefixMatrix w 1 = real A ∧
      futureProduct (w 1) = !![1,1;(Q:ℝ),((Q+σ:ℤ):ℝ)] ∧
      futureProduct (w 2) = !![0,1;1,(h:ℝ)] ∧
      w 2 = [true] ++ lowerWord h.toNat ∧
      (σ = 1 → w 1 = [false,true] ++ lowerWord Q.toNat) ∧
      (σ = -1 → w 1 = [true,false,true] ++ lowerWord (Q-1).toNat) ∧
      (∀ i, prefixMatrix w i *ᵥ p.column = p.column+
        ((![0,m,m+1,m+1+h] : Fin 4 → ℤ) i:ℝ) • p.direction) ∧
      OrientedKernelGenerator w p.matrix ∧ ParameterForm w p (![0,m,m+1,m+1+h]) ∧
      ∀ S : Mat, PositiveRankOne S → ∃ f ℓ : Fin 2 → ℝ,
        Positive f ∧ Positive ℓ ∧ S = Matrix.vecMulVec f ℓ ∧
        (∀ u : List Bool, Positive (futureProduct u *ᵥ f)) ∧
        ∀ k δ : ℝ, ∀ i : Fin 4,
          (1+(i.val:ℝ)*k)*(ℓ ⬝ᵥ (prefixMatrix w i *ᵥ f))+δ =
          (1+(i.val:ℝ)*k)*Matrix.trace (prefixMatrix w i*S)+δ
private theorem example_rank : Module.finrank ℝ (LinearMap.range
    (endpointDifference (real (!![7,1;6,1] : ZMat)) (!![1,1;2,3]) (!![0,1;1,4]))) = 3 := by
  have he : endpointDifference (real (!![7,1;6,1] : ZMat)) (!![1,1;2,3]) (!![0,1;1,4]) =
      prefixDifference PhaseRigidity.WholeClass.exampleWords := by
    ext X i
    change Matrix.trace ((![real (!![7,1;6,1] : ZMat),
      (!![1,1;2,3] : Mat)*real (!![7,1;6,1] : ZMat),
      (!![0,1;1,4] : Mat)*((!![1,1;2,3] : Mat)*real (!![7,1;6,1] : ZMat))] : Fin 3 → Mat) i*X)-Matrix.trace X = _
    change _ = Matrix.trace (prefixMatrix PhaseRigidity.WholeClass.exampleWords i.succ*X)-Matrix.trace X
    rw [PhaseRigidity.WholeClass.example_endpoints]
    fin_cases i <;> norm_num [real,Matrix.trace,Matrix.diag,Matrix.mul_apply,Fin.sum_univ_two] <;> ring
  rw [he]
  exact PhaseRigidity.WholeClass.example_rank
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hlaw
  obtain ⟨w,p,_,_,_,_,hpos,_⟩ := hlaw 2 1 1 1 1 (!![7,1;6,1])
    (by norm_num) (by norm_num) (by norm_num [Int.isCoprime_iff_gcd_eq_one])
    (by norm_num) (by norm_num) (by left; rfl) (by norm_num)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one])
    (by intro i j; fin_cases i <;> fin_cases j <;> norm_num)
    (by left; norm_num [Matrix.det_fin_two])
    (by ext i; fin_cases i <;> norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_two])
    (by convert example_rank using 1 <;> norm_num)
  change (0:ℤ) < 0 at hpos
  exact lt_irrefl _ hpos
def family : Registration arena (type_of% @admitted_parameters_realize) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨admitted_parameters_realize,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    norm_num [actual,realize]
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@admitted_parameters_realize) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.InteriorForwardRealization.admitted_parameters_realize.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.InteriorForwardRealization.family
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
    owner := `D5.S3.Observer.CubicGain.InteriorForwardRealization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","arg","body","arg","body","arg","arg","arg","arg","fn","arg","arg"]
      stateBinder := 18
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


#print axioms family
#print axioms registration
end Reg.D5.S3.Observer.CubicGain.InteriorForwardRealization
