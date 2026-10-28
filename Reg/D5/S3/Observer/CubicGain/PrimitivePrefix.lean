import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.PrimitivePrefix
import Reg.Support.SingleDependentReadout

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.CubicGain
open _root_.D5.S3.Observer.CubicGain.CommonWordSensitivity
open _root_.D5.S3.Observer.CubicGain.PrimitivePrefix
open scoped Matrix

noncomputable section
namespace Reg.D5.S3.Observer.CubicGain.PrimitivePrefix

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Fin 3 → List Bool) (fun _ => Fin 4 → Mat)

def actual : Realization signature :=
  realize signature (fun _ _ w => endpoint w) (fun e => nomatch e)

private def fractionalEndpoints : Fin 4 → Mat :=
  ![1, !![1,1;0,1], !![1,1;1/2,2], !![1,2;1,1]]

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fractionalEndpoints) (fun e => nomatch e)

private def levels (A : Fin 4 → Mat) (a b c d : ℤ) (m : Fin 4 → ℤ) : Prop :=
  m 0 = 0 ∧ ∀ i : Fin 4,
    A i *ᵥ (![(a:ℝ),-(b:ℝ)] : Fin 2 → ℝ) =
      ![(a:ℝ),-(b:ℝ)] + (m i:ℝ) • ![(d:ℝ),(c:ℝ)]

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (w : Fin 3 → List Bool) (N : Mat),
    OrientedKernel (R.readout () () w) N ↔
      Module.finrank ℝ (LinearMap.range (prefixMap (R.readout () () w))) = 3 ∧
      ∃ (a b c d : ℤ) (s : ℝ) (m : Fin 4 → ℤ),
        PrimitiveParameters a b c d ∧ 0 < s ∧
        N = s • signedMatrix a b c d ∧ levels (R.readout () () w) a b c d m

private theorem fractional_kernel : OrientedKernel fractionalEndpoints !![1,0;0,0] := by
  have hv (X : Mat) : prefixValue fractionalEndpoints X =
      ![X 1 0,X 0 1/2+X 1 0+X 1 1,X 0 1+2*X 1 0] := by
    ext i
    fin_cases i <;> norm_num [prefixValue,fractionalEndpoints,
      Matrix.trace,Matrix.diag,Matrix.mul_apply,Fin.sum_univ_two] <;> ring
  refine ⟨?_,by norm_num [Matrix.det_fin_two],?_,?_⟩
  · intro h
    have he := congrArg (fun X : Mat => X 0 0) h
    norm_num at he
  · intro X
    rw [hv]
    constructor
    · intro h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      have h2 := congrFun h 2
      simp at h0 h1 h2
      have hq : X 0 1=0 := by linarith
      have hs : X 1 1=0 := by linarith
      refine ⟨X 0 0,?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hq,hs,h0]
    · rintro ⟨v,rfl⟩
      ext i
      fin_cases i <;> simp
  · intro S hS _
    have he : polar S !![1,0;0,0] = S 1 1 := by
      simp [polar,Matrix.det_fin_two,Matrix.add_apply]
      <;> ring
    rw [he]
    exact hS 1 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_,a,b,c,d,s,m,hpar,hs,hgen,hlev⟩ :=
    (h (fun _ => []) !![1,0;0,0]).mp fractional_kernel
  obtain ⟨ha,hb,hc,hd,hab,hcd,ht⟩ := hpar
  have he00 := congrArg (fun X : Mat => X 0 0) hgen
  have he10 := congrArg (fun X : Mat => X 1 0) hgen
  simp only [signedMatrix,Matrix.smul_apply,smul_eq_mul,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one] at he00 he10
  have hcne : (c:ℝ) ≠ 0 := by intro hz; simp [hz] at he00
  have hbc : (b:ℝ)*(c:ℝ)=0 := by
    exact (mul_eq_zero.mp (show s*((b:ℝ)*(c:ℝ))=0 by nlinarith [he10])).resolve_left (ne_of_gt hs)
  have hb0 : b=0 := by exact_mod_cast (mul_eq_zero.mp hbc).resolve_right hcne
  have ha1 : a=1 := by
    rw [hb0] at hab
    have hh : a.natAbs=1 := by simpa using hab
    have hh' : |a|=1 := by exact_mod_cast hh
    rwa [abs_of_nonneg ha] at hh'
  have hlevel := congrFun (hlev.2 (2 : Fin 4)) 1
  change (fractionalEndpoints 2 *ᵥ (![(a:ℝ),-(b:ℝ)] : Fin 2 → ℝ)) 1 =
    (![(a:ℝ),-(b:ℝ)] + (m 2:ℝ) • ![(d:ℝ),(c:ℝ)]) 1 at hlevel
  simp [fractionalEndpoints,Matrix.mulVec,dotProduct,Fin.sum_univ_two,ha1,hb0] at hlevel
  have hi : (1:ℤ)=2*(m 2*c) := by
    exact_mod_cast (show (1:ℝ)=2*((m 2:ℝ)*(c:ℝ)) by linarith [hlevel])
  omega

def family : Registration arena (type_of% @whole_word_primitive_representation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨whole_word_primitive_representation, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (fun _ => []), ![[false],[],[]], ?_⟩
    intro h
    have he := congrArg (fun A : Fin 4 → Mat => A 1 0 0) h
    norm_num [actual,realize,endpoint,
      CommonWordSensitivity.futureProduct,CommonWordSensitivity.actionM] at he

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@whole_word_primitive_representation) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.PrimitivePrefix.whole_word_primitive_representation.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.PrimitivePrefix.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => endpoint w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.PrimitivePrefix
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.Observer.CubicGain.PrimitivePrefix
