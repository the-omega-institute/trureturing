import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail.Endpoint
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Dependent-family registration of the full original eight-binder telescope.
The coordinates [0,1,2,3] retain all original exponents, with both actual
OriginalOrder readouts and their natural seed operands. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail.Endpoint
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.PeriodicShortening
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail
noncomputable section

abbrev Params := Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ

private def arity (p : Params) : ℕ := p.1+p.2.1+p.2.2.1+p.2.2.2
abbrev signature : Signature where
  Params := Params
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output side p := match side with
    | false => List (Fin (arity p)) → Prop
    | true => List (Fin (arity p+1)) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun side p seed => match side with
    | false => OriginalOrder (arity p) seed
    | true => OriginalOrder (arity p+1) seed) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun side _ _ => match side with
    | false => fun _ => False
    | true => fun _ => False) (fun e => nomatch e)
def deleted (side : Bool) : Realization signature :=
  realize signature (fun j p seed =>
    if j=side then rejected.readout j p seed else actual.readout j p seed)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b c d : ℕ) (ha : 2≤a) (had : a≤d) (hdb : d<b) (hbc : b<c),
    ∃ sigma : List (Fin (a+b+c+d)), ∃ j : ℕ,
      j=(if d=a ∧ b=d+1 then b else a+b+1) ∧ j<a+b+c+d ∧
      R.readout false ⟨a,b,c,d⟩ (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      R.readout true ⟨a,b,c,d⟩ (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma j) ∧
      (∀ m n : ℕ, ((((List.replicate m sigma).flatten).take n).map
        (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum ∈
        Set.Icc (0:ℤ) (modulus (a+b+c+d)/2)) ∧
      (∀ m n : ℕ, ((((List.replicate m (earWord (a+b+c+d) sigma j)).flatten).take n).map
        (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum ∈
        Set.Icc (0:ℤ) (modulus (a+b+c+d))) ∧
      (∀ m : ℕ,
        (((List.replicate m sigma).flatten).map
          (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum=0 ∧
        (((List.replicate m (earWord (a+b+c+d) sigma j)).flatten).map
          (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum=0)

private theorem actual_law : arena.Law actual := by
  exact actualSource_third_peak_intermediate_tail_joint_lift
private theorem rejected_law : ¬ arena.Law rejected := by
  intro H
  obtain ⟨sigma,j,_,_,hold,_⟩ := H 2 3 4 2 (by decide) (by decide) (by decide) (by decide)
  simp [rejected,realize] at hold
private theorem deleted_law (side : Bool) : ¬ arena.Law (deleted side) := by
  intro H
  obtain ⟨sigma,j,_,_,hold,hnew,_⟩ := H 2 3 4 2 (by decide) (by decide) (by decide) (by decide)
  cases side
  · simp [deleted,rejected,realize] at hold
  · simp [deleted,rejected,realize] at hnew

-- Dependence changes an actual seed at a fixed admissible original tuple.
-- It is not witnessed merely by comparing actual to an artificial bad family.
private theorem zero_old : OriginalOrder 11 0 (List.finRange 11) := by
  have hf : actualSource 11 0=fun _ => (0:ℤ) := by
    funext i
    fin_cases i <;> norm_num [actualSource,centered,modulus]
  refine ⟨List.Perm.refl _,?_,?_⟩
  · simp [hf]
  · intro n
    simp only [hf, ←List.map_take, List.map_const', List.sum_replicate, nsmul_zero]
    norm_num [modulus]
private theorem zero_new : OriginalOrder 12 0 (List.finRange 12) := by
  have hf : actualSource 12 0=fun _ => (0:ℤ) := by
    funext i
    fin_cases i <;> norm_num [actualSource,centered,modulus]
  refine ⟨List.Perm.refl _,?_,?_⟩
  · simp [hf]
  · intro n
    simp only [hf, ←List.map_take, List.map_const', List.sum_replicate, nsmul_zero]
    norm_num [modulus]
private theorem bad_old : ¬ OriginalOrder 11 2 (List.finRange 11) := by
  intro H
  have hp := H.2.2 10
  norm_num [List.finRange_succ,actualSource,centered,modulus] at hp
private theorem bad_new : ¬ OriginalOrder 12 2 (List.finRange 12) := by
  intro H
  have hp := H.2.2 11
  norm_num [List.finRange_succ,actualSource,centered,modulus] at hp
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro side
  cases side
  · refine ⟨⟨2,3,4,2⟩,0,2,?_⟩
    intro he
    have hp := congrFun he (List.finRange 11)
    change OriginalOrder 11 0 (List.finRange 11)=OriginalOrder 11 2 (List.finRange 11) at hp
    exact bad_old (hp.mp zero_old)
  · refine ⟨⟨2,3,4,2⟩,0,2,?_⟩
    intro he
    have hp := congrFun he (List.finRange 12)
    change OriginalOrder 12 0 (List.finRange 12)=OriginalOrder 12 2 (List.finRange 12) at hp
    exact bad_new (hp.mp zero_new)

def source_registration : Registration arena
    (type_of% (@actualSource_third_peak_intermediate_tail_joint_lift)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro side
      refine ⟨deleted side,?_,rfl,deleted_law side⟩
      intro j hj
      simp [deleted,realize,hj]
    · intro e
      exact nomatch e
  dependence := actual_dependence

-- Source-derived paths: descend eight forall bodies, then Exists sigma and
-- Exists j (arg/body twice). Skip j=cut and j<k with two right And operands;
-- the old readout is the left operand's function. One further right And
-- operand reaches the new readout. In each selected OriginalOrder k seed
-- function the argument operand is the actual natural seed. Operand mode
-- creates a synthetic state, so stateBinder is exactly zero by the contract.
-- Bool.fintype enumerates true before false: enlarged readout precedes old.
def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail.actualSource_third_peak_intermediate_tail_joint_lift)
    (Realization signature) Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail.actualSource_third_peak_intermediate_tail_joint_lift.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail.Endpoint.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail.Endpoint
    definition := none
    coordinates := #[0,1,2,3]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","arg","body","arg","body","arg","arg","arg","fn","arg","fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body","body","body","body","body","body","body","body","arg","body","arg","body","arg","arg","fn","arg","fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms audit
end
end Reg.D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail.Endpoint
