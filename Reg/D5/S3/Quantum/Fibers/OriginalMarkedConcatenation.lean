import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fibers.OriginalMarkedConcatenation
import Reg.Support.DependentFamily

/-! Source-bound attempt for native chronological marked composition. -/
noncomputable section
open D5.S3.Quantum.Fibers
open D5.S3.Quantum.Fibers.OriginalControlMarkedJump
open D5.S3.Quantum.Fibers.OriginalControlComposition
open D5.S3.Quantum.Fibers.OriginalMarkedConcatenation
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set MeasureTheory
open scoped BigOperators Matrix
namespace Reg.D5.S3.Quantum.Fibers.OriginalMarkedConcatenation
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option relaxedAutoImplicit false

structure Input where
  first : Leg
  second : Leg
  beta : ℝ
  parity : ℤ
  phases : Fin 5 → ℝ

abbrev signature : Signature where
  Params := Unit
  State := fun _ => Input
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Measure Leg.Record
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ d => markedLaw d.first.c d.first.x d.beta (d.first.duration+d.second.duration)
    d.parity d.phases (concatenate d.first.height d.second.height d.first.duration))
  (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law obs := ∀ (L R : Leg) (hC : R.c=L.c) (hj : L.y=R.x)
    (chi beta : ℝ) (m : ℤ) (theta : Fin 5 → ℝ),
    OriginalControl (L.c,L.c,1-2*L.c) (L.duration+R.duration)
      (concatenate L.height R.height L.duration) (fun _ => chi) ∧
    ∀ E : Set Leg.Record, MeasurableSet E →
      obs.readout () () ⟨L,R,beta,m,theta⟩ E =
      (if Sum.inl () ∈ E then
        ENNReal.ofReal (L.survival L.duration*R.survival R.duration) else 0) +
      (∑ i : Fin 5, ∫⁻ t in (Ioc 0 L.duration) ∩ {t | Sum.inr (i,t) ∈ E},
        ENNReal.ofReal (L.density t i)) +
      ENNReal.ofReal (L.survival L.duration) *
        (∑ i : Fin 5, ∫⁻ t in (Ioc L.duration (L.duration+R.duration)) ∩
            {t | Sum.inr (i,t) ∈ E},
          ENNReal.ofReal (R.density (t-L.duration) i))

private def wait : Leg where
  c := 3/8
  x := 1/4
  y := 1/4
  duration := 1
  c_lt := by norm_num
  x_pos := by norm_num
  x_lt := by norm_num
  y_pos := by norm_num
  y_lt := by norm_num
  duration_pos := by norm_num
private def move : Leg where
  c := 3/8
  x := 1/4
  y := 5/16
  duration := 1
  c_lt := by norm_num
  x_pos := by norm_num
  x_lt := by norm_num
  y_pos := by norm_num
  y_lt := by norm_num
  duration_pos := by norm_num

private theorem wait_survival : wait.survival wait.duration=1 := by
  have he := (wait.affine_marked_probability 0 0 0 (fun _ => 0)).2.2.2.2.2.2.1
    wait.duration ⟨wait.duration_pos.le,le_rfl⟩
  norm_num [wait,Leg.height,Leg.speed] at he ⊢
  exact he
private theorem move_survival : move.survival move.duration=4/5 := by
  have he := (move.affine_marked_probability 0 0 0 (fun _ => 0)).2.2.2.2.2.2.1
    move.duration ⟨move.duration_pos.le,le_rfl⟩
  norm_num [move,Leg.height,Leg.speed] at he ⊢
  exact he
private theorem success_measurable : MeasurableSet ({Sum.inl ()} : Set Leg.Record) := by
  simpa only [Set.image_singleton] using
    (show MeasurableSet ({()} : Set Unit) from measurableSet_singleton ()).inl_image

private theorem actual_law : arena.Law actual := by
  intro L R hC hj chi beta m theta
  exact native_marked_join L R hC hj chi beta m theta
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have he := (h wait wait rfl rfl 0 0 0 (fun _ => 0)).2
    {Sum.inl ()} success_measurable
  have hempty (i : Fin 5) : {t : ℝ | Sum.inr (i,t) ∈ ({Sum.inl ()} : Set Leg.Record)}=∅ := by
    ext t
    simp
  simp [rejected,realize,hempty,wait_survival] at he

private theorem success_mass (L R : Leg) (hC : R.c=L.c) (hj : L.y=R.x) :
    markedLaw L.c L.x 0 (L.duration+R.duration) 0 (fun _ => 0)
      (concatenate L.height R.height L.duration) {Sum.inl ()}=
      ENNReal.ofReal (L.survival L.duration*R.survival R.duration) := by
  have he := (native_marked_join L R hC hj 0 0 0 (fun _ => 0)).2
    {Sum.inl ()} success_measurable
  have hempty (i : Fin 5) : {t : ℝ | Sum.inr (i,t) ∈ ({Sum.inl ()} : Set Leg.Record)}=∅ := by
    ext t
    simp
  simpa [hempty] using he

def registration : Registration arena (type_of% (@native_marked_join)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,rejected,rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_fails⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(),⟨wait,wait,0,0,fun _ => 0⟩,⟨wait,move,0,0,fun _ => 0⟩,?_⟩
    intro he
    have hm := congrArg (fun mu : Measure Leg.Record => mu {Sum.inl ()}) he
    change markedLaw wait.c wait.x 0 (wait.duration+wait.duration) 0 (fun _ => 0)
      (concatenate wait.height wait.height wait.duration) {Sum.inl ()}=
      markedLaw wait.c wait.x 0 (wait.duration+move.duration) 0 (fun _ => 0)
        (concatenate wait.height move.height wait.duration) {Sum.inl ()} at hm
    rw [success_mass wait wait rfl rfl,success_mass wait move rfl rfl,
      wait_survival,move_survival] at hm
    have hr := congrArg ENNReal.toReal hm
    norm_num at hr

noncomputable def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@native_marked_join)
    (type_of% (realize signature
      (fun _ _ d => markedLaw d.first.c d.first.x d.beta (d.first.duration+d.second.duration)
        d.parity d.phases (concatenate d.first.height d.second.height d.first.duration))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.OriginalMarkedConcatenation.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.OriginalMarkedConcatenation.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ d => markedLaw d.first.c d.first.x d.beta (d.first.duration+d.second.duration)
      d.parity d.phases (concatenate d.first.height d.second.height d.first.duration))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.OriginalMarkedConcatenation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body",
        "arg","body","body","fn","arg","fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


namespace Native
structure Input where
  c : ℝ
  firstTime : ℝ
  secondTime : ℝ
  firstHeight : ℝ → ℝ
  secondHeight : ℝ → ℝ

abbrev signature : Signature where
  Params := Unit
  State := fun _ => Input
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def value (d : Input) : ℝ := survival d.c
  (concatenate d.firstHeight d.secondHeight d.firstTime) (d.firstTime+d.secondTime)
def actual : Realization signature := realize signature
  (fun _ _ d => value d) (fun e => nomatch e)
def changed (i : Fin 3) : Realization signature := realize signature
  (fun j _ d => if j=i then 0 else value d) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law obs := ∀ (c T s a chi : ℝ) (k K : ℝ → ℝ)
    (hc : c < 1 / 2) (hT : 0 ≤ T) (hs : 0 ≤ s) (hj : k T = K 0)
    (ha : a ∈ Ioo 0 c) (hb : k T ∈ Ioo 0 c) (hk : K s ∈ Ioo 0 c)
    (h0 : OriginalControl (c, c, 1-2 * c) T k (fun _ => chi))
    (h1 : OriginalControl (c, c, 1-2 * c) s K (fun _ => chi)),
    (∀ᵐ t : ℝ ∂volume, hazard c (concatenate k K T) t = if t ≤ T then hazard c k t else hazard c K (t-T)) ∧
    obs.readout 0 () ⟨c,T,s,k,K⟩ = survival c k T * survival c K s ∧
    (∀ psi : Fin 5 → ℂ,
      successfulKraus c (k T) (K s) (survival c K s) *ᵥ
        (successfulKraus c a (k T) (survival c k T) *ᵥ psi) = successfulKraus c a (K s) (obs.readout 1 () ⟨c,T,s,k,K⟩) *ᵥ psi) ∧
    (∀ (g : Fin 5 → ℝ) (i : Fin 5) (psi : Fin 5 → ℂ),
      jumpKraus c (k T) (K s) (survival c K s) g i *ᵥ
        (successfulKraus c a (k T) (survival c k T) *ᵥ psi) = jumpKraus c a (K s) (obs.readout 2 () ⟨c,T,s,k,K⟩) g i *ᵥ psi)

private theorem actual_law : arena.Law actual := by
  intro c T s a chi k K hc hT hs hj ha hb hk h0 h1
  exact native_concatenation c T s a chi k K hc hT hs hj ha hb hk h0 h1

private theorem changed_fails (i : Fin 3) : ¬ arena.Law (changed i) := by
  intro h
  have h0 := (wait.affine_marked_probability 0 0 0 (fun _ => 0)).1
  have hj : wait.height wait.duration=wait.height 0 := by
    norm_num [wait,Leg.height,Leg.speed]
  have hb : wait.height wait.duration ∈ Ioo 0 wait.c := by
    norm_num [wait,Leg.height,Leg.speed]
  have hh := h wait.c wait.duration wait.duration wait.x 0 wait.height wait.height
    wait.c_lt wait.duration_pos.le wait.duration_pos.le hj ⟨wait.x_pos,wait.x_lt⟩ hb hb h0 h0
  fin_cases i
  · have he := hh.2.1
    change 0=survival wait.c wait.height wait.duration*survival wait.c wait.height wait.duration at he
    rw [leg_survival wait,wait_survival] at he
    norm_num at he
  · have he := hh.2.2.1 (fun _ => 1)
    have he0 := congrFun he 0
    simp [changed,realize,leg_survival wait,wait_survival] at he0
    norm_num [successful_action,live,wait,Leg.height,Leg.speed,p,
      FiniteRectangleTransport.probability] at he0
  · have he := hh.2.2.2 (fun _ => 1) 0 (fun _ => 1)
    have he0 := congrFun he 0
    simp [changed,realize,leg_survival wait,wait_survival] at he0
    norm_num [jump_action,successful_action,jump,live,wait,Leg.height,Leg.speed,p,
      FiniteRectangleTransport.probability] at he0

private theorem wait_value : value ⟨wait.c,wait.duration,wait.duration,wait.height,wait.height⟩=1 := by
  have h0 := (wait.affine_marked_probability 0 0 0 (fun _ => 0)).1
  have hj : wait.height wait.duration=wait.height 0 := by norm_num [wait,Leg.height,Leg.speed]
  have hb : wait.height wait.duration ∈ Ioo 0 wait.c := by norm_num [wait,Leg.height,Leg.speed]
  have he := (native_concatenation wait.c wait.duration wait.duration wait.x 0 wait.height wait.height
    wait.c_lt wait.duration_pos.le wait.duration_pos.le hj ⟨wait.x_pos,wait.x_lt⟩ hb hb h0 h0).2.1
  simpa [value,leg_survival wait,wait_survival] using he
private theorem move_value : value ⟨wait.c,wait.duration,move.duration,wait.height,move.height⟩=4/5 := by
  have h0 := (wait.affine_marked_probability 0 0 0 (fun _ => 0)).1
  have h1 := (move.affine_marked_probability 0 0 0 (fun _ => 0)).1
  have hj : wait.height wait.duration=move.height 0 := by norm_num [wait,move,Leg.height,Leg.speed]
  have hb : wait.height wait.duration ∈ Ioo 0 wait.c := by norm_num [wait,Leg.height,Leg.speed]
  have hk : move.height move.duration ∈ Ioo 0 wait.c := by norm_num [wait,move,Leg.height,Leg.speed]
  have he := (native_concatenation wait.c wait.duration move.duration wait.x 0 wait.height move.height
    wait.c_lt wait.duration_pos.le move.duration_pos.le hj ⟨wait.x_pos,wait.x_lt⟩ hb hk h0 h1).2.1
  have hm : survival wait.c move.height move.duration = 4/5 := by
    change survival move.c move.height move.duration = 4/5
    rw [leg_survival move,move_survival]
  simpa [value,leg_survival wait,wait_survival,hm] using he

def registration : Registration arena (type_of% (@native_concatenation)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,changed 0,changed_fails 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨changed i,?_,rfl,changed_fails i⟩
      intro j hj
      funext param d
      change value d = if (j : Fin 3) = i then 0 else value d
      rw [ite_eq_right (show (j : Fin 3) ≠ i from hj)]
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(),⟨wait.c,wait.duration,wait.duration,wait.height,wait.height⟩,
      ⟨wait.c,wait.duration,move.duration,wait.height,move.height⟩,?_⟩
    intro he
    change value ⟨wait.c,wait.duration,wait.duration,wait.height,wait.height⟩=
      value ⟨wait.c,wait.duration,move.duration,wait.height,move.height⟩ at he
    rw [wait_value,move_value] at he
    norm_num at he

noncomputable def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@native_concatenation)
    (type_of% (realize signature (fun _ _ d => value d) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.OriginalMarkedConcatenation.Native.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.OriginalMarkedConcatenation.Native.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => value d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.OriginalMarkedConcatenation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body",
        "body","body","body","body","body","body","body","body",
        "arg","fn","arg","fn","arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Native

end Reg.D5.S3.Quantum.Fibers.OriginalMarkedConcatenation
