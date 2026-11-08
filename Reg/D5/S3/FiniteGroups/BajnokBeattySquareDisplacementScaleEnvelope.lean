/- Faithful dependent-family source attempt, with no validated binding.
Reuse FourthEnvelope Reg State/signature/actual/zeroRole and the two
unchanged-proof suppliers dependence and zero_ratio_fails. No supplier Reg
copy or evaluated giant binomial fixture is required. Both count roles vary on
the same full family, and whole-role zeroing fails at the actual (5,3,5) state.
sourceSelection/escapeFrom/familyRecord are none; continuation is unknown.
The exact theorem and shared-helper source binding remains unfinished:
https://github.com/the-omega-institute/trureturing/issues/25856 . -/
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattySquareDisplacementScaleEnvelope
import Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthEnvelope
import Reg.Support.DependentFamily

set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementScaleEnvelope
open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementScaleEnvelope
open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementSingleCrossing
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

abbrev State := _root_.Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthEnvelope.State
abbrev signature := _root_.Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthEnvelope.signature
noncomputable abbrev actual :=
  _root_.Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthEnvelope.actual
noncomputable abbrev zeroRole :=
  _root_.Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthEnvelope.zeroRole

def law (R : Realization signature) : Prop :=
  ∀ x : State,
    let nReal : ℝ := (x.p : ℝ)*(2*(x.q : ℝ)*(x.t : ℝ)-1)
    let s : ℝ := (((x.q : ℝ)^2-1)*(x.p : ℝ)^2)/(2*(nReal+1))
    let nu : ℝ := (x.q : ℝ)^2
    let C : ℝ := 2*(nu+1)/(3*(nu-1)^2)
    let E : ℝ := 4/(3*(nu-1)^2)
    let Bcoef : ℝ := 16*(nu^2+nu+1)/(15*(nu-1)^4)
    let G : ℝ := Real.exp s+Real.exp (-nu*s)
    let H : ℝ := C*s^3*(Real.exp s-nu^2*Real.exp (-nu*s))
    let K : ℝ := -E*s^3*(Real.exp s-nu*Real.exp (-nu*s))+
      Bcoef*s^5*(Real.exp s-nu^3*Real.exp (-nu*s))+
      (C^2/2)*s^6*(Real.exp s+nu^4*Real.exp (-nu*s))
    let N : ℝ := nu-1
    (2/3 : ℝ) ≤ s → s ≤ 5/7 →
      |2*(R.readout 0 () x : ℝ)/(R.readout 1 () x : ℝ)-
        G-H/(x.p : ℝ)^2-K/(x.p : ℝ)^4| ≤
        (17/N^3+(8*nu+27*nu^2/100+4*nu^3/375)*Real.exp (-2*nu/3))/(x.p : ℝ)^6

abbrev arena : Arena where
  signature := signature
  Law := law

private theorem bridge : (type_of% actual_square_displacement_scale_envelope) ↔ arena.Law actual := by
  constructor
  · intro h x
    simpa [arena,law,actual,signature,
      _root_.Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthEnvelope.actual,realize]
      using h x.p x.q x.t x.hp5 x.hpo x.hq3 x.hqo x.ht
  · intro h p q t hp5 hpo hq3 hqo ht
    simpa [arena,law,actual,signature,
      _root_.Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthEnvelope.actual,realize]
      using h (⟨p,q,t,hp5,hpo,hq3,hqo,ht⟩ : State)

private theorem actual_law : arena.Law actual :=
  bridge.mp actual_square_displacement_scale_envelope

/-- The new error at (5,3,5) is below the old rejection radius. One existing
quartic estimate at nine suffices; no new exponential or count proof is used. -/
private theorem radius53 :
    (17/(8:ℝ)^3+(8*9+27*9^2/100+4*9^3/375)*Real.exp (-6))/(5:ℝ)^6 ≤
      2439/125000000 := by
  have ht := _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthCoefficient.quartic_tail
    (by norm_num : (9:ℝ) ≤ 9)
  have he : Real.exp (-6:ℝ) ≤ 1/400 := by
    norm_num at ht ⊢
    linarith only [ht]
  have hh := mul_le_mul_of_nonneg_left he
    (by norm_num : (0:ℝ) ≤ 8*9+27*9^2/100+4*9^3/375)
  norm_num at hh ⊢
  linarith only [hh]

private theorem rejected (i : Fin 2) : ¬ arena.Law (zeroRole i) := by
  intro h
  let x : State := ⟨5,3,5,by norm_num,by decide,by norm_num,by decide,by norm_num⟩
  have hh := h x
  have hz :
      |0-(Real.exp (50/73:ℝ)+Real.exp (-9*(50/73:ℝ)))-
        (5/48)*(50/73:ℝ)^3*(Real.exp (50/73:ℝ)-81*Real.exp (-9*(50/73:ℝ)))/25-
        (-(1/48)*(50/73:ℝ)^3*(Real.exp (50/73:ℝ)-9*Real.exp (-9*(50/73:ℝ)))+
          (91/3840)*(50/73:ℝ)^5*(Real.exp (50/73:ℝ)-729*Real.exp (-9*(50/73:ℝ)))+
          ((5/48)^2/2)*(50/73:ℝ)^6*(Real.exp (50/73:ℝ)+6561*Real.exp (-9*(50/73:ℝ))))/625| ≤
        (17/(8:ℝ)^3+(8*9+27*9^2/100+4*9^3/375)*Real.exp (-6))/(5:ℝ)^6 := by
    have hband := hh (by norm_num [x]) (by norm_num [x])
    fin_cases i <;>
      norm_num [arena,law,zeroRole,actual,signature,x,
        _root_.Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthEnvelope.zeroRole,
        _root_.Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthEnvelope.actual,realize]
        at hband ⊢ <;> exact hband
  exact _root_.Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthEnvelope.zero_ratio_fails
    (hz.trans radius53)

noncomputable def source : Registration arena
    (type_of% actual_square_displacement_scale_envelope) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law,zeroRole 0,rejected 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨zeroRole i,?_,rfl,rejected i⟩
      intro j hj
      funext p x
      simp [zeroRole,
        _root_.Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthEnvelope.zeroRole,realize,hj]
    · intro e
      exact nomatch e
  dependence := _root_.Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthEnvelope.dependence

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@actual_square_displacement_scale_envelope)
      (Realization signature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattySquareDisplacementScaleEnvelope.actual_square_displacement_scale_envelope.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementScaleEnvelope.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun i _ x => if i = 0 then (square_return_pair x.p x.q x.t).1
      else (square_return_pair x.p x.q x.t).2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementScaleEnvelope
