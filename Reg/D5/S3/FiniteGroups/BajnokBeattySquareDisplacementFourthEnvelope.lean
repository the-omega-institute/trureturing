/- Dependent-family registration; source binding remains unfinished.
The full original domain is represented by State, with the band conditional in
Law. Both roles are the actual square_return_pair coordinates. Whole-role
zeroing fails at (5,3,5); actual variation uses (5,3,4) and (5,3,5) and the
unchanged-proof export Reg.UpperEnvelope.choose_grow_diagonal. No binomial
fixture is evaluated. sourceSelection and escapeFrom remain none, familyRecord
is none, and continuation is unknown. Exact source binding remains unfinished:
https://github.com/the-omega-institute/trureturing/issues/25856 . -/
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthEnvelope
import Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianUpperEnvelope
import Reg.Support.DependentFamily

set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthEnvelope
open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthEnvelope
open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementSingleCrossing
open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementThresholdBracket
open _root_.Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianUpperEnvelope
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

structure State where
  p : ℤ
  q : ℤ
  t : ℕ
  hp5 : 5 ≤ p
  hpo : Odd p
  hq3 : 3 ≤ q
  hqo : Odd q
  ht : ((q+1)/2).toNat ≤ t

abbrev signature : Signature where
  Params := Unit
  State _ := State
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature
    (fun i _ x => if i = 0 then (square_return_pair x.p x.q x.t).1
      else (square_return_pair x.p x.q x.t).2)
    (fun e => nomatch e)

noncomputable def zeroRole (i : Fin 2) : Realization signature :=
  realize signature (fun j p x => if j = i then 0 else actual.readout j p x)
    (fun e => nomatch e)

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
    (2/3 : ℝ) ≤ s → s ≤ 5/7 →
      |2*(R.readout 0 () x : ℝ)/(R.readout 1 () x : ℝ)-
        G-H/(x.p : ℝ)^2-K/(x.p : ℝ)^4| ≤ 2439/(8000*(x.p : ℝ)^6)

abbrev arena : Arena where
  signature := signature
  Law := law

private theorem bridge : (type_of% actual_square_displacement_fourth_envelope) ↔ arena.Law actual := by
  constructor
  · intro h x
    simpa [arena,law,actual,realize]
      using h x.p x.q x.t x.hp5 x.hpo x.hq3 x.hqo x.ht
  · intro h p q t hp5 hpo hq3 hqo ht
    simpa [arena,law,actual,realize]
      using h (State.mk p q t hp5 hpo hq3 hqo ht)

private theorem actual_law : arena.Law actual :=
  bridge.mp actual_square_displacement_fourth_envelope

private def state53 (t : ℕ) (ht : 2 ≤ t) : State :=
  ⟨5,3,t,by norm_num,by decide,by norm_num,by decide,by simpa using ht⟩

/-- Purely rational coefficients suffice to reject the zero ratio at a band state. -/
theorem zero_ratio_fails :
    let s : ℝ := 50/73
    let C : ℝ := 5/48
    let E : ℝ := 1/48
    let B : ℝ := 91/3840
    ¬ |0-(Real.exp s+Real.exp (-9*s))-
      C*s^3*(Real.exp s-81*Real.exp (-9*s))/25-
      (-E*s^3*(Real.exp s-9*Real.exp (-9*s))+
        B*s^5*(Real.exp s-729*Real.exp (-9*s))+
        (C^2/2)*s^6*(Real.exp s+6561*Real.exp (-9*s)))/625| ≤
      2439/125000000 := by
  dsimp only
  let s : ℝ := 50/73
  let c : ℝ := 1+(5/48)*s^3/25+
    (-(1/48)*s^3+(91/3840)*s^5+((5/48)^2/2)*s^6)/625
  let d : ℝ := 1-81*(5/48)*s^3/25+
    (9*(1/48)*s^3-729*(91/3840)*s^5+6561*((5/48)^2/2)*s^6)/625
  have hc : 1 ≤ c := by norm_num [c,s]
  have hd : 0 ≤ d := by norm_num [d,s]
  have hexp : 1 < Real.exp s := by
    have hh := Real.add_one_le_exp s
    norm_num [s] at hh ⊢
  have hmodel : 1 < c*Real.exp s+d*Real.exp (-9*s) := by
    have hh := mul_le_mul_of_nonneg_right hc (Real.exp_pos s).le
    have ht : 0 ≤ d*Real.exp (-9*s) := mul_nonneg hd (Real.exp_pos _).le
    nlinarith only [hh,ht,hexp]
  have hid : 0-(Real.exp s+Real.exp (-9*s))-
      (5/48)*s^3*(Real.exp s-81*Real.exp (-9*s))/25-
      (-(1/48)*s^3*(Real.exp s-9*Real.exp (-9*s))+
        (91/3840)*s^5*(Real.exp s-729*Real.exp (-9*s))+
        ((5/48)^2/2)*s^6*(Real.exp s+6561*Real.exp (-9*s)))/625 =
      -(c*Real.exp s+d*Real.exp (-9*s)) := by dsimp [c,d]; ring
  intro h
  change |0-(Real.exp s+Real.exp (-9*s))-
    (5/48)*s^3*(Real.exp s-81*Real.exp (-9*s))/25-
    (-(1/48)*s^3*(Real.exp s-9*Real.exp (-9*s))+
      (91/3840)*s^5*(Real.exp s-729*Real.exp (-9*s))+
      ((5/48)^2/2)*s^6*(Real.exp s+6561*Real.exp (-9*s)))/625| ≤ _ at h
  rw [hid,abs_neg,abs_of_pos (by linarith only [hmodel])] at h
  exact (not_le_of_gt hmodel) (h.trans (by norm_num))

private theorem rejected (i : Fin 2) : ¬ arena.Law (zeroRole i) := by
  intro h
  have hh := h (state53 5 (by norm_num))
  apply zero_ratio_fails
  fin_cases i <;>
    norm_num [arena,law,zeroRole,actual,realize,state53] at hh ⊢ <;> exact hh

/-- State classification is reused, including its complete quotient-count bridge. -/
private theorem counts53 (t : ℕ) (ht : 2 ≤ t) :
    (square_return_pair 5 3 t).1 =
      2*(Nat.choose (30*t-5) (15*t)+Nat.choose (30*t-5) (15*t+20)) ∧
    (square_return_pair 5 3 t).2 = 4*Nat.choose (30*t-5) (15*t+5) := by
  obtain ⟨n,a,r,hN,hna,hr,hfit,hWa,hWq⟩ := state_data 5 3 t
    (by norm_num) (by decide) (by norm_num) (by decide) (by simpa using ht)
  change 2*r = 2*5 at hr
  change n+5 = 2*a at hna
  change (square_return_pair 5 3 t).1 = 2*(Nat.choose n a+Nat.choose n (a+4*r)) at hWa
  change (square_return_pair 5 3 t).2 = 4*Nat.choose n (a+r) at hWq
  have hn : (n:ℤ) = 30*(t:ℤ)-5 := by nlinarith only [hN]
  have hn' : n = 30*t-5 := by omega
  have ha : a = 15*t := by omega
  have hr' : r = 5 := by omega
  simpa only [hn',ha,hr',show 4*5 = (20:ℕ) by norm_num] using And.intro hWa hWq

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),state53 4 (by norm_num),state53 5 (by norm_num),?_⟩
  have h4 := counts53 4 (by norm_num)
  have h5 := counts53 5 (by norm_num)
  simp only [show 30*4-5 = (115:ℕ) by decide,show 15*4 = (60:ℕ) by decide,
    show 60+20 = (80:ℕ) by decide,show 60+5 = (65:ℕ) by decide] at h4
  simp only [show 30*5-5 = (145:ℕ) by decide,show 15*5 = (75:ℕ) by decide,
    show 75+20 = (95:ℕ) by decide,show 75+5 = (80:ℕ) by decide] at h5
  have hA := choose_grow_diagonal 115 60 15 (by omega) (by omega)
  have hD := choose_grow_diagonal 115 80 15 (by omega) (by omega)
  have hB := choose_grow_diagonal 115 65 15 (by omega) (by omega)
  simp only [show 115+2*15 = (145:ℕ) by decide,
    show 60+15 = (75:ℕ) by decide] at hA
  simp only [show 115+2*15 = (145:ℕ) by decide,
    show 80+15 = (95:ℕ) by decide] at hD
  simp only [show 115+2*15 = (145:ℕ) by decide,
    show 65+15 = (80:ℕ) by decide] at hB
  have ha : (square_return_pair 5 3 4).1 < (square_return_pair 5 3 5).1 := by
    rw [h4.1,h5.1]; omega
  have hb : (square_return_pair 5 3 4).2 < (square_return_pair 5 3 5).2 := by
    rw [h4.2,h5.2]; omega
  fin_cases i
  · simpa [actual,realize,state53] using ne_of_lt ha
  · simpa [actual,realize,state53] using ne_of_lt hb

noncomputable def source : Registration arena
    (type_of% actual_square_displacement_fourth_envelope) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law,zeroRole 0,rejected 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨zeroRole i,?_,rfl,rejected i⟩
      intro j hj
      funext p x
      simp [zeroRole,realize,hj]
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@actual_square_displacement_fourth_envelope)
      (Realization signature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthEnvelope.actual_square_displacement_fourth_envelope.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthEnvelope.source
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

end Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementFourthEnvelope
