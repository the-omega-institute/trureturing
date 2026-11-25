import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Asymptotics.FinitePairGaussianLimit

/-! Source-dependent square and Gaussian readouts for the pair-moment estimates. -/

namespace Reg.D5.S3.Fourier.Asymptotics.FinitePairGaussianLimit

open Finset Filter
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Asymptotics.FinitePairGaussianLimit
open _root_.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
open _root_.D5.S3.Weil.DirichletPolynomialMeanSquare (phase)
open _root_.Reg.Support
noncomputable section
universe u

private def g : ULift.{u} (Fin 2) → ℝ := fun i => (i.down.val:ℝ)
private def w : ULift.{u} (Fin 2) → ℝ := fun _ => 1/2

private theorem mass : ∑ i : ULift.{u} (Fin 2), w i = 1 := by
  rw [← (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2)).sum_comp w]
  norm_num [w, Fin.sum_univ_two]

private theorem momentTwo : pairMoment g.{u} w.{u} 2 = 1/2 := by
  unfold pairMoment
  rw [← (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2)).sum_comp (fun i => ∑ j, w i*w j*(g i-g j)^2)]
  simp_rw [← (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2)).sum_comp (fun j => w _*w j*(g _-g j)^2)]
  norm_num [g,w,Fin.sum_univ_two]

private theorem momentFour : pairMoment g.{u} w.{u} 4 = 1/2 := by
  unfold pairMoment
  rw [← (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2)).sum_comp (fun i => ∑ j, w i*w j*(g i-g j)^4)]
  simp_rw [← (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2)).sum_comp (fun j => w _*w j*(g _-g j)^4)]
  norm_num [g,w,Fin.sum_univ_two]

private theorem scoreZero : complexScore g.{u} w.{u} 0 = 1 := by
  unfold complexScore phase
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, ← Complex.ofReal_sum]
  rw [mass]
  norm_num

namespace Quartic
abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => ‖z‖^2) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual,realize]

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} [Fintype J] (g w : J → ℝ), (∀ i j, 0≤w i*w j) → ∀ (t : ℝ),
    let square := R.readout () ()
    0 ≤ square (complexScore g w t)-((∑ i, w i)^2-pairMoment g w 2*t^2/2) ∧
    square (complexScore g w t)-((∑ i, w i)^2-pairMoment g w 2*t^2/2) ≤ pairMoment g w 4*t^4/24

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  have h := (law g.{u} w.{u} (by intro i j; norm_num [w]) 0).1
  change 0 ≤ 0 - ((∑ i : ULift.{u} (Fin 2), w i)^2-pairMoment g.{u} w.{u} 2*0^2/2) at h
  rw [mass] at h
  norm_num at h

def evidence : Registration arena.{u} (type_of% @score_quartic.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@score_quartic.{u}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@score_quartic.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.FinitePairGaussianLimit.Quartic.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.FinitePairGaussianLimit.Quartic.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.FinitePairGaussianLimit
    definition := none
    coordinates := #[]
    readouts :=  #[{
      path := #["body","body","body","body","body","body","value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Quartic

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ t => Real.exp t) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  exact Real.exp_injective.ne zero_ne_one

namespace Limit
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {J : ℕ → Type u} [∀ n, Fintype (J n)] (g w : ∀ n, J n → ℝ),
    (∀ᶠ n in atTop, ∀ i j, 0≤w n i*w n j) → (∀ᶠ n in atTop, ∑ j, w n j = 1) →
    (∀ᶠ n in atTop, 0 < pairMoment (g n) (w n) 2) →
    Tendsto (fun n => pairMoment (g n) (w n) 4 / ((n:ℝ)*pairMoment (g n) (w n) 2^2)) atTop (𝓝 0) →
    ∀ u : ℝ, let gaussian := R.readout () ()
    Tendsto (fun n => ‖complexScore (g n) (w n)
      (u/Real.sqrt ((n:ℝ)*pairMoment (g n) (w n) 2/2))‖^(2*n)) atTop (𝓝 (gaussian (-u^2)))
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  have hr : Tendsto (fun n : ℕ => pairMoment g.{u} w.{u} 4 /
    ((n:ℝ)*pairMoment g.{u} w.{u} 2^2)) atTop (𝓝 0) := by
    simp only [momentTwo,momentFour]
    have h := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 2
    rw [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    change 2 * (n:ℝ)⁻¹ = (1/2:ℝ) / ((n:ℝ)*(1/2)^2)
    field_simp [hn']

  have h := law (fun _ => g.{u}) (fun _ => w.{u})
    (Eventually.of_forall fun _ i j => by norm_num [w])
    (Eventually.of_forall fun _ => mass.{u})
    (Eventually.of_forall fun _ => by rw [momentTwo]; norm_num) hr 0
  simp [rejected,realize,scoreZero] at h

def evidence : Registration arena.{u} (type_of% @score_gaussian_limit.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@score_gaussian_limit.{u}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@score_gaussian_limit.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.FinitePairGaussianLimit.Limit.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.FinitePairGaussianLimit.Limit.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.FinitePairGaussianLimit
    definition := none
    coordinates := #[]
    readouts :=  #[{
      path := #["body","body","body","body","body","body","body","body","body","value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Limit

namespace Envelope
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} [Fintype J] (g w : J → ℝ),
    (∀ i j, 0≤w i*w j) → (∑ i, w i=1) → ∀ (n : ℕ), 0<n →
    0<pairMoment g w 2 → ∀ u : ℝ,
    u^2*pairMoment g w 4 ≤ 3*(n:ℝ)*pairMoment g w 2^2 →
    let gaussian := R.readout () ()
    ‖complexScore g w (u/Real.sqrt ((n:ℝ)*pairMoment g w 2/2))‖^(2*n) ≤
      gaussian (-u^2/2)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  have h := law g.{u} w.{u} (by intro i j; norm_num [w]) mass 1 (by decide)
    (by rw [momentTwo]; norm_num) 0 (by rw [momentTwo]; norm_num)
  norm_num [rejected,realize,scoreZero] at h

def evidence : Registration arena.{u} (type_of% @score_gaussian_envelope.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@score_gaussian_envelope.{u}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@score_gaussian_envelope.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.FinitePairGaussianLimit.Envelope.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.FinitePairGaussianLimit.Envelope.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.FinitePairGaussianLimit
    definition := none
    coordinates := #[]
    readouts :=  #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Envelope

end
end Reg.D5.S3.Fourier.Asymptotics.FinitePairGaussianLimit
