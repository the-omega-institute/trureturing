import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Asymptotics.MovingFejerGaussianPrincipal

/-! Kernel and window dependence for the central Gaussian integral. -/

namespace Reg.D5.S3.Fourier.Asymptotics.MovingFejerGaussianPrincipal

open Finset Filter MeasureTheory
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Asymptotics.MovingFejerGaussianPrincipal
open _root_.D5.S3.Fourier.Asymptotics.FinitePairGaussianLimit
open _root_.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
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

namespace Principal

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => Real.sinc z^2) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, Real.pi, ?_⟩
  simp [actual,realize,Real.sinc_of_ne_zero Real.pi_ne_zero,Real.sin_pi]

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {J : ℕ → Type u} [∀ n,Fintype (J n)] (g w : ∀ n,J n → ℝ),
    (∀ᶠ n in atTop, ∀ i j, 0≤w n i*w n j) → (∀ᶠ n in atTop, ∑ j,w n j=1) →
    (∀ᶠ n in atTop, 0<pairMoment (g n) (w n) 2) →
    ∀ (ρ A : ℕ → ℝ), Tendsto ρ atTop (𝓝 0) → Tendsto A atTop atTop →
    (∀ᶠ n in atTop, A n^2*pairMoment (g n) (w n) 4 ≤ 6*(n:ℝ)*pairMoment (g n) (w n) 2^2) →
    let kernel := R.readout () ()
    Tendsto (fun n => (1/(2*Real.pi))*(∫ u in -(A n)..A n,
      kernel (ρ n*u/2) * ‖complexScore (g n) (w n)
        (u/Real.sqrt ((n:ℝ)*pairMoment (g n) (w n) 2/2))‖^(2*n)))
      atTop (𝓝 (1/(2*Real.sqrt Real.pi)))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  have hA : Tendsto (fun n : ℕ => Real.sqrt (n:ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hwin : ∀ᶠ n : ℕ in atTop, (Real.sqrt (n:ℝ))^2*pairMoment g.{u} w.{u} 4 ≤
      6*(n:ℝ)*pairMoment g.{u} w.{u} 2^2 := by
    apply Eventually.of_forall
    intro n
    rw [Real.sq_sqrt (by positivity),momentTwo,momentFour]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have h := law (fun _ => g.{u}) (fun _ => w.{u})
    (Eventually.of_forall fun _ i j => by norm_num [w])
    (Eventually.of_forall fun _ => mass.{u})
    (Eventually.of_forall fun _ => by rw [momentTwo]; norm_num)
    (fun _ => 0) (fun n => Real.sqrt (n:ℝ)) tendsto_const_nhds hA hwin
  have hz : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 (1/(2*Real.sqrt Real.pi))) := by
    simpa [rejected,realize] using h
  have he := tendsto_nhds_unique tendsto_const_nhds hz
  exact (ne_of_gt (by positivity : 0 < (1:ℝ)/(2*Real.sqrt Real.pi))) he.symm

def evidence : Registration arena.{u} (type_of% @central_fejer_gaussian_limit.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@central_fejer_gaussian_limit.{u}, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@central_fejer_gaussian_limit.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.MovingFejerGaussianPrincipal.Principal.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.MovingFejerGaussianPrincipal.Principal.evidence
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
    owner := `D5.S3.Fourier.Asymptotics.MovingFejerGaussianPrincipal
    definition := none
    coordinates := #[]
    readouts :=  #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Principal

end
end Reg.D5.S3.Fourier.Asymptotics.MovingFejerGaussianPrincipal
