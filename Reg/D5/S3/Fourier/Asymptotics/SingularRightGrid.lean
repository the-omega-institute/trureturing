import D5.S3.Fourier.Asymptotics.SingularRightGrid
import Reg.Support.DependentFamily

open Set MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid

abbrev signature : Signature where
  Params := Σ _ : ℝ, Σ _ : ℝ → ℂ, ℝ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p b =>
    |(∑ k ∈ Finset.range (Nat.floor (b/p.2.2)),
        (‖p.2.1 (((k:ℝ)+1)*p.2.2)‖^2-‖p.2.1 0‖^2) / ((k:ℝ)+1)) -
      ∫ x in 0..b, (‖p.2.1 x‖^2-‖p.2.1 0‖^2)/x|)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1:ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (A : ℝ), 0 < A → ∀ (f : ℝ → ℂ),
    AbsolutelyContinuousOnInterval f 0 A →
    IntervalIntegrable (fun x => ‖deriv f x‖^2) volume 0 A →
    ∀ (h b : ℝ), 0 < h → h ≤ b → b ≤ A →
    r.readout () ⟨A,f,h⟩ b ≤ 14*(1/Real.sqrt A+Real.sqrt A)*Real.sqrt h*
      (∫ x in 0..A, (‖f x‖^2+‖deriv f x‖^2))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (0:ℂ)) 0 1 :=
    contDiffOn_const.absolutelyContinuousOnInterval
  have hi : IntervalIntegrable (fun x => ‖deriv (fun _ : ℝ => (0:ℂ)) x‖^2) volume 0 1 := by
    simpa using (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume 0 1)
  have H := h 1 zero_lt_one (fun _ => 0) hc hi 1 1 zero_lt_one le_rfl le_rfl
  norm_num [rejected,realize] at H

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1,(fun x : ℝ => (x:ℂ)),1⟩,0,1,?_⟩
  have he : (∫ x in (0:ℝ)..1, (‖(x:ℂ)‖^2-‖(0:ℂ)‖^2)/x) = 1/2 := by
    have heq : (fun x : ℝ => (‖(x:ℂ)‖^2-‖(0:ℂ)‖^2)/x) = fun x => x := by
      funext x
      simp only [norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero,
        Complex.norm_real,Real.norm_eq_abs,sq_abs]
      by_cases hx : x=0
      · simp [hx]
      · field_simp
    rw [heq,integral_id]
    norm_num
  simp only [actual,realize]
  have he' : (∫ x in (0:ℝ)..1, x^2/x) = 1/2 := by
    simpa only [norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero,
      Complex.norm_real,Real.norm_eq_abs,sq_abs] using he
  norm_num [Finset.sum_range_succ,he']

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Fourier.Asymptotics.SingularRightGrid.result,
    rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j h
      exact (h (show j=i from @Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := dependence

register_information_theorem _root_.D5.S3.Fourier.Asymptotics.SingularRightGrid.result in arena
  readout via (realize signature (fun _ p b =>
    |(∑ k ∈ Finset.range (Nat.floor (b/p.2.2)),
        (‖p.2.1 (((k:ℝ)+1)*p.2.2)‖^2-‖p.2.1 0‖^2) / ((k:ℝ)+1)) -
      ∫ x in 0..b, (‖p.2.1 x‖^2-‖p.2.1 0‖^2)/x|) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Fourier.Asymptotics.SingularRightGrid
    coordinates := #[0,2,5]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 6 }] })
  escape continues (open)

#print axioms registration
end Reg.D5.S3.Fourier.Asymptotics.SingularRightGrid
