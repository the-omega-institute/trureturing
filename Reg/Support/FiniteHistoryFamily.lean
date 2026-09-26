import D5.S3.ConceptDynamics.InformationEscape.FiniteHistoryFamily
import LeanInformationAudit.Syntax

open MeasureTheory Finset
open scoped BigOperators ENNReal
noncomputable section
namespace Reg.Support.FiniteHistoryFamily
open _root_.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
open _root_.D5.S3.ConceptDynamics.InformationEscape.FiniteHistoryFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
universe u v

theorem fullLaw_identity : FullLaw identityFamily.{u,v} :=
  @history_law_conditional_expectation.{u,v}

theorem badFamily_target : badFamily TargetJ.{u} TargetZ.{v} 1 = trueTargetReadout := by
  classical
  unfold badFamily badFiber
  exact Function.update_self targetFiber trueTargetReadout (fun x ω => ω.2)

theorem target_hnu : (∀ j : TargetJ.{u}, 0 ≤ targetNu j) ∧ ∑ j, targetNu j = 1 := by
  simp [targetNu]

theorem target_hK : ∀ n < 1, (∀ j h z, 0 ≤ targetK.{u,v} n j h z) ∧
    ∀ j h, ∑ z, targetK n j h z = 1 := by
  intro n hn
  constructor
  · intro j h z
    cases z with | up b => cases b <;> norm_num [targetK]
  · intro j h
    change (∑ z : ULift Bool, if z.down = false then (1 : ℝ) else 0) = 1
    rw [← (Equiv.ulift : ULift Bool ≃ Bool).symm.sum_comp]
    simp

theorem bad_integral_one :
    (∫ ω : TargetJ.{u} × History TargetZ.{v} 1,
      targetF ω.1 (readPrefix (show 1 ≤ 1 from le_rfl) (trueTargetReadout ω))
      ∂historyLaw targetNu targetK 1) = 1 := by
  letI : IsProbabilityMeasure (historyLaw targetNu.{u} targetK.{u,v} 1) :=
    (history_law_conditional_expectation targetNu target_hnu targetK 1 target_hK).1
  change (∫ _ : TargetJ × History TargetZ 1, (1 : ℝ) ∂historyLaw targetNu targetK 1) = 1
  simp

theorem target_sum_zero :
    (∑ j : TargetJ.{u}, ∑ h : History TargetZ.{v} 1,
      targetNu j * likelihood targetK 1 j h * targetF j h) = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro h _
  have hz : Fin.last 0 = (0 : Fin 1) := rfl
  simp only [likelihood, one_mul, hz, targetK, targetF, targetNu]
  cases hb : (h 0).down <;> simp [hb]

theorem bad_not_law : ¬ FullLaw badFamily.{u,v} := by
  intro h
  have e := (h targetNu target_hnu targetK 1 target_hK).2.1 1 le_rfl targetF
  rw [badFamily_target] at e
  have bad : (1 : ℝ) = 0 := bad_integral_one.symm.trans (e.trans target_sum_zero)
  exact one_ne_zero bad

theorem global_variation : ∃ ρ ρ' : Family.{u,v}, FullLaw ρ ∧ ¬FullLaw ρ' :=
  ⟨identityFamily, badFamily, fullLaw_identity, bad_not_law⟩

theorem history_zero_subsingleton (J : Type u) (Z : ℕ → Type v)
    (ρ ρ' : Readout (J := J) (Z := Z) 0) : ρ = ρ' := by
  funext ω i
  exact Fin.elim0 i

theorem zero_no_variation (J : Type u) (Z : ℕ → Type v)
    (L : Readout (J := J) (Z := Z) 0 → Prop) :
    ¬ ∃ ρ ρ', L ρ ∧ ¬ L ρ' := by
  rintro ⟨ρ, ρ', hp, hn⟩
  exact hn ((history_zero_subsingleton J Z ρ ρ') ▸ hp)

theorem variation : Variation arena.{u,v} actual :=
  ⟨fullLaw_identity, rejected, bad_not_law⟩

theorem sensitivity : Sensitivity arena.{u,v} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, bad_not_law⟩
    intro j h
    exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
  · intro i
    exact nomatch i

theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro i
  refine ⟨targetFiber, (⟨()⟩, fun _ => ⟨false⟩), (⟨()⟩, fun _ => ⟨true⟩), ?_⟩
  intro h
  have h := congrArg (fun f : History TargetZ.{v} 1 => (f 0).down) h
  cases h

end Reg.Support.FiniteHistoryFamily
