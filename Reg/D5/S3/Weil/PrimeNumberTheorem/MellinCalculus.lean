import D5.S3.Weil.PrimeNumberTheorem.MellinCalculus
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus

open Set Function Filter Complex Real MeasureTheory
open scoped ContDiff
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := ℝ → ℝ
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ ν s => ‖mellin (fun x => (ν x : ℂ)) s‖)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ s => s.im ^ 2 + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2),
    ∃ C > 0, ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2),
      r.readout () ν s ≤ C * ‖s‖⁻¹

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨C, hC, bound⟩ := h (ν := fun _ => 0) contDiff_const (by simp)
  let s : ℂ := 1 + (C + 1) * Complex.I
  have hre : s.re = 1 := by norm_num [s]
  have him : s.im = C + 1 := by norm_num [s]
  have hs : (1 : ℝ) ≤ ‖s‖ := by
    rw [← hre]
    exact Complex.re_le_norm s
  have hb := bound 1 (by norm_num) s (by rw [hre]) (by rw [hre]; norm_num)
  change s.im ^ 2 + 1 ≤ C * ‖s‖⁻¹ at hb
  have hright : C * ‖s‖⁻¹ ≤ C := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hs) hC.le
  rw [him] at hb
  have hbad := hb.trans hright
  nlinarith [sq_nonneg C]

def registration : Registration arena
    (∀ {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
      (suppν : ν.support ⊆ Set.Icc (1 / 2) 2),
      ∃ C > 0, ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2),
        ‖mellin (fun x => (ν x : ℂ)) s‖ ≤ C * ‖s‖⁻¹) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.MellinOfPsi, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    let ν : ℝ → ℝ := (Set.Ioc (0 : ℝ) 1).indicator fun _ => 1
    refine ⟨ν, (1 : ℂ), (2 : ℂ), ?_⟩
    change ‖mellin (fun x => (ν x : ℂ)) 1‖ ≠
      ‖mellin (fun x => (ν x : ℂ)) 2‖
    have hcast : (fun x => (ν x : ℂ)) =
        (Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1 <;>
        simp [ν, Set.indicator_apply, hx]
    rw [hcast]
    have h1 := (hasMellin_one_Ioc (s := (1 : ℂ)) (by norm_num)).2
    have h2 := (hasMellin_one_Ioc (s := (2 : ℂ)) (by norm_num)).2
    rw [h1, h2]
    norm_num [norm_div]

register_information_theorem _root_.MellinOfPsi
  in arena
  readout via (realize signature
    (fun _ ν s => ‖mellin (fun x => (ν x : ℂ)) s‖) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Weil.PrimeNumberTheorem.MellinCalculus
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "body",
        "body", "body", "body", "fn", "arg"]
      stateBinder := 6 }] })
  escape continues (open)

end

end Reg.D5.S3.Weil.PrimeNumberTheorem.MellinCalculus
