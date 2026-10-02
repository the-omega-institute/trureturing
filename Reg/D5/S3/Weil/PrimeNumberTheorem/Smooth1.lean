import D5.S3.Weil.PrimeNumberTheorem.Smooth1
import Reg.Support.DependentFamily
import Reg.Support.PntAuditFacts

namespace Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1

open Set Function Filter Complex Real MeasureTheory
open scoped ContDiff Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.PntAuditFacts
open LeanInformationAudit

noncomputable section

namespace Below

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ c ε => 1 - c * ε) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 5) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1),
    ∃ c : ℝ, 0 < c ∧ c = Real.log 2 ∧
      ∀ (ε x : ℝ) (_ : 0 < ε), 0 < x → x ≤ r.readout () c ε →
        _root_.Smooth1 ν ε x = 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ν, _hd, _hn, hs, hm⟩ := normalized_smooth_kernel
  obtain ⟨c, _hc, _hceq, below⟩ := h hs hm
  have h1 := below (1 / 2) 5 (by norm_num) (by norm_num) (by norm_num [rejected, realize])
  obtain ⟨d, _hd, hdeq, above⟩ := Smooth1Properties_above hs
  have hd : d ≤ 2 := by rw [hdeq]; linarith [log_two_le_one]
  have h0 := above (1 / 2) 5 (by constructor <;> norm_num) (by linarith)
  rw [h0] at h1
  norm_num at h1

def registration : Registration arena
    (∀ {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2)
      (mass_one : ∫ x in Ioi 0, ν x / x = 1),
      ∃ c : ℝ, 0 < c ∧ c = Real.log 2 ∧
        ∀ (ε x : ℝ) (_ : 0 < ε), 0 < x → x ≤ 1 - c * ε →
          _root_.Smooth1 ν ε x = 1) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.Smooth1Properties_below, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), ?_⟩
    change (1 : ℝ) - 1 * 0 ≠ 1 - 1 * 1
    norm_num

register_information_theorem _root_.Smooth1Properties_below in arena
  readout via (realize signature (fun _ c ε => 1 - c * ε) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Weil.PrimeNumberTheorem.Smooth1
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "arg",
        "body", "body", "body", "body", "domain", "arg"]
      stateBinder := 4 }] })
  escape continues (open)

end Below

namespace Above

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ c ε => 1 + c * ε) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2),
    ∃ c : ℝ, 0 < c ∧ c = 2 * Real.log 2 ∧
      ∀ (ε x : ℝ) (_ : ε ∈ Ioo 0 1), r.readout () c ε ≤ x →
        _root_.Smooth1 ν ε x = 0

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ν, _hd, _hn, hs, hm⟩ := normalized_smooth_kernel
  obtain ⟨c, _hc, _hceq, above⟩ := h hs
  have h0 := above (1 / 4) (1 / 4) (by constructor <;> norm_num)
    (by norm_num [rejected, realize])
  obtain ⟨d, _hd, hdeq, below⟩ := Smooth1Properties_below hs hm
  have hd : d ≤ 1 := by rw [hdeq]; exact log_two_le_one
  have h1 := below (1 / 4) (1 / 4) (by norm_num) (by norm_num) (by linarith)
  rw [h0] at h1
  norm_num at h1

def registration : Registration arena
    (∀ {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2),
      ∃ c : ℝ, 0 < c ∧ c = 2 * Real.log 2 ∧
        ∀ (ε x : ℝ) (_ : ε ∈ Ioo 0 1), 1 + c * ε ≤ x →
          _root_.Smooth1 ν ε x = 0) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.Smooth1Properties_above, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), ?_⟩
    change (1 : ℝ) + 1 * 0 ≠ 1 + 1 * 1
    norm_num

register_information_theorem _root_.Smooth1Properties_above in arena
  readout via (realize signature (fun _ c ε => 1 + c * ε) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Weil.PrimeNumberTheorem.Smooth1
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "arg", "body",
        "body", "body", "domain", "fn", "arg"]
      stateBinder := 3 }] })
  escape continues (open)

end Above

namespace Transform

abbrev signature : Signature where
  Params := Σ _ : (ℝ → ℝ), ℝ
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p s => s⁻¹ * mellin (fun x => (p.1 x : ℂ)) (p.2 * s))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (εpos : 0 < ε) {s : ℂ} (hs : 0 < s.re),
    mellin (fun x => (_root_.Smooth1 ν ε x : ℂ)) s = r.readout () ⟨ν, ε⟩ s

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (ν := fun _ => 0) contDiff_const (by simp)
    (ε := 1) (by norm_num) (s := 1) (by norm_num)
  simpa [rejected, realize, smooth1_zero, mellin] using hh

def registration : Registration arena
    (∀ {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
      (suppν : ν.support ⊆ Icc (1 / 2) 2)
      {ε : ℝ} (εpos : 0 < ε) {s : ℂ} (hs : 0 < s.re),
      mellin (fun x => (_root_.Smooth1 ν ε x : ℂ)) s =
        s⁻¹ * mellin (fun x => (ν x : ℂ)) (ε * s)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.MellinOfSmooth1a, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    let ν : ℝ → ℝ := (Set.Ioc (0 : ℝ) 1).indicator fun _ => 1
    refine ⟨⟨ν, (1 : ℝ)⟩, (1 : ℂ), (2 : ℂ), ?_⟩
    change (1 : ℂ)⁻¹ * mellin (fun x => (ν x : ℂ)) (1 * 1) ≠
      (2 : ℂ)⁻¹ * mellin (fun x => (ν x : ℂ)) (1 * 2)
    have hcast : (fun x => (ν x : ℂ)) =
        (Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1 <;>
        simp [ν, Set.indicator_apply, hx]
    rw [hcast]
    simp only [one_mul]
    have h1 := (hasMellin_one_Ioc (s := (1 : ℂ)) (by norm_num)).2
    have h2 := (hasMellin_one_Ioc (s := (2 : ℂ)) (by norm_num)).2
    rw [h1, h2]
    norm_num

register_information_theorem _root_.MellinOfSmooth1a in arena
  readout via (realize signature
    (fun _ p s => s⁻¹ * mellin (fun x => (p.1 x : ℂ)) (p.2 * s))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Weil.PrimeNumberTheorem.Smooth1
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 5 }] })
  escape continues (open)

end Transform

namespace Continuity

abbrev signature : Signature where
  Params := Σ _ : (ℝ → ℝ), ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => _root_.Smooth1 p.1 p.2 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => if x = 1 then 1 else 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x) (suppν : ν.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (εpos : 0 < ε) {y : ℝ} (ypos : 0 < y),
    ContinuousAt (fun x => r.readout () ⟨ν, ε⟩ x) y

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := h (ν := fun _ => 0) contDiff_const (by simp) (by simp)
    (ε := 1) (by norm_num) (y := 1) (by norm_num)
  change ContinuousAt (fun x : ℝ => if x = 1 then (1 : ℝ) else 0) 1 at hc
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hc (1 / 2) (by norm_num)
  have hx : (1 + δ / 2 : ℝ) ≠ 1 := by linarith
  have hd : dist (1 + δ / 2 : ℝ) 1 < δ := by
    rw [Real.dist_eq, show (1 + δ / 2 : ℝ) - 1 = δ / 2 by ring,
      abs_of_pos (by positivity : 0 < δ / 2)]
    linarith
  have hh := hball hd
  norm_num [hx, Real.dist_eq] at hh

def registration : Registration arena
    (∀ {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
      (νpos : ∀ x > 0, 0 ≤ ν x) (suppν : ν.support ⊆ Icc (1 / 2) 2)
      {ε : ℝ} (εpos : 0 < ε) {y : ℝ} (ypos : 0 < y),
      ContinuousAt (fun x => _root_.Smooth1 ν ε x) y) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.Smooth1ContinuousAt, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    obtain ⟨ν, h1, h0⟩ := smooth1_distinct_values
    refine ⟨⟨ν, (1 / 4 : ℝ)⟩, (1 / 4 : ℝ), (5 : ℝ), ?_⟩
    change _root_.Smooth1 ν (1 / 4) (1 / 4) ≠ _root_.Smooth1 ν (1 / 4) 5
    rw [h1, h0]
    norm_num

register_information_theorem _root_.Smooth1ContinuousAt in arena
  readout via (realize signature
    (fun _ p x => _root_.Smooth1 p.1 p.2 x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Weil.PrimeNumberTheorem.Smooth1
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg"]
      stateBinder := 0
      functionOperand := true }] })
  escape continues (open)

end Continuity
end
end Reg.D5.S3.Weil.PrimeNumberTheorem.Smooth1
