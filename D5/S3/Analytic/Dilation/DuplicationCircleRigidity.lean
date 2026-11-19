/- GID: D5/S3/Analytic/Dilation/DuplicationCircleRigidity
   generality: G
   mirror-B: D5/B/S3/Analytic/Dilation/DuplicationCircleRigidity
   mirror-E: none
   anchors: []
   utility: kind=none; basis=not_applicable
   digest: Continuity and the unit fibre determine faithful real duplication solutions. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete
import Mathlib.Algebra.Order.ToIntervalMod

/-! A bounded continuous duplication solution with an isolated period fibre is a cosine. -/

namespace D5.S3.Analytic.Dilation.DuplicationCircleRigidity

open Set

private theorem le_zero_of_bounded_doubling {s : Set ℝ} (f : ℝ → ℝ) {C : ℝ}
    (hbound : ∀ x ∈ s, f x ≤ C)
    (hstep : ∀ x ∈ s, ∃ y ∈ s, 2 * f x ≤ f y) {x : ℝ} (hx : x ∈ s) :
    f x ≤ 0 := by
  have hiter (n : ℕ) : ∀ x ∈ s, (2 : ℝ) ^ n * f x ≤ C := by
    induction n with
    | zero => simpa using hbound
    | succ n ih =>
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hstep x hx
      calc
        (2 : ℝ) ^ (n + 1) * f x = 2 ^ n * (2 * f x) := by rw [pow_succ, mul_assoc]
        _ ≤ 2 ^ n * f y := mul_le_mul_of_nonneg_left hxy (by positivity)
        _ ≤ C := ih y hy
  by_contra! hpos
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / f x) (by norm_num : (1 : ℝ) < 2)
  exact (not_lt_of_ge (hiter n x hx)) ((div_lt_iff₀ hpos).mp hn)

/-- A continuous bounded duplication solution starting at one must return to one
at a positive argument. -/
theorem no_faithful_duplication_on_line :
    ¬ ∃ p : ℝ → ℝ, Continuous p ∧ p 0 = 1 ∧
      (∀ t, |p t| ≤ 1) ∧ (∀ t, p (2 * t) = 2 * (p t) ^ 2 - 1) ∧
      (∀ t > 0, p t < 1) := by
  rintro ⟨p, hcont, hzero, hbound, hdup, hstrict⟩
  have hnegOne (t : ℝ) (ht : 0 < t) : p t ≠ -1 := by
    intro hp
    have he := hdup t
    rw [hp] at he
    norm_num at he
    exact (ne_of_lt (hstrict (2 * t) (by positivity))) he
  have hnonzero (t : ℝ) (ht : 0 < t) : p t ≠ 0 := by
    intro hp
    apply hnegOne (2 * t) (by positivity)
    rw [hdup, hp]
    norm_num
  have hpos (t : ℝ) (ht : 0 < t) : 0 < p t := by
    by_contra! hle
    obtain ⟨u, hu, hpu⟩ := intermediate_value_Icc' ht.le hcont.continuousOn
      (show (0 : ℝ) ∈ Icc (p t) (p 0) from ⟨hle, by rw [hzero]; norm_num⟩)
    have hu0 : 0 < u := by
      apply lt_of_le_of_ne hu.1
      intro he
      rw [← he, hzero] at hpu
      norm_num at hpu
    exact hnonzero u hu0 hpu
  have hvanish : 1 - p 1 ≤ 0 :=
    le_zero_of_bounded_doubling (s := Ioi 0) (fun t => 1 - p t)
      (C := 2) (fun t _ => by linarith [(abs_le.mp (hbound t)).1])
      (fun t (ht : 0 < t) => by
        refine ⟨2 * t, by change 0 < 2 * t; positivity, ?_⟩
        rw [hdup]
        nlinarith [mul_nonneg (hpos t ht).le (sub_nonneg.mpr (hstrict t ht).le)])
      (show (0 : ℝ) < 1 by norm_num)
  linarith [hstrict 1 (by norm_num)]

/-- For a faithful continuous even solution on the circle, the duplication law
fixes the cosine coordinate. -/
theorem eq_cos_of_circle_duplication {p : ℝ → ℝ}
    (hcont : Continuous p) (hperiod : Function.Periodic p (2 * Real.pi))
    (heven : ∀ t, p (-t) = p t) (hbound : ∀ t, |p t| ≤ 1)
    (hdup : ∀ t, p (2 * t) = 2 * (p t) ^ 2 - 1)
    (hfibre : ∀ t, p t = 1 ↔ ∃ k : ℤ, t = 2 * Real.pi * (k : ℝ)) :
    p = Real.cos := by
  have hone (t : ℝ) : p t = 1 ↔ Real.cos t = 1 := by
    rw [hfibre, Real.cos_eq_one_iff]
    constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, by linarith⟩
  have hp0 : p 0 = 1 := (hone 0).mpr Real.cos_zero
  have hquad (x : ℝ) : 2 * x ^ 2 - 1 = 1 ↔ x = 1 ∨ x = -1 := by
    constructor
    · intro hx
      have hprod : (x - 1) * (x + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hprod with hh | hh
      · left; linarith
      · right; linarith
    · rintro (rfl | rfl) <;> norm_num
  have hminus (t : ℝ) : p t = -1 ↔ Real.cos t = -1 := by
    have hd := hone (2 * t)
    rw [hdup, Real.cos_two_mul, hquad, hquad] at hd
    constructor
    · intro ht
      exact (hd.mp (Or.inr ht)).resolve_left fun hc => by
        linarith [(hone t).mpr hc]
    · intro ht
      exact (hd.mpr (Or.inr ht)).resolve_left fun hp => by
        linarith [(hone t).mp hp]
  have hzero (t : ℝ) : p t = 0 ↔ Real.cos t = 0 := by
    have hd := hminus (2 * t)
    rw [hdup, Real.cos_two_mul] at hd
    constructor
    · intro h
      apply sq_eq_zero_iff.mp
      apply (show 2 * (Real.cos t) ^ 2 - 1 = -1 → (Real.cos t) ^ 2 = 0 by intro he; linarith)
      apply hd.mp
      rw [h]
      norm_num
    · intro h
      apply sq_eq_zero_iff.mp
      apply (show 2 * (p t) ^ 2 - 1 = -1 → (p t) ^ 2 = 0 by intro he; linarith)
      apply hd.mpr
      rw [h]
      norm_num
  have hppi : p Real.pi = -1 := (hminus _).mpr Real.cos_pi
  have hpquarter : p (Real.pi / 2) = 0 := (hzero _).mpr Real.cos_pi_div_two
  have hsole (x : ℝ) (hx : x ∈ Icc 0 Real.pi) (h : p x = 0) : x = Real.pi / 2 := by
    apply Real.injOn_cos hx ⟨by positivity, by linarith [Real.pi_pos]⟩
    rw [(hzero x).mp h, Real.cos_pi_div_two]
  have hleft (x : ℝ) (hx : 0 ≤ x) (hhalf : x ≤ Real.pi / 2) : 0 ≤ p x := by
    by_contra! hneg
    obtain ⟨u, hu, hpu⟩ := intermediate_value_Icc' hx hcont.continuousOn
      (show (0 : ℝ) ∈ Icc (p x) (p 0) from ⟨hneg.le, by rw [hp0]; norm_num⟩)
    have hu' := hsole u ⟨hu.1, by linarith [hu.2, Real.pi_pos]⟩ hpu
    have : x = Real.pi / 2 := by linarith [hu.2]
    rw [this, hpquarter] at hneg
    exact (lt_irrefl _ hneg)
  have hright (x : ℝ) (hhalf : Real.pi / 2 ≤ x) (hx : x ≤ Real.pi) : p x ≤ 0 := by
    by_contra! hpos
    obtain ⟨u, hu, hpu⟩ := intermediate_value_Icc' hx hcont.continuousOn
      (show (0 : ℝ) ∈ Icc (p Real.pi) (p x) from ⟨by rw [hppi]; norm_num, hpos.le⟩)
    have hu' := hsole u ⟨by linarith [hu.1, Real.pi_pos], hu.2⟩ hpu
    have : x = Real.pi / 2 := by linarith [hu.1]
    rw [this, hpquarter] at hpos
    exact (lt_irrefl _ hpos)
  let angle (x : ℝ) := Real.arccos (p x)
  have hangle (t : ℝ) : angle t ∈ Icc 0 Real.pi :=
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hcos (t : ℝ) : Real.cos (angle t) = p t :=
    Real.cos_arccos (abs_le.mp (hbound t)).1 (abs_le.mp (hbound t)).2
  have hreflect (t : ℝ) : p (2 * Real.pi - t) = p t :=
    (hperiod.sub_eq' (x := t)).trans (heven t)
  have hvanish {x : ℝ} (hx : x ∈ Icc 0 Real.pi) : |angle x - x| ≤ 0 := by
    apply le_zero_of_bounded_doubling (s := Icc 0 Real.pi) (fun t => |angle t - t|)
      (C := Real.pi) _ _ hx
    · intro t ht
      exact abs_le.mpr ⟨by linarith [(hangle t).1, ht.2], by linarith [(hangle t).2, ht.1]⟩
    · intro t ht
      by_cases h : t ≤ Real.pi / 2
      · have ha := Real.arccos_le_pi_div_two.mpr (hleft t ht.1 h)
        have hh : angle (2 * t) = 2 * angle t := by
          apply Real.injOn_cos (hangle _) ⟨by linarith [(hangle t).1], by linarith⟩
          rw [hcos, Real.cos_two_mul, hcos, hdup]
        refine ⟨2 * t, ⟨by linarith [ht.1], by linarith⟩, ?_⟩
        rw [hh, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      · have ha := Real.pi_div_two_le_arccos.mpr (hright t (le_of_not_ge h) ht.2)
        have hh : angle (2 * Real.pi - 2 * t) = 2 * Real.pi - 2 * angle t := by
          apply Real.injOn_cos (hangle _) ⟨by linarith [(hangle t).2], by linarith⟩
          rw [hcos, hreflect, Real.cos_two_pi_sub, Real.cos_two_mul, hcos, hdup]
        refine ⟨2 * Real.pi - 2 * t, ⟨by linarith [ht.2], by linarith⟩, ?_⟩
        rw [hh, show 2 * Real.pi - 2 * angle t - (2 * Real.pi - 2 * t) =
          -(2 * (angle t - t)) by ring, abs_neg, abs_mul,
          abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hhalf (x : ℝ) (hx : x ∈ Icc 0 Real.pi) : p x = Real.cos x := by
    have he : angle x = x := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (hvanish hx) (abs_nonneg _)))
    simpa only [he] using (hcos x).symm
  funext t
  have hperiod_pos : 0 < 2 * Real.pi := by positivity
  let k := toIcoDiv hperiod_pos 0 t
  let x := t - k • (2 * Real.pi)
  have hx : x ∈ Ico 0 (2 * Real.pi) := by
    simpa only [zero_add] using sub_toIcoDiv_zsmul_mem_Ico hperiod_pos 0 t
  rw [← hperiod.sub_zsmul_eq (x := t) k, ← Real.cos_periodic.sub_zsmul_eq (x := t) k]
  change p x = Real.cos x
  by_cases h : x ≤ Real.pi
  · exact hhalf x ⟨hx.1, h⟩
  · rw [← hreflect x, ← Real.cos_two_pi_sub x]
    exact hhalf _ ⟨by linarith [hx.2], by linarith⟩

/-- If the unit fibre consists of periods and is discrete at zero, it is an
integer lattice and its positive generator fixes the frequency. -/
theorem eq_scaled_cos_of_discrete_fibre {p : ℝ → ℝ}
    (hcont : Continuous p) (hbound : ∀ t, |p t| ≤ 1) (hzero : p 0 = 1)
    (heven : ∀ t, p (-t) = p t) (hdup : ∀ t, p (2 * t) = 2 * (p t) ^ 2 - 1)
    (hisolated : ∃ ε > 0, ∀ t ∈ Ioo (-ε) ε, p t = 1 → t = 0)
    (hperiod : ∀ s, p s = 1 → Function.Periodic p s) :
    ∃ T > 0, (∀ t, p t = 1 ↔ ∃ k : ℤ, t = T * (k : ℝ)) ∧
      ∀ t, p t = Real.cos (2 * Real.pi * t / T) := by
  let H : AddSubgroup ℝ :=
    { carrier := {t | p t = 1}
      zero_mem' := hzero
      add_mem' := fun {x y} hx hy => (hperiod y hy x).trans hx
      neg_mem' := fun {x} hx => (heven x).trans hx }
  have hnotdense : ¬ Dense (H : Set ℝ) := by
    intro hd
    obtain ⟨ε, hε, hiso⟩ := hisolated
    have hopen : IsOpen (Ioo (0 : ℝ) ε) := isOpen_Ioo
    have hne : (Ioo (0 : ℝ) ε).Nonempty := nonempty_Ioo.mpr hε
    obtain ⟨x, hx, hxH⟩ := hd.inter_open_nonempty _ hopen hne
    exact hx.1.ne' (hiso x ⟨by linarith [hx.1], hx.2⟩ hxH)
  have hex : ∃ x > 0, p x = 1 := by
    by_contra! h
    exact no_faithful_duplication_on_line ⟨p, hcont, hzero, hbound, hdup,
      fun t ht => lt_of_le_of_ne (abs_le.mp (hbound t)).2 (h t ht)⟩
  obtain ⟨g, hg⟩ := H.isAddCyclic_iff_exists_zmultiples_eq_top.mp
    (H.dense_or_isCyclic.resolve_left hnotdense)
  have hrepr (t : ℝ) : p t = 1 ↔ ∃ k : ℤ, t = (g : ℝ) * (k : ℝ) := by
    change t ∈ H ↔ _
    rw [← hg, AddSubgroup.mem_zmultiples_iff]
    exact exists_congr fun k => by rw [zsmul_eq_mul, mul_comm (k : ℝ), eq_comm]
  let T := |(g : ℝ)|
  have hT : 0 < T := by
    obtain ⟨x, hx, hx1⟩ := hex
    obtain ⟨k, hk⟩ := (hrepr x).mp hx1
    refine abs_pos.mpr ?_
    intro h
    rw [h, zero_mul] at hk
    exact hx.ne' hk
  have hTfibre (t : ℝ) : p t = 1 ↔ ∃ k : ℤ, t = T * (k : ℝ) := by
    rw [hrepr]
    by_cases h : 0 ≤ (g : ℝ)
    · simp [T, abs_of_nonneg h]
    · simp only [T, abs_of_neg (lt_of_not_ge h)]
      constructor <;> rintro ⟨k, hk⟩ <;> refine ⟨-k, ?_⟩ <;> push_cast <;> linarith
  let q (x : ℝ) := p (T * x / (2 * Real.pi))
  have hπ : 2 * Real.pi ≠ 0 := by positivity
  have hTperiod : Function.Periodic p T :=
    hperiod T ((hTfibre T).mpr ⟨1, by simp⟩)
  have hq : q = Real.cos := by
    apply eq_cos_of_circle_duplication
    · exact hcont.comp (by fun_prop)
    · intro x
      change p (T * (x + 2 * Real.pi) / (2 * Real.pi)) = p (T * x / (2 * Real.pi))
      rw [show T * (x + 2 * Real.pi) / (2 * Real.pi) = T * x / (2 * Real.pi) + T by
        field_simp]
      exact hTperiod _
    · intro x
      change p (T * -x / (2 * Real.pi)) = p (T * x / (2 * Real.pi))
      rw [mul_neg, neg_div, heven]
    · exact fun x => hbound _
    · intro x
      change p (T * (2 * x) / (2 * Real.pi)) = 2 * (p (T * x / (2 * Real.pi))) ^ 2 - 1
      rw [show T * (2 * x) / (2 * Real.pi) = 2 * (T * x / (2 * Real.pi)) by ring, hdup]
    · intro x
      change p (T * x / (2 * Real.pi)) = 1 ↔ _
      rw [hTfibre]
      constructor <;> rintro ⟨k, hk⟩ <;> refine ⟨k, ?_⟩
      · apply (mul_left_cancel₀ hT.ne')
        rw [div_eq_iff hπ] at hk
        linarith
      · rw [hk]
        field_simp
  refine ⟨T, hT, hTfibre, fun t => ?_⟩
  have hh := congrFun hq (2 * Real.pi * t / T)
  change p (T * (2 * Real.pi * t / T) / (2 * Real.pi)) = _ at hh
  rw [show T * (2 * Real.pi * t / T) / (2 * Real.pi) = t by field_simp] at hh
  exact hh

end D5.S3.Analytic.Dilation.DuplicationCircleRigidity
