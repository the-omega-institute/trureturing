/- GID: D5/S3/Observer/MetricGeometry/SimplexDeletionMinimax
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometry/SimplexDeletionMinimax
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A common probability center gives the sharp full-scale deletion-noise minimax risk. -/

import D5.S3.Observer.MeasureSeparation.RobustMinimaxKernelBound
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.MetricGeometry.SimplexDeletionMinimax

open D5.S3.Observer.MeasureSeparation.RobustMinimaxKernelBound

private theorem interval_mass {m : ℕ} (a b : Fin m → ℝ)
    (hab : ∀ i, a i ≤ b i) (ha : ∑ i, a i ≤ 1) (hb : 1 ≤ ∑ i, b i) :
    ∃ q : Fin m → ℝ, (∀ i, a i ≤ q i ∧ q i ≤ b i) ∧ ∑ i, q i = 1 := by
  classical
  by_cases heq : (∑ i, a i) = ∑ i, b i
  · exact ⟨a, fun i => ⟨le_rfl, hab i⟩, le_antisymm ha (heq ▸ hb)⟩
  · have hsum : (∑ i, a i) < ∑ i, b i :=
      lt_of_le_of_ne (Finset.sum_le_sum fun i _ => hab i) heq
    let t : ℝ := (1 - ∑ i, a i) / ((∑ i, b i) - ∑ i, a i)
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hsum.le)
    have ht1 : t ≤ 1 := (div_le_one (sub_pos.mpr hsum)).mpr (by linarith)
    refine ⟨fun i => a i + t * (b i - a i), ?_, ?_⟩
    · intro i
      have hdiff := sub_nonneg.mpr (hab i)
      constructor
      · nlinarith
      · nlinarith
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
      dsimp only [t]
      rw [div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hsum))]
      ring

/-- A single probability vector centers the entire compact source family. -/
theorem simplex_common_center {m : ℕ} (hm : 2 ≤ m)
    (K : Set (Fin m → ℝ)) (hK : IsCompact K) (hne : K.Nonempty)
    (hprob : K ⊆ stdSimplex ℝ (Fin m)) (w : ℝ) (hw : 0 ≤ w)
    (hdiam : ∀ p ∈ K, ∀ q ∈ K, ∀ i, |p i - q i| ≤ w) :
    ∃ q ∈ stdSimplex ℝ (Fin m),
      ∀ p ∈ K, ∀ i, |p i - q i| ≤ (1 - 1 / (m : ℝ)) * w := by
  classical
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  let r : ℝ := (1 - 1 / (m : ℝ)) * w
  have hdiv1 : (1 : ℝ) / m ≤ 1 := (div_le_one hmpos).mpr (by linarith)
  have hr0 : 0 ≤ r := mul_nonneg (sub_nonneg.mpr hdiv1) hw
  have hrw : r ≤ w := by dsimp [r]; nlinarith [div_pos (by norm_num : (0 : ℝ) < 1) hmpos]
  have hwr : w ≤ 2 * r := by
    have hdiv : (1 : ℝ) / m ≤ 1 / 2 := by
      exact one_div_le_one_div_of_le (by norm_num) hmR
    dsimp [r]
    nlinarith
  have hmr : (m : ℝ) * r = ((m : ℝ) - 1) * w := by
    dsimp [r]
    field_simp
  have hmin (i : Fin m) : ∃ p ∈ K, ∀ q ∈ K, p i ≤ q i :=
    hK.exists_isMinOn hne (continuous_apply i).continuousOn
  have hmax (i : Fin m) : ∃ p ∈ K, ∀ q ∈ K, q i ≤ p i :=
    hK.exists_isMaxOn hne (continuous_apply i).continuousOn
  choose pl hplK hpl using hmin
  choose pu hpuK hpu using hmax
  let l : Fin m → ℝ := fun i => pl i i
  let u : Fin m → ℝ := fun i => pu i i
  let a : Fin m → ℝ := fun i => max 0 (u i - r)
  let b : Fin m → ℝ := fun i => l i + r
  have hl0 (i : Fin m) : 0 ≤ l i := (hprob (hplK i)).1 i
  have hwidth (i : Fin m) : u i - l i ≤ w :=
    (abs_le.mp (hdiam (pu i) (hpuK i) (pl i) (hplK i) i)).2
  have hab (i : Fin m) : a i ≤ b i := by
    apply max_le
    · dsimp [b]; linarith [hl0 i]
    · dsimp [b]; linarith [hwidth i]
  have active_sum (S : Finset (Fin m)) (hS : S.Nonempty) :
      (∑ i ∈ S, u i) ≤ 1 + ((S.card : ℝ) - 1) * w := by
    obtain ⟨j, hj⟩ := hS
    have hpoint (i : Fin m) :
        u i ≤ pu j i + w - (if i = j then w else 0) := by
      by_cases hij : i = j
      · subst i; simp [u]
      · simp only [if_neg hij, sub_zero]
        have hd := (abs_le.mp (hdiam (pu i) (hpuK i) (pu j) (hpuK j) i)).2
        dsimp [u]
        linarith
    have hs := Finset.sum_le_sum (s := S) (fun i _ => hpoint i)
    have hmass : (∑ i ∈ S, pu j i) ≤ 1 := by
      calc
        _ ≤ ∑ i, pu j i := Finset.sum_le_univ_sum_of_nonneg
          (fun i => (hprob (hpuK j)).1 i)
        _ = 1 := (hprob (hpuK j)).2
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul, Finset.sum_ite_eq', hj, if_true] at hs
    nlinarith
  have ha : (∑ i, a i) ≤ 1 := by
    let S : Finset (Fin m) := Finset.univ.filter (fun i => r < u i)
    have heq : (∑ i, a i) = ∑ i ∈ S, (u i - r) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : r < u i
      · simp [a, hi, max_eq_right (sub_nonneg.mpr hi.le)]
      · simp [a, hi, max_eq_left (sub_nonpos.mpr (le_of_not_gt hi))]
    rw [heq]
    rcases S.eq_empty_or_nonempty with hS | hS
    · simp [hS]
    · have hs := active_sum S hS
      have hcard : (S.card : ℝ) ≤ m := by
        have hc : S.card ≤ m := by
          simpa only [Finset.card_univ, Fintype.card_fin] using
            (Finset.card_le_card (Finset.subset_univ S))
        exact_mod_cast hc
      have hc := mul_le_mul_of_nonneg_right hcard (sub_nonneg.mpr hrw)
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      nlinarith [hmr]
  have hb : 1 ≤ ∑ i, b i := by
    let j : Fin m := ⟨0, by omega⟩
    have hpoint (i : Fin m) : pl j i ≤ l i + w - (if i = j then w else 0) := by
      by_cases hij : i = j
      · subst i
        simp [l]
      · simp only [if_neg hij, sub_zero]
        have hd := (abs_le.mp (hdiam (pl j) (hplK j) (pl i) (hplK i) i)).2
        dsimp [l]
        linarith
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at hs
    rw [(hprob (hplK j)).2] at hs
    simp only [b, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    nlinarith [hmr]
  obtain ⟨q, hq, hqsum⟩ := interval_mass a b hab ha hb
  refine ⟨q, ⟨fun i => (le_max_left 0 (u i - r)).trans (hq i).1, hqsum⟩, ?_⟩
  intro p hp i
  have hlo := hpl i p hp
  have hhi := hpu i p hp
  have hqa : u i - r ≤ q i := (le_max_right 0 (u i - r)).trans (hq i).1
  have hqb : q i ≤ l i + r := (hq i).2
  apply abs_le.mpr
  dsimp [l, u] at hqa hqb
  change -r ≤ p i - q i ∧ p i - q i ≤ r
  constructor <;> linarith


local notation "Source" => (fun m : ℕ => {p : Fin m → ℝ // p ∈ stdSimplex ℝ (Fin m)})
local notation "Datum" => (fun m : ℕ => ℝ × (Fin m → ℝ))

private def Fits {m : ℕ} (ε : ℝ) (p : Source m) (y : Datum m) : Prop :=
  |y.1 - 1| ≤ ε ∧ ∀ i, |y.2 i - (1 - p.val i)| ≤ ε

private theorem probability_estimator_upper {m : ℕ} (hm : 2 ≤ m)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ A : Datum m → Source m,
      ∀ p y, Fits ε p y →
        ‖(A y).val - p.val‖ ≤ (1 - 1 / (m : ℝ)) * min (2 * ε) 1 := by
  classical
  let w : ℝ := min (2 * ε) 1
  have hw : 0 ≤ w := le_min (by positivity) zero_le_one
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hr : 0 ≤ (1 - 1 / (m : ℝ)) * w :=
    mul_nonneg (sub_nonneg.mpr ((div_le_one hmpos).mpr (by linarith))) hw
  have hc (y : Datum m) : ∃ q ∈ stdSimplex ℝ (Fin m),
      ∀ p : Source m, Fits ε p y → ∀ i,
        |p.val i - q i| ≤ (1 - 1 / (m : ℝ)) * w := by
    let K : Set (Fin m → ℝ) :=
      stdSimplex ℝ (Fin m) ∩ {p | ∀ i, |y.2 i - (1 - p i)| ≤ ε}
    have hcompact : IsCompact K := by
      apply (isCompact_stdSimplex ℝ (Fin m)).inter_right
      have heq : {p : Fin m → ℝ | ∀ i, |y.2 i - (1 - p i)| ≤ ε} =
          ⋂ i, {p : Fin m → ℝ | |y.2 i - (1 - p i)| ≤ ε} := by ext; simp
      rw [heq]
      apply isClosed_iInter
      intro i
      exact isClosed_le
        ((continuous_const.sub (continuous_const.sub (continuous_apply i))).abs)
        continuous_const
    by_cases hne : K.Nonempty
    · have hdiam : ∀ p ∈ K, ∀ q ∈ K, ∀ i, |p i - q i| ≤ w := by
        intro p hp q hq i
        have hpε := abs_le.mp (hp.2 i)
        have hqε := abs_le.mp (hq.2 i)
        have hp01 := mem_Icc_of_mem_stdSimplex hp.1 i
        have hq01 := mem_Icc_of_mem_stdSimplex hq.1 i
        apply le_min
        · apply abs_le.mpr; constructor <;> linarith
        · apply abs_le.mpr; constructor <;> linarith [hp01.1,hp01.2,hq01.1,hq01.2]
      obtain ⟨q, hq, hbound⟩ := simplex_common_center hm K hcompact hne
        (fun _ hp => hp.1) w hw hdiam
      exact ⟨q, hq, fun p hp => hbound p.val ⟨p.property, hp.2⟩⟩
    · let j : Fin m := ⟨0, by omega⟩
      refine ⟨Pi.single j 1, single_mem_stdSimplex ℝ j, ?_⟩
      intro p hp
      exact (hne ⟨p.val, p.property, hp.2⟩).elim
  choose c hcp hcb using hc
  refine ⟨fun y => ⟨c y, hcp y⟩, ?_⟩
  intro p y hp
  apply (pi_norm_le_iff_of_nonneg hr).mpr
  intro i
  simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm] using hcb y p hp i

private theorem probability_estimator_lower {m : ℕ} (hm : 2 ≤ m)
    (ε : ℝ) (hε : 0 ≤ ε) (A : Datum m → Source m) :
    ∃ p y, Fits ε p y ∧
      (1 - 1 / (m : ℝ)) * min (2 * ε) 1 ≤ ‖(A y).val - p.val‖ := by
  classical
  let w : ℝ := min (2 * ε) 1
  have hw0 : 0 ≤ w := le_min (by positivity) zero_le_one
  have hw1 : w ≤ 1 := min_le_right _ _
  have hwε : w ≤ 2 * ε := min_le_left _ _
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  let b : ℝ := (1 - w) / m
  have hb0 : 0 ≤ b := div_nonneg (by linarith) hmpos.le
  let y : Datum m := (1, fun _ => 1 - b - w / 2)
  obtain ⟨j, _, hj⟩ := Finset.exists_le_of_sum_le
    (s := Finset.univ) (f := (A y).val) (g := fun _ => 1 / (m : ℝ))
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ (by
      simp only [(A y).property.2, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one_div_cancel hmne, le_refl])
  let p : Source m := ⟨fun i => b + if i = j then w else 0, by
    constructor
    · intro i; dsimp only; split_ifs <;> linarith
    · simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      dsimp [b]
      field_simp
      ring⟩
  refine ⟨p, y, ?_, ?_⟩
  · constructor
    · simpa only [y, sub_self, abs_zero] using hε
    · intro i
      change |(1-b-w/2) - (1-(b+if i=j then w else 0))| ≤ ε
      split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith
  · have hnorm := norm_le_pi_norm ((A y).val - p.val) j
    simp only [Pi.sub_apply, Real.norm_eq_abs] at hnorm
    have hjval : p.val j = b + w := by simp [p]
    rw [hjval] at hnorm
    have hid : b + w - 1 / (m : ℝ) = (1 - 1 / (m : ℝ)) * w := by
      dsimp [b]
      ring
    have habs := neg_le_abs ((A y).val j - (b + w))
    change (1 - 1 / (m : ℝ)) * w ≤ _
    linarith

private theorem fits_iff {m : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (p : Source m) (y : Datum m) : Fits ε p y ↔ ‖y - (1, fun i => 1 - p.val i)‖ ≤ ε := by
  simp only [norm_prod_le_iff, pi_norm_le_iff_of_nonneg hε, Real.norm_eq_abs]
  rfl

/-- Deterministic minimax risk over every probability source and every bounded
additive noise, including the empty-operation coordinate. -/
theorem simplex_deletion_minimax {m : ℕ} (hm : 2 ≤ m) (ε : ℝ) (hε : 0 ≤ ε) :
    (⨅ A : Datum m → Source m,
      worstCaseCost {s : Source m × Datum m | ‖s.2‖ ≤ ε}
        (fun s A => ENNReal.ofReal
          ‖(A ((1, fun i => 1 - s.1.val i) + s.2)).val - s.1.val‖) A) =
      ENNReal.ofReal ((1 - 1 / (m : ℝ)) * min (2 * ε) 1) := by
  obtain ⟨A, hA⟩ := probability_estimator_upper hm ε hε
  apply le_antisymm
  · apply (iInf_le _ A).trans
    apply iSup_le
    rintro ⟨⟨p, η⟩, hη⟩
    apply ENNReal.ofReal_le_ofReal
    apply hA p _
    apply (fits_iff hε p _).mpr
    simpa only [add_sub_cancel_left] using (show ‖η‖ ≤ ε from hη)
  · apply le_iInf
    intro A
    obtain ⟨p, y, hp, hl⟩ := probability_estimator_lower hm ε hε A
    apply (ENNReal.ofReal_le_ofReal hl).trans
    apply le_iSup_of_le
      (⟨(p, y - (1, fun i => 1 - p.val i)), (fits_iff hε p y).mp hp⟩ :
        {s : Source m × Datum m | ‖s.2‖ ≤ ε})
    simp only [add_sub_cancel, le_refl]

#print axioms simplex_common_center
#print axioms simplex_deletion_minimax

end D5.S3.Observer.MetricGeometry.SimplexDeletionMinimax
