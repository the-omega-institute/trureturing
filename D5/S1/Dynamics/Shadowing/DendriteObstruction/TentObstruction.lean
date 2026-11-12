/- GID: D5/S1/Dynamics/Shadowing/DendriteObstruction/TentObstruction
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/DendriteObstruction/TentObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform continuity obstructs arbitrarily deep tent lifts of a path. -/

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic

/-! The oscillation obstruction in the classical continuum expansion argument. -/

open Set Function

namespace D5.S1.Dynamics.Shadowing.DendriteObstruction

/-- The two-branch tent map on the real line. -/
def continuumTent (t : ℝ) : ℝ := min (2 * t) (2 - 2 * t)

/-- The two affine inverse branches on the closed unit interval. -/
theorem continuumTent_half {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    continuumTent (t / 2) = t ∧ continuumTent (1 - t / 2) = t := by
  dsimp [continuumTent]
  constructor
  · have he : 2 * (t / 2) = t := by ring
    rw [he, min_eq_left_iff]
    linarith [ht.2]
  · have he : 2 - 2 * (1 - t / 2) = t := by ring
    rw [he, min_eq_right_iff]
    linarith [ht.2]

private theorem tent_dyadic (m j : ℕ) (hj : j ≤ 2 ^ m) :
    continuumTent^[m] ((j : ℝ) / 2 ^ m) = (j % 2 : ℕ) := by
  induction m generalizing j with
  | zero =>
      have : j = 0 ∨ j = 1 := by norm_num at hj; omega
      rcases this with rfl | rfl <;> norm_num
  | succ m ih =>
      rw [iterate_succ_apply]
      have hp : (0 : ℝ) < 2 ^ m := by positivity
      by_cases hhalf : j ≤ 2 ^ m
      · have hrange : (j : ℝ) / 2 ^ m ∈ Icc (0 : ℝ) 1 := by
          constructor
          · positivity
          · apply (div_le_one hp).mpr
            exact_mod_cast hhalf
        have he : (j : ℝ) / 2 ^ (m + 1) = ((j : ℝ) / 2 ^ m) / 2 := by
          rw [pow_succ, div_mul_eq_div_div]
        rw [he, (continuumTent_half hrange).1]
        exact ih j hhalf
      · let k := 2 ^ (m + 1) - j
        have hk : k ≤ 2 ^ m := by dsimp [k]; rw [pow_succ] at *; omega
        have heven : 2 ^ (m + 1) % 2 = 0 := by simp [pow_succ]
        have hmod : k % 2 = j % 2 := by dsimp [k]; omega
        have hrange : (k : ℝ) / 2 ^ m ∈ Icc (0 : ℝ) 1 := by
          constructor
          · positivity
          · apply (div_le_one hp).mpr
            exact_mod_cast hk
        have hkcast : (k : ℝ) = 2 ^ (m + 1) - j := by
          dsimp [k]
          rw [Nat.cast_sub hj]
          push_cast
          rfl
        have he : (j : ℝ) / 2 ^ (m + 1) = 1 - ((k : ℝ) / 2 ^ m) / 2 := by
          rw [hkcast, pow_succ]
          field_simp
          ring
        rw [he, (continuumTent_half hrange).2, ih k hk, hmod]

private theorem ordered_hits {u : ℝ → ℝ} (hu : ContinuousOn u (Icc (0 : ℝ) 1))
    (hu0 : u 0 = 0) (hu1 : 1 / 2 ≤ u 1) :
    ∃ t : Icc (0 : ℝ) (1 / 2) → ℝ,
      (∀ v, t v ∈ Icc (0 : ℝ) 1) ∧ StrictMono t ∧ ∀ v, u (t v) = v := by
  classical
  have hex (v : Icc (0 : ℝ) (1 / 2)) :
      ∃ t ∈ Icc (0 : ℝ) 1 ∩ u ⁻¹' {v.1},
        ∀ s ∈ Icc (0 : ℝ) 1 ∩ u ⁻¹' {v.1}, t ≤ s := by
    have hne : (Icc (0 : ℝ) 1 ∩ u ⁻¹' {v.1}).Nonempty := by
      obtain ⟨s, hs, he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hu
        (show v.1 ∈ Icc (u 0) (u 1) from ⟨by rw [hu0]; exact v.2.1, v.2.2.trans hu1⟩)
      exact ⟨s, hs, he⟩
    have hc : IsCompact (Icc (0 : ℝ) 1 ∩ u ⁻¹' {v.1}) :=
      isCompact_Icc.of_isClosed_subset
        (hu.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
    obtain ⟨t, ht, hmin⟩ := hc.exists_isMinOn hne continuous_id.continuousOn
    exact ⟨t, ht, hmin⟩
  choose t ht hmin using hex
  refine ⟨t, fun v => (ht v).1, ?_, fun v => (ht v).2⟩
  intro a b hab
  have htb := (ht b).1
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc htb.1
    (hu.mono (Icc_subset_Icc le_rfl htb.2))
    (show a.1 ∈ Icc (u 0) (u (t b)) from
      ⟨by rw [hu0]; exact a.2.1, by rw [(ht b).2]; exact le_of_lt hab⟩)
  have hle : t a ≤ t b := (hmin a s ⟨⟨hs.1, hs.2.trans htb.2⟩, he⟩).trans hs.2
  apply lt_of_le_of_ne hle
  intro heq
  have hv := congrArg u heq
  rw [(ht a).2, (ht b).2] at hv
  exact (ne_of_lt hab) (Subtype.ext hv)

/-- A fixed continuous path cannot have tent-map lifts of every finite depth
whose endpoint values are zero and two thirds. -/
theorem no_unbounded_tent_lifts {h : ℝ → ℝ} (hh : ContinuousOn h (Icc (0 : ℝ) 1))
    (lifts : ∀ m : ℕ, ∃ u : ℝ → ℝ, ContinuousOn u (Icc (0 : ℝ) 1) ∧
      u 0 = 0 ∧ u 1 = 2 / 3 ∧ ∀ t ∈ Icc (0 : ℝ) 1, h t = continuumTent^[m] (u t)) :
    False := by
  obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hh) (1 / 2) (by norm_num)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (1 / δ) (by norm_num : (1 : ℝ) < 2)
  have hbig : 1 < (2 : ℝ) ^ m * δ := (div_lt_iff₀ hδ).mp hm
  obtain ⟨u, hu, hu0, hu1, heq⟩ := lifts (m + 1)
  obtain ⟨t, ht, hmono, htu⟩ := ordered_hits hu hu0 (by rw [hu1]; norm_num)
  let N := 2 ^ m
  have hN : 0 < N := by dsimp [N]; positivity
  let v : Fin (N + 1) → Icc (0 : ℝ) (1 / 2) := fun j =>
    ⟨(j.1 : ℝ) / 2 ^ (m + 1), by
      constructor
      · positivity
      · have hj : (j.1 : ℝ) ≤ (2 : ℝ) ^ m := by exact_mod_cast (Nat.le_of_lt_succ j.2)
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (m + 1))).mpr
        rw [pow_succ]
        linarith⟩
  let s : Fin (N + 1) → ℝ := fun j => t (v j)
  have hs (j : Fin (N + 1)) : s j ∈ Icc (0 : ℝ) 1 := ht _
  have hsmono : StrictMono s := by
    intro a b hab
    apply hmono
    change (a.1 : ℝ) / 2 ^ (m + 1) < (b.1 : ℝ) / 2 ^ (m + 1)
    exact (div_lt_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hab)
  have hval (j : Fin (N + 1)) : h (s j) = (j.1 % 2 : ℕ) := by
    rw [heq _ (hs j)]
    change continuumTent^[m + 1] (u (t (v j))) = _
    rw [htu]
    exact tent_dyadic (m + 1) j.1 (by
      have := Nat.le_of_lt_succ j.2
      dsimp [N] at this
      rw [pow_succ]
      omega)
  have hgap (j : ℕ) (hj : j < N) :
      δ ≤ s ⟨j + 1, by omega⟩ - s ⟨j, by omega⟩ := by
    by_contra hbad
    have hlt : dist (s ⟨j, by omega⟩) (s ⟨j + 1, by omega⟩) < δ := by
      rw [Real.dist_eq, abs_of_nonpos (le_of_lt (sub_neg.mpr (hsmono (by simp)) ))]
      linarith
    have hout := huc _ (hs ⟨j, by omega⟩) _ (hs ⟨j + 1, by omega⟩) hlt
    rw [hval, hval, Real.dist_eq] at hout
    have hjmod : j % 2 = 0 ∨ j % 2 = 1 := by omega
    rcases hjmod with hmod | hmod
    · have hnext : (j + 1) % 2 = 1 := by omega
      norm_num [hmod, hnext] at hout
    · have hnext : (j + 1) % 2 = 0 := by omega
      norm_num [hmod, hnext] at hout
  have hsum : ∀ k (hk : k ≤ N), (k : ℝ) * δ ≤ s ⟨k, by omega⟩ - s ⟨0, by omega⟩ := by
    intro k
    induction k with
    | zero => intro hk; simp
    | succ k ih =>
        intro hk
        have hi := ih (by omega)
        have hg := hgap k (by omega)
        push_cast
        linarith
  have hb := hsum N le_rfl
  have h0 := hs ⟨0, by omega⟩
  have hlast := hs ⟨N, by omega⟩
  have hcast : (N : ℝ) = 2 ^ m := by dsimp [N]; norm_cast
  rw [hcast] at hb
  linarith [h0.1, hlast.2]

end D5.S1.Dynamics.Shadowing.DendriteObstruction
