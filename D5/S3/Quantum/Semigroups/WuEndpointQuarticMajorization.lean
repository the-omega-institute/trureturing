/- GID: D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuEndpointQuarticMajorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quartic prefix majorization and the physical trace floor for the Wu endpoint. -/

import D5.S3.Quantum.Semigroups.WuEndpointQuarticPrefix
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic

/-!
# Quartic majorization for the Wu endpoint

The three proper-prefix constraints in dimension four become bounds on each
coordinate and each pair sum after allowing permutations. This makes a
two-sided transfer at the first slack prefix feasible even at ties.
-/

noncomputable section

open Filter Set
open scoped BigOperators ComplexOrder Topology

namespace WuRankOneEndpointFloor

abbrev Spectrum4 := Fin 4 → ℝ

private def quartic (κ t : ℝ) : ℝ := t ^ 4 - κ * t ^ 3

def wuQuarticSum (κ : ℝ) (z : Spectrum4) : ℝ := ∑ i, quartic κ (z i)

private def total (z : Spectrum4) : ℝ := ∑ i, z i

private def admissible (v : Spectrum4) : Set Spectrum4 :=
  Icc (fun _ => v 3) (fun _ => v 0) ∩
    ({z | total z = total v} ∩ {z | ∀ i j, i ≠ j → z i + z j ≤ v 0 + v 1})

private theorem continuous_total : Continuous total := by
  unfold total
  exact continuous_finsetSum Finset.univ fun i _ => continuous_apply i

private theorem admissible_compact (v : Spectrum4) : IsCompact (admissible v) := by
  unfold admissible
  refine (isCompact_Icc (a := fun _ : Fin 4 => v 3) (b := fun _ : Fin 4 => v 0)).inter_right ?_
  have htotal : IsClosed {z : Spectrum4 | total z = total v} :=
    isClosed_eq continuous_total continuous_const
  refine htotal.inter ?_
  have hset : {z : Spectrum4 | ∀ i j, i ≠ j → z i + z j ≤ v 0 + v 1} =
      ⋂ i : Fin 4, ⋂ j : Fin 4, {z : Spectrum4 | i ≠ j → z i + z j ≤ v 0 + v 1} := by
    ext z
    simp
  rw [hset]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  by_cases hij : i = j
  · simp [hij]
  · simpa [hij] using (isClosed_le ((continuous_apply i).add (continuous_apply j))
      (continuous_const (y := v 0 + v 1)))

private theorem adjacent {z : Spectrum4} (hz : Antitone z) :
    z 1 ≤ z 0 ∧ z 2 ≤ z 1 ∧ z 3 ≤ z 2 :=
  ⟨hz (by decide : (0 : Fin 4) ≤ 1), hz (by decide : (1 : Fin 4) ≤ 2),
    hz (by decide : (2 : Fin 4) ≤ 3)⟩

private theorem admissible_of_prefix {v z : Spectrum4} (hz : Antitone z)
    (hp : ∀ k, endpointPrefixSum z k ≤ endpointPrefixSum v k)
    (ht : total z = total v) : z ∈ admissible v := by
  have h0 : z 0 ≤ v 0 := hp 0
  have h1 : z 0 + z 1 ≤ v 0 + v 1 := hp 1
  have h2 : z 0 + z 1 + z 2 ≤ v 0 + v 1 + v 2 := hp 2
  have h3 : v 3 ≤ z 3 := by
    simp only [total, Fin.sum_univ_four] at ht
    linarith only [ht, h2]
  refine ⟨⟨fun i => h3.trans (hz (Fin.le_last i)), fun i => (hz (Fin.zero_le i)).trans h0⟩,
    ht, ?_⟩
  intro i j hij
  obtain ⟨h01, h12, h23⟩ := adjacent hz
  fin_cases i <;> fin_cases j <;>
    try (exact (hij rfl).elim) <;>
    try (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]) <;>
    linarith only [h01, h12, h23, h1]

private theorem perm_admissible {v z : Spectrum4} (hz : z ∈ admissible v)
    (e : Equiv.Perm (Fin 4)) : z ∘ e ∈ admissible v := by
  refine ⟨⟨fun i => hz.1.1 (e i), fun i => hz.1.2 (e i)⟩, ?_, ?_⟩
  · exact (e.sum_comp z).trans hz.2.1
  · exact fun i j hij => hz.2.2 (e i) (e j) (e.injective.ne hij)

private theorem exists_sorted_max {v : Spectrum4} (hv : Antitone v) (κ : ℝ) :
    ∃ z ∈ admissible v, Antitone z ∧ IsMaxOn (wuQuarticSum κ) (admissible v) z := by
  have hv' : v ∈ admissible v := admissible_of_prefix hv (fun _ => le_rfl) rfl
  have hc : Continuous (wuQuarticSum κ) := by
    have hq : Continuous (quartic κ) := by
      unfold quartic
      fun_prop
    unfold wuQuarticSum
    exact continuous_finsetSum Finset.univ fun i _ => hq.comp (continuous_apply i)
  obtain ⟨z, hz, hm⟩ := (admissible_compact v).exists_isMaxOn ⟨v, hv'⟩ hc.continuousOn
  let e := Tuple.sort (fun i => -z i)
  refine ⟨z ∘ e, perm_admissible hz e, ?_, ?_⟩
  · intro i j hij
    exact neg_le_neg_iff.mp (Tuple.monotone_sort (fun i => -z i) hij)
  · have he : wuQuarticSum κ (z ∘ e) = wuQuarticSum κ z :=
      e.sum_comp (fun i => quartic κ (z i))
    exact isMaxOn_iff.mpr fun w hw => (isMaxOn_iff.mp hm w hw).trans_eq he.symm

private def centeredPair (κ m d : ℝ) : ℝ := quartic κ (m + d) + quartic κ (m - d)

private theorem centeredPair_formula (κ m d : ℝ) :
    centeredPair κ m d =
      2 * quartic κ m + (12 * m ^ 2 - 6 * κ * m) * d ^ 2 + 2 * d ^ 4 := by
  unfold centeredPair quartic
  ring

private theorem centeredPair_change (κ m d t : ℝ) :
    centeredPair κ m (d + t) - centeredPair κ m d =
      let Δ := (d + t) ^ 2 - d ^ 2
      2 * Δ ^ 2 + (4 * d ^ 2 + 12 * m ^ 2 - 6 * κ * m) * Δ := by
  rw [centeredPair_formula, centeredPair_formula]
  dsimp
  ring

private theorem centeredPair_hasDerivAt (κ m d : ℝ) :
    HasDerivAt (fun t => centeredPair κ m (d + t))
      (2 * d * (4 * d ^ 2 + 12 * m ^ 2 - 6 * κ * m)) 0 := by
  have hl : HasDerivAt (fun t : ℝ => d + t) 1 0 :=
    (hasDerivAt_id' (0 : ℝ)).const_add d
  have h := (((hl.pow 2).const_mul (12 * m ^ 2 - 6 * κ * m)).add
    ((hl.pow 4).const_mul 2)).const_add (2 * quartic κ m)
  convert h using 1
  · funext t
    exact centeredPair_formula κ m (d + t)
  · simp <;> ring

private theorem centeredPair_localMax {κ m d : ℝ} (hm : 0 ≤ m) (hd : 0 ≤ d)
    (hmax : IsLocalMax (fun t => centeredPair κ m (d + t)) 0) :
    d = 0 ∧ m ≤ κ / 2 := by
  have hstationary := hmax.hasDerivAt_eq_zero (centeredPair_hasDerivAt κ m d)
  have hcoeff : 4 * d ^ 2 + 12 * m ^ 2 - 6 * κ * m < 0 := by
    by_contra! hc
    have hnear : ∀ᶠ t : ℝ in 𝓝 0, centeredPair κ m (d + t) ≤ centeredPair κ m (d + 0) :=
      hmax
    obtain ⟨ε, hε, hεmax⟩ := Metric.eventually_nhds_iff.mp hnear
    have ht : 0 < ε / 2 := by positivity
    have hdist : dist (ε / 2) (0 : ℝ) < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht]
      linarith
    have hΔ : 0 < (d + ε / 2) ^ 2 - d ^ 2 := by
      have hpos : 0 < (ε / 2) * (2 * d + ε / 2) :=
        mul_pos ht (by linarith)
      nlinarith only [hpos]
    have hchange := centeredPair_change κ m d (ε / 2)
    dsimp only at hchange
    have hstrict : 0 < centeredPair κ m (d + ε / 2) - centeredPair κ m d := by
      rw [hchange]
      exact add_pos_of_pos_of_nonneg (mul_pos (by norm_num) (pow_pos hΔ 2))
        (mul_nonneg hc hΔ.le)
    have hle := hεmax hdist
    rw [add_zero] at hle
    exact (not_lt_of_ge (sub_nonpos.mpr hle)) hstrict
  have hd0 : d = 0 := by
    rcases mul_eq_zero.mp hstationary with h | h
    · linarith
    · exact (hcoeff.ne h).elim
  refine ⟨hd0, ?_⟩
  by_contra! hlarge
  have hprod := mul_nonneg hm (show 0 ≤ 2 * m - κ by linarith)
  rw [hd0] at hcoeff
  nlinarith only [hcoeff, hprod]

private theorem quartic_hasDerivAt (κ x : ℝ) :
    HasDerivAt (quartic κ) (4 * x ^ 3 - 3 * κ * x ^ 2) x := by
  have h := ((hasDerivAt_id' x).pow 4).sub (((hasDerivAt_id' x).pow 3).const_mul κ)
  convert h using 1 <;> simp [quartic] <;> ring

private theorem quartic_deriv_hasDerivAt (κ x : ℝ) :
    HasDerivAt (fun t => 4 * t ^ 3 - 3 * κ * t ^ 2) (6 * x * (2 * x - κ)) x := by
  have h := (((hasDerivAt_id' x).pow 3).const_mul 4).sub
    (((hasDerivAt_id' x).pow 2).const_mul (3 * κ))
  convert h using 1 <;> simp <;> ring

private theorem quartic_concave (κ : ℝ) : ConcaveOn ℝ (Icc 0 (κ / 2)) (quartic κ) := by
  refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _) ?_ ?_ ?_ ?_
  · exact (show Continuous (quartic κ) by unfold quartic; fun_prop).continuousOn
  · exact fun x _ => (quartic_hasDerivAt κ x).hasDerivWithinAt
  · exact fun x _ => (quartic_deriv_hasDerivAt κ x).hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Icc 0 (κ / 2) := interior_subset hx
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) hx'.1)
      (by linarith only [hx'.2])

private theorem tail_jensen {n : ℕ} (hn : 0 < n) {κ : ℝ} (z : Fin n → ℝ)
    (hz : ∀ i, z i ∈ Icc 0 (κ / 2)) :
    (∑ i, quartic κ (z i)) ≤ (n : ℝ) * quartic κ ((∑ i, z i) / (n : ℝ)) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have h := (quartic_concave κ).le_map_sum (t := Finset.univ)
    (w := fun _ : Fin n => (n : ℝ)⁻¹) (p := z)
    (fun _ _ => inv_nonneg.mpr hn'.le)
    (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_inv_cancel₀ hn'.ne']) (fun i _ => hz i)
  simp only [smul_eq_mul, ← Finset.mul_sum, ← div_eq_inv_mul] at h
  exact (div_le_iff₀' hn').mp h

private def transfer (z : Spectrum4) (i j : Fin 4) (t : ℝ) : Spectrum4 :=
  fun k => z k + (if k = i then t else 0) - (if k = j then t else 0)

private theorem transfer_left (z : Spectrum4) {i j : Fin 4} (hij : i ≠ j) (t : ℝ) :
    transfer z i j t i = z i + t := by simp [transfer, hij]

private theorem transfer_right (z : Spectrum4) {i j : Fin 4} (hij : i ≠ j) (t : ℝ) :
    transfer z i j t j = z j - t := by simp [transfer, hij.symm]

private theorem transfer_other (z : Spectrum4) {i j k : Fin 4}
    (hki : k ≠ i) (hkj : k ≠ j) (t : ℝ) :
    transfer z i j t k = z k := by simp [transfer, hki, hkj]

private theorem total_transfer (z : Spectrum4) (i j : Fin 4) (t : ℝ) :
    total (transfer z i j t) = total z := by
  simp only [total, transfer, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Fintype.sum_ite_eq', add_sub_cancel_right]

private theorem quarticSum_transfer_sub (κ : ℝ) (z : Spectrum4) {i j : Fin 4}
    (hij : i ≠ j) (t : ℝ) :
    wuQuarticSum κ (transfer z i j t) - wuQuarticSum κ z =
      quartic κ (z i + t) - quartic κ (z i) + (quartic κ (z j - t) - quartic κ (z j)) := by
  have hterm (k : Fin 4) : quartic κ (transfer z i j t k) - quartic κ (z k) =
      (if k = i then quartic κ (z i + t) - quartic κ (z i) else 0) +
      (if k = j then quartic κ (z j - t) - quartic κ (z j) else 0) := by
    by_cases hki : k = i
    · subst k
      simp [transfer_left z hij, hij]
    by_cases hkj : k = j
    · subst k
      simp [transfer_right z hij, hki]
    · simp [transfer_other z hki hkj, hki, hkj]
  have h := Finset.sum_congr (s₁ := Finset.univ) rfl (fun k _ => hterm k)
  simpa only [wuQuarticSum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Fintype.sum_ite_eq'] using h

/-- A transfer preserves the pair sum of the moving coordinates. The only
other affected inequalities need slack at the starting point. -/
private theorem eventually_transfer_mem {v z : Spectrum4} {i j : Fin 4}
    (hz : z ∈ admissible v) (hij : i ≠ j) (horder : z j ≤ z i)
    (hlo : v 3 < z j) (hhi : z i < v 0)
    (hp : ∀ k, k ≠ i → k ≠ j → z i + z k < v 0 + v 1 ∧ z j + z k < v 0 + v 1) :
    ∀ᶠ t : ℝ in 𝓝 0, transfer z i j t ∈ admissible v := by
  have hci : Continuous (fun t : ℝ => z i + t) := continuous_const.add continuous_id
  have hcj : Continuous (fun t : ℝ => z j - t) := continuous_const.sub continuous_id
  have hi : ∀ᶠ t : ℝ in 𝓝 0, v 3 < z i + t ∧ z i + t < v 0 :=
    (continuous_const.continuousAt.eventually_lt (x₀ := (0 : ℝ)) hci.continuousAt
      (by simpa using hlo.trans_le horder)).and
      (hci.continuousAt.eventually_lt (x₀ := (0 : ℝ)) continuous_const.continuousAt
        (by simpa using hhi))
  have hj : ∀ᶠ t : ℝ in 𝓝 0, v 3 < z j - t ∧ z j - t < v 0 :=
    (continuous_const.continuousAt.eventually_lt (x₀ := (0 : ℝ)) hcj.continuousAt
      (by simpa using hlo)).and
      (hcj.continuousAt.eventually_lt (x₀ := (0 : ℝ)) continuous_const.continuousAt
        (by simpa using lt_of_le_of_lt horder hhi))
  have hpair : ∀ᶠ t : ℝ in 𝓝 0, ∀ k, k ≠ i → k ≠ j →
      z i + t + z k < v 0 + v 1 ∧ z j - t + z k < v 0 + v 1 := by
    apply eventually_all.mpr
    intro k
    by_cases hki : k = i
    · exact Eventually.of_forall fun _ h _ => (h hki).elim
    by_cases hkj : k = j
    · exact Eventually.of_forall fun _ _ h => (h hkj).elim
    have hleft := (hci.add continuous_const : Continuous (fun t => z i + t + z k)).continuousAt
    have hright := (hcj.add continuous_const : Continuous (fun t => z j - t + z k)).continuousAt
    have hp₁ := hleft.eventually_lt (x₀ := (0 : ℝ)) continuous_const.continuousAt
      (show z i + 0 + z k < v 0 + v 1 by simpa using (hp k hki hkj).1)
    have hp₂ := hright.eventually_lt (x₀ := (0 : ℝ)) continuous_const.continuousAt
      (show z j - 0 + z k < v 0 + v 1 by simpa using (hp k hki hkj).2)
    exact (hp₁.and hp₂).mono fun _ h _ _ => h
  filter_upwards [hi, hj, hpair] with t hi' hj' hp'
  have hbox (k : Fin 4) : v 3 ≤ transfer z i j t k ∧ transfer z i j t k ≤ v 0 := by
    by_cases hki : k = i
    · subst k
      rw [transfer_left z hij]
      exact ⟨hi'.1.le, hi'.2.le⟩
    by_cases hkj : k = j
    · subst k
      rw [transfer_right z hij]
      exact ⟨hj'.1.le, hj'.2.le⟩
    · rw [transfer_other z hki hkj]
      exact ⟨hz.1.1 k, hz.1.2 k⟩
  refine ⟨⟨fun k => (hbox k).1, fun k => (hbox k).2⟩,
    (total_transfer z i j t).trans hz.2.1, ?_⟩
  have hboth : transfer z i j t i + transfer z i j t j ≤ v 0 + v 1 := by
    rw [transfer_left z hij, transfer_right z hij]
    linarith only [hz.2.2 i j hij]
  have hother (k : Fin 4) (hki : k ≠ i) (hkj : k ≠ j) :
      transfer z i j t i + transfer z i j t k ≤ v 0 + v 1 ∧
      transfer z i j t j + transfer z i j t k ≤ v 0 + v 1 := by
    rw [transfer_left z hij, transfer_right z hij, transfer_other z hki hkj]
    exact ⟨(hp' k hki hkj).1.le, (hp' k hki hkj).2.le⟩
  intro k l hkl
  rcases eq_or_ne k i with rfl | hki
  · rcases eq_or_ne l j with rfl | hlj
    · exact hboth
    · exact (hother l hkl.symm hlj).1
  rcases eq_or_ne k j with rfl | hkj
  · rcases eq_or_ne l i with rfl | hli
    · simpa only [add_comm] using hboth
    · exact (hother l hli hkl.symm).2
  rcases eq_or_ne l i with rfl | hli
  · simpa only [add_comm] using (hother k hki hkj).1
  rcases eq_or_ne l j with rfl | hlj
  · simpa only [add_comm] using (hother k hki hkj).2
  rw [transfer_other z hki hkj, transfer_other z hli hlj]
  exact hz.2.2 k l hkl

private theorem pair_at_max {κ : ℝ} {v z : Spectrum4} {i j : Fin 4}
    (hv : 0 ≤ v 3) (hz : z ∈ admissible v)
    (hmax : IsMaxOn (wuQuarticSum κ) (admissible v) z)
    (hij : i ≠ j) (horder : z j ≤ z i) (hlo : v 3 < z j) (hhi : z i < v 0)
    (hp : ∀ k, k ≠ i → k ≠ j → z i + z k < v 0 + v 1 ∧ z j + z k < v 0 + v 1) :
    z i = z j ∧ z i ≤ κ / 2 := by
  let m := (z i + z j) / 2
  let d := (z i - z j) / 2
  have hm : 0 ≤ m := by dsimp [m]; linarith only [hv, hlo, horder]
  have hd : 0 ≤ d := by dsimp [d]; linarith only [horder]
  have hplus (t : ℝ) : m + (d + t) = z i + t := by dsimp [m, d]; ring
  have hminus (t : ℝ) : m - (d + t) = z j - t := by dsimp [m, d]; ring
  have hlocal : IsLocalMax (fun t => centeredPair κ m (d + t)) 0 := by
    change ∀ᶠ t : ℝ in 𝓝 0, centeredPair κ m (d + t) ≤ centeredPair κ m (d + 0)
    filter_upwards [eventually_transfer_mem hz hij horder hlo hhi hp] with t ht
    have hle := isMaxOn_iff.mp hmax _ ht
    have hdiff := quarticSum_transfer_sub κ z hij t
    unfold centeredPair
    rw [hplus t, hminus t, hplus 0, hminus 0, add_zero, sub_zero]
    linarith only [hle, hdiff]
  obtain ⟨hd', hm'⟩ := centeredPair_localMax hm hd hlocal
  have he : z i = z j := by dsimp [d] at hd'; linarith only [hd']
  exact ⟨he, by dsimp [m] at hm'; linarith only [he, hm']⟩

private theorem quarticSum_le_of_concave_tail {κ : ℝ} {v z : Spectrum4}
    (k : Fin 4) (ht : total z = total v) (hprefix : ∀ i < k, z i = v i)
    (htail : ∀ i, k ≤ i → z i ∈ Icc 0 (κ / 2)) :
    wuQuarticSum κ z ≤ wuQuarticSum κ (endpointPrefixAverage k v) := by
  have htotal : z 0 + z 1 + z 2 + z 3 = v 0 + v 1 + v 2 + v 3 := by
    simpa only [total, Fin.sum_univ_four] using ht
  fin_cases k
  · have hj := tail_jensen (κ := κ) (by decide : 0 < 4) z
      (fun i => htail i (Fin.zero_le i))
    have hmean : spectralMoment 1 v = (z 0 + z 1 + z 2 + z 3) / 4 := by
      simp only [spectralMoment, pow_one, Fin.sum_univ_four]
      rw [htotal]
    simp [wuQuarticSum, endpointPrefixAverage, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hj ⊢
    rw [hmean]
    linarith only [hj]
  · have he₀ : z 0 = v 0 := hprefix 0 (by decide)
    have hmean : (v 1 + v 2 + v 3) / 3 = (z 1 + z 2 + z 3) / 3 := by
      linarith only [htotal, he₀]
    have hj := tail_jensen (κ := κ) (by decide : 0 < 3) (![z 1, z 2, z 3] : Fin 3 → ℝ)
      (by
        intro i
        fin_cases i
        · exact htail 1 (by decide)
        · exact htail 2 (by decide)
        · exact htail 3 (by decide))
    simp [wuQuarticSum, endpointPrefixAverage, Fin.sum_univ_four, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hj ⊢
    rw [he₀, hmean]
    linarith only [hj]
  · have he₀ : z 0 = v 0 := hprefix 0 (by decide)
    have he₁ : z 1 = v 1 := hprefix 1 (by decide)
    have hmean : (v 2 + v 3) / 2 = (z 2 + z 3) / 2 := by
      linarith only [htotal, he₀, he₁]
    have hj := tail_jensen (κ := κ) (by decide : 0 < 2) (![z 2, z 3] : Fin 2 → ℝ)
      (by
        intro i
        fin_cases i
        · exact htail 2 (by decide)
        · exact htail 3 (by decide))
    simp [wuQuarticSum, endpointPrefixAverage, Fin.sum_univ_four, Fin.sum_univ_two,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hj ⊢
    rw [he₀, he₁, hmean]
    linarith only [hj]
  · have he₀ : z 0 = v 0 := hprefix 0 (by decide)
    have he₁ : z 1 = v 1 := hprefix 1 (by decide)
    have he₂ : z 2 = v 2 := hprefix 2 (by decide)
    have he₃ : z 3 = v 3 := by linarith only [htotal, he₀, he₁, he₂]
    simp [wuQuarticSum, endpointPrefixAverage, Fin.sum_univ_four,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, he₀, he₁, he₂, he₃]

private theorem maximizer_le_prefixAverage {κ : ℝ} {v z : Spectrum4}
    (hv : Antitone v) (hv₀ : 0 ≤ v 3) (hz : z ∈ admissible v) (hzs : Antitone z)
    (hm : IsMaxOn (wuQuarticSum κ) (admissible v) z) :
    ∃ k : Fin 4, wuQuarticSum κ z ≤ wuQuarticSum κ (endpointPrefixAverage k v) := by
  obtain ⟨hv01, hv12, hv23⟩ := adjacent hv
  obtain ⟨hz01, hz12, hz23⟩ := adjacent hzs
  have htotal : z 0 + z 1 + z 2 + z 3 = v 0 + v 1 + v 2 + v 3 := by
    simpa only [total, Fin.sum_univ_four] using hz.2.1
  have hp₀ : z 0 ≤ v 0 := hz.1.2 0
  have hp₁ : z 0 + z 1 ≤ v 0 + v 1 := hz.2.2 0 1 (by decide)
  have hp₂ : z 0 + z 1 + z 2 ≤ v 0 + v 1 + v 2 := by
    linarith only [htotal, hz.1.1 3]
  have htail (i : Fin 4) (hi : z i ≤ κ / 2) :
      ∀ j, i ≤ j → z j ∈ Icc 0 (κ / 2) :=
    fun j hij => ⟨hv₀.trans (hz.1.1 j), (hzs hij).trans hi⟩
  -- The first slack prefix determines the adjacent pair to move. Earlier
  -- tight prefixes identify the entries that will be kept in the candidate.
  rcases lt_or_eq_of_le hp₀ with hslack | h0
  · have hlo : v 3 < z 1 := by
      linarith only [htotal, hslack, hv12, hv23, hz12, hz23]
    -- A tight pair (0, 2) would give z 2 ≤ v 2 by the third prefix,
    -- contradicting z 0 < v 0 and v 2 ≤ v 1.
    have h02 : z 0 + z 2 < v 0 + v 1 := by
      linarith only [hslack, hp₁, hp₂, hv12, hz12]
    have hout (k : Fin 4) (hk₀ : k ≠ 0) (hk₁ : k ≠ 1) :
        z 0 + z k < v 0 + v 1 ∧ z 1 + z k < v 0 + v 1 := by
      fin_cases k <;> try (exact (hk₀ rfl).elim) <;> try (exact (hk₁ rfl).elim) <;>
        try (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]) <;>
        constructor <;> linarith only [h02, hz01, hz23]
    have htop := (pair_at_max hv₀ hz hm (by decide : (0 : Fin 4) ≠ 1)
      hz01 hlo hslack hout).2
    exact ⟨0, quarticSum_le_of_concave_tail 0 hz.2.1
      (fun i hi => (not_lt_of_ge (Fin.zero_le i) hi).elim) (htail 0 htop)⟩
  rcases lt_or_eq_of_le hp₁ with hslack | h01
  · have hhi : z 1 < v 0 := by linarith only [hslack, h0, hv01]
    have hlo : v 3 < z 2 := by
      linarith only [htotal, h0, hslack, hv23, hz23]
    have hout (k : Fin 4) (hk₁ : k ≠ 1) (hk₂ : k ≠ 2) :
        z 1 + z k < v 0 + v 1 ∧ z 2 + z k < v 0 + v 1 := by
      fin_cases k <;> try (exact (hk₁ rfl).elim) <;> try (exact (hk₂ rfl).elim) <;>
        try (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]) <;>
        constructor <;> linarith only [hslack, hz01, hz12, hz23]
    have htop := (pair_at_max hv₀ hz hm (by decide : (1 : Fin 4) ≠ 2)
      hz12 hlo hhi hout).2
    refine ⟨1, quarticSum_le_of_concave_tail 1 hz.2.1 ?_ (htail 1 htop)⟩
    intro i hi
    fin_cases i <;> first | exact h0 | exact False.elim (by omega)
  have h1 : z 1 = v 1 := by linarith only [h01, h0]
  rcases lt_or_eq_of_le hp₂ with hslack | h012
  · have hlt : z 2 < v 2 := by linarith only [hslack, h0, h1]
    have hhi : z 2 < v 0 := hlt.trans_le (hv12.trans hv01)
    have hlo : v 3 < z 3 := by linarith only [htotal, h0, h1, hlt]
    have hout (k : Fin 4) (hk₂ : k ≠ 2) (hk₃ : k ≠ 3) :
        z 2 + z k < v 0 + v 1 ∧ z 3 + z k < v 0 + v 1 := by
      fin_cases k <;> try (exact (hk₂ rfl).elim) <;> try (exact (hk₃ rfl).elim) <;>
        try (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]) <;>
        constructor <;> linarith only [h0, h1, hlt, hv01, hv12, hz23]
    have htop := (pair_at_max hv₀ hz hm (by decide : (2 : Fin 4) ≠ 3)
      hz23 hlo hhi hout).2
    refine ⟨2, quarticSum_le_of_concave_tail 2 hz.2.1 ?_ (htail 2 htop)⟩
    intro i hi
    fin_cases i <;> first | exact h0 | exact h1 | exact False.elim (by omega)
  have h2 : z 2 = v 2 := by linarith only [h012, h0, h1]
  have h3 : z 3 = v 3 := by linarith only [htotal, h0, h1, h2]
  have he : z = v := by
    funext i
    fin_cases i <;> first | exact h0 | exact h1 | exact h2 | exact h3
  subst z
  exact ⟨3, le_rfl⟩

/-- A decreasing spectrum majorized by a nonnegative decreasing reference
spectrum is bounded by one of the four tail averages. -/
theorem wuQuartic_le_some_prefixAverage (κ : ℝ) {v y : Spectrum4}
    (hv : Antitone v) (hv₀ : 0 ≤ v 3) (hy : Antitone y)
    (hp : ∀ k, endpointPrefixSum y k ≤ endpointPrefixSum v k)
    (ht : (∑ i, y i) = ∑ i, v i) :
    ∃ k : Fin 4, wuQuarticSum κ y ≤ wuQuarticSum κ (endpointPrefixAverage k v) := by
  have hy' := admissible_of_prefix hy hp ht
  obtain ⟨z, hz, hzs, hm⟩ := exists_sorted_max hv κ
  obtain ⟨k, hk⟩ := maximizer_le_prefixAverage hv hv₀ hz hzs hm
  exact ⟨k, (isMaxOn_iff.mp hm y hy').trans hk⟩

def wuQuarticPrefixMax (κ : ℝ) (v : Spectrum4) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun k : Fin 4 =>
    wuQuarticSum κ (endpointPrefixAverage k v))

theorem wuQuartic_le_prefixMax (κ : ℝ) {v y : Spectrum4}
    (hv : Antitone v) (hv₀ : 0 ≤ v 3) (hy : Antitone y)
    (hp : ∀ k, endpointPrefixSum y k ≤ endpointPrefixSum v k)
    (ht : (∑ i, y i) = ∑ i, v i) :
    wuQuarticSum κ y ≤ wuQuarticPrefixMax κ v := by
  obtain ⟨k, hk⟩ := wuQuartic_le_some_prefixAverage κ hv hv₀ hy hp ht
  exact hk.trans (Finset.le_sup' _ (Finset.mem_univ k))

private theorem quarticSum_eq_moments (κ : ℝ) (z : Spectrum4) :
    wuQuarticSum κ z = 4 * (spectralMoment 4 z - κ * spectralMoment 3 z) := by
  simp only [wuQuarticSum, quartic, spectralMoment, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Transfer the coefficient bound to any ordered spectrum satisfying the
same majorization constraints as the physical output. -/
theorem endpoint_quartic_floor_of_majorization {x y : Spectrum4}
    (hx : Antitone x) (hx₀ : ∀ i, 0 ≤ x i) (hy : Antitone y)
    (hp : ∀ k, endpointPrefixSum y k ≤ endpointPrefixSum (endpointClassical x) k)
    (ht : (∑ i, y i) = ∑ i, endpointClassical x i) :
    (spectralMoment 1 x) ^ 2 * (spectralMoment 2 x - (spectralMoment 1 x) ^ 2) ^ 2 / 5 ≤
      spectralMoment 3 x * spectralMoment 3 y - spectralMoment 2 x * spectralMoment 4 y := by
  have h₂ : 0 ≤ spectralMoment 2 x := by
    exact div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg (x i)) (by norm_num)
  rcases lt_or_eq_of_le h₂ with h₂pos | h₂zero
  · let κ := spectralMoment 3 x / spectralMoment 2 x
    have hκ : spectralMoment 2 x * κ = spectralMoment 3 x := by
      exact mul_div_cancel₀ _ h₂pos.ne'
    have hscale (w : Spectrum4) :
        spectralMoment 2 x * wuQuarticSum κ w =
          4 * (spectralMoment 2 x * spectralMoment 4 w -
            spectralMoment 3 x * spectralMoment 3 w) := by
      rw [quarticSum_eq_moments]
      calc
        _ = 4 * (spectralMoment 2 x * spectralMoment 4 w -
          (spectralMoment 2 x * κ) * spectralMoment 3 w) := by ring
        _ = _ := by rw [hκ]
    have hb := endpointBeta_nonneg
    have ha := hb.trans endpointBeta_le_alpha
    have hv₀ : 0 ≤ endpointClassical x 3 := by
      have hx0 := hx₀ 0
      have hx1 := hx₀ 1
      have hx2 := hx₀ 2
      have hx3 := hx₀ 3
      simp [endpointClassical, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;>
        positivity
    obtain ⟨k, hk⟩ := wuQuartic_le_some_prefixAverage κ
      (endpointClassical_antitone x hx) hv₀ hy hp ht
    have hcompare := mul_le_mul_of_nonneg_left hk h₂
    rw [hscale y, hscale (endpointPrefixAverage k (endpointClassical x))] at hcompare
    have hcert := endpoint_quartic_prefix x hx hx₀ k
    linarith only [hcompare, hcert]
  · have hsum : (∑ i : Fin 4, x i ^ 2) = 0 := by
      have h : (∑ i : Fin 4, x i ^ 2) / 4 = 0 := h₂zero.symm
      linarith only [h]
    have hxzero : x = 0 := by
      funext i
      exact (Finset.sum_sq_eq_zero_iff Finset.univ x).mp hsum i (Finset.mem_univ i)
    subst x
    simp [spectralMoment]

open Matrix Unitary

private abbrev modeIndex : Fin 4 ≃ Mode :=
  Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card Mode))

private theorem eigenvalues_at_modeIndex {X : TwoMode} (hX : X.IsHermitian) (i : Fin 4) :
    hX.eigenvalues (modeIndex i) = hX.eigenvalues₀ i := by
  change hX.eigenvalues₀ (modeIndex.symm (modeIndex i)) = _
  rw [Equiv.symm_apply_apply]

/-- The quartic floor for the actual signed two-mode endpoint on PSD inputs. -/
theorem A1_spectral_quartic_floor (X : TwoMode) (hX : X.PosSemidef) :
    let x := hX.isHermitian.eigenvalues₀
    let y := (A₁_isHermitian X hX.isHermitian).eigenvalues₀
    (spectralMoment 1 x) ^ 2 * (spectralMoment 2 x - (spectralMoment 1 x) ^ 2) ^ 2 / 5 ≤
      spectralMoment 3 x * spectralMoment 3 y - spectralMoment 2 x * spectralMoment 4 y := by
  have hx₀ (i : Fin 4) : 0 ≤ hX.isHermitian.eigenvalues₀ i := by
    rw [← eigenvalues_at_modeIndex hX.isHermitian i]
    exact hX.eigenvalues_nonneg (modeIndex i)
  obtain ⟨_, hp, ht⟩ := A1_spectral_majorization X hX.isHermitian
  exact endpoint_quartic_floor_of_majorization hX.isHermitian.eigenvalues₀_antitone hx₀
    (A₁_isHermitian X hX.isHermitian).eigenvalues₀_antitone hp ht

/-- The normalized real trace of a power in the four-dimensional matrix model. -/
def endpointTraceMoment (k : ℕ) (X : TwoMode) : ℝ :=
  ((X ^ k).trace).re / 4

private theorem traceMoment_eq_spectralMoment (k : ℕ) {X : TwoMode} (hX : X.IsHermitian) :
    endpointTraceMoment k X = spectralMoment k hX.eigenvalues₀ := by
  let d : Mode → ℂ := RCLike.ofReal ∘ hX.eigenvalues
  let U := hX.eigenvectorUnitary
  have hpow : X ^ k = conjStarAlgAut ℂ TwoMode U (diagonal (d ^ k)) := by
    rw [← diagonal_pow d k, ← map_pow (conjStarAlgAut ℂ TwoMode U) (diagonal d) k]
    exact congrArg (fun M : TwoMode => M ^ k) hX.spectral_theorem
  unfold endpointTraceMoment spectralMoment
  rw [hpow, conjStarAlgAut_apply, trace_mul_cycle, coe_star_mul_self, one_mul,
    trace_diagonal, Complex.re_sum]
  refine congrArg (fun s : ℝ => s / 4) ?_
  calc
    (∑ i : Mode, ((d ^ k) i).re) =
        ∑ i : Fin 4, ((d ^ k) (modeIndex i)).re :=
      (modeIndex.sum_comp (fun i : Mode => ((d ^ k) i).re)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      change ((hX.eigenvalues (modeIndex i) : ℂ) ^ k).re = _
      rw [eigenvalues_at_modeIndex hX i, ← Complex.ofReal_pow, Complex.ofReal_re]

/-- Trace form of the `1/5` floor for the endpoint Euler expression. -/
theorem A1_quartic_floor (X : TwoMode) (hX : X.PosSemidef) :
    (endpointTraceMoment 1 X) ^ 2 *
      (endpointTraceMoment 2 X - (endpointTraceMoment 1 X) ^ 2) ^ 2 / 5 ≤
        endpointTraceMoment 3 X * endpointTraceMoment 3 (A₁ X) -
          endpointTraceMoment 2 X * endpointTraceMoment 4 (A₁ X) := by
  simpa only [traceMoment_eq_spectralMoment _ hX.isHermitian,
    traceMoment_eq_spectralMoment _ (A₁_isHermitian X hX.isHermitian)] using
    A1_spectral_quartic_floor X hX

end WuRankOneEndpointFloor
