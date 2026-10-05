/- GID: D5/S3/Arith/FibonacciAtomic/OptimalLawTwoMinimalAtoms
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/OptimalLawTwoMinimalAtoms
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Every positive attaining law has at least two labels at its minimum mass. -/

import D5.S3.Arith.FibonacciAtomic.OptimalLawNearestStrictCeiling
import Mathlib.Algebra.BigOperators.Ring.Nat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.OptimalLawTwoMinimalAtoms

open scoped BigOperators
open CarryGraphCriticalAttainment (alpha)
open DyadicSupportLines (cost residual)

/-- A positive real law attaining the full-real dyadic cost slope cannot have a
unique minimum atom. -/
theorem result (m : ℕ) (hm : 2 ≤ m) (p : Fin m → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1)
    (hopt : cost p = alpha m * sInf (Set.range p)) :
    ∃ i j : Fin m, i ≠ j ∧ p i = sInf (Set.range p) ∧
      p j = sInf (Set.range p) := by
  classical
  letI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  let t := sInf (Set.range p)
  obtain ⟨k, hk0⟩ := (Set.range_nonempty p).csInf_mem (Set.finite_range p)
  have hk : p k = t := by simpa [t] using hk0
  have low (i : Fin m) : t ≤ p i := by
    exact csInf_le (Set.finite_range p).bddBelow ⟨i, rfl⟩
  have tpos : 0 < t := by simpa [hk] using hp k
  by_contra hnone
  have unique (i : Fin m) (hi : p i = t) : i = k := by
    by_contra hne
    apply hnone
    exact ⟨k, i, fun h => hne h.symm, hk, hi⟩
  let depth : Fin m → ℕ := fun i => if h : t < p i then
    Nat.find (OptimalLawLargerAtomsTerminate.result m hm p hp hs hopt i h) else 0
  have at_depth (i : Fin m) (hi : k ≠ i) :
      ∃ N : ℕ, p i = (N : ℝ) / (2 : ℝ) ^ depth i := by
    have hti : t < p i := lt_of_le_of_ne (low i) (fun e =>
      hi (unique i e.symm).symm)
    simpa only [depth, dif_pos hti] using
      Nat.find_spec (OptimalLawLargerAtomsTerminate.result m hm p hp hs hopt i hti)
  let D₀ := ∑ i, depth i
  have depth_le (i : Fin m) : depth i ≤ D₀ := by
    exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have common (i : Fin m) (hi : k ≠ i) :
      ∃ N : ℕ, p i = (N : ℝ) / (2 : ℝ) ^ D₀ := by
    obtain ⟨N, hN⟩ := at_depth i hi
    refine ⟨N * 2 ^ (D₀ - depth i), ?_⟩
    rw [hN, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    have power : (2 : ℝ) ^ D₀ = (2 : ℝ) ^ depth i * (2 : ℝ) ^ (D₀ - depth i) := by
      rw [← pow_add, Nat.add_sub_of_le (depth_le i)]
    rw [power]
    field_simp
  let num : Fin m → ℕ := fun i => if hi : k = i then 0 else
    Classical.choose (common i hi)
  have num_spec (i : Fin m) (hi : k ≠ i) :
      p i = (num i : ℝ) / (2 : ℝ) ^ D₀ := by
    dsimp only [num]
    rw [dif_neg hi]
    exact Classical.choose_spec (common i hi)
  have sum_other :
      ∑ i ∈ (Finset.univ.erase k), p i =
        (∑ i ∈ (Finset.univ.erase k), (num i : ℝ)) / (2 : ℝ) ^ D₀ := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    exact num_spec i (Finset.mem_erase.mp hi).1.symm
  have hsum_grid :
      t + (∑ i ∈ (Finset.univ.erase k), p i) = 1 := by
    calc
      t + (∑ i ∈ (Finset.univ.erase k), p i) =
          p k + (∑ i ∈ (Finset.univ.erase k), p i) := by rw [hk]
      _ = (∑ i ∈ (Finset.univ.erase k), p i) + p k := by ring
      _ = ∑ i, p i := Finset.sum_erase_add _ _ (Finset.mem_univ k)
      _ = 1 := hs
  let Kz : ℤ := (2 : ℤ) ^ D₀ - ∑ i ∈ (Finset.univ.erase k), (num i : ℤ)
  have ht_grid_int : t = (Kz : ℝ) / (2 : ℝ) ^ D₀ := by
    have hpow : (2 : ℝ) ^ D₀ ≠ 0 := by positivity
    have hsum_num :
        (∑ i ∈ (Finset.univ.erase k), (num i : ℝ)) =
          (∑ i ∈ (Finset.univ.erase k), (num i : ℤ) : ℤ) := by
      norm_cast
    dsimp only [Kz]
    rw [sum_other] at hsum_grid
    rw [hsum_num] at hsum_grid
    field_simp at hsum_grid ⊢
    have hK : (Kz : ℝ) = (2 : ℝ) ^ D₀ -
        ∑ i ∈ (Finset.univ.erase k), (num i : ℝ) := by
      norm_num [Kz]
    rw [hK]
    linarith
  have Kpos : 0 < Kz := by
    have H := (div_pos_iff.mp (show 0 < (Kz : ℝ) / (2 : ℝ) ^ D₀ from ht_grid_int ▸ tpos))
    rcases H with H | H
    · exact_mod_cast H.1
    · exfalso
      have hden : (0 : ℝ) < (2 : ℝ) ^ D₀ := by positivity
      linarith [H.2, hden]
  have K_nonneg : 0 ≤ Kz := Kpos.le
  let K : ℕ := Kz.toNat
  have Kcast : (K : ℝ) = (Kz : ℝ) := by
    dsimp only [K]
    exact_mod_cast (Int.toNat_of_nonneg K_nonneg)
  have ht_grid : t = (K : ℝ) / (2 : ℝ) ^ D₀ := by
    rw [ht_grid_int, Kcast]
  have all_grid_exists : ∃ D : ℕ, ∀ i : Fin m, ∃ N : ℕ,
      p i = (N : ℝ) / (2 : ℝ) ^ D := by
    refine ⟨D₀, ?_⟩
    intro i
    by_cases hi : k = i
    · subst i
      exact ⟨K, by simpa [hk, ht_grid]⟩
    · exact common i hi
  let D := Nat.find all_grid_exists
  have all_grid (i : Fin m) : ∃ N : ℕ,
      p i = (N : ℝ) / (2 : ℝ) ^ D :=
    Nat.find_spec all_grid_exists i
  have Dmin (E : ℕ) (hE : E < D) : ¬ (∀ i : Fin m, ∃ N : ℕ,
      p i = (N : ℝ) / (2 : ℝ) ^ E) := by
    exact Nat.find_min all_grid_exists hE
  let numD : Fin m → ℕ := fun i => Classical.choose (all_grid i)
  have numD_spec (i : Fin m) :
      p i = (numD i : ℝ) / (2 : ℝ) ^ D :=
    Classical.choose_spec (all_grid i)
  have hsum_num_real :
      (∑ i, (numD i : ℝ)) = (2 : ℝ) ^ D := by
    have H : (∑ i, (numD i : ℝ) / (2 : ℝ) ^ D) = 1 := by
      rw [← hs]
      exact Finset.sum_congr rfl (fun i _ => (numD_spec i).symm)
    have hpow : (2 : ℝ) ^ D ≠ 0 := by positivity
    simp only [div_eq_mul_inv] at H
    rw [← Finset.sum_mul] at H
    field_simp at H
    linarith
  have hsum_num : ∑ i, numD i = 2 ^ D := by
    exact_mod_cast hsum_num_real
  have num_pos (i : Fin m) : 0 < numD i := by
    have H := hp i
    rw [numD_spec i] at H
    have hpow : (0 : ℝ) < (2 : ℝ) ^ D := by positivity
    rcases (div_pos_iff.mp H) with ⟨H', _⟩ | ⟨H', H''⟩
    · exact_mod_cast H'
    · have : (0 : ℝ) ≤ (2 : ℝ) ^ D := by positivity
      linarith
  have Dpos : 0 < D := by
    by_contra hD
    have hD0 : D = 0 := by omega
    have H : ∀ i : Fin m, 1 ≤ numD i := by
      intro i
      have H' := num_pos i
      omega
    have Hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
      (fun i _ => H i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at Hsum
    rw [hsum_num, hD0] at Hsum
    norm_num at Hsum
    omega
  have num_lt (i : Fin m) (hi : k ≠ i) : numD k < numD i := by
    have hlt : p k < p i := by
      apply lt_of_le_of_ne (by simpa [hk] using low i)
      intro e
      apply hi
      exact (unique i (e.symm.trans hk)).symm
    have hpow : (0 : ℝ) < (2 : ℝ) ^ D := by positivity
    have H := (div_lt_div_iff_of_pos_right hpow).mp (by simpa [numD_spec, hk] using hlt)
    exact_mod_cast H
  have floor_grid (i : Fin m) :
      ⌊(2 : ℝ) ^ D * p i⌋ = (numD i : ℤ) := by
    rw [numD_spec i]
    field_simp
    norm_num [Int.floor_intCast]
  have not_grid_pred := Dmin (D - 1) (by omega)
  push_neg at not_grid_pred
  obtain ⟨odd_i, hodd_i⟩ := not_grid_pred
  obtain ⟨Nodd, hNodd⟩ := all_grid odd_i
  have pow_prev : (2 : ℝ) ^ D = (2 : ℝ) ^ (D - 1) * 2 := by
    calc
      (2 : ℝ) ^ D = (2 : ℝ) ^ (D - 1 + 1) := by
        congr 1
        omega
      _ = (2 : ℝ) ^ (D - 1) * 2 := by rw [pow_succ]
  have odd_num (i : Fin m) (hNi : ∀ N : ℕ, p i ≠ (N : ℝ) / (2 : ℝ) ^ (D - 1)) :
      Odd (numD i) := by
    rcases Nat.even_or_odd (numD i) with he | ho
    · rcases he with ⟨q, hq⟩
      exfalso
      apply hNi
      rw [numD_spec i, hq]
      rw [pow_prev]
      norm_num [Nat.cast_add]
      field_simp
      ring
    · exact ho
  have odd_i_num : Odd (numD odd_i) := odd_num odd_i hodd_i
  let oddSet : Finset (Fin m) := Finset.univ.filter (fun i => Odd (numD i))
  have odd_mem (i : Fin m) : i ∈ oddSet ↔ Odd (numD i) := by
    simp only [oddSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have odd_nonempty : oddSet.Nonempty := by
    exact ⟨odd_i, (odd_mem odd_i).mpr odd_i_num⟩
  have sum_even : Even (∑ i, numD i) := by
    refine ⟨2 ^ (D - 1), ?_⟩
    rw [hsum_num]
    calc
      (2 : ℕ) ^ D = 2 ^ (D - 1 + 1) := by
        congr 1
        omega
      _ = 2 ^ (D - 1) * 2 := by rw [pow_succ]
    ring_nf
  have odd_card_even : Even oddSet.card := by
    have H := (Finset.even_sum_iff_even_card_odd (s := (Finset.univ : Finset (Fin m))) numD).mp
      (by simpa using sum_even)
    simpa [oddSet] using H
  have odd_mem_num (i : Fin m) (hi : i ∈ oddSet) : Odd (numD i) := (odd_mem i).mp hi
  have floor_pred_grid (i : Fin m) (hi : i ∈ oddSet) :
      ⌊(2 : ℝ) ^ (D - 1) * p i⌋ = (numD i / 2 : ℕ) := by
    have H := Int.floor_div_natCast ((2 : ℝ) ^ D * p i) 2
    have divide : (2 : ℝ) ^ D * p i / (2 : ℕ) =
        (2 : ℝ) ^ (D - 1) * p i := by
      rw [pow_prev]
      ring
    rw [divide, floor_grid i] at H
    exact_mod_cast H
  have law_data (r : Fin m → ℝ) (hr : ∀ i, 0 ≤ r i) (hsr : ∑ i, r i = 1) :
      (∀ d, 0 ≤ DyadicSupportLines.residual r d ∧ DyadicSupportLines.residual r d ≤ m) ∧
        Summable (fun d => DyadicSupportLines.residual r d / (2 : ℝ) ^ d) := by
    have bounds (d : ℕ) : 0 ≤ DyadicSupportLines.residual r d ∧ DyadicSupportLines.residual r d ≤ m := by
      have hsum : ∑ i, (2 : ℝ) ^ d * r i = (2 : ℝ) ^ d := by
        rw [← Finset.mul_sum, hsr, mul_one]
      have hlo : (∑ i, (⌊(2 : ℝ) ^ d * r i⌋ : ℝ)) ≤ (2 : ℝ) ^ d := by
        calc
          _ ≤ ∑ i, (2 : ℝ) ^ d * r i := Finset.sum_le_sum (fun i _ => Int.floor_le _)
          _ = _ := hsum
      have hhi : (2 : ℝ) ^ d < (∑ i, (⌊(2 : ℝ) ^ d * r i⌋ : ℝ)) + m := by
        have H := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin m)))
          (by simp : (Finset.univ : Finset (Fin m)).Nonempty)
          (fun i _ => Int.lt_floor_add_one ((2 : ℝ) ^ d * r i))
        simpa [hsum, Finset.sum_add_distrib] using H
      have hi : (2 : ℤ) ^ d - ∑ i, ⌊(2 : ℝ) ^ d * r i⌋ < m := by
        have H : ((2 : ℤ) ^ d - ∑ i, ⌊(2 : ℝ) ^ d * r i⌋ : ℝ) < m := by
          push_cast
          linarith only [hhi]
        exact_mod_cast H
      constructor
      · simp only [DyadicSupportLines.residual, Int.cast_sum]
        linarith only [hlo]
      · have H : (2 : ℤ) ^ d - ∑ i, ⌊(2 : ℝ) ^ d * r i⌋ ≤ m - 1 := by omega
        have H' : ((2 : ℤ) ^ d - ∑ i, ⌊(2 : ℝ) ^ d * r i⌋ : ℝ) ≤ m - 1 := by
          exact_mod_cast H
        change DyadicSupportLines.residual r d ≤ (m : ℝ)
        rw [DyadicSupportLines.residual]
        norm_num [Int.cast_sub, Int.cast_sum] at H' ⊢
        exact H'.trans (by linarith)
    refine ⟨fun d => (bounds d), ?_⟩
    apply Summable.of_nonneg_of_le
      (fun d => div_nonneg (bounds d).1 (by positivity))
      (fun d => div_le_div_of_nonneg_right (bounds d).2 (by positivity))
    simpa only [div_eq_mul_inv, one_mul, inv_pow] using
      (summable_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)).mul_left (m : ℝ)
  have optimal_lower (r : Fin m → ℝ) (hr : ∀ i, 0 < r i) (hsr : ∑ i, r i = 1)
      (z : Fin m) (hz : ∀ i, r z ≤ r i) : alpha m * r z ≤ cost r := by
    obtain ⟨V, f, _, _, paths, _, zero, _⟩ := CarryGraphCriticalAttainment.result m hm
    obtain ⟨γ, hγ, _, _, _, ha, hc⟩ :=
      (CarryGraphEmbedding.result m hm).2.2.2 r hr hsr z hz
    have H := (paths (alpha m)).2.2 γ hγ
    rw [zero, ha, hc] at H
    linarith
  let δ : ℝ := 1 / (2 : ℝ) ^ D
  have δpos : 0 < δ := by dsimp only [δ]; positivity
  have prev_floor (i : Fin m) :
      ⌊(2 : ℝ) ^ (D - 1) * p i⌋ = (numD i / 2 : ℕ) := by
    have H := Int.floor_div_natCast ((2 : ℝ) ^ D * p i) 2
    have divide : (2 : ℝ) ^ D * p i / (2 : ℕ) =
        (2 : ℝ) ^ (D - 1) * p i := by
      rw [pow_prev]
      ring
    rw [divide, floor_grid i] at H
    exact_mod_cast H
  have shallow_odd (j : Fin m) (hjodd : Odd (numD j)) :
      ∀ h : ℕ, h < D →
        ⌊(2 : ℝ) ^ h * (p j - δ)⌋ = ⌊(2 : ℝ) ^ h * p j⌋ := by
    rcases hjodd with ⟨q, hq⟩
    have expansion : (2 : ℝ) ^ (D - 1) * p j = (q : ℝ) + 1 / 2 := by
      rw [numD_spec j, hq]
      rw [pow_prev]
      field_simp
      norm_num [Nat.cast_add, Nat.cast_mul]
    have reduced : (2 : ℝ) ^ (D - 1) * (p j - δ) = (q : ℝ) := by
      have H : (2 : ℝ) ^ (D - 1) / (2 : ℝ) ^ D = 1 / 2 := by
        rw [pow_prev]
        field_simp
      rw [mul_sub, ← mul_div_assoc, mul_one, H, expansion]
      ring
    have floor_expansion :
        ⌊(2 : ℝ) ^ (D - 1) * p j⌋ = (q : ℤ) := by
      apply Int.floor_eq_iff.mpr
      rw [expansion]
      constructor <;> norm_num
    have floor_reduced :
        ⌊(2 : ℝ) ^ (D - 1) * (p j - δ)⌋ = (q : ℤ) := by
      rw [reduced]
      exact Int.floor_intCast _
    intro h hh
    have divide (z : ℝ) :
        (2 : ℝ) ^ (D - 1) * z / ((2 ^ (D - 1 - h) : ℕ) : ℝ) =
          (2 : ℝ) ^ h * z := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
      have power : (2 : ℝ) ^ (D - 1) =
          (2 : ℝ) ^ h * (2 : ℝ) ^ (D - 1 - h) := by
        rw [← pow_add, Nat.add_sub_of_le (by omega : h ≤ D - 1)]
      rw [power]
      field_simp
    have H := Int.floor_div_natCast
      ((2 : ℝ) ^ (D - 1) * (p j - δ)) (2 ^ (D - 1 - h))
    have H' := Int.floor_div_natCast
      ((2 : ℝ) ^ (D - 1) * p j) (2 ^ (D - 1 - h))
    rw [divide, floor_reduced] at H
    rw [divide, floor_expansion] at H'
    exact H.trans H'.symm
  have contradiction_single (j : Fin m) (hjk : j ≠ k)
      (hjodd : Odd (numD j)) (hgap : numD k + 2 ≤ numD j)
      : False := by
    let P : Fin m → ℝ := fun i => p i + (if i = k then δ else 0) -
      (if i = j then δ else 0)
    have Psum : ∑ i, P i = 1 := by
      simp only [P, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring_nf
      exact hs
    have Plower (i : Fin m) : t + δ ≤ P i := by
      by_cases hik : i = k
      · subst i
        simp [P, hjk, hjk.symm]
        linarith [hk]
      · by_cases hij : i = j
        · subst i
          simp only [P, if_neg hjk, if_pos rfl]
          have H' : t + δ ≤ p j - δ := by
            rw [← hk, numD_spec k, numD_spec j]
            dsimp only [δ]
            field_simp
            have H : (numD k : ℝ) + 2 ≤ (numD j : ℝ) := by
              exact_mod_cast hgap
            linarith
          simpa [P, hjk, hjk.symm] using H'
        · simp only [P, if_neg hik, if_neg hij, sub_zero, add_zero]
          have Hnum : numD k + 1 ≤ numD i := by
            exact Nat.succ_le_of_lt (num_lt i (fun h => hik h.symm))
          rw [← hk, numD_spec k, numD_spec i]
          dsimp only [δ]
          field_simp
          norm_num [Nat.cast_add]
          exact_mod_cast Hnum
    have Ppos (i : Fin m) : 0 < P i := by
      have H := Plower i
      linarith [tpos, δpos]
    have Pgrid (i : Fin m) : ∃ N : ℕ,
        P i = (N : ℝ) / (2 : ℝ) ^ D := by
      by_cases hik : i = k
      · subst i
        refine ⟨numD k + 1, ?_⟩
        simp [P, hjk, hjk.symm]
        rw [numD_spec k]
        dsimp only [δ]
        field_simp
      · by_cases hij : i = j
        · subst i
          refine ⟨numD j - 1, ?_⟩
          have hn : 1 ≤ numD j := by omega
          simp [P, hjk, hjk.symm]
          rw [numD_spec j]
          dsimp only [δ]
          field_simp
          norm_num [Nat.cast_sub hn]
        · refine ⟨numD i, ?_⟩
          simp only [P, if_neg hik, if_neg hij, sub_zero, add_zero]
          exact numD_spec i
    have floor_change (h : ℕ) (hh : h < D) (i : Fin m) :
        ⌊(2 : ℝ) ^ h * p i⌋ ≤ ⌊(2 : ℝ) ^ h * P i⌋ := by
      by_cases hik : i = k
      · subst i
        simp [P, hjk, hjk.symm]
        apply Int.floor_mono
        have hpow : 0 ≤ (2 : ℝ) ^ h := by positivity
        have hmul : 0 ≤ (2 : ℝ) ^ h * δ := mul_nonneg hpow δpos.le
        nlinarith
      · by_cases hij : i = j
        · subst i
          simp [P, hjk, hjk.symm]
          exact (shallow_odd j hjodd h hh).symm.le
        · simp [P, hik, hij]
    have residual_le (h : ℕ) (hh : h < D) : DyadicSupportLines.residual P h ≤ DyadicSupportLines.residual p h := by
      simp only [DyadicSupportLines.residual, Int.cast_sum]
      have H : (∑ i, (⌊(2 : ℝ) ^ h * p i⌋ : ℝ)) ≤
          ∑ i, (⌊(2 : ℝ) ^ h * P i⌋ : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact_mod_cast floor_change h hh i
      linarith
    have floor_k_strict (hkodd : Odd (numD k)) :
        ⌊(2 : ℝ) ^ (D - 1) * P k⌋ =
          ⌊(2 : ℝ) ^ (D - 1) * p k⌋ + 1 := by
      rcases hkodd with ⟨q, hq⟩
      have expansion : (2 : ℝ) ^ (D - 1) * p k = (q : ℝ) + 1 / 2 := by
        rw [numD_spec k, hq]
        rw [pow_prev]
        field_simp
        norm_num [Nat.cast_add, Nat.cast_mul]
      have expandedP : (2 : ℝ) ^ (D - 1) * P k = (q : ℝ) + 1 := by
        simp [P, hjk, hjk.symm]
        rw [mul_add, expansion]
        dsimp only [δ]
        field_simp [pow_prev]
        rw [pow_prev]
        ring
      rw [expandedP, expansion]
      norm_num [Int.floor_intCast]
    have residual_strict (hkodd : Odd (numD k)) :
        DyadicSupportLines.residual P (D - 1) < DyadicSupportLines.residual p (D - 1) := by
      simp only [DyadicSupportLines.residual, Int.cast_sum]
      have Hle : (∑ i ∈ (Finset.univ.erase k),
          (⌊(2 : ℝ) ^ (D - 1) * p i⌋ : ℝ)) ≤
          ∑ i ∈ (Finset.univ.erase k), (⌊(2 : ℝ) ^ (D - 1) * P i⌋ : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact_mod_cast floor_change (D - 1) (by omega) i
      have HsumP := Finset.sum_erase_add (Finset.univ : Finset (Fin m))
        (fun i => (⌊(2 : ℝ) ^ (D - 1) * P i⌋ : ℝ)) (Finset.mem_univ k)
      have Hsump := Finset.sum_erase_add (Finset.univ : Finset (Fin m))
        (fun i => (⌊(2 : ℝ) ^ (D - 1) * p i⌋ : ℝ)) (Finset.mem_univ k)
      have Hfloor : (⌊(2 : ℝ) ^ (D - 1) * P k⌋ : ℝ) =
          (⌊(2 : ℝ) ^ (D - 1) * p k⌋ : ℝ) + 1 := by
        exact_mod_cast floor_k_strict hkodd
      rw [← HsumP, ← Hsump, Hfloor]
      linarith
    have residual_zero (r : Fin m → ℝ) (hrgrid : ∀ i, ∃ N : ℕ,
        r i = (N : ℝ) / (2 : ℝ) ^ D)
        (hsgrid : ∑ i, ((Classical.choose (hrgrid i) : ℕ) : ℝ) = (2 : ℝ) ^ D)
        (d : ℕ) (hd : D ≤ d) : DyadicSupportLines.residual r d = 0 := by
      simp only [DyadicSupportLines.residual, Int.cast_sum]
      have floors (i : Fin m) :
          ⌊(2 : ℝ) ^ d * r i⌋ = (((2 ^ (d - D) * Classical.choose (hrgrid i) : ℕ) : ℕ) : ℤ) := by
        let N : ℕ := Classical.choose (hrgrid i)
        have hN : r i = (N : ℝ) / (2 : ℝ) ^ D := Classical.choose_spec (hrgrid i)
        change ⌊(2 : ℝ) ^ d * r i⌋ = (((2 ^ (d - D) * N : ℕ) : ℤ))
        have hpow : (2 : ℝ) ^ d = (2 : ℝ) ^ D * (2 : ℝ) ^ (d - D) := by
          rw [← pow_add, Nat.add_sub_of_le hd]
        have hmul : (2 : ℝ) ^ d * ((N : ℝ) / (2 : ℝ) ^ D) =
            (2 : ℝ) ^ (d - D) * (N : ℝ) := by
          rw [hpow]
          field_simp
        have hcast : (2 : ℝ) ^ (d - D) * (N : ℝ) =
            (((2 ^ (d - D) * N : ℕ) : ℤ) : ℝ) := by norm_num
        have hfloorN : ⌊(2 : ℝ) ^ d * ((N : ℝ) / (2 : ℝ) ^ D)⌋ =
            (((2 ^ (d - D) * N : ℕ) : ℤ)) := by
          rw [hmul, hcast]
          exact Int.floor_intCast _
        calc
          ⌊(2 : ℝ) ^ d * r i⌋ =
              ⌊(2 : ℝ) ^ d * ((N : ℝ) / (2 : ℝ) ^ D)⌋ := by rw [hN]
          _ = (((2 ^ (d - D) * N : ℕ) : ℤ)) := hfloorN
      simp_rw [floors]
      norm_num [Int.cast_sum, Int.cast_mul, Nat.cast_mul, Nat.cast_pow]
      rw [← Finset.mul_sum]
      rw [hsgrid]
      rw [show (2 : ℝ) ^ d = (2 : ℝ) ^ D * (2 : ℝ) ^ (d - D) by
        rw [← pow_add, Nat.add_sub_of_le hd]]
      ring
    have term_le (h : ℕ) : DyadicSupportLines.residual P h / (2 : ℝ) ^ h ≤
        DyadicSupportLines.residual p h / (2 : ℝ) ^ h := by
      by_cases hh : h < D
      · exact div_le_div_of_nonneg_right (residual_le h hh) (by positivity)
      · have Psum_grid :
          (∑ i, ((Classical.choose (Pgrid i) : ℕ) : ℝ)) = (2 : ℝ) ^ D := by
          have H : (∑ i, ((Classical.choose (Pgrid i) : ℕ) : ℝ) /
              (2 : ℝ) ^ D) = 1 := by
            calc
              _ = ∑ i, P i := by
                exact Finset.sum_congr rfl
                  (fun i _ => (Classical.choose_spec (Pgrid i)).symm)
              _ = 1 := Psum
          have H' :
              (∑ i, ((Classical.choose (Pgrid i) : ℕ) : ℝ)) /
                (2 : ℝ) ^ D = 1 := by
            rw [Finset.sum_div]
            exact H
          have hpow : (2 : ℝ) ^ D ≠ 0 := by positivity
          simpa only [one_mul] using (div_eq_iff hpow).mp H'
        rw [residual_zero P Pgrid Psum_grid h (le_of_not_gt hh),
          residual_zero p (fun i => all_grid i) hsum_num_real h (le_of_not_gt hh)]
    have data_p := law_data p (fun i => (hp i).le) hs
    have data_P := law_data P (fun i => (Ppos i).le) Psum
    have cost_le : cost P ≤ cost p := by
      exact data_P.2.tsum_le_tsum term_le data_p.2
    have cost_strict (hkodd : Odd (numD k)) : cost P < cost p := by
      exact data_p.2.tsum_lt_tsum_of_nonneg
        (fun h => div_nonneg (data_P.1 h).1 (by positivity))
        term_le
        (div_lt_div_of_pos_right (residual_strict hkodd) (by positivity))
    obtain ⟨z, hz⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin m)) P
      Finset.univ_nonempty
    have hz' : ∀ i, P z ≤ P i := fun i => hz.2 i (Finset.mem_univ i)
    have lower_bound : alpha m * P z ≤ cost P := optimal_lower P Ppos Psum z hz'
    have min_strict : t + δ ≤ P z := Plower z
    have alpha_pos : 0 < alpha m := by
      have alpha_pos_all : ∀ n : ℕ, 2 ≤ n → 0 < alpha n := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n ih =>
            intro hn
            by_cases h2 : n = 2
            · simpa [h2, OptimalLawStrictSlope.result.2.1]
            · have hn3 : 3 ≤ n := by omega
              have hslope := OptimalLawStrictSlope.result.2.2 n hn3
              have hprev := ih (n - 1) (by omega) (by omega)
              linarith
      exact alpha_pos_all m hm
    have new_lower : alpha m * (t + δ) ≤ cost P :=
      (mul_le_mul_of_nonneg_left min_strict alpha_pos.le).trans lower_bound
    have old : cost p = alpha m * t := by simpa [t] using hopt
    by_cases hkodd' : Odd (numD k)
    · have : cost P < alpha m * (t + δ) := by
        calc cost P < cost p := cost_strict hkodd'
             _ = alpha m * t := old
             _ < alpha m * (t + δ) := by nlinarith [mul_pos alpha_pos δpos]
      exact (not_lt_of_ge new_lower) this
    · have : cost P < alpha m * (t + δ) := by
        calc cost P ≤ cost p := cost_le
             _ = alpha m * t := old
             _ < alpha m * (t + δ) := by nlinarith [mul_pos alpha_pos δpos]
      exact (not_lt_of_ge new_lower) this
  have contradiction_double (j₁ j₂ : Fin m) (hjk₁ : j₁ ≠ k) (hjk₂ : j₂ ≠ k)
      (h12 : j₁ ≠ j₂) (hodd₁ : Odd (numD j₁)) (hodd₂ : Odd (numD j₂))
      (heq₁ : numD j₁ = numD k + 1) (heq₂ : numD j₂ = numD k + 1)
      (hk_even : Even (numD k)) : False := by
    let P : Fin m → ℝ := fun i => p i + (if i = k then 2 * δ else 0) -
      (if i = j₁ then δ else 0) - (if i = j₂ then δ else 0)
    have Psum : ∑ i, P i = 1 := by
      simp only [P, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring_nf
      exact hs
    have Plower (i : Fin m) : t ≤ P i := by
      by_cases hik : i = k
      · subst i
        simp [P, hjk₁, hjk₂, hjk₁.symm, hjk₂.symm]
        linarith [hk, δpos.le]
      · by_cases hi₁ : i = j₁
        · subst i
          simp [P, hjk₁, h12]
          rw [← hk, numD_spec j₁, numD_spec k, heq₁]
          dsimp only [δ]
          field_simp
          norm_num [Nat.cast_add]
        · by_cases hi₂ : i = j₂
          · subst i
            simp [P, hjk₂, h12.symm]
            rw [← hk, numD_spec j₂, numD_spec k, heq₂]
            dsimp only [δ]
            field_simp
            norm_num [Nat.cast_add]
          · simp only [P, if_neg hik, if_neg hi₁, if_neg hi₂, sub_zero, add_zero]
            exact low i
    have Ppos (i : Fin m) : 0 < P i := lt_of_lt_of_le tpos (Plower i)
    have Pgrid (i : Fin m) : ∃ N : ℕ,
        P i = (N : ℝ) / (2 : ℝ) ^ D := by
      by_cases hik : i = k
      · subst i
        refine ⟨numD k + 2, ?_⟩
        simp [P, hjk₁, hjk₂, hjk₁.symm, hjk₂.symm]
        rw [numD_spec k]
        dsimp only [δ]
        field_simp
      · by_cases hi₁ : i = j₁
        · subst i
          refine ⟨numD j₁ - 1, ?_⟩
          have hn : 1 ≤ numD j₁ := by omega
          simp [P, hjk₁, h12]
          rw [numD_spec j₁]
          dsimp only [δ]
          rw [← sub_div, Nat.cast_sub hn]
          field_simp
          norm_num
        · by_cases hi₂ : i = j₂
          · subst i
            refine ⟨numD j₂ - 1, ?_⟩
            have hn : 1 ≤ numD j₂ := by omega
            simp [P, hjk₂, h12.symm]
            rw [numD_spec j₂]
            dsimp only [δ]
            rw [← sub_div, Nat.cast_sub hn]
            field_simp
            norm_num
          · refine ⟨numD i, ?_⟩
            simp only [P, if_neg hik, if_neg hi₁, if_neg hi₂, sub_zero, add_zero]
            exact numD_spec i
    have floor_change (h : ℕ) (hh : h < D) (i : Fin m) :
        ⌊(2 : ℝ) ^ h * p i⌋ ≤ ⌊(2 : ℝ) ^ h * P i⌋ := by
      by_cases hik : i = k
      · subst i
        simp [P, hjk₁, hjk₂, hjk₁.symm, hjk₂.symm]
        apply Int.floor_mono
        have H : 0 ≤ (2 : ℝ) ^ h * (2 * δ) := by positivity
        ring_nf
        nlinarith
      · by_cases hi₁ : i = j₁
        · subst i
          simpa [P, hjk₁, h12] using (shallow_odd j₁ hodd₁ h hh).ge
        · by_cases hi₂ : i = j₂
          · subst i
            simpa [P, hjk₂, h12.symm] using (shallow_odd j₂ hodd₂ h hh).ge
          · simp only [P, if_neg hik, if_neg hi₁, if_neg hi₂, sub_zero, add_zero]
            exact le_rfl
    have residual_le (h : ℕ) (hh : h < D) : DyadicSupportLines.residual P h ≤ DyadicSupportLines.residual p h := by
      simp only [DyadicSupportLines.residual, Int.cast_sum]
      have H : (∑ i, (⌊(2 : ℝ) ^ h * p i⌋ : ℝ)) ≤
          ∑ i, (⌊(2 : ℝ) ^ h * P i⌋ : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact_mod_cast floor_change h hh i
      linarith
    have floor_k_strict :
        ⌊(2 : ℝ) ^ (D - 1) * P k⌋ =
          ⌊(2 : ℝ) ^ (D - 1) * p k⌋ + 1 := by
      rcases hk_even with ⟨q, hq⟩
      have expansion : (2 : ℝ) ^ (D - 1) * p k = (q : ℝ) := by
        rw [numD_spec k, hq, pow_prev]
        field_simp
        norm_num [Nat.cast_add]
        ring
      have expandedP : (2 : ℝ) ^ (D - 1) * P k = (q : ℝ) + 1 := by
        simp [P, hjk₁, hjk₂, hjk₁.symm, hjk₂.symm]
        rw [mul_add, expansion]
        dsimp only [δ]
        have hterm : (2 : ℝ) ^ (D - 1) * (2 * (1 / (2 : ℝ) ^ D)) = 1 := by
          rw [pow_prev]
          field_simp
        rw [hterm]
      rw [expandedP, expansion]
      norm_num [Int.floor_intCast]
    have residual_strict : DyadicSupportLines.residual P (D - 1) < DyadicSupportLines.residual p (D - 1) := by
      simp only [DyadicSupportLines.residual, Int.cast_sum]
      have Hle : (∑ i ∈ (Finset.univ.erase k),
          (⌊(2 : ℝ) ^ (D - 1) * p i⌋ : ℝ)) ≤
          ∑ i ∈ (Finset.univ.erase k),
            (⌊(2 : ℝ) ^ (D - 1) * P i⌋ : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact_mod_cast floor_change (D - 1) (by omega) i
      have HsumP := Finset.sum_erase_add (Finset.univ : Finset (Fin m))
        (fun i => (⌊(2 : ℝ) ^ (D - 1) * P i⌋ : ℝ)) (Finset.mem_univ k)
      have Hsump := Finset.sum_erase_add (Finset.univ : Finset (Fin m))
        (fun i => (⌊(2 : ℝ) ^ (D - 1) * p i⌋ : ℝ)) (Finset.mem_univ k)
      rw [← HsumP, ← Hsump, floor_k_strict]
      norm_num [Int.cast_add] at *
      linarith
    have residual_zero (r : Fin m → ℝ) (hrgrid : ∀ i, ∃ N : ℕ,
        r i = (N : ℝ) / (2 : ℝ) ^ D)
        (hsgrid : ∑ i, ((Classical.choose (hrgrid i) : ℕ) : ℝ) = (2 : ℝ) ^ D)
        (d : ℕ) (hd : D ≤ d) : DyadicSupportLines.residual r d = 0 := by
      simp only [DyadicSupportLines.residual, Int.cast_sum]
      have floors (i : Fin m) :
          ⌊(2 : ℝ) ^ d * r i⌋ = (((2 ^ (d - D) * Classical.choose (hrgrid i) : ℕ) : ℤ)) := by
        let N : ℕ := Classical.choose (hrgrid i)
        have hN : r i = (N : ℝ) / (2 : ℝ) ^ D := Classical.choose_spec (hrgrid i)
        have hpow : (2 : ℝ) ^ d = (2 : ℝ) ^ D * (2 : ℝ) ^ (d - D) := by
          rw [← pow_add, Nat.add_sub_of_le hd]
        have hmul : (2 : ℝ) ^ d * ((N : ℝ) / (2 : ℝ) ^ D) =
            (2 : ℝ) ^ (d - D) * (N : ℝ) := by
          rw [hpow]
          field_simp
        have hcast : (2 : ℝ) ^ (d - D) * (N : ℝ) =
            (((2 ^ (d - D) * N : ℕ) : ℤ) : ℝ) := by norm_num
        have hfloorN : ⌊(2 : ℝ) ^ d * ((N : ℝ) / (2 : ℝ) ^ D)⌋ =
            (((2 ^ (d - D) * N : ℕ) : ℤ)) := by
          rw [hmul, hcast]
          exact Int.floor_intCast _
        calc
          ⌊(2 : ℝ) ^ d * r i⌋ =
              ⌊(2 : ℝ) ^ d * ((N : ℝ) / (2 : ℝ) ^ D)⌋ := by rw [hN]
          _ = (((2 ^ (d - D) * N : ℕ) : ℤ)) := hfloorN
          _ = (((2 ^ (d - D) * Classical.choose (hrgrid i) : ℕ) : ℤ)) := by rfl
      simp_rw [floors]
      norm_num [Int.cast_sum, Int.cast_mul, Nat.cast_mul, Nat.cast_pow]
      rw [← Finset.mul_sum, hsgrid]
      rw [show (2 : ℝ) ^ d = (2 : ℝ) ^ D * (2 : ℝ) ^ (d - D) by
        rw [← pow_add, Nat.add_sub_of_le hd]]
      ring
    have term_le (h : ℕ) : DyadicSupportLines.residual P h / (2 : ℝ) ^ h ≤
        DyadicSupportLines.residual p h / (2 : ℝ) ^ h := by
      by_cases hh : h < D
      · exact div_le_div_of_nonneg_right (residual_le h hh) (by positivity)
      · have Psum_grid :
          (∑ i, ((Classical.choose (Pgrid i) : ℕ) : ℝ)) = (2 : ℝ) ^ D := by
          have H : (∑ i, ((Classical.choose (Pgrid i) : ℕ) : ℝ) /
              (2 : ℝ) ^ D) = 1 := by
            rw [← Psum]
            exact Finset.sum_congr rfl (fun i _ => (Classical.choose_spec (Pgrid i)).symm)
          have H' :
              (∑ i, ((Classical.choose (Pgrid i) : ℕ) : ℝ)) /
                (2 : ℝ) ^ D = 1 := by
            rw [Finset.sum_div]
            exact H
          have hpow : (2 : ℝ) ^ D ≠ 0 := by positivity
          simpa only [one_mul] using (div_eq_iff hpow).mp H'
        rw [residual_zero P Pgrid Psum_grid h (le_of_not_gt hh),
          residual_zero p (fun i => all_grid i) hsum_num_real h (le_of_not_gt hh)]
    have data_p := law_data p (fun i => (hp i).le) hs
    have data_P := law_data P (fun i => (Ppos i).le) Psum
    have cost_strict : cost P < cost p := by
      exact data_p.2.tsum_lt_tsum_of_nonneg
        (fun h => div_nonneg (data_P.1 h).1 (by positivity))
        term_le
        (div_lt_div_of_pos_right residual_strict (by positivity))
    obtain ⟨z, hz⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin m)) P
      Finset.univ_nonempty
    have hz' : ∀ i, P z ≤ P i := fun i => hz.2 i (Finset.mem_univ i)
    have lower_bound : alpha m * P z ≤ cost P := optimal_lower P Ppos Psum z hz'
    have alpha_pos : 0 < alpha m := by
      have alpha_pos_all : ∀ n : ℕ, 2 ≤ n → 0 < alpha n := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n ih =>
            intro hn
            by_cases h2 : n = 2
            · simpa [h2, OptimalLawStrictSlope.result.2.1]
            · have hn3 : 3 ≤ n := by omega
              have hslope := OptimalLawStrictSlope.result.2.2 n hn3
              have hprev := ih (n - 1) (by omega) (by omega)
              linarith
      exact alpha_pos_all m hm
    have new_lower : alpha m * t ≤ cost P :=
      (mul_le_mul_of_nonneg_left (Plower z) alpha_pos.le).trans lower_bound
    have old : cost p = alpha m * t := by simpa [t] using hopt
    exact (not_lt_of_ge new_lower) (by
      calc cost P < cost p := cost_strict
           _ = alpha m * t := old)

  by_cases hkodd : Odd (numD k)
  · have card_ge : 2 ≤ oddSet.card := by
      rcases odd_card_even with ⟨q, hq⟩
      have hp' : 0 < oddSet.card := Finset.card_pos.mpr odd_nonempty
      omega
    obtain ⟨j, hjmem, hjk⟩ := Finset.exists_mem_ne (by omega : 1 < oddSet.card) k
    have hjodd : Odd (numD j) := odd_mem_num j hjmem
    have hgap : numD k + 2 ≤ numD j := by
      rcases hkodd with ⟨a, ha⟩
      rcases hjodd with ⟨b, hb⟩
      have hlt := num_lt j hjk.symm
      omega
    exact contradiction_single j hjk hjodd hgap
  · have hk_even : Even (numD k) := (Nat.even_or_odd (numD k)).resolve_right hkodd
    have odd_i_ne_k : odd_i ≠ k := by
      intro e
      subst odd_i
      rcases hk_even with ⟨a, ha⟩
      rcases odd_i_num with ⟨b, hb⟩
      omega
    have card_ge : 2 ≤ oddSet.card := by
      rcases odd_card_even with ⟨q, hq⟩
      have hp' : 0 < oddSet.card := Finset.card_pos.mpr odd_nonempty
      omega
    by_cases hsmall : ∀ j : Fin m, j ∈ oddSet → numD j = numD k + 1
    · obtain ⟨j₂, hj₂mem, hj₂ne⟩ :=
        Finset.exists_mem_ne (by omega : 1 < oddSet.card) odd_i
      have hj₂odd : Odd (numD j₂) := odd_mem_num j₂ hj₂mem
      have hj₂k : j₂ ≠ k := by
        intro e
        subst j₂
        rcases hk_even with ⟨a, ha⟩
        rcases hj₂odd with ⟨b, hb⟩
        omega
      have heq₁ := hsmall odd_i ((odd_mem odd_i).mpr odd_i_num)
      have heq₂ := hsmall j₂ hj₂mem
      exact contradiction_double odd_i j₂ odd_i_ne_k hj₂k hj₂ne.symm odd_i_num hj₂odd heq₁ heq₂ hk_even
    · push_neg at hsmall
      obtain ⟨j, hjmem, hjneq⟩ := hsmall
      have hjodd : Odd (numD j) := odd_mem_num j hjmem
      have hjk : j ≠ k := by
        intro e
        subst j
        rcases hk_even with ⟨a, ha⟩
        rcases hjodd with ⟨b, hb⟩
        omega
      have hgap : numD k + 3 ≤ numD j := by
        rcases hk_even with ⟨a, ha⟩
        rcases hjodd with ⟨b, hb⟩
        have hlt := num_lt j hjk.symm
        omega
      have hkplus : numD k + 2 ≤ numD j := by omega
      exact contradiction_single j hjk hjodd hkplus

end D5.S3.Arith.FibonacciAtomic.OptimalLawTwoMinimalAtoms
