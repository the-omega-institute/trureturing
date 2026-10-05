/- GID: D5/S3/Arith/FibonacciAtomic/OptimalLawNearestStrictCeiling
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/OptimalLawNearestStrictCeiling
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Each larger atom of an attaining law is the nearest strict ceiling at its least binary depth. -/

import D5.S3.Arith.FibonacciAtomic.OptimalLawLargerAtomsTerminate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.OptimalLawNearestStrictCeiling

open scoped BigOperators
open CarryGraphCriticalAttainment (alpha)
open DyadicSupportLines (cost residual)

open Classical in
/-- At the least terminating binary depth of an atom above the minimum,
an attaining law places that atom at the first grid point strictly above
the minimum, including when the minimum itself lies on that grid. -/
theorem result (m : ℕ) (hm : 2 ≤ m) (p : Fin m → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1)
    (hopt : cost p = alpha m * sInf (Set.range p))
    (i : Fin m) (hi : sInf (Set.range p) < p i) :
    let D := Nat.find (OptimalLawLargerAtomsTerminate.result m hm p hp hs hopt i hi)
    p i = ((⌊(2 : ℝ) ^ D * sInf (Set.range p)⌋ : ℝ) + 1) / (2 : ℝ) ^ D := by
  classical
  let t := sInf (Set.range p)
  let depth : Fin m → ℕ := fun a => if h : t < p a then
    Nat.find (OptimalLawLargerAtomsTerminate.result m hm p hp hs hopt a h) else 0
  have at_depth (a : Fin m) (ha : t < p a) :
      ∃ N : ℕ, p a = (N : ℝ) / (2 : ℝ) ^ depth a := by
    simpa only [depth, dif_pos ha] using
      Nat.find_spec (OptimalLawLargerAtomsTerminate.result m hm p hp hs hopt a ha)
  have minimal (a : Fin m) (ha : t < p a) (h : ℕ) (hh : h < depth a) :
      ¬ ∃ N : ℕ, p a = (N : ℝ) / (2 : ℝ) ^ h := by
    apply Nat.find_min (OptimalLawLargerAtomsTerminate.result m hm p hp hs hopt a ha)
    simpa only [depth, dif_pos ha] using hh
  have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  obtain ⟨k, hk0⟩ := (Set.range_nonempty p).csInf_mem (Set.finite_range p)
  have hk : p k = t := hk0
  have low (a : Fin m) : t ≤ p a :=
    csInf_le (Set.finite_range p).bddBelow ⟨a, rfl⟩
  have tpos : 0 < t := hk ▸ hp k
  suffices goal : p i = ((⌊(2 : ℝ) ^ depth i * t⌋ : ℝ) + 1) / (2 : ℝ) ^ depth i by
    simpa only [depth, dif_pos hi, t] using goal
  by_contra failure
  let bad : Finset (Fin m) := Finset.univ.filter (fun a => t < p a ∧
    p a ≠ ((⌊(2 : ℝ) ^ depth a * t⌋ : ℝ) + 1) / (2 : ℝ) ^ depth a)
  have ibad : i ∈ bad := by
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hi, failure⟩
  obtain ⟨j, jbad, maximal⟩ := Finset.exists_max_image bad depth ⟨i, ibad⟩
  have jdata := (Finset.mem_filter.mp jbad).2
  have hj : t < p j := jdata.1
  let d := depth j
  let δ := 1 / (2 : ℝ) ^ d
  let b : ℤ := ⌊(2 : ℝ) ^ d * t⌋
  let Q : ℝ := ((b : ℝ) + 1) / (2 : ℝ) ^ d
  have powpos : 0 < (2 : ℝ) ^ d := by positivity
  have δpos : 0 < δ := by dsimp only [δ]; positivity
  have Qt : t < Q := by
    apply (lt_div_iff₀ powpos).mpr
    simpa only [b, mul_comm] using Int.lt_floor_add_one ((2 : ℝ) ^ d * t)
  have grid (a : Fin m) (ha : t < p a) (hD : depth a ≤ d) :
      ∃ N : ℕ, p a = (N : ℝ) / (2 : ℝ) ^ d := by
    obtain ⟨N, hN⟩ := at_depth a ha
    refine ⟨N * 2 ^ (d - depth a), ?_⟩
    rw [hN, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    have power : (2 : ℝ) ^ d = (2 : ℝ) ^ depth a * (2 : ℝ) ^ (d - depth a) := by
      rw [← pow_add, Nat.add_sub_of_le hD]
    rw [power]
    field_simp
  obtain ⟨N, hN⟩ := at_depth j hj
  change p j = (N : ℝ) / (2 : ℝ) ^ d at hN
  have Nj : (2 : ℝ) ^ d * p j = N := by rw [hN]; field_simp
  have donor_gap : Q + δ ≤ p j := by
    have bN : b < (N : ℤ) := by
      have H := mul_lt_mul_of_pos_left hj powpos
      have H' := Int.floor_le ((2 : ℝ) ^ d * t)
      rw [Nj] at H
      have cast_lt : (b : ℝ) < (N : ℝ) := lt_of_le_of_lt H' H
      exact_mod_cast cast_lt
    have ne : (N : ℤ) ≠ b + 1 := by
      intro eq
      apply jdata.2
      change p j = Q
      dsimp only [Q]
      rw [hN]
      have H : (N : ℝ) = (b : ℝ) + 1 := by exact_mod_cast eq
      rw [H]
    have H : b + 2 ≤ (N : ℤ) := by omega
    have H' : (b : ℝ) + 2 ≤ N := by exact_mod_cast H
    dsimp only [Q, δ]
    rw [hN, ← add_div]
    apply (div_le_div_iff_of_pos_right powpos).mpr
    linarith only [H']
  let S : Finset (Fin m) := Finset.univ.filter (fun a => p a < Q)
  have memS (a : Fin m) : a ∈ S ↔ p a < Q := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have kS : k ∈ S := (memS k).mpr (hk ▸ Qt)
  have jS : j ∉ S := by
    intro H
    have H' := (memS j).mp H
    linarith only [donor_gap, δpos, H']
  let n := S.card
  have npos : 0 < n := Finset.card_pos.mpr ⟨k, kS⟩
  have nlt : n < m := by
    have H : S ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ S, fun eq => jS (eq.symm ▸ Finset.mem_univ j)⟩
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_lt_card H
  have outside_grid (a : Fin m) (ha : a ∉ S) :
      ∃ A : ℕ, p a = (A : ℝ) / (2 : ℝ) ^ d := by
    have Qa : Q ≤ p a := le_of_not_gt (fun H => ha ((memS a).mpr H))
    have hat : t < p a := Qt.trans_le Qa
    by_cases hD : depth a ≤ d
    · exact grid a hat hD
    have deeper : d < depth a := by omega
    have good : p a = ((⌊(2 : ℝ) ^ depth a * t⌋ : ℝ) + 1) / (2 : ℝ) ^ depth a := by
      by_contra H
      have abad : a ∈ bad := by
        simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hat, H⟩
      have H' := maximal a abad
      change depth a ≤ d at H'
      omega
    have QB : ∃ B : ℕ, Q = (B : ℝ) / (2 : ℝ) ^ depth a := by
      have bnonneg : 0 ≤ b := Int.floor_nonneg.mpr (mul_nonneg powpos.le tpos.le)
      refine ⟨(b + 1).toNat * 2 ^ (depth a - d), ?_⟩
      have castB : ((b + 1).toNat : ℝ) = (b : ℝ) + 1 := by
        exact_mod_cast (Int.toNat_of_nonneg (by omega : 0 ≤ b + 1))
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, castB]
      have power : (2 : ℝ) ^ depth a = (2 : ℝ) ^ d * (2 : ℝ) ^ (depth a - d) := by
        rw [← pow_add, Nat.add_sub_of_le deeper.le]
      dsimp only [Q]
      rw [power]
      field_simp
    obtain ⟨B, hB⟩ := QB
    have ceil_le : p a ≤ Q := by
      rw [good, hB]
      apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < (2 : ℝ) ^ depth a)).mpr
      have H := mul_lt_mul_of_pos_left Qt (by positivity : (0 : ℝ) < (2 : ℝ) ^ depth a)
      have HB : (2 : ℝ) ^ depth a * Q = B := by rw [hB]; field_simp
      rw [HB] at H
      have H' : ⌊(2 : ℝ) ^ depth a * t⌋ < (B : ℤ) := Int.floor_lt.mpr (by exact H)
      exact_mod_cast (show ⌊(2 : ℝ) ^ depth a * t⌋ + 1 ≤ (B : ℤ) by omega)
    have equal : p a = Q := le_antisymm ceil_le Qa
    apply False.elim
    apply minimal a hat d deeper
    have bnonneg : 0 ≤ b := Int.floor_nonneg.mpr (mul_nonneg powpos.le tpos.le)
    refine ⟨(b + 1).toNat, ?_⟩
    rw [equal]
    dsimp only [Q]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg (by omega : 0 ≤ b + 1)).symm
  have inside_floor (a : Fin m) (ha : a ∈ S) : ⌊(2 : ℝ) ^ d * p a⌋ = b := by
    apply Int.floor_eq_iff.mpr
    have H := mul_le_mul_of_nonneg_left (low a) powpos.le
    have H' := (lt_div_iff₀ powpos).mp ((memS a).mp ha)
    constructor
    · exact (Int.floor_le ((2 : ℝ) ^ d * t)).trans H
    · simpa only [mul_comm] using H'
  have outside_fract (a : Fin m) (ha : a ∉ S) : Int.fract ((2 : ℝ) ^ d * p a) = 0 := by
    obtain ⟨A, hA⟩ := outside_grid a ha
    have H : (2 : ℝ) ^ d * p a = A := by rw [hA]; field_simp
    rw [H]
    exact Int.fract_natCast A
  let R : ℤ := (2 : ℤ) ^ d - ∑ a, ⌊(2 : ℝ) ^ d * p a⌋
  have sum_fract : (∑ a ∈ S, Int.fract ((2 : ℝ) ^ d * p a)) = (R : ℝ) := by
    have H : (∑ a ∈ S, Int.fract ((2 : ℝ) ^ d * p a)) =
        ∑ a, Int.fract ((2 : ℝ) ^ d * p a) := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro a _ ha
      exact outside_fract a ha
    rw [H]
    dsimp only [R, Int.fract]
    push_cast
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hs, mul_one]
  have fractional_lower : (n : ℝ) * Int.fract ((2 : ℝ) ^ d * t) ≤ R := by
    rw [← sum_fract]
    have H := Finset.sum_le_sum (s := S) (fun a ha =>
      show Int.fract ((2 : ℝ) ^ d * t) ≤ Int.fract ((2 : ℝ) ^ d * p a) from by
        dsimp only [Int.fract]
        rw [inside_floor a ha]
        exact sub_le_sub_right (mul_le_mul_of_nonneg_left (low a) powpos.le) _)
    simpa only [Finset.sum_const, nsmul_eq_mul] using H
  have fractional_upper : R ≤ (n : ℤ) - 1 := by
    have H := Finset.sum_lt_sum_of_nonempty (s := S) ⟨k, kS⟩
      (fun a _ => Int.fract_lt_one ((2 : ℝ) ^ d * p a))
    rw [sum_fract] at H
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at H
    have H' : R < (n : ℤ) := by exact_mod_cast H
    omega
  have gap_bound : δ / n ≤ Q - t := by
    have H : (n : ℝ) * Int.fract ((2 : ℝ) ^ d * t) ≤ (n : ℝ) - 1 :=
      fractional_lower.trans (by exact_mod_cast fractional_upper)
    have Npos : (0 : ℝ) < n := by exact_mod_cast npos
    have identity : Q - t = δ * (1 - Int.fract ((2 : ℝ) ^ d * t)) := by
      dsimp only [Q, δ, Int.fract, b]
      field_simp
      ring
    rw [identity]
    apply (div_le_iff₀ Npos).mpr
    nlinarith only [mul_nonneg δpos.le (show 0 ≤ (n : ℝ) - 1 -
      n * Int.fract ((2 : ℝ) ^ d * t) by linarith only [H])]
  have shallow : ∀ h : ℕ, h < d →
      ⌊(2 : ℝ) ^ h * (p j - 1 / (2 : ℝ) ^ d)⌋ = ⌊(2 : ℝ) ^ h * p j⌋ := by
    have pjlt : p j < 1 := by
      have kj : k ≠ j := by
        intro eq
        have H : p j = t := eq ▸ hk
        rw [H] at hj
        exact (lt_irrefl t) hj
      have H := Finset.single_lt_sum kj (Finset.mem_univ j) (Finset.mem_univ k)
        (hp k) (fun a (_ : a ∈ (Finset.univ : Finset (Fin m))) _ => (hp a).le)
      simpa only [hs] using H
    have dpos : 0 < d := by
      by_contra H
      have dz : d = 0 := by omega
      rw [dz, pow_zero, div_one] at hN
      have HN : (1 : ℝ) ≤ N := by
        exact_mod_cast (show 1 ≤ N by have H := hp j; rw [hN] at H; exact_mod_cast H)
      linarith
    have oddN : N % 2 = 1 := by
      by_contra H
      have evenN : N = 2 * (N / 2) := by omega
      apply minimal j hj (d - 1) (by omega)
      refine ⟨N / 2, ?_⟩
      have power : (2 : ℝ) ^ d = (2 : ℝ) ^ (d - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel dpos]
      have cast_even : (N : ℝ) = 2 * ((N / 2 : ℕ) : ℝ) := by exact_mod_cast evenN
      rw [hN, cast_even, power]
      field_simp
    intro h hh
    let a := d - 1
    have da : d = a + 1 := by dsimp only [a]; omega
    have odd_eq : (N : ℝ) = 2 * ((N / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (show N = 2 * (N / 2) + 1 by omega)
    have expansion : (2 : ℝ) ^ a * p j = ((N / 2 : ℕ) : ℝ) + 1 / 2 := by
      rw [hN, da, pow_succ, odd_eq]
      field_simp
    have reduced : (2 : ℝ) ^ a * (p j - 1 / (2 : ℝ) ^ d) = ((N / 2 : ℕ) : ℝ) := by
      have H : (2 : ℝ) ^ a / (2 : ℝ) ^ d = 1 / 2 := by rw [da, pow_succ]; field_simp
      rw [mul_sub, ← mul_div_assoc, mul_one, H, expansion]
      ring
    have floor_a : ⌊(2 : ℝ) ^ a * p j⌋ = (N / 2 : ℕ) := by
      apply Int.floor_eq_iff.mpr
      rw [expansion]
      simp only [Int.cast_natCast]
      constructor <;> linarith only
    have floor_reduced : ⌊(2 : ℝ) ^ a * (p j - 1 / (2 : ℝ) ^ d)⌋ = (N / 2 : ℕ) := by
      rw [reduced]
      exact Int.floor_natCast _
    have divide (z : ℝ) : (2 : ℝ) ^ a * z / ((2 ^ (a - h) : ℕ) : ℝ) = (2 : ℝ) ^ h * z := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
      have power : (2 : ℝ) ^ a = (2 : ℝ) ^ h * (2 : ℝ) ^ (a - h) := by
        rw [← pow_add, Nat.add_sub_of_le (show h ≤ a by omega)]
      rw [power]
      field_simp
    have H := Int.floor_div_natCast ((2 : ℝ) ^ a * (p j - 1 / (2 : ℝ) ^ d)) (2 ^ (a - h))
    have H' := Int.floor_div_natCast ((2 : ℝ) ^ a * p j) (2 ^ (a - h))
    rw [divide, floor_reduced] at H
    rw [divide, floor_a] at H'
    exact H.trans H'.symm
  have attaining (n : ℕ) (hn : 0 < n) :
      ∃ (q : Fin n → ℝ) (l : Fin n), (∀ i, 0 < q i) ∧ (∑ i, q i) = 1 ∧
        (∀ i, q l ≤ q i) ∧ cost q = alpha n * q l := by
    by_cases h1 : n = 1
    · subst n
      refine ⟨fun _ => 1, 0, by norm_num, by simp, fun _ => le_rfl, ?_⟩
      rw [OptimalLawStrictSlope.result.1, zero_mul]
      have zeros (d : ℕ) : residual (fun _ : Fin 1 => (1 : ℝ)) d / (2 : ℝ) ^ d = 0 := by
        have integer_pow : ⌊(2 : ℝ) ^ d⌋ = (2 : ℤ) ^ d := by
          exact_mod_cast (Int.floor_intCast (R := ℝ) ((2 : ℤ) ^ d))
        simp [DyadicSupportLines.residual, integer_pow]
      simp only [cost, zeros, tsum_zero]
    · have hn2 : 2 ≤ n := by omega
      obtain ⟨V, f, _, _, _, _, _, H⟩ := CarryGraphCriticalAttainment.result n hn2
      dsimp only at H
      rcases H with ⟨ht, hq, hsum, hmin, _, _, _, _, hcost⟩
      let γ := CarryGraphCriticalAttainment.policyPath n (f (alpha n))
        ⟨CarryGraphEmbedding.root n, by
          dsimp [CarryGraphEmbedding.IsState, CarryGraphEmbedding.root]
          omega⟩
      let q : Fin n → ℝ := fun i => Real.ofDigits (CarryGraphRealization.labelDigit γ i)
      change (∀ i, 0 < q i) at hq
      change (∑ i, q i) = 1 at hsum
      change sInf (Set.range q) = CarryGraphEmbedding.anchorValue γ at hmin
      change cost q = alpha n * CarryGraphEmbedding.anchorValue γ at hcost
      have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      obtain ⟨l, hl⟩ := (Set.range_nonempty q).csInf_mem (Set.finite_range q)
      refine ⟨q, l, hq, hsum, ?_, ?_⟩
      · intro i
        rw [hl]
        exact csInf_le (Set.finite_range q).bddBelow ⟨i, rfl⟩
      · rw [hl, hmin]
        exact hcost
  have growth : StrictMono (fun n : ℕ => alpha (n + 1)) := by
    apply strictMono_nat_of_lt_succ
    intro n
    by_cases hn : n = 0
    · subst n
      norm_num only [Nat.zero_add, Nat.reduceAdd, OptimalLawStrictSlope.result.1,
        OptimalLawStrictSlope.result.2.1]
    · simpa only [Nat.add_sub_cancel] using
        OptimalLawStrictSlope.result.2.2 (n + 1 + 1) (by omega)
  let enum : S ≃ Fin n := S.equivFin
  obtain ⟨q, l, hq, hsum, hlow, hcost⟩ := attaining n npos
  let u := q l
  have upos : 0 < u := hq l
  have u_le : u ≤ 1 / n := by
    have H := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hlow a)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum] at H
    apply (le_div_iff₀ (by exact_mod_cast npos : (0 : ℝ) < n)).mpr
    linarith only [H]
  have threshold : t + δ * u ≤ Q := by
    have H := mul_le_mul_of_nonneg_left u_le δpos.le
    rw [← div_eq_mul_one_div] at H
    linarith only [H, gap_bound]
  let receiver : Fin m → ℝ := fun a => if ha : a ∈ S then q (enum ⟨a, ha⟩) else 0
  let P : Fin m → ℝ := fun a => p a + δ * receiver a - if a = j then δ else 0
  have lower (a : Fin m) : t + δ * u ≤ P a := by
    by_cases ha : a ∈ S
    · have naj : a ≠ j := fun H => jS (H ▸ ha)
      have H := hlow (enum ⟨a, ha⟩)
      dsimp only [P, receiver]
      rw [dif_pos ha, if_neg naj, sub_zero]
      have H' := mul_le_mul_of_nonneg_left H δpos.le
      linarith only [H', low a]
    · have Qa : Q ≤ p a := le_of_not_gt (fun H => ha ((memS a).mpr H))
      dsimp only [P, receiver]
      rw [dif_neg ha, mul_zero, add_zero]
      by_cases aj : a = j
      · subst a
        rw [if_pos rfl]
        linarith only [donor_gap, threshold]
      · rw [if_neg aj, sub_zero]
        exact threshold.trans Qa
  have Ppos (a : Fin m) : 0 < P a := by
    have H := lower a
    have H' := mul_pos δpos upos
    linarith only [H, H', tpos]
  obtain ⟨Psum, cost_bound⟩ := OptimalLawLargerAtomsTerminate.transfer m n p hs S enum q
    (fun a => (hq a).le) hsum j jS d shallow
  have αnm : alpha n < alpha m := by
    convert growth (show n - 1 < m - 1 by omega) using 1 <;> congr 1 <;> omega
  have αpos : 0 < alpha m := by
    have H := growth (show 0 < m - 1 by omega)
    simpa only [Nat.zero_add, Nat.sub_add_cancel (show 1 ≤ m by omega),
      OptimalLawStrictSlope.result.1] using H
  obtain ⟨z, _, hz⟩ := Finset.exists_min_image Finset.univ P Finset.univ_nonempty
  have hz' : ∀ a, P z ≤ P a := fun a => hz a (Finset.mem_univ a)
  have optimal_lower : alpha m * P z ≤ cost P := by
    obtain ⟨V, f, _, _, paths, _, zero, _⟩ := CarryGraphCriticalAttainment.result m hm
    obtain ⟨γ, hγ, _, _, _, ha, hc⟩ := (CarryGraphEmbedding.result m hm).2.2.2 P Ppos Psum z hz'
    have H := (paths (alpha m)).2.2 γ hγ
    rw [zero, ha, hc] at H
    linarith only [H]
  have bound : cost P ≤ alpha m * t + δ * (alpha n * u) := by
    simpa only [hopt, hcost] using cost_bound
  have new_lower : alpha m * (t + δ * u) ≤ cost P :=
    (mul_le_mul_of_nonneg_left (lower z) αpos.le).trans optimal_lower
  have improvement : alpha m * t + δ * (alpha n * u) < alpha m * (t + δ * u) := by
    have H := mul_lt_mul_of_pos_right αnm (mul_pos δpos upos)
    nlinarith only [H]
  exact (not_lt_of_ge (new_lower.trans bound)) improvement

end D5.S3.Arith.FibonacciAtomic.OptimalLawNearestStrictCeiling
