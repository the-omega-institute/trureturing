/- GID: D5/S3/Arith/FibonacciAtomic/MersenneDyadicEqualityLaws
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/MersenneDyadicEqualityLaws
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Equality laws of both dyadic support lines on Mersenne probability simplices. -/

import D5.S3.Arith.FibonacciAtomic.MersenneDyadicSupportLines
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.MersenneDyadicEqualityLaws

open scoped BigOperators
open D5.S3.Arith.FibonacciAtomic.DyadicSupportLines

/-- Both support-line equality classifications on the complete real probability simplex. -/
theorem result (h : ℕ) (hh : 2 ≤ h) (p : Fin (2 ^ h - 1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    let t := Finset.univ.inf' (by
      have := Nat.lt_two_pow_self (n := h)
      exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩) p
    (cost p = ((h : ℝ) * 2 ^ h - 2) * t ↔
      ∃ j, p = (fun i => if i = j then (1 : ℝ) else 0) ∨
        p = (fun i => (1 + if i = j then (1 : ℝ) else 0) / (2 : ℝ) ^ h)) ∧
      (cost p = (((h : ℝ) + 2) * 2 ^ h - 2) * t - 2 ↔
        p = (fun _i => 1 / ((2 ^ h - 1 : ℕ) : ℝ)) ∨
          ∃ r j, p = (fun i => if i = j then
            1 / ((2 ^ h - 1 : ℕ) : ℝ) + ((2 : ℝ) ^ h - 2) /
              (((2 ^ h - 1 : ℕ) : ℝ) * ((2 : ℝ) ^ h) ^ (r + 1))
            else 1 / ((2 ^ h - 1 : ℕ) : ℝ) - 1 /
              (((2 ^ h - 1 : ℕ) : ℝ) * ((2 : ℝ) ^ h) ^ (r + 1)))) := by
  classical
  let m := 2 ^ h - 1
  let M := (2 : ℝ) ^ h
  have hM4 : 4 ≤ M := by
    have H := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hh
    norm_num at H
    exact H
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) hM4
  have hmcast : (m : ℝ) = M - 1 := by
    dsimp [m, M]
    rw [Nat.cast_sub (by have := Nat.lt_two_pow_self (n := h); omega)]
    norm_cast
  have hm3 : 3 ≤ m := by
    have E : (3 : ℝ) ≤ m := by rw [hmcast]; linarith only [hM4]
    exact_mod_cast E
  have nonempty : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  change (cost p = ((h : ℝ) * M - 2) * Finset.univ.inf' nonempty p ↔
    ∃ j, p = (fun i => if i = j then (1 : ℝ) else 0) ∨
      p = (fun i => (1 + if i = j then (1 : ℝ) else 0) / M)) ∧
    (cost p = (((h : ℝ) + 2) * M - 2) * Finset.univ.inf' nonempty p - 2 ↔
      p = (fun _i => 1 / (m : ℝ)) ∨ ∃ r j, p = (fun i => if i = j then
        1 / (m : ℝ) + (M - 2) / ((m : ℝ) * M ^ (r + 1))
        else 1 / (m : ℝ) - 1 / ((m : ℝ) * M ^ (r + 1))))
  have entropy {ι : Type} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
      (hs : ∑ i, p i = 1) : (∑ i, Real.negMulLog (p i)) / Real.log 2 ≤ cost p := by
    classical
    let f := fun (i : ι) (d : ℕ) => p i - (⌊(2 : ℝ) ^ d * p i⌋ : ℝ) / (2 : ℝ) ^ d
    have f0 (i : ι) (d : ℕ) : 0 ≤ f i d := by
      dsimp [f]
      exact sub_nonneg.mpr ((div_le_iff₀ (by positivity)).mpr (by
        simpa [mul_comm] using Int.floor_le ((2 : ℝ) ^ d * p i)))
    have fbound (i : ι) (d : ℕ) : f i d ≤ 1 / (2 : ℝ) ^ d := by
      have H := Int.lt_floor_add_one ((2 : ℝ) ^ d * p i)
      dsimp [f]
      apply (le_div_iff₀ (by positivity)).mpr
      field_simp
      simp only [mul_comm] at H
      linarith
    have fsum (i : ι) : Summable (f i) :=
      Summable.of_nonneg_of_le (f0 i) (fbound i) (by
        simpa [one_div, inv_pow] using
          summable_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num))
    have total (d : ℕ) : D5.S3.Arith.FibonacciAtomic.DyadicSupportLines.residual p d / (2 : ℝ) ^ d = ∑ i, f i d := by
      simp only [f, Finset.sum_sub_distrib, hs, ← Finset.sum_div, D5.S3.Arith.FibonacciAtomic.DyadicSupportLines.residual, Int.cast_sum]
      field_simp
    have scalar (i : ι) : Real.negMulLog (p i) / Real.log 2 ≤ ∑' d, f i d := by
      by_cases hz : p i = 0
      · simp [hz, Real.negMulLog, f]
      have hpos : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hz)
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / p i) (by norm_num : (1 : ℝ) < 2)
      have hex : ∃ k : ℕ, 1 ≤ (2 : ℝ) ^ k * p i := ⟨n, by
        have H := (div_lt_iff₀ hpos).mp hn
        simpa [mul_comm] using H.le⟩
      let k := Nat.find hex
      have hk : 1 ≤ (2 : ℝ) ^ k * p i := Nat.find_spec hex
      have floors (d : ℕ) (hd : d ∈ Finset.range k) : ⌊(2 : ℝ) ^ d * p i⌋ = 0 := by
        apply Int.floor_eq_iff.mpr
        simp only [Int.cast_zero, zero_add]
        exact ⟨mul_nonneg (by positivity) (hp i),
          lt_of_not_ge (Nat.find_min hex (Finset.mem_range.mp hd))⟩
      have prefix_bound : (k : ℝ) * p i ≤ ∑' d, f i d := by
        calc
          _ = ∑ d ∈ Finset.range k, f i d := by
            simp only [f]
            rw [Finset.sum_congr rfl (fun d hd => show
              p i - (⌊(2 : ℝ) ^ d * p i⌋ : ℝ) / (2 : ℝ) ^ d = p i by simp [floors d hd])]
            simp
          _ ≤ _ := (fsum i).sum_le_tsum _ (fun d _ => f0 i d)
      have hx : 1 / (2 : ℝ) ^ k ≤ p i :=
        (div_le_iff₀ (by positivity)).mpr (by simpa [mul_comm] using hk)
      have logbound := Real.log_le_log (by positivity : (0 : ℝ) < 1 / 2 ^ k) hx
      rw [Real.log_div (by norm_num) (by positivity), Real.log_one, Real.log_pow] at logbound
      have H := mul_le_mul_of_nonneg_left logbound (hp i)
      have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
      apply le_trans _ prefix_bound
      apply (div_le_iff₀ hl).mpr
      dsimp [Real.negMulLog]
      nlinarith only [H]
    calc
      _ = ∑ i, Real.negMulLog (p i) / Real.log 2 := by rw [Finset.sum_div]
      _ ≤ ∑ i, ∑' d, f i d := Finset.sum_le_sum (fun i _ => scalar i)
      _ = cost p := by
        unfold cost
        simp_rw [total]
        exact (Summable.tsum_finsetSum (s := Finset.univ) (fun i _ => fsum i)).symm
  have low_rigidity (h : ℕ) (hh : 2 ≤ h) (p : Fin (2 ^ h - 1) → ℝ)
      (hs : ∑ i, p i = 1) (t : ℝ) (ht : 0 < t)
      (hmin : ∀ i, t ≤ p i) (hlow : t ≤ 1 / (2 : ℝ) ^ h)
      (he : ∑ i, Real.negMulLog (p i) ≤ ((h : ℝ) * 2 ^ h - 2) * t * Real.log 2) :
      t = 1 / (2 : ℝ) ^ h ∧ ∃ j, ∀ i,
        p i = (1 + if i = j then (1 : ℝ) else 0) / (2 : ℝ) ^ h := by
    classical
    let m := 2 ^ h - 1
    let M := (2 : ℝ) ^ h
    have hM4 : 4 ≤ M := by
      have H := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hh
      norm_num at H
      exact H
    have hM : 0 < M := lt_of_lt_of_le (by norm_num) hM4
    have hm : (m : ℝ) = M - 1 := by
      dsimp [m, M]
      rw [Nat.cast_sub (by have := Nat.lt_two_pow_self (n := h); omega)]
      norm_cast
    have hS : ∑ i : Fin m, p i = 1 := hs
    let w : Fin m → ℝ := fun i => (p i - t) / (1 - (m : ℝ) * t)
    let c := M * t
    have hc0 : 0 < c := mul_pos hM ht
    have hc1 : c ≤ 1 := by
      dsimp [c]
      simpa [mul_comm] using (le_div_iff₀ hM).mp hlow
    have den : 0 < 1 - (m : ℝ) * t := by rw [hm]; nlinarith only [hc1, ht]
    have hw0 (i : Fin m) : 0 ≤ w i := div_nonneg (sub_nonneg.mpr (hmin i)) den.le
    have hws : ∑ i, w i = 1 := by
      simp only [w, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hS]
      exact div_self den.ne'
    let vertex := fun (z : Fin m × Bool) (i : Fin m) =>
      if z.2 then (1 + if i = z.1 then (1 : ℝ) else 0) / M
        else (if i = z.1 then (1 : ℝ) else 0)
    let weight := fun z : Fin m × Bool => (if z.2 then c else 1 - c) * w z.1
    have weight0 (z : Fin m × Bool) : 0 ≤ weight z := by
      dsimp [weight]
      split <;> exact mul_nonneg (by linarith only [hc0, hc1]) (hw0 z.1)
    have weights : ∑ z, weight z = 1 := by
      simp only [weight, Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true,
        ↓reduceIte, ← add_mul, add_sub_cancel, one_mul, hws]
    have vertices (z : Fin m × Bool) (i : Fin m) : vertex z i ∈ Set.Ici (0 : ℝ) := by
      dsimp [vertex, Set.mem_Ici]
      split <;> split <;> norm_num <;> positivity
    have mix (i : Fin m) : ∑ z, weight z * vertex z i = p i := by
      have term (j : Fin m) : weight (j, true) * vertex (j, true) i +
          weight (j, false) * vertex (j, false) i =
          (c / M) * w j + (c / M + (1 - c)) * w j * (if i = j then (1 : ℝ) else 0) := by
        simp only [weight, vertex, Bool.false_eq_true, ↓reduceIte]
        ring
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, term]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hws, mul_one]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      have cm : c / M = t := by dsimp [c]; rw [mul_div_cancel_left₀ _ hM.ne']
      have dc : c / M + (1 - c) = 1 - (m : ℝ) * t := by
        rw [cm, hm]
        dsimp [c]
        ring
      rw [dc, cm]
      dsimp only [w]
      rw [mul_div_cancel₀ _ den.ne']
      ring
    have entvertex (j : Fin m) : ∑ i, Real.negMulLog (vertex (j, true) i) =
        ((h : ℝ) - 2 / M) * Real.log 2 := by
      have eval1 : Real.negMulLog (1 / M) = (h : ℝ) * Real.log 2 / M := by
        simp only [Real.negMulLog, Real.log_div one_ne_zero hM.ne', Real.log_one, zero_sub]
        dsimp [M]
        rw [Real.log_pow]
        ring
      have eval2 : Real.negMulLog (2 / M) = 2 * ((h : ℝ) - 1) * Real.log 2 / M := by
        simp only [Real.negMulLog, Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hM.ne']
        dsimp [M]
        rw [Real.log_pow]
        ring
      have eqv (i : Fin m) : Real.negMulLog (vertex (j, true) i) =
          (h : ℝ) * Real.log 2 / M +
            if i = j then ((h : ℝ) - 2) * Real.log 2 / M else 0 := by
        by_cases hi : i = j
        · simp only [vertex, ↓reduceIte, hi, one_add_one_eq_two, eval2]
          ring
        · simpa only [vertex, ↓reduceIte, hi, add_zero] using eval1
      simp_rw [eqv]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rw [hm]
      field_simp <;> ring
    have entpoint (j : Fin m) : ∑ i, Real.negMulLog (vertex (j, false) i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : i = j <;> simp [vertex, hi]
    have vertexsum : ∑ i, ∑ z, weight z * Real.negMulLog (vertex z i) =
        ((h : ℝ) * M - 2) * t * Real.log 2 := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, Fintype.sum_prod_type, Fintype.sum_bool,
        weight, entvertex, entpoint, mul_zero, add_zero, Bool.false_eq_true, ↓reduceIte,
        ← Finset.sum_mul, ← Finset.mul_sum, hws, mul_one]
      dsimp [c]
      field_simp <;> ring
    have jensen (i : Fin m) :
        ∑ z, weight z * Real.negMulLog (vertex z i) ≤ Real.negMulLog (p i) := by
      have H := Real.strictConcaveOn_negMulLog.concaveOn.le_map_sum
        (t := Finset.univ) (w := weight) (p := fun z => vertex z i)
        (fun z _ => weight0 z) weights (fun z _ => vertices z i)
      simpa only [smul_eq_mul, mix i] using H
    have equal (i : Fin m) : Real.negMulLog (p i) =
        ∑ z, weight z * Real.negMulLog (vertex z i) := by
      have total : (∑ i, ∑ z, weight z * Real.negMulLog (vertex z i)) =
          ∑ i, Real.negMulLog (p i) := by
        apply le_antisymm (Finset.sum_le_sum (fun i _ => jensen i))
        rw [vertexsum]
        exact he
      exact ((Finset.sum_eq_sum_iff_of_le (fun i _ => jensen i)).mp total i
        (Finset.mem_univ i)).symm
    have same (i : Fin m) (z z' : Fin m × Bool) (hz : weight z ≠ 0) (hz' : weight z' ≠ 0) :
        vertex z i = vertex z' i := by
      apply (Real.strictConcaveOn_negMulLog.map_sum_eq_iff_of_nonneg
        (t := Finset.univ) (w := weight) (p := fun z => vertex z i)
        (fun z _ => weight0 z) weights (fun z _ => vertices z i)).mp
        (by simpa only [smul_eq_mul, mix i] using equal i)
        (Finset.mem_univ z) hz (Finset.mem_univ z') hz'
    obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hws]; norm_num)
    have active : weight (j, true) ≠ 0 := by
      simpa [weight] using mul_ne_zero hc0.ne' hj
    have hc : c = 1 := by
      by_contra H
      have other : weight (j, false) ≠ 0 := by
        simpa [weight] using mul_ne_zero (sub_ne_zero.mpr (Ne.symm H)) hj
      have E := same j (j, false) (j, true) other active
      simp [vertex] at E
      have E' := (eq_div_iff hM.ne').mp E
      linarith only [E', hM4]
    have htM : t = 1 / M := by dsimp [c] at hc; apply (eq_div_iff hM.ne').mpr; linarith only [hc]
    refine ⟨htM, j, ?_⟩
    intro i
    calc
      p i = ∑ z, weight z * vertex z i := (mix i).symm
      _ = ∑ z, weight z * vertex (j, true) i := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : weight z = 0
        · simp [hz]
        · rw [same i z (j, true) hz active]
      _ = vertex (j, true) i := by rw [← Finset.sum_mul, weights, one_mul]
      _ = _ := by simp [vertex, M]
  have biased_cost (h : ℕ) (hh : 2 ≤ h) (j : Fin (2 ^ h - 1)) :
      cost (fun i : Fin (2 ^ h - 1) => (1 + if i = j then (1 : ℝ) else 0) / (2 : ℝ) ^ h) =
        (h : ℝ) - 2 / (2 : ℝ) ^ h := by
    classical
    let M := (2 : ℝ) ^ h
    let p := fun i : Fin (2 ^ h - 1) => (1 + if i = j then (1 : ℝ) else 0) / M
    have hM : 0 < M := by positivity
    have card : ((2 ^ h - 1 : ℕ) : ℝ) = M - 1 := by
      dsimp [M]
      rw [Nat.cast_sub (by have := Nat.lt_two_pow_self (n := h); omega)]
      norm_cast
    have ratio (d : ℕ) : (2 : ℝ) ^ d / M =
        if d < h then 1 / (2 : ℝ) ^ (h - d) else (2 : ℝ) ^ (d - h) := by
      dsimp [M]
      split
      · field_simp <;> ring
        rw [← pow_add, Nat.add_sub_of_le (by omega : d ≤ h)]
      · exact (pow_sub₀ (2 : ℝ) (by norm_num) (by omega : h ≤ d)).symm
    have headfloor (i : Fin (2 ^ h - 1)) (d : ℕ) (hd : d < h - 1) :
        ⌊(2 : ℝ) ^ d * p i⌋ = 0 := by
      have H : 4 ≤ (2 : ℝ) ^ (h - d) := by
        have E := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 2 ≤ h - d)
        norm_num at E
        exact E
      apply Int.floor_eq_iff.mpr
      simp only [Int.cast_zero, zero_add]
      dsimp [p]
      have eqn : (2 : ℝ) ^ d * ((1 + if i = j then (1 : ℝ) else 0) / M) =
          (1 + if i = j then (1 : ℝ) else 0) / (2 : ℝ) ^ (h - d) := by
        calc
          _ = ((2 : ℝ) ^ d / M) * (1 + if i = j then (1 : ℝ) else 0) := by ring
          _ = _ := by rw [ratio, if_pos (by omega)]; ring
      rw [eqn]
      by_cases hi : i = j
      · simp only [hi, ite_true, one_add_one_eq_two]
        exact ⟨by positivity, (div_lt_one (by positivity)).mpr (by linarith)⟩
      · simp only [hi, if_false, add_zero]
        exact ⟨by positivity, (div_lt_one (by positivity)).mpr (by linarith)⟩
    have boundaryfloor (i : Fin (2 ^ h - 1)) :
        ⌊(2 : ℝ) ^ (h - 1) * p i⌋ = if i = j then (1 : ℤ) else 0 := by
      have ratio' : (2 : ℝ) ^ (h - 1) / M = 1 / 2 := by
        rw [ratio, if_pos (by omega), show h - (h - 1) = 1 by omega]
        norm_num
      have eqn : (2 : ℝ) ^ (h - 1) * p i = (1 + if i = j then (1 : ℝ) else 0) / 2 := by
        dsimp [p]
        calc
          _ = ((2 : ℝ) ^ (h - 1) / M) * (1 + if i = j then (1 : ℝ) else 0) := by ring
          _ = _ := by rw [ratio']; ring
      rw [eqn]
      by_cases hi : i = j <;> norm_num [hi]
    have tailfloor (i : Fin (2 ^ h - 1)) (d : ℕ) (hd : h ≤ d) :
        ⌊(2 : ℝ) ^ d * p i⌋ = (2 : ℤ) ^ (d - h) * (1 + if i = j then (1 : ℤ) else 0) := by
      have eqn : (2 : ℝ) ^ d * p i =
          (((2 : ℤ) ^ (d - h) * (1 + if i = j then (1 : ℤ) else 0) : ℤ) : ℝ) := by
        dsimp [p]
        calc
          _ = ((2 : ℝ) ^ d / M) * (1 + if i = j then (1 : ℝ) else 0) := by ring
          _ = _ := by rw [ratio, if_neg (by omega)]; norm_cast
      rw [eqn, Int.floor_intCast]
    have headterm (d : ℕ) (hd : d < h - 1) :
        D5.S3.Arith.FibonacciAtomic.DyadicSupportLines.residual p d / (2 : ℝ) ^ d = 1 := by
      simp only [D5.S3.Arith.FibonacciAtomic.DyadicSupportLines.residual, headfloor _ _ hd,
        Int.cast_zero, Finset.sum_const_zero, sub_zero]
      exact div_self (by positivity)
    have boundaryterm : D5.S3.Arith.FibonacciAtomic.DyadicSupportLines.residual p (h - 1) /
        (2 : ℝ) ^ (h - 1) = 1 - 2 / M := by
      simp only [D5.S3.Arith.FibonacciAtomic.DyadicSupportLines.residual, boundaryfloor,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Int.cast_one]
      have E : (2 : ℝ) ^ (h - 1) * 2 = M := by
        dsimp [M]
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      field_simp <;> ring
      linarith only [E]
    have tailterm (d : ℕ) (hd : h ≤ d) :
        D5.S3.Arith.FibonacciAtomic.DyadicSupportLines.residual p d / (2 : ℝ) ^ d = 0 := by
      unfold D5.S3.Arith.FibonacciAtomic.DyadicSupportLines.residual
      rw [Finset.sum_congr rfl (fun i _ => tailfloor i d hd), ← Finset.mul_sum,
        Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      push_cast
      rw [card]
      have E : (2 : ℝ) ^ d = (2 : ℝ) ^ (d - h) * M := by
        dsimp [M]
        rw [← pow_add, Nat.sub_add_cancel hd]
      rw [E]
      ring
    change cost p = (h : ℝ) - 2 / M
    unfold cost
    rw [tsum_eq_sum (s := Finset.range h) (fun d hd => tailterm d (by simpa using hd))]
    have split := Finset.sum_range_succ
      (fun d => D5.S3.Arith.FibonacciAtomic.DyadicSupportLines.residual p d / (2 : ℝ) ^ d) (h - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ h)] at split
    rw [split, boundaryterm]
    rw [Finset.sum_congr rfl (fun d hd => headterm d (Finset.mem_range.mp hd))]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [Nat.cast_sub (by omega : 1 ≤ h)]
    ring
  have tail_nonneg (P : Fin m → ℝ) (hS : ∑ i, P i = 1) (d : ℕ) :
      0 ≤ D5.S3.Arith.FibonacciAtomic.DyadicSupportLines.residual P d / (2 : ℝ) ^ d :=
    div_nonneg ((MersenneDyadicSupportLines.simplex_data h P hS).1 d).1 (by positivity)
  have zero_point (P : Fin m → ℝ) (hP : ∀ i, 0 ≤ P i) (hS : ∑ i, P i = 1)
      (hzero : cost P = 0) : ∃ j, P = fun i => if i = j then (1 : ℝ) else 0 := by
    have sumP := (D5.S3.Arith.FibonacciAtomic.MersenneDyadicSupportLines.mersenne_support_lines
      h hh P hP hS).1
    have H := sumP.le_tsum 0 (fun d _ => tail_nonneg P hS d)
    change D5.S3.Arith.FibonacciAtomic.DyadicSupportLines.residual P 0 / (2 : ℝ) ^ 0 ≤ cost P at H
    rw [hzero] at H
    have S : ∑ i, (⌊P i⌋ : ℝ) = 1 := by
      have Z := tail_nonneg P hS 0
      simp only [D5.S3.Arith.FibonacciAtomic.DyadicSupportLines.residual, pow_zero,
        one_mul, div_one, Int.cast_sum] at H Z
      linarith only [H, Z]
    obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [S]; norm_num)
    have floorj : (1 : ℤ) ≤ ⌊P j⌋ := by
      have H0 : (0 : ℤ) ≤ ⌊P j⌋ := Int.floor_nonneg.mpr (hP j)
      have Hne : ⌊P j⌋ ≠ 0 := by exact_mod_cast hj
      omega
    have pj1 : P j = 1 := by
      have upper := Finset.single_le_sum (s := Finset.univ) (fun i _ => hP i) (Finset.mem_univ j)
      rw [hS] at upper
      have cast : (1 : ℝ) ≤ (⌊P j⌋ : ℝ) := by exact_mod_cast floorj
      exact le_antisymm upper (cast.trans (Int.floor_le _))
    have dom (i : Fin m) : (if i = j then (1 : ℝ) else 0) ≤ P i := by
      by_cases hi : i = j
      · simp [hi, pj1]
      · simpa [hi] using hP i
    refine ⟨j, funext fun i => ?_⟩
    have E : (∑ i : Fin m, if i = j then (1 : ℝ) else 0) = ∑ i, P i := by
      simp [hS]
    exact ((Finset.sum_eq_sum_iff_of_le (fun i _ => dom i)).mp E i (Finset.mem_univ i)).symm
  have minimum_profile (j : Fin m) (x y : ℝ) (hxy : x ≤ y) :
      Finset.univ.inf' nonempty (fun i : Fin m => if i = j then y else x) = x := by
    obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card (by simp; omega : 1 < Fintype.card (Fin m)) j
    apply le_antisymm
    · exact (Finset.inf'_le _ (Finset.mem_univ k)).trans (by simp [hk])
    · apply Finset.le_inf'
      intro i _
      by_cases hi : i = j <;> simp [hi, hxy]
  have point_cost (j : Fin m) : cost (fun i : Fin m => if i = j then (1 : ℝ) else 0) = 0 := by
    unfold cost
    calc
      _ = ∑' _d : ℕ, (0 : ℝ) := by
        apply tsum_congr
        intro d
        have floors (i : Fin m) : ⌊(2 : ℝ) ^ d * (if i = j then (1 : ℝ) else 0)⌋ =
            if i = j then (2 : ℤ) ^ d else 0 := by
          by_cases hi : i = j
          · simp only [hi, ↓reduceIte, mul_one]
            have cast : (2 : ℝ) ^ d = (((2 : ℕ) ^ d : ℕ) : ℝ) := by norm_cast
            rw [cast, Int.floor_natCast]
            norm_cast
          · simp [hi]
        simp only [D5.S3.Arith.FibonacciAtomic.DyadicSupportLines.residual, floors,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Int.cast_pow,
          Int.cast_ofNat, sub_self, zero_div]
      _ = 0 := tsum_zero
  have first_forward (P : Fin m → ℝ) (hP : ∀ i, 0 ≤ P i) (hS : ∑ i, P i = 1)
      (eqcost : cost P = ((h : ℝ) * M - 2) * Finset.univ.inf' nonempty P) :
      ∃ j, P = (fun i => if i = j then (1 : ℝ) else 0) ∨
        P = (fun i => (1 + if i = j then (1 : ℝ) else 0) / M) := by
    let t := Finset.univ.inf' nonempty P
    have lower (i : Fin m) : t ≤ P i := Finset.inf'_le _ (Finset.mem_univ i)
    have ht0 : 0 ≤ t := Finset.le_inf' _ _ (fun i _ => hP i)
    change cost P = ((h : ℝ) * M - 2) * t at eqcost
    by_cases ht : t = 0
    · have H : cost P = 0 := by simpa only [ht, mul_zero] using eqcost
      obtain ⟨j, hj⟩ := zero_point P hP hS H
      exact ⟨j, Or.inl hj⟩
    have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have htlow : t ≤ 1 / M := by
      by_contra H
      have H' : 1 < M * t := by
        simpa [mul_comm] using (div_lt_iff₀ hM).mp (lt_of_not_ge H)
      have line2 := (D5.S3.Arith.FibonacciAtomic.MersenneDyadicSupportLines.mersenne_support_lines
        h hh P hP hS).2.2.2.2
      change (((h : ℝ) + 2) * M - 2) * t - 2 ≤ cost P at line2
      change cost P = ((h : ℝ) * M - 2) * t at eqcost
      nlinarith only [H', line2, eqcost]
    have EH : ∑ i, Real.negMulLog (P i) ≤ ((h : ℝ) * M - 2) * t * Real.log 2 := by
      have H := entropy P hP hS
      have H' := (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp H
      change cost P = ((h : ℝ) * M - 2) * t at eqcost
      rwa [eqcost] at H'
    obtain ⟨_, j, hj⟩ := low_rigidity h hh P hS t htpos lower htlow EH
    exact ⟨j, Or.inr (funext hj)⟩
  have first_reverse (P : Fin m → ℝ)
      (law : ∃ j, P = (fun i => if i = j then (1 : ℝ) else 0) ∨
        P = (fun i => (1 + if i = j then (1 : ℝ) else 0) / M)) :
      cost P = ((h : ℝ) * M - 2) * Finset.univ.inf' nonempty P := by
    obtain ⟨j, hj | hj⟩ := law
    · rw [hj, point_cost j, minimum_profile j 0 1 (by norm_num), mul_zero]
    · have profile : (fun i : Fin m => (1 + if i = j then (1 : ℝ) else 0) / M) =
          (fun i : Fin m => if i = j then 2 / M else 1 / M) := by
        ext i
        by_cases hi : i = j <;> norm_num [hi]
      rw [hj, biased_cost h hh j, profile,
        minimum_profile j (1 / M) (2 / M) (by apply div_le_div_of_nonneg_right; norm_num; positivity)]
      dsimp only [M]
      field_simp <;> ring
  have scaling (h : ℕ) (hh : 2 ≤ h) (P : Fin (2 ^ h - 1) → ℝ)
      (hS : ∑ i, P i = 1) (hlo : ∀ i, 1 / (2 : ℝ) ^ h < P i) :
      let Q := fun i => (2 : ℝ) ^ h * P i - 1
      (∀ i, 0 ≤ Q i) ∧ (∑ i, Q i = 1) ∧ cost P = (h : ℝ) + cost Q / (2 : ℝ) ^ h := by
    classical
    have ne : (Finset.univ : Finset (Fin (2 ^ h - 1))).Nonempty := by
      have := Nat.lt_two_pow_self (n := h)
      exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    exact MersenneDyadicSupportLines.scaling h hh P hS (Finset.univ.inf' ne P)
      (fun i => Finset.inf'_le _ (Finset.mem_univ i))
      ((Finset.lt_inf'_iff ne).mpr (fun i _ => hlo i))
  let c := 1 / (m : ℝ)
  let b := (((h : ℝ) + 2) * M - 2)
  let S := fun (r : ℕ) (j : Fin m) (i : Fin m) =>
    if i = j then c + (M - 2) / ((m : ℝ) * M ^ (r + 1))
      else c - 1 / ((m : ℝ) * M ^ (r + 1))
  let tr := fun r : ℕ => c - 1 / ((m : ℝ) * M ^ (r + 1))
  have hmc : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hM1 : 1 < M := by linarith only [hM4]
  have hMm : M - 1 ≠ 0 := by linarith only [hM4]
  have fixed : M * c - 1 = c := by dsimp [c]; rw [hmcast]; field_simp [hM.ne', hmc.ne', hMm] <;> ring
  have csum : ∑ _i : Fin m, c = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, c]
    exact mul_one_div_cancel hmc.ne'
  have cmin : Finset.univ.inf' nonempty (fun _i : Fin m => c) = c := by simp
  have minimum_exists (P : Fin m → ℝ) : ∃ i, Finset.univ.inf' nonempty P = P i := by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' nonempty P
    exact ⟨i, hi⟩
  have second_forward (P : Fin m → ℝ) (hP : ∀ i, 0 ≤ P i) (hS : ∑ i, P i = 1)
      (eqcost : cost P = b * Finset.univ.inf' nonempty P - 2) :
      P = (fun _i => c) ∨ ∃ r j, P = S r j := by
    let t := Finset.univ.inf' nonempty P
    have lower (i : Fin m) : t ≤ P i := Finset.inf'_le _ (Finset.mem_univ i)
    have htmax : t ≤ c := (D5.S3.Arith.FibonacciAtomic.MersenneDyadicSupportLines.mersenne_support_lines
      h hh P hP hS).2.2.1
    by_cases ht : t = c
    · left
      ext i
      have E : (∑ _i : Fin m, c) = ∑ i, P i := by rw [csum, hS]
      exact ((Finset.sum_eq_sum_iff_of_le (fun i _ => by rw [← ht]; exact lower i)).mp
        E i (Finset.mem_univ i)).symm
    have gap : 0 < c - t := sub_pos.mpr (lt_of_le_of_ne htmax ht)
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((c - 1 / M) / (c - t)) hM1
    have exit_exists : ∃ k : ℕ, c - M ^ k * (c - t) ≤ 1 / M := by
      refine ⟨k, ?_⟩
      have E := (div_lt_iff₀ gap).mp hk
      linarith only [E]
    let n := Nat.find exit_exists
    let T := fun k : ℕ => c - M ^ k * (c - t)
    let R := fun (k : ℕ) (i : Fin m) => c + M ^ k * (P i - c)
    have R0 : R 0 = P := by ext i; simp [R]
    have T0 : T 0 = t := by simp [T]
    have Tnext (k : ℕ) : T (k + 1) = M * T k - 1 := by
      dsimp [T]
      rw [pow_succ]
      linear_combination -fixed
    have Rnext (k : ℕ) : R (k + 1) = (fun i => M * R k i - 1) := by
      ext i
      dsimp [R]
      rw [pow_succ]
      linear_combination -fixed
    have Rsum (k : ℕ) : ∑ i, R k i = 1 := by
      simp only [R, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_sub_distrib, csum, hS, sub_self, mul_zero, add_zero]
    have Rlower (k : ℕ) (i : Fin m) : T k ≤ R k i := by
      have E := mul_le_mul_of_nonneg_left (lower i) (pow_nonneg hM.le k)
      dsimp [T, R]
      linarith only [E]
    have Rmin (k : ℕ) : Finset.univ.inf' nonempty (R k) = T k := by
      obtain ⟨i, hi⟩ := minimum_exists P
      apply le_antisymm
      · have E := Finset.inf'_le (R k) (Finset.mem_univ i)
        have at_i : R k i = T k := by dsimp [R, T]; rw [← hi]; change c + M ^ k * (t - c) = _; ring
        rwa [at_i] at E
      · exact Finset.le_inf' _ _ (fun i _ => Rlower k i)
    have propagated (k : ℕ) : k ≤ n → (∀ i, 0 ≤ R k i) ∧ cost (R k) = b * T k - 2 := by
      induction k with
      | zero => intro _; simpa only [R0, T0] using And.intro hP eqcost
      | succ k ih =>
        intro hk
        have prev := ih (by omega)
        have above : 1 / M < T k := by
          have E := Nat.find_min exit_exists (by omega : k < n)
          exact lt_of_not_ge E
        have strictly (i : Fin m) : 1 / M < R k i := above.trans_le (Rlower k i)
        obtain ⟨hQ, _, H⟩ := scaling h hh (R k) (Rsum k) strictly
        change cost (R k) = (h : ℝ) + cost (fun i => M * R k i - 1) / M at H
        rw [← Rnext k] at H
        change ∀ i, 0 ≤ M * R k i - 1 at hQ
        refine ⟨?_, ?_⟩
        · intro i
          have E := congrFun (Rnext k) i
          rw [E]
          exact hQ i
        have EQ : M * cost (R k) = (h : ℝ) * M + cost (R (k + 1)) := by
          rw [H]
          field_simp [hM.ne', hmc.ne', hMm] <;> ring
        rw [prev.2] at EQ
        rw [Tnext]
        dsimp only [b] at EQ ⊢
        nlinarith only [EQ]
    have finished := propagated n le_rfl
    have end_le : T n ≤ 1 / M := Nat.find_spec exit_exists
    have line1 := (D5.S3.Arith.FibonacciAtomic.MersenneDyadicSupportLines.mersenne_support_lines
      h hh (R n) finished.1 (Rsum n)).2.2.2.1
    rw [Rmin n, finished.2] at line1
    have end_eq : T n = 1 / M := by
      dsimp only [b] at line1
      have E : 1 ≤ M * T n := by nlinarith only [line1]
      exact le_antisymm end_le ((div_le_iff₀ hM).mpr (by simpa [mul_comm] using E))
    have first_eq : cost (R n) = ((h : ℝ) * M - 2) * Finset.univ.inf' nonempty (R n) := by
      rw [finished.2, Rmin n, end_eq]
      dsimp only [b]
      field_simp [hM.ne', hmc.ne', hMm] <;> ring
    obtain ⟨j, hj | hj⟩ := first_forward (R n) finished.1 (Rsum n) first_eq
    · have E := Rmin n
      rw [hj, minimum_profile j 0 1 (by norm_num), end_eq] at E
      have HM : (1 : ℝ) / M ≠ 0 := by positivity
      exact (HM E.symm).elim
    · right
      refine ⟨n, j, funext fun i => ?_⟩
      have E := congrFun hj i
      change c + M ^ n * (P i - c) = (1 + if i = j then (1 : ℝ) else 0) / M at E
      have solved : P i = c + (((1 + if i = j then (1 : ℝ) else 0) / M) - c) / M ^ n := by
        have eqsub : P i - c = (((1 + if i = j then (1 : ℝ) else 0) / M) - c) / M ^ n := by
          apply (eq_div_iff (pow_ne_zero n hM.ne')).mpr
          linarith only [E]
        linarith only [eqsub]
      rw [solved]
      dsimp only [S, c]
      by_cases hi : i = j <;> simp only [hi, ↓reduceIte]
      all_goals rw [hmcast, pow_succ]; field_simp [hM.ne', hmc.ne', hMm] <;> ring
  have Szero (j : Fin m) : S 0 j = (fun i => (1 + if i = j then (1 : ℝ) else 0) / M) := by
    ext i
    dsimp [S, c]
    by_cases hi : i = j <;> simp only [hi, ↓reduceIte, pow_one]
    all_goals rw [hmcast]; field_simp [hM.ne', hmc.ne', hMm] <;> ring
  have trzero : tr 0 = 1 / M := by dsimp [tr, c]; rw [hmcast]; field_simp [hM.ne', hmc.ne', hMm] <;> ring
  have Snext (r : ℕ) (j : Fin m) : S (r + 1) j = (fun i => (1 + S r j i) / M) := by
    ext i
    dsimp only [S, c]
    by_cases hi : i = j <;> simp only [hi, ↓reduceIte]
    all_goals rw [hmcast, pow_succ]; field_simp [hM.ne', hmc.ne', hMm] <;> ring
  have trnext (r : ℕ) : tr (r + 1) = (1 + tr r) / M := by
    dsimp only [tr, c]
    rw [hmcast, pow_succ]
    field_simp [hM.ne', hmc.ne', hMm] <;> ring
  have Smin (r : ℕ) (j : Fin m) : Finset.univ.inf' nonempty (S r j) = tr r := by
    apply minimum_profile
    change c - 1 / ((m : ℝ) * M ^ (r + 1)) ≤ c + (M - 2) / ((m : ℝ) * M ^ (r + 1))
    exact (sub_le_self c (by positivity)).trans
      (le_add_of_nonneg_right (div_nonneg (by linarith only [hM4]) (by positivity)))
  have Sabove (r : ℕ) (j : Fin m) (i : Fin m) : 1 / M < S (r + 1) j i := by
    have Hpow : 1 < M ^ (r + 1) := one_lt_pow₀ hM1 (by omega)
    have identity : tr (r + 1) - 1 / M =
        (M ^ (r + 1) - 1) / ((m : ℝ) * M ^ (r + 2)) := by
      dsimp [tr, c]
      rw [hmcast, show r + 1 + 1 = r + 2 by omega, pow_succ]
      field_simp [hM.ne', hmc.ne', hMm] <;> ring
    have positive : 0 < tr (r + 1) - 1 / M := by
      rw [identity]
      exact div_pos (sub_pos.mpr Hpow) (by positivity)
    have E := Finset.inf'_le (S (r + 1) j) (Finset.mem_univ i)
    rw [Smin] at E
    exact (sub_pos.mp positive).trans_le E
  have Sdata (r : ℕ) (j : Fin m) : (∑ i, S r j i = 1) ∧ cost (S r j) = b * tr r - 2 := by
    induction r with
    | zero =>
      rw [Szero, trzero]
      constructor
      · simp only [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        rw [hmcast]
        field_simp [hM.ne', hmc.ne', hMm] <;> ring
      · rw [biased_cost h hh j]
        dsimp only [M, b]
        field_simp [hM.ne', hmc.ne', hMm] <;> ring
    | succ r ih =>
      have sumS : ∑ i, S (r + 1) j i = 1 := by
        rw [Snext]
        simp only [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, ih.1, hmcast]
        field_simp [hM.ne', hmc.ne', hMm] <;> ring
      have H := (scaling h hh (S (r + 1) j) sumS (Sabove r j)).2.2
      have after : (fun i => M * S (r + 1) j i - 1) = S r j := by
        rw [Snext]
        ext i
        field_simp [hM.ne', hmc.ne', hMm] <;> ring
      change cost (S (r + 1) j) = (h : ℝ) + cost (fun i => M * S (r + 1) j i - 1) / M at H
      rw [after, ih.2] at H
      refine ⟨sumS, ?_⟩
      rw [H, trnext]
      dsimp only [b]
      field_simp [hM.ne', hmc.ne', hMm] <;> ring
  have uniform_cost : cost (fun _i : Fin m => c) = b * c - 2 := by
    have hlo : ∀ _i : Fin m, 1 / M < c := by
      intro i
      dsimp [c]
      apply (one_div_lt_one_div hM hmc).mpr
      rw [hmcast]
      linarith
    have H := (scaling h hh (fun _i : Fin m => c) csum hlo).2.2
    have after : (fun _i : Fin m => M * c - 1) = (fun _i : Fin m => c) := by
      ext i
      exact fixed
    change cost (fun _i : Fin m => c) = (h : ℝ) + cost (fun _i : Fin m => M * c - 1) / M at H
    rw [after] at H
    have E := (eq_div_iff hM.ne').mp (show cost (fun _i : Fin m => c) - (h : ℝ) =
      cost (fun _i : Fin m => c) / M by linarith only [H])
    have product : (M - 1) * (b * c - 2) = (h : ℝ) * M := by
      dsimp only [b, c]
      rw [hmcast]
      field_simp [hM.ne', hmc.ne', hMm] <;> ring
    have EQ : (M - 1) * (cost (fun _i : Fin m => c) - (b * c - 2)) = 0 := by
      nlinarith only [E, product]
    exact sub_eq_zero.mp ((mul_eq_zero.mp EQ).resolve_left (by linarith only [hM4]))
  have second_reverse (P : Fin m → ℝ) (law : P = (fun _i => c) ∨ ∃ r j, P = S r j) :
      cost P = b * Finset.univ.inf' nonempty P - 2 := by
    obtain hU | ⟨r, j, hR⟩ := law
    · rw [hU, cmin, uniform_cost]
    · rw [hR, Smin r j, (Sdata r j).2]
  exact ⟨⟨first_forward p hp hs, first_reverse p⟩,
    ⟨second_forward p hp hs, second_reverse p⟩⟩

end D5.S3.Arith.FibonacciAtomic.MersenneDyadicEqualityLaws
