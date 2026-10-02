/- GID: D5/S3/Arith/FibonacciAtomic/SourceDensityCrossing
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/SourceDensityCrossing
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Real finite-product extension of adjacent Fibonacci source densities. -/

import D5.S3.Arith.FibonacciAtomic.SourceDensityMonotonicity
import Mathlib.Data.Nat.Factorial.BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Arith.FibonacciAtomic.SourceDensityCrossing

open scoped BigOperators
open Filter Set SourceDensityMonotonicity

/-- Density of the iterated substitution image in its actual composition fiber. -/
noncomputable def sourceDensity (k t i : ℕ) : ℝ :=
  (GenealogicalFiberTransport.fiberCount (t - i, i) : ℝ) /
    (GenealogicalFiberTransport.fiberCount
      (GraftAffineClosure.step^[3 * k] (t - i, i)) : ℝ)

/-- The six clauses of the real crossing and integer source-density bridge. -/
def Conclusion (k j : ℕ) : Prop :=
  0 < c k ∧
  StrictMonoOn (q k j) (Ici ((j : ℝ) + 1)) ∧
  Tendsto (fun t : ℝ => q k j t / t) atTop (nhds (c k / (j + 1))) ∧
  (∃! τ : ℝ, τ ∈ Ici ((j : ℝ) + 1) ∧ q k j τ = 1) ∧
  (∃ τ : ℝ, τ ∈ Ici ((j : ℝ) + 1) ∧ q k j τ = 1 ∧
    2 * j + 1 < τ ∧ τ < j + (j + 1) / c k ∧
    ∀ t : ℕ, j + 1 ≤ t →
      (q k j t < 1 ↔ (t : ℝ) < τ) ∧
      (q k j t = 1 ↔ (t : ℝ) = τ) ∧
      (1 < q k j t ↔ τ < (t : ℝ)) ∧
      (sourceDensity k t (j + 1) / sourceDensity k t j < 1 ↔ (t : ℝ) < τ) ∧
      (sourceDensity k t (j + 1) / sourceDensity k t j = 1 ↔ (t : ℝ) = τ) ∧
      (1 < sourceDensity k t (j + 1) / sourceDensity k t j ↔ τ < (t : ℝ))) ∧
  (∀ t : ℕ, j + 1 ≤ t →
    q k j t = sourceDensity k t (j + 1) / sourceDensity k t j)

/-- Strict increase, asymptotic slope, and the unique bounded crossing of the real ratio. -/
theorem result (k : ℕ) (hk : 1 ≤ k) (j : ℕ) :
    0 < c k ∧
    (∀ t : ℝ, (j : ℝ) + 1 ≤ t →
      0 < q k j t ∧
      HasDerivAt (fun z : ℝ => Real.log (q k j z)) (g k j t) t ∧
      lowerEnvelope k j t ≤ g k j t) ∧
    StrictMonoOn (q k j) (Ici ((j : ℝ) + 1)) ∧
    Tendsto (fun t : ℝ => q k j t / t) atTop (nhds (c k / (j + 1))) ∧
    (∃! τ : ℝ, τ ∈ Ici ((j : ℝ) + 1) ∧ q k j τ = 1) ∧
    (∃ τ : ℝ, τ ∈ Ici ((j : ℝ) + 1) ∧ q k j τ = 1 ∧
      2 * j + 1 < τ ∧ τ < j + (j + 1) / c k ∧
      ∀ t : ℕ, j + 1 ≤ t →
        (q k j t < 1 ↔ (t : ℝ) < τ) ∧
        (q k j t = 1 ↔ (t : ℝ) = τ) ∧
        (1 < q k j t ↔ τ < (t : ℝ)) ∧
        (sourceDensity k t (j + 1) / sourceDensity k t j < 1 ↔ (t : ℝ) < τ) ∧
        (sourceDensity k t (j + 1) / sourceDensity k t j = 1 ↔ (t : ℝ) = τ) ∧
        (1 < sourceDensity k t (j + 1) / sourceDensity k t j ↔ τ < (t : ℝ))) ∧
    (∀ t : ℕ, j + 1 ≤ t →
      q k j t = sourceDensity k t (j + 1) / sourceDensity k t j) := by
  have real := SourceDensityMonotonicity.result k hk j
  have hδeq : D k = E k + A k := by
    dsimp [D, E, A]
    rw [show 3 * k = (3 * k - 2) + 2 by omega, Nat.fib_add_two]
    congr 2 <;> omega
  have hℓeq : L k = A k + D k := by
    dsimp [L, A, D]
    rw [show 3 * k + 1 = (3 * k - 1) + 2 by omega, Nat.fib_add_two]
    congr 2 <;> omega
  have iterate_coords (d x y : ℕ) :
      GraftAffineClosure.step^[d + 1] (x, y) =
        (Nat.fib d * x + Nat.fib (d + 1) * y,
          Nat.fib (d + 1) * x + Nat.fib (d + 2) * y) := by
    induction d with
    | zero => simp [GraftAffineClosure.step]
    | succ d ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [GraftAffineClosure.step, Nat.fib_add_two, Nat.succ_eq_add_one]
      congr 1 <;> ring
  have grid_coords (t i : ℕ) (hi : i ≤ t) :
      GraftAffineClosure.step^[3 * k] (t - i, i) =
        (A k * t + E k * i, D k * t + A k * i) := by
    have hh := iterate_coords (3 * k - 1) (t - i) i
    have h1 : 3 * k - 1 + 1 = 3 * k := by omega
    have h2 : 3 * k - 1 + 2 = 3 * k + 1 := by omega
    rw [h1, h2] at hh
    rw [hh]
    change (A k * (t - i) + D k * i, D k * (t - i) + L k * i) = _
    ext <;> simp only [hδeq, hℓeq]
    · calc
        _ = A k * ((t - i) + i) + E k * i := by ring
        _ = _ := by rw [Nat.sub_add_cancel hi]
    · calc
        _ = (E k + A k) * ((t - i) + i) + A k * i := by ring
        _ = _ := by rw [Nat.sub_add_cancel hi]
  have factorial_pos (m : ℕ) : (0 : ℝ) < m.factorial := by
    exact_mod_cast Nat.factorial_pos m
  have count_formula (x y : ℕ) (hxy : 1 ≤ x + y) :
      (GenealogicalFiberTransport.fiberCount (x, y) : ℝ) =
        ((2 * (x + y - 1)).factorial : ℝ) /
          (((x + y - 1).factorial : ℝ) * x.factorial * y.factorial) := by
    let m := x + y - 1
    have hm : m + 1 = x + y := by dsimp [m]; omega
    have hc : (x + y).choose x * x.factorial * y.factorial = (x + y).factorial := by
      simpa only [Nat.add_sub_cancel_left] using
        (Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right x y))
    have hs : (x + y) * catalan m = Nat.centralBinom m := by
      rw [← hm]; exact succ_mul_catalan_eq_centralBinom m
    have hb : Nat.centralBinom m * m.factorial * m.factorial = (2 * m).factorial := by
      simpa only [Nat.centralBinom, two_mul] using
        Nat.add_choose_mul_factorial_mul_factorial m m
    have hn : GenealogicalFiberTransport.fiberCount (x, y) * m.factorial *
        x.factorial * y.factorial = (2 * m).factorial := by
      calc
        _ = catalan m * m.factorial * ((x + y).choose x * x.factorial * y.factorial) := by
          dsimp [GenealogicalFiberTransport.fiberCount, m]; ring
        _ = catalan m * m.factorial * (x + y).factorial := by rw [hc]
        _ = ((x + y) * catalan m) * m.factorial * m.factorial := by
          rw [← hm, Nat.factorial_succ]; ring
        _ = _ := by rw [hs, hb]
    apply (eq_div_iff (by positivity :
      ((m.factorial : ℝ) * x.factorial * y.factorial) ≠ 0)).mpr
    exact_mod_cast (by simpa only [m, mul_assoc] using hn)
  have rising_cast (x m : ℕ) : (x.ascFactorial m : ℝ) = rising x m := by
    simp only [Nat.ascFactorial_eq_prod_range, Nat.cast_prod, Nat.cast_add, rising]
  have factorial_shift (x m : ℕ) :
      ((x + m).factorial : ℝ) = (x.factorial : ℝ) * rising (x + 1) m := by
    simpa only [Nat.cast_mul, rising_cast, Nat.cast_add, Nat.cast_one] using
      (congrArg (fun u : ℕ => (u : ℝ)) (Nat.factorial_mul_ascFactorial x m)).symm
  have rising_succ (x : ℝ) (m : ℕ) :
      rising x (m + 1) = rising x m * (x + m) := by
    simp only [rising, Finset.prod_range_succ]
  have duplication (x : ℝ) (m : ℕ) :
      rising (2 * x) (2 * m) = 4 ^ m * rising x m * rising (x + 1 / 2) m := by
    induction m with
    | zero => simp [rising]
    | succ m ih =>
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
        rising_succ, rising_succ, ih, rising_succ, rising_succ, pow_succ]
      push_cast
      ring
  have rising_pos (x : ℝ) (hx : 0 < x) (m : ℕ) : 0 < rising x m :=
    Finset.prod_pos (fun i _ => by have := Nat.cast_nonneg (α := ℝ) i; positivity)
  have count_shift (x y e α : ℕ) (hxy : 1 ≤ x + y) :
      (GenealogicalFiberTransport.fiberCount (x, y) : ℝ) /
        (GenealogicalFiberTransport.fiberCount (x + e, y + α) : ℝ) =
      rising (x + y : ℕ) (e + α) * rising (x + 1) e * rising (y + 1) α /
        rising (2 * (x + y : ℕ) - 1 : ℝ) (2 * (e + α)) := by
    rw [count_formula x y hxy, count_formula (x + e) (y + α) (by omega)]
    have hs : x + e + (y + α) - 1 = (x + y - 1) + (e + α) := by omega
    have hd : 2 * (x + e + (y + α) - 1) = 2 * (x + y - 1) + 2 * (e + α) := by omega
    rw [hd, hs, factorial_shift (2 * (x + y - 1)) (2 * (e + α)),
      factorial_shift (x + y - 1) (e + α), factorial_shift x e, factorial_shift y α]
    have hn : ((x + y - 1 : ℕ) : ℝ) + 1 = (x + y : ℕ) := by
      exact_mod_cast (show x + y - 1 + 1 = x + y by omega)
    have hn2 : ((2 * (x + y - 1) : ℕ) : ℝ) + 1 = 2 * (x + y : ℕ) - 1 := by
      push_cast at hn ⊢; linarith
    rw [hn, hn2]
    have hp := rising_pos _ (by positivity : (0 : ℝ) < x + 1) e
    have hq := rising_pos _ (by positivity : (0 : ℝ) < y + 1) α
    have hr := rising_pos _ (by exact_mod_cast (show 0 < x + y by omega) : (0 : ℝ) < (x + y : ℕ)) (e + α)
    have ht := rising_pos _ (by
      have hh : (1 : ℝ) ≤ (x + y : ℕ) := by exact_mod_cast hxy
      linarith : (0 : ℝ) < 2 * (x + y : ℕ) - 1) (2 * (e + α))
    field_simp [(factorial_pos (2 * (x + y - 1))).ne',
      (factorial_pos (x + y - 1)).ne', (factorial_pos x).ne',
      (factorial_pos y).ne', hp.ne', hq.ne', hr.ne', ht.ne']
    <;> ring
  have count_pos (x y : ℕ) (hxy : 1 ≤ x + y) :
      (0 : ℝ) < GenealogicalFiberTransport.fiberCount (x, y) := by
    rw [count_formula x y hxy]
    exact div_pos (factorial_pos _) (by positivity)
  have source_ratio (t : ℕ) (ht : j + 1 ≤ t) :
      (GenealogicalFiberTransport.fiberCount (t - (j + 1), j + 1) : ℝ) /
        (GenealogicalFiberTransport.fiberCount (t - j, j) : ℝ) =
        ((t : ℝ) - j) / (j + 1) := by
    have htotal0 : t - j + j = t := Nat.sub_add_cancel (by omega)
    have htotal1 : t - (j + 1) + (j + 1) = t := Nat.sub_add_cancel ht
    have hchoose : (t.choose (j + 1) : ℝ) * ((j : ℝ) + 1) =
        (t.choose j : ℝ) * ((t : ℝ) - j) := by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_sub (show j ≤ t by omega)] using
        congrArg (fun u : ℕ => (u : ℝ)) (Nat.choose_succ_right_eq t j)
    apply (div_eq_div_iff (count_pos _ _ (by omega)).ne' (by positivity)).mpr
    simp only [GenealogicalFiberTransport.fiberCount, htotal0, htotal1,
      Nat.choose_symm (show j ≤ t by omega), Nat.choose_symm ht, Nat.cast_mul]
    linear_combination (catalan (t - 1) : ℝ) * hchoose
  have bridge (t : ℕ) (ht : j + 1 ≤ t) :
      q k j t = sourceDensity k t (j + 1) / sourceDensity k t j := by
    let x := A k * t + E k * j
    let y := D k * t + A k * j
    have htotal : x + y = L k * t + D k * j := by
      dsimp [x, y]; rw [hℓeq, hδeq]; ring
    have hpos : 1 ≤ x + y := by
      have hL : 0 < L k := Nat.fib_pos.mpr (by omega)
      rw [htotal]
      have hprod := Nat.mul_pos hL (show 0 < t by omega)
      omega
    have hshift : (A k * t + E k * (j + 1), D k * t + A k * (j + 1)) =
        (x + E k, y + A k) := by dsimp [x, y]; ext <;> ring
    have htarget := count_shift x y (E k) (A k) hpos
    have hn : (x + y : ℝ) = n k j t := by
      rw [← Nat.cast_add, htotal]; simp [n]
    have ha : (x : ℝ) = a k j t := by dsimp [x, a]; push_cast; ring
    have hb : (y : ℝ) = b k j t := by dsimp [y, b]; push_cast; ring
    have hnpos : 0 < n k j t - 1 / 2 := by
      have hh : (1 : ℝ) ≤ (x + y : ℕ) := by exact_mod_cast hpos
      rw [← hn]; push_cast at hh; linarith
    have hdup : rising (2 * n k j t - 1) (2 * D k) =
        4 ^ D k * rising (n k j t - 1 / 2) (D k) * rising (n k j t) (D k) := by
      simpa only [show 2 * (n k j t - 1 / 2) = 2 * n k j t - 1 by ring,
        show n k j t - 1 / 2 + 1 / 2 = n k j t by ring] using
        duplication (n k j t - 1 / 2) (D k)
    have hV : (GenealogicalFiberTransport.fiberCount (x, y) : ℝ) /
        (GenealogicalFiberTransport.fiberCount (x + E k, y + A k) : ℝ) = H k j t := by
      rw [← hδeq, Nat.cast_add, hn, ha, hb, hdup] at htarget
      rw [htarget, H]
      have hnr := rising_pos _ (by linarith : 0 < n k j t) (D k)
      have hhalf := rising_pos _ hnpos (D k)
      field_simp [hnr.ne', hhalf.ne']
      <;> ring
    dsimp [sourceDensity]
    rw [grid_coords t (j + 1) ht, grid_coords t j (by omega), hshift]
    change q k j t =
      ((GenealogicalFiberTransport.fiberCount (t - (j + 1), j + 1) : ℝ) /
        (GenealogicalFiberTransport.fiberCount (x + E k, y + A k) : ℝ)) /
      ((GenealogicalFiberTransport.fiberCount (t - j, j) : ℝ) /
        (GenealogicalFiberTransport.fiberCount (x, y) : ℝ))
    rw [div_div_div_comm, source_ratio t ht, div_div_eq_mul_div,
      mul_div_assoc, hV, q]
    ring
  rcases real with ⟨hc, hd, hm, hl, hu, τ, hτ, hr, hlo, hhi, hcmp⟩
  refine ⟨hc, hd, hm, hl, hu, ⟨τ, hτ, hr, hlo, hhi, ?_⟩, bridge⟩
  intro t ht
  obtain ⟨hlt, heq, hgt⟩ := hcmp t ht
  exact ⟨hlt, heq, hgt, by rwa [← bridge t ht], by rwa [← bridge t ht],
    by rwa [← bridge t ht]⟩

#print axioms result

end D5.S3.Arith.FibonacciAtomic.SourceDensityCrossing
