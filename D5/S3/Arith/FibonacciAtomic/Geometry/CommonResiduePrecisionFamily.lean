/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/CommonResiduePrecisionFamily
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/CommonResiduePrecisionFamily
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A common integer residue class preserves nonunit denominator precision. -/

import D5.S3.Arith.FibonacciAtomic.SourceDensityCrossing
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.NumberTheory.Padics.PadicVal.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Arith.FibonacciAtomic.Geometry.CommonResiduePrecisionFamily

open scoped BigOperators
open SourceDensityMonotonicity

/-- Integer numerator of the adjacent source-density ratio, with minority count `m = j+1`. -/
def numerator (k : ℕ) (t m : ℤ) : ℤ :=
  (t - m + 1) * (∏ r ∈ Finset.range (E k), ((A k : ℤ) * t + E k * m - r)) *
    ∏ s ∈ Finset.range (A k), ((D k : ℤ) * t + A k * m - s)

/-- The actual, possibly nonunit, integer denominator. -/
def denominator (k : ℕ) (t m : ℤ) : ℤ :=
  2 ^ D k * m * ∏ h ∈ Finset.range (D k),
    (2 * (L k : ℤ) * t + 2 * D k * m - 2 * D k + 2 * h - 1)

/-- Quadratic numerator coefficient at the origin. -/
def G (k : ℕ) : ℕ := A k * D k * (E k - 1).factorial * (A k - 1).factorial

/-- Linear denominator coefficient at the origin. -/
def K (k : ℕ) : ℕ := 2 ^ D k * ∏ h ∈ Finset.range (D k), (2 * h + 3)

private def reducedNumerator (k : ℕ) (z : ℤ) : ℤ :=
  (K k * z - G k * K k * z ^ 2 + 1) *
    ((A k : ℤ) * K k + E k * G k * K k * z) *
    ((D k : ℤ) * K k + A k * G k * K k * z) *
    (∏ r ∈ Finset.range (E k - 1),
      ((A k : ℤ) * K k * z + E k * G k * K k * z ^ 2 - (r + 1))) *
    ∏ s ∈ Finset.range (A k - 1),
      ((D k : ℤ) * K k * z + A k * G k * K k * z ^ 2 - (s + 1))

private def reducedDenominator (k : ℕ) (z : ℤ) : ℤ :=
  2 ^ D k * (G k : ℤ) * K k * ∏ h ∈ Finset.range (D k),
    (2 * (L k : ℤ) * K k * z + 2 * D k * G k * K k * z ^ 2 -
      2 * D k + 2 * h - 1)

private theorem lengths (k : ℕ) (hk : 1 ≤ k) :
    0 < E k ∧ 0 < A k ∧ 0 < D k ∧ 0 < L k ∧
    D k = E k + A k ∧ Even (D k) := by
  have he : 0 < E k := Nat.fib_pos.mpr (by omega)
  have ha : 0 < A k := Nat.fib_pos.mpr (by omega)
  have hd : 0 < D k := Nat.fib_pos.mpr (by omega)
  have hl : 0 < L k := Nat.fib_pos.mpr (by omega)
  have hsum : D k = E k + A k := by
    change Nat.fib (3 * k) = Nat.fib (3 * k - 2) + Nat.fib (3 * k - 1)
    calc
      Nat.fib (3 * k) = Nat.fib ((3 * k - 2) + 2) := congrArg Nat.fib (by omega)
      _ = Nat.fib (3 * k - 2) + Nat.fib ((3 * k - 2) + 1) := Nat.fib_add_two
      _ = _ := congrArg (Nat.fib (3 * k - 2) + ·) (congrArg Nat.fib (by omega))
  have hdiv : 2 ∣ D k := by
    change Nat.fib 3 ∣ Nat.fib (3 * k)
    exact Nat.fib_dvd 3 (3 * k) (dvd_mul_right 3 k)
  exact ⟨he, ha, hd, hl, hsum, even_iff_two_dvd.mpr hdiv⟩

private theorem seed_factorization (k : ℕ) (hk : 1 ≤ k) (z : ℤ) :
    numerator k (K k * z) (G k * K k * z ^ 2) = z ^ 2 * reducedNumerator k z ∧
    denominator k (K k * z) (G k * K k * z ^ 2) = z ^ 2 * reducedDenominator k z := by
  obtain ⟨he, ha, _, _, _, _⟩ := lengths k hk
  constructor
  · unfold numerator reducedNumerator
    conv_lhs =>
      arg 1; arg 2; arg 1; rw [show E k = (E k - 1) + 1 by omega]
    rw [Finset.prod_range_succ']
    conv_lhs =>
      arg 2; arg 1; rw [show A k = (A k - 1) + 1 by omega]
    rw [Finset.prod_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero]
    ring
  · unfold denominator reducedDenominator
    simp only [mul_assoc]
    ring

private theorem reduced_at_zero (k : ℕ) (hk : 1 ≤ k) :
    reducedNumerator k 0 = (G k : ℤ) * K k ^ 2 ∧
    reducedDenominator k 0 = (G k : ℤ) * K k ^ 2 := by
  obtain ⟨he, ha, _, _, hsum, hd⟩ := lengths k hk
  have hsign : Even (E k - 1 + (A k - 1)) := by
    rcases hd with ⟨r, hr⟩
    exact ⟨r - 1, by omega⟩
  have factorial_block (n : ℕ) :
      (∏ i ∈ Finset.range n, -((i : ℤ) + 1)) = (-1 : ℤ) ^ n * n.factorial := by
    rw [Finset.prod_neg, Finset.card_range]
    congr 1
    exact_mod_cast Finset.prod_range_add_one_eq_factorial n
  constructor
  · simp only [reducedNumerator, mul_zero, zero_pow (by decide : 2 ≠ 0),
      sub_zero, zero_sub, add_zero, zero_add]
    rw [one_mul, factorial_block, factorial_block]
    have hs : (-1 : ℤ) ^ (E k - 1) * (-1 : ℤ) ^ (A k - 1) = 1 := by
      rw [← pow_add, hsign.neg_one_pow]
    dsimp [G]
    push_cast
    calc
      _ = (A k : ℤ) * D k * (E k - 1).factorial * (A k - 1).factorial * K k ^ 2 *
          ((-1 : ℤ) ^ (E k - 1) * (-1 : ℤ) ^ (A k - 1)) := by ring
      _ = _ := by rw [hs, mul_one]
  · have block : (∏ h ∈ Finset.range (D k), (-2 * (D k : ℤ) + 2 * h - 1)) =
        ∏ h ∈ Finset.range (D k), (2 * (h : ℤ) + 3) := by
      calc
        _ = ∏ h ∈ Finset.range (D k), -(2 * ((D k - 1 - h : ℕ) : ℤ) + 3) := by
          apply Finset.prod_congr rfl
          intro h hh
          have hh' := Finset.mem_range.mp hh
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
          push_cast
          ring
        _ = ∏ h ∈ Finset.range (D k), -(2 * (h : ℤ) + 3) :=
          Finset.prod_range_reflect (fun h : ℕ => -(2 * (h : ℤ) + 3)) (D k)
        _ = _ := by rw [Finset.prod_neg, Finset.card_range, hd.neg_one_pow, one_mul]
    simp only [reducedDenominator, mul_zero, zero_pow (by decide : 2 ≠ 0),
      zero_add, add_zero, zero_sub]
    simp only [neg_mul] at block
    rw [block]
    have hK : (K k : ℤ) = 2 ^ D k * ∏ h ∈ Finset.range (D k), (2 * (h : ℤ) + 3) := by
      simp [K]
    rw [hK]
    ring

attribute [local gcongr] Int.ModEq.add Int.ModEq.sub Int.ModEq.mul

private theorem reduced_congruence (k : ℕ) (z : ℤ) :
    reducedNumerator k z ≡ reducedNumerator k 0 [ZMOD z] ∧
    reducedDenominator k z ≡ reducedDenominator k 0 [ZMOD z] := by
  have hz : z ≡ 0 [ZMOD z] := Int.modulus_modEq_zero
  constructor <;> dsimp only [reducedNumerator, reducedDenominator] <;> gcongr

private theorem constants_positive (k : ℕ) (hk : 1 ≤ k) : 0 < G k ∧ 0 < K k := by
  obtain ⟨_, ha, hd, _, _, _⟩ := lengths k hk
  constructor
  · exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos ha hd) (Nat.factorial_pos _))
      (Nat.factorial_pos _)
  · exact Nat.mul_pos (by positivity) (Finset.prod_pos fun i _ => by omega)

private theorem denominator_positive (k : ℕ) (hk : 1 ≤ k) (t m : ℤ)
    (ht : 1 ≤ t) (hm : 1 ≤ m) : 0 < denominator k t m := by
  have hl : (1 : ℤ) ≤ L k := by exact_mod_cast (lengths k hk).2.2.2.1
  have hd : (0 : ℤ) ≤ D k := Nat.cast_nonneg _
  unfold denominator
  apply mul_pos (mul_pos (by positivity) (by omega))
  apply Finset.prod_pos
  intro h _
  have hh : (0 : ℤ) ≤ h := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left ht (by omega : 0 ≤ (L k : ℤ)),
    mul_nonneg hd (show 0 ≤ m - 1 by omega)]

private theorem unit_factor_valuation (p B : ℕ) [Fact p.Prime] (hpB : p ∣ B)
    (c w : ℤ) (hc : c ≠ 0) (hunit : 1 + (B : ℤ) * w ≠ 0) :
    padicValInt p (c * (1 + (B : ℤ) * w)) = padicValInt p c := by
  have hnot : ¬ (p : ℤ) ∣ 1 + (B : ℤ) * w := by
    intro h
    have hBw : (p : ℤ) ∣ (B : ℤ) * w := dvd_mul_of_dvd_left (by exact_mod_cast hpB) w
    have h1 : (p : ℤ) ∣ 1 := by simpa using dvd_sub h hBw
    exact (Fact.out : p.Prime).not_dvd_one (by exact_mod_cast h1)
  rw [padicValInt.mul hc hunit, padicValInt.eq_zero_of_not_dvd hnot, add_zero]

private theorem seed_certificate (k B : ℕ) (hk : 1 ≤ k) (hB : 2 ≤ B) :
    ∃ t₀ m₀ : ℕ, 1 ≤ t₀ ∧ 1 ≤ m₀ ∧ 0 < denominator k t₀ m₀ ∧
      ∀ p : ℕ, p.Prime → p ∣ B →
        (p : ℤ) ^ (padicValInt p (denominator k t₀ m₀) + padicValNat p B) ∣
          numerator k t₀ m₀ - denominator k t₀ m₀ := by
  let v : ℕ := G k * K k ^ 2
  let z : ℕ := v * B
  let t₀ : ℕ := K k * z
  let m₀ : ℕ := G k * K k * z ^ 2
  have hv : 0 < v := Nat.mul_pos (constants_positive k hk).1
    (pow_pos (constants_positive k hk).2 _)
  have hz : 0 < z := Nat.mul_pos hv (by omega)
  have ht : 1 ≤ t₀ := Nat.mul_pos (constants_positive k hk).2 hz
  have hm : 1 ≤ m₀ := Nat.mul_pos
    (Nat.mul_pos (constants_positive k hk).1 (constants_positive k hk).2) (pow_pos hz _)
  have hb := denominator_positive k hk t₀ m₀ (by exact_mod_cast ht) (by exact_mod_cast hm)
  have hn0 : reducedNumerator k 0 = (v : ℤ) := by
    simpa only [v, Nat.cast_mul, Nat.cast_pow] using (reduced_at_zero k hk).1
  have hd0 : reducedDenominator k 0 = (v : ℤ) := by
    simpa only [v, Nat.cast_mul, Nat.cast_pow] using (reduced_at_zero k hk).2
  obtain ⟨u, hu⟩ := Int.modEq_iff_add_fac.mp (reduced_congruence k (z : ℤ)).1.symm
  obtain ⟨w, hw⟩ := Int.modEq_iff_add_fac.mp (reduced_congruence k (z : ℤ)).2.symm
  rw [hn0] at hu
  rw [hd0] at hw
  have hfac := seed_factorization k hk (z : ℤ)
  have hden : denominator k t₀ m₀ = (z : ℤ) ^ 2 * v * (1 + (B : ℤ) * w) := by
    simpa only [t₀, m₀, Nat.cast_mul, Nat.cast_pow] using
      (hfac.2.trans (by rw [hw]; dsimp [z]; push_cast; ring))
  have hnum : numerator k t₀ m₀ - denominator k t₀ m₀ =
      (B : ℤ) * ((z : ℤ) ^ 2 * v) * (u - w) := by
    change numerator k (K k * z : ℕ) (G k * K k * z ^ 2 : ℕ) -
      denominator k (K k * z : ℕ) (G k * K k * z ^ 2 : ℕ) = _
    push_cast
    rw [hfac.1, hfac.2, hu, hw]
    dsimp [z]
    push_cast
    ring
  refine ⟨t₀, m₀, ht, hm, hb, ?_⟩
  intro p hp hpB
  letI : Fact p.Prime := ⟨hp⟩
  have hc : (z : ℤ) ^ 2 * v ≠ 0 := by positivity
  have hw0 : 1 + (B : ℤ) * w ≠ 0 := by
    intro h
    rw [h, mul_zero] at hden
    omega
  have hvp : padicValInt p (denominator k t₀ m₀) =
      padicValInt p ((z : ℤ) ^ 2 * v) := by
    rw [hden]
    exact unit_factor_valuation p B hpB _ w hc hw0
  rw [hvp, hnum, pow_add]
  apply dvd_mul_of_dvd_left
  rw [mul_comm (B : ℤ)]
  exact mul_dvd_mul (padicValInt_dvd _) (by
    exact_mod_cast (pow_padicValNat_dvd (p := p) (n := B)))

private theorem polynomial_congruence (k : ℕ) {Λ t m t₀ m₀ : ℤ}
    (ht : t ≡ t₀ [ZMOD Λ]) (hm : m ≡ m₀ [ZMOD Λ]) :
    numerator k t m ≡ numerator k t₀ m₀ [ZMOD Λ] ∧
    denominator k t m ≡ denominator k t₀ m₀ [ZMOD Λ] := by
  constructor
  · exact (((ht.sub hm).add_right 1).mul
      (Int.ModEq.prod fun r _ => ((ht.mul_left _).add (hm.mul_left _)).sub_right _)).mul
      (Int.ModEq.prod fun r _ => ((ht.mul_left _).add (hm.mul_left _)).sub_right _)
  · exact (hm.mul_left _).mul (Int.ModEq.prod fun r _ =>
      (((ht.mul_left _).add (hm.mul_left _)).sub_right _).add_right _ |>.sub_right _)

private theorem residue_precision (k B p : ℕ) [Fact p.Prime] (hpB : p ∣ B)
    (t₀ m₀ t m : ℤ) (hb₀ : 0 < denominator k t₀ m₀)
    (hb : 0 < denominator k t m)
    (hseed : (p : ℤ) ^ (padicValInt p (denominator k t₀ m₀) + padicValNat p B) ∣
      numerator k t₀ m₀ - denominator k t₀ m₀)
    (ht : t ≡ t₀ [ZMOD (B : ℤ) * denominator k t₀ m₀])
    (hm : m ≡ m₀ [ZMOD (B : ℤ) * denominator k t₀ m₀]) :
    padicValInt p (denominator k t m) = padicValInt p (denominator k t₀ m₀) ∧
    (p : ℤ) ^ (padicValInt p (denominator k t m) + padicValNat p B) ∣
      numerator k t m - denominator k t m := by
  obtain ⟨ha, hd⟩ := polynomial_congruence k ht hm
  obtain ⟨w, hw⟩ := Int.modEq_iff_add_fac.mp hd.symm
  have hd' : denominator k t m = denominator k t₀ m₀ * (1 + (B : ℤ) * w) := by
    rw [hw]; ring
  have hunit : 1 + (B : ℤ) * w ≠ 0 := by
    intro h; rw [h, mul_zero] at hd'; omega
  have hval : padicValInt p (denominator k t m) = padicValInt p (denominator k t₀ m₀) := by
    rw [hd']
    exact unit_factor_valuation p B hpB _ w hb₀.ne' hunit
  refine ⟨hval, ?_⟩
  rw [hval]
  have hΛ : (p : ℤ) ^ (padicValInt p (denominator k t₀ m₀) + padicValNat p B) ∣
      (B : ℤ) * denominator k t₀ m₀ := by
    rw [pow_add, mul_comm (B : ℤ)]
    exact mul_dvd_mul (padicValInt_dvd _) (by
      exact_mod_cast (pow_padicValNat_dvd (p := p) (n := B)))
  have hdiff := hΛ.trans (ha.sub hd).symm.dvd
  simpa only [sub_add_cancel] using dvd_add hdiff hseed

private theorem right_grid_point (t₀ Λ : ℕ) (hΛ : 0 < Λ) (τ : ℝ) (hτ : 0 ≤ τ) :
    ∃ t : ℕ, τ < (t : ℝ) ∧ (t : ℝ) ≤ τ + Λ ∧
      (t : ℤ) ≡ t₀ [ZMOD (Λ : ℤ)] := by
  let x : ℝ := (τ - t₀) / Λ
  let t : ℤ := t₀ + Λ * (⌊x⌋ + 1)
  have hΛr : (0 : ℝ) < Λ := by exact_mod_cast hΛ
  have hlow : τ < (t : ℝ) := by
    have h := (div_lt_iff₀ hΛr).mp (Int.lt_floor_add_one x)
    dsimp [x] at h
    dsimp [t]
    push_cast
    nlinarith
  have hupp : (t : ℝ) ≤ τ + Λ := by
    have h := (le_div_iff₀ hΛr).mp (Int.floor_le x)
    dsimp [x] at h
    dsimp [t]
    push_cast
    nlinarith
  have ht : 0 ≤ t := by exact_mod_cast hτ.trans hlow.le
  have hcast : (t.toNat : ℝ) = (t : ℝ) := by exact_mod_cast (Int.toNat_of_nonneg ht)
  refine ⟨t.toNat, ?_, ?_, ?_⟩
  · rwa [hcast]
  · rwa [hcast]
  · rw [Int.toNat_of_nonneg ht]
    exact Int.modEq_add_fac_self

/-- A single residue class has legal points immediately to the right of every moving root,
while preserving the exact denominator valuation at every prime of the chosen modulus. -/
private theorem common_residue_family (k B : ℕ) (hk : 1 ≤ k) (hB : 2 ≤ B) :
    ∃ t₀ m₀ Λ : ℕ, ∃ t : ℕ → ℕ, ∃ τ : ℕ → ℝ,
      1 ≤ t₀ ∧ 1 ≤ m₀ ∧ 0 < denominator k t₀ m₀ ∧
      (Λ : ℤ) = B * denominator k t₀ m₀ ∧ 0 < Λ ∧
      Function.Injective (fun N => (t N, m₀ + Λ * N - 1)) ∧
      ∀ N : ℕ, let m := m₀ + Λ * N
        m ≤ t N ∧ q k (m - 1) (τ N) = 1 ∧
        (2 * (m - 1) + 1 : ℕ) < τ N ∧
        τ N < (t N : ℝ) ∧ (t N : ℝ) ≤ τ N + Λ ∧
        (t N : ℤ) ≡ t₀ [ZMOD (Λ : ℤ)] ∧
        (m : ℤ) ≡ m₀ [ZMOD (Λ : ℤ)] ∧
        1 < q k (m - 1) (t N) ∧
        ∀ p : ℕ, p.Prime → p ∣ B →
          padicValInt p (denominator k (t N) m) = padicValInt p (denominator k t₀ m₀) ∧
          (p : ℤ) ^ (padicValInt p (denominator k (t N) m) + padicValNat p B) ∣
            numerator k (t N) m - denominator k (t N) m := by
  classical
  obtain ⟨t₀, m₀, ht₀, hm₀, hb₀, hseed⟩ := seed_certificate k B hk hB
  let b₀ := (denominator k t₀ m₀).toNat
  have hbcast : (b₀ : ℤ) = denominator k t₀ m₀ := Int.toNat_of_nonneg hb₀.le
  have hbpos : 0 < b₀ := by exact_mod_cast (hbcast.symm ▸ hb₀)
  let Λ := B * b₀
  have hΛ : 0 < Λ := Nat.mul_pos (by omega) hbpos
  have hΛcast : (Λ : ℤ) = B * denominator k t₀ m₀ := by
    simp only [Λ, Nat.cast_mul, hbcast]
  let m : ℕ → ℕ := fun N => m₀ + Λ * N
  have hm (N : ℕ) : 1 ≤ m N := by dsimp [m]; omega
  have roots (N : ℕ) := (SourceDensityCrossing.result k hk (m N - 1)).2.2.2.2.2.1
  choose τ hτmem hτroot hτlow hτupper hτsign using roots
  have hτpos (N : ℕ) : 0 ≤ τ N := by
    have h := hτmem N
    exact (by positivity : (0 : ℝ) ≤ (m N - 1 : ℕ) + 1).trans h
  choose t htlow htupper htcong using fun N => right_grid_point t₀ Λ hΛ (τ N) (hτpos N)
  have hlegal (N : ℕ) : m N ≤ t N := by
    have h := (hτmem N).trans (htlow N).le
    have hm' := hm N
    have hcast : ((m N - 1 : ℕ) : ℝ) + 1 = m N := by
      exact_mod_cast (Nat.sub_add_cancel hm')
    rw [hcast] at h
    exact_mod_cast h
  have hmcong (N : ℕ) : (m N : ℤ) ≡ m₀ [ZMOD (Λ : ℤ)] := by
    dsimp [m]
    push_cast
    exact Int.modEq_add_fac_self
  refine ⟨t₀, m₀, Λ, t, τ, ht₀, hm₀, hb₀, hΛcast, hΛ, ?_, ?_⟩
  · intro N M h
    have hj := congrArg Prod.snd h
    have heq : m₀ + Λ * N = m₀ + Λ * M := by
      have := hm N; have := hm M; dsimp [m] at *; omega
    exact Nat.eq_of_mul_eq_mul_left hΛ (Nat.add_left_cancel heq)
  · intro N
    change m N ≤ t N ∧ _
    refine ⟨hlegal N, hτroot N, ?_, htlow N, htupper N, htcong N, hmcong N, ?_, ?_⟩
    · exact_mod_cast hτlow N
    · exact ((hτsign N (t N) (by have := hlegal N; have := hm N; omega)).2.2.1).mpr (htlow N)
    · intro p hp hpB
      letI : Fact p.Prime := ⟨hp⟩
      exact residue_precision k B p hpB t₀ m₀ (t N) (m N) hb₀
        (denominator_positive k hk _ _ (by exact_mod_cast ((hm N).trans (hlegal N)))
          (by exact_mod_cast hm N))
        (hseed p hp hpB) (hΛcast ▸ htcong N) (hΛcast ▸ hmcong N)

/-- Rational adjacent ratio; its tree interpretation is restricted to `1 ≤ m ≤ t`. -/
def ratio (k t m : ℕ) : ℚ := (numerator k t m : ℚ) / denominator k t m

private theorem ratio_cast (k t m : ℕ) (hm : 1 ≤ m) :
    (ratio k t m : ℝ) = q k (m - 1) t := by
  have hmcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub hm, Nat.cast_one]
  have reverse_block (n : ℕ) (x : ℝ) :
      (∏ r ∈ Finset.range n, (x + n - r)) = rising (x + 1) n := by
    rw [← Finset.prod_range_reflect (fun r : ℕ => x + n - r) n]
    unfold rising
    apply Finset.prod_congr rfl
    intro r hr
    have h := Finset.mem_range.mp hr
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
    ring
  have hnum : (numerator k t m : ℝ) =
      ((t : ℝ) - (m - 1 : ℕ)) * rising (a k (m - 1) t + 1) (E k) *
        rising (b k (m - 1) t + 1) (A k) := by
    unfold numerator
    push_cast
    rw [hmcast]
    have hfirst : (∏ r ∈ Finset.range (E k),
        ((A k : ℝ) * t + E k * m - r)) = rising (a k (m - 1) t + 1) (E k) := by
      rw [← reverse_block]
      apply Finset.prod_congr rfl
      intro r _
      dsimp [a]
      rw [hmcast]
      ring
    have hsecond : (∏ r ∈ Finset.range (A k),
        ((D k : ℝ) * t + A k * m - r)) = rising (b k (m - 1) t + 1) (A k) := by
      rw [← reverse_block]
      apply Finset.prod_congr rfl
      intro r _
      dsimp [b]
      rw [hmcast]
      ring
    rw [hfirst, hsecond]
    ring
  have hden : (denominator k t m : ℝ) =
      (4 : ℝ) ^ D k * m * rising (n k (m - 1) t - 1 / 2) (D k) := by
    unfold denominator
    push_cast
    have hprod : (∏ h ∈ Finset.range (D k),
        (2 * (L k : ℝ) * t + 2 * D k * m - 2 * D k + 2 * h - 1)) =
        (2 : ℝ) ^ D k * rising (n k (m - 1) t - 1 / 2) (D k) := by
      calc
        _ = ∏ h ∈ Finset.range (D k), 2 * (n k (m - 1) t - 1 / 2 + h) := by
          apply Finset.prod_congr rfl
          intro h _
          dsimp [n]
          rw [hmcast]
          ring
        _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]; rfl
    rw [hprod]
    have hp : (2 : ℝ) ^ D k * 2 ^ D k = 4 ^ D k := by rw [← mul_pow]; norm_num
    calc
      _ = ((2 : ℝ) ^ D k * 2 ^ D k) * m * rising (n k (m - 1) t - 1 / 2) (D k) := by ring
      _ = _ := by rw [hp]
  simp only [ratio, Rat.cast_div, Rat.cast_intCast, hnum, hden, q, H]
  rw [hmcast]
  simp only [sub_add_cancel]
  ring

private theorem logarithmic_upper (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (x : ℝ) (hx : 2 * (m : ℝ) - 1 < x) : g k (m - 1) x ≤ (D k + 1 : ℝ) / m := by
  obtain ⟨he, ha, hd, hl, hsum, _⟩ := lengths k hk
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hj : (0 : ℝ) ≤ (m - 1 : ℕ) := Nat.cast_nonneg _
  have hmcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub hm, Nat.cast_one]
  have hxm : (m : ℝ) ≤ x := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hxpos : 0 < x := hmpos.trans_le hxm
  have hA : (0 : ℝ) < A k := by exact_mod_cast ha
  have hD : (0 : ℝ) < D k := by exact_mod_cast hd
  have hL : (0 : ℝ) < L k := by exact_mod_cast hl
  have first : 1 / (x - (m - 1 : ℕ)) ≤ 1 / (m : ℝ) := by
    rw [hmcast]
    apply one_div_le_one_div_of_le hmpos
    linarith
  have block (c e : ℝ) (hc : 0 < c) (he : 0 ≤ e) (r : ℕ) :
      c * (∑ i ∈ Finset.range r, 1 / (c * x + e * (m - 1 : ℕ) + 1 + i)) ≤
        (r : ℝ) / m := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ _i ∈ Finset.range r, 1 / (m : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [mul_one_div]
        apply (div_le_div_iff₀ (by positivity : 0 < c * x + e * (m - 1 : ℕ) + 1 + i) hmpos).mpr
        have := mul_le_mul_of_nonneg_left hxm hc.le
        have := mul_nonneg he hj
        have := (Nat.cast_nonneg i : (0 : ℝ) ≤ i)
        nlinarith
      _ = _ := by simp [div_eq_mul_inv]
  have hfirst := block (A k) (E k) hA (Nat.cast_nonneg _) (E k)
  have hsecond := block (D k) (A k) hD hA.le (A k)
  have hnegative : 0 ≤ (L k : ℝ) *
      ∑ i ∈ Finset.range (D k), 1 / (n k (m - 1) x - 1 / 2 + i) := by
    apply mul_nonneg hL.le
    apply Finset.sum_nonneg
    intro i _
    apply one_div_nonneg.mpr
    dsimp [n]
    have hL1 : (1 : ℝ) ≤ L k := by exact_mod_cast hl
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have := mul_le_mul_of_nonneg_left hxm hL.le
    have := mul_nonneg hD.le hj
    have := (Nat.cast_nonneg i : (0 : ℝ) ≤ i)
    nlinarith
  have hsumcast : (D k : ℝ) = E k + A k := by exact_mod_cast hsum
  dsimp [g, a, b]
  conv_rhs => rw [hsumcast, add_div, add_div]
  linarith

private theorem log_grid_bound (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (τ y : ℝ) (hroot : q k (m - 1) τ = 1)
    (hτ : 2 * (m : ℝ) - 1 < τ) (hy : τ ≤ y) :
    Real.log (q k (m - 1) y) ≤ ((D k + 1 : ℝ) / m) * (y - τ) := by
  have hmcast : ((m - 1 : ℕ) : ℝ) + 1 = m := by exact_mod_cast Nat.sub_add_cancel hm
  have hτm : (m : ℝ) ≤ τ := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hd (x : ℝ) (hx : τ ≤ x) :
      HasDerivAt (fun z : ℝ => Real.log (q k (m - 1) z)) (g k (m - 1) x) x :=
    ((SourceDensityCrossing.result k hk (m - 1)).2.1 x (by rw [hmcast]; linarith)).2.1
  have h := (convex_Icc τ y).image_sub_le_mul_sub_of_deriv_le
    (fun x hx => (hd x hx.1).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx).1).differentiableAt.differentiableWithinAt)
    (C := (D k + 1 : ℝ) / m)
    (fun x hx => by
      rw [(hd x (interior_subset hx).1).deriv]
      exact logarithmic_upper k m hk hm x (hτ.trans_le (interior_subset hx).1))
    τ ⟨le_rfl, hy⟩ y ⟨hy, le_rfl⟩ hy
  simpa only [hroot, Real.log_one, sub_zero] using h

/-- One injective legal integer family realizes strict real approach to one and every
prime precision prescribed by the same fixed modulus. -/
theorem result (k B : ℕ) (hk : 1 ≤ k) (hB : 2 ≤ B) :
    ∃ t j : ℕ → ℕ,
      Function.Injective (fun N => (t N, j N)) ∧
      (∀ N : ℕ, 1 ≤ t N ∧ j N < t N ∧ 1 < ratio k (t N) (j N + 1) ∧
        (ratio k (t N) (j N + 1) : ℝ) =
          SourceDensityCrossing.sourceDensity k (t N) (j N + 1) /
            SourceDensityCrossing.sourceDensity k (t N) (j N) ∧
        ∀ p : ℕ, p.Prime → p ∣ B →
          (padicValNat p B : ℤ) ≤ padicValRat p (ratio k (t N) (j N + 1) - 1)) ∧
      Filter.Tendsto (fun N => (ratio k (t N) (j N + 1) : ℝ)) Filter.atTop (nhds 1) := by
  obtain ⟨t₀, m₀, Λ, t, τ, ht₀, hm₀, hb₀, hΛcast, hΛ, hinj, hfamily⟩ :=
    common_residue_family k B hk hB
  let m : ℕ → ℕ := fun N => m₀ + Λ * N
  have hm (N : ℕ) : 1 ≤ m N := by dsimp [m]; omega
  have hsuccess (N : ℕ) := hfamily N
  change ∀ N, m N ≤ t N ∧ _ at hsuccess
  have hj (N : ℕ) : m N - 1 + 1 = m N := Nat.sub_add_cancel (hm N)
  have hq (N : ℕ) : 1 < (ratio k (t N) (m N) : ℝ) := by
    rw [ratio_cast k _ _ (hm N)]
    exact (hsuccess N).2.2.2.2.2.2.2.1
  refine ⟨t, (fun N => m N - 1), hinj, ?_, ?_⟩
  · intro N
    dsimp only
    rw [hj]
    refine ⟨(hm N).trans (hsuccess N).1, by have := (hsuccess N).1; have := hm N; omega,
      by exact_mod_cast hq N, ?_, ?_⟩
    · rw [ratio_cast k _ _ (hm N)]
      convert (SourceDensityCrossing.result k hk (m N - 1)).2.2.2.2.2.2 (t N)
        (by rw [hj]; exact (hsuccess N).1) using 1
      rw [hj]
    · intro p hp hpB
      letI : Fact p.Prime := ⟨hp⟩
      have hden := denominator_positive k hk (t N) (m N)
        (by exact_mod_cast ((hm N).trans (hsuccess N).1)) (by exact_mod_cast hm N)
      have hdenq : (denominator k (t N) (m N) : ℚ) ≠ 0 := by exact_mod_cast hden.ne'
      have hnum : numerator k (t N) (m N) - denominator k (t N) (m N) ≠ 0 := by
        intro hz
        have he : ratio k (t N) (m N) = 1 := by
          simp only [ratio, sub_eq_zero.mp hz, div_self hdenq]
        have := hq N
        simp only [he, Rat.cast_one, lt_self_iff_false] at this
      have hdiv := ((hsuccess N).2.2.2.2.2.2.2.2 p hp hpB).2
      have hval := ((padicValInt_dvd_iff _ _).mp hdiv).resolve_left hnum
      change padicValInt p (denominator k (t N) (m N)) + padicValNat p B ≤
        padicValInt p (numerator k (t N) (m N) - denominator k (t N) (m N)) at hval
      have hrat : ratio k (t N) (m N) - 1 =
          ((numerator k (t N) (m N) - denominator k (t N) (m N) : ℤ) : ℚ) /
            denominator k (t N) (m N) := by
        simp only [ratio, Int.cast_sub]
        field_simp
      rw [hrat, padicValRat.div (by exact_mod_cast hnum) hdenq,
        padicValRat.of_int, padicValRat.of_int]
      omega
  · have hlogbound (N : ℕ) :
        0 ≤ Real.log (ratio k (t N) (m N) : ℝ) ∧
        Real.log (ratio k (t N) (m N) : ℝ) ≤ ((D k + 1 : ℝ) * Λ) / m N := by
      constructor
      · exact Real.log_nonneg (hq N).le
      · rw [ratio_cast k _ _ (hm N)]
        have hr := hsuccess N
        have hτ : 2 * (m N : ℝ) - 1 < τ N := by
          have hh := hr.2.2.1
          have hcast : ((m N - 1 : ℕ) : ℝ) = (m N : ℝ) - 1 := by
            rw [Nat.cast_sub (hm N), Nat.cast_one]
          push_cast at hh
          rw [hcast] at hh
          linarith
        have hbound := log_grid_bound k (m N) hk (hm N) (τ N) (t N)
          hr.2.1 hτ hr.2.2.2.1.le
        have hdist : (t N : ℝ) - τ N ≤ Λ := by linarith [hr.2.2.2.2.1]
        calc
          _ ≤ ((D k + 1 : ℝ) / m N) * ((t N : ℝ) - τ N) := hbound
          _ ≤ ((D k + 1 : ℝ) / m N) * Λ := mul_le_mul_of_nonneg_left hdist (by positivity)
          _ = _ := by ring
    have hmTop : Filter.Tendsto m Filter.atTop Filter.atTop := by
      simpa only [m, Function.comp_def, id_eq, Nat.add_comm] using
        (Filter.tendsto_add_atTop_nat m₀).comp (Filter.tendsto_id.const_mul_atTop' hΛ)
    have hmReal : Filter.Tendsto (fun N => (m N : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.comp hmTop
    have hinv := tendsto_inv_atTop_zero.comp hmReal
    have hupper : Filter.Tendsto (fun N => ((D k + 1 : ℝ) * Λ) / m N)
        Filter.atTop (nhds 0) := by
      simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
        (Filter.Tendsto.const_mul ((D k + 1 : ℝ) * Λ) hinv)
    have hlog : Filter.Tendsto (fun N => Real.log (ratio k (t N) (m N) : ℝ))
        Filter.atTop (nhds 0) :=
      squeeze_zero (fun N => (hlogbound N).1) (fun N => (hlogbound N).2) hupper
    have hexp := Real.continuous_exp.continuousAt.tendsto.comp hlog
    have heq : (Real.exp ∘ fun N => Real.log (ratio k (t N) (m N) : ℝ)) =
        (fun N => (ratio k (t N) (m N) : ℝ)) :=
      funext fun N => Real.exp_log (lt_trans zero_lt_one (hq N))
    rw [heq, Real.exp_zero] at hexp
    simpa only [hj] using hexp


end D5.S3.Arith.FibonacciAtomic.Geometry.CommonResiduePrecisionFamily
