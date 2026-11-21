import D5.S1.Recurrence.Asymptotic.DominantRootForcing
import D5.S0.Tower.Tribonacci.Values
import Mathlib.NumberTheory.Real.GoldenRatio

set_option autoImplicit false

noncomputable section

namespace D5.S1.Recurrence.RoundedNormBoundedError

open Polynomial Asymptotics Filter

/-- Upper comparison: `b (n + m) ≤ K ∑ b (n + i)` with `K ∑ c^i ≤ c^m` gives `b n = O(c^n)`. -/
private theorem upper_compare {m : ℕ} {b : ℕ → ℝ} {K c : ℝ} (hK : 0 ≤ K) (hc : 0 < c)
    (hcK : K * ∑ i ∈ Finset.range m, c ^ i ≤ c ^ m) (N : ℕ)
    (h : ∀ n, N ≤ n → b (n + m) ≤ K * ∑ i ∈ Finset.range m, b (n + i)) :
    ∃ M, ∀ n, N ≤ n → b n ≤ M * c ^ n := by
  set M := ∑ i ∈ Finset.range m, |b (N + i)| / c ^ (N + i) with hMdef
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => by positivity
  refine ⟨M, fun n => ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n (N + m) with hlt | hge
    · obtain ⟨i, rfl⟩ : ∃ i, n = N + i := ⟨n - N, by omega⟩
      have hi : i ∈ Finset.range m := Finset.mem_range.mpr (by omega)
      have hle : |b (N + i)| / c ^ (N + i) ≤ M :=
        Finset.single_le_sum (f := fun i => |b (N + i)| / c ^ (N + i))
          (fun j _ => by positivity) hi
      have hcp : 0 < c ^ (N + i) := pow_pos hc _
      calc b (N + i) ≤ |b (N + i)| := le_abs_self _
        _ = |b (N + i)| / c ^ (N + i) * c ^ (N + i) := by field_simp
        _ ≤ M * c ^ (N + i) := by gcongr
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + m := ⟨n - m, by omega⟩
      have hk : N ≤ k := by omega
      calc b (k + m) ≤ K * ∑ i ∈ Finset.range m, b (k + i) := h k hk
        _ ≤ K * ∑ i ∈ Finset.range m, M * c ^ (k + i) := by
            gcongr with i hi
            exact ih (k + i) (by simp at hi; omega) (by omega)
        _ = M * c ^ k * (K * ∑ i ∈ Finset.range m, c ^ i) := by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
        _ ≤ M * c ^ k * c ^ m := by gcongr
        _ = M * c ^ (k + m) := by ring

/-- Lower comparison: `K ∑ b (n + i) ≤ b (n + m)` with `c^m ≤ K ∑ c^i` and a positive starting
window gives `b n ≥ M c^n` with `M > 0`. -/
private theorem lower_compare {m : ℕ} (hm : 0 < m) {b : ℕ → ℝ} {K c : ℝ} (hK : 0 ≤ K)
    (hc : 0 < c) (hcK : c ^ m ≤ K * ∑ i ∈ Finset.range m, c ^ i) (N : ℕ)
    (hpos : ∀ i, i < m → 0 < b (N + i))
    (h : ∀ n, N ≤ n → K * ∑ i ∈ Finset.range m, b (n + i) ≤ b (n + m)) :
    ∃ M, 0 < M ∧ ∀ n, N ≤ n → M * c ^ n ≤ b n := by
  have hne : (Finset.range m).Nonempty := ⟨0, Finset.mem_range.mpr hm⟩
  set M := (Finset.range m).inf' hne (fun i => b (N + i) / c ^ (N + i)) with hMdef
  have hM0 : 0 < M := by
    rw [hMdef, Finset.lt_inf'_iff]
    intro i hi
    have := hpos i (Finset.mem_range.mp hi)
    positivity
  refine ⟨M, hM0, fun n => ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n (N + m) with hlt | hge
    · obtain ⟨i, rfl⟩ : ∃ i, n = N + i := ⟨n - N, by omega⟩
      have hi : i ∈ Finset.range m := Finset.mem_range.mpr (by omega)
      have hle : M ≤ b (N + i) / c ^ (N + i) := Finset.inf'_le _ hi
      have hcp : 0 < c ^ (N + i) := pow_pos hc _
      calc M * c ^ (N + i) ≤ b (N + i) / c ^ (N + i) * c ^ (N + i) := by gcongr
        _ = b (N + i) := by field_simp
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + m := ⟨n - m, by omega⟩
      have hk : N ≤ k := by omega
      calc M * c ^ (k + m) = M * c ^ k * c ^ m := by ring
        _ ≤ M * c ^ k * (K * ∑ i ∈ Finset.range m, c ^ i) := by gcongr
        _ = K * ∑ i ∈ Finset.range m, M * c ^ (k + i) := by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
        _ ≤ K * ∑ i ∈ Finset.range m, b (k + i) := by
            gcongr with i hi
            exact ih (k + i) (by simp at hi; omega) (by omega)
        _ ≤ b (k + m) := h k hk

/-- `√(c^n) = (√c)^n` bound used for the forcing estimates. -/
private theorem sqrt_le_of_le_pow {s A c : ℝ} (n : ℕ) (hA : 0 ≤ A) (hc : 0 ≤ c)
    (h : s ≤ A * c ^ n) : Real.sqrt s ≤ Real.sqrt A * Real.sqrt c ^ n := by
  have hpow : (Real.sqrt c ^ n) ^ 2 = c ^ n := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hc]
  have h2 : (Real.sqrt A * Real.sqrt c ^ n) ^ 2 = A * c ^ n := by
    rw [mul_pow, Real.sq_sqrt hA, hpow]
  calc Real.sqrt s ≤ Real.sqrt (A * c ^ n) := Real.sqrt_le_sqrt h
    _ = Real.sqrt A * Real.sqrt c ^ n := by
        rw [← h2, Real.sqrt_sq (by positivity)]

/-- The analytic core: a nonnegative sequence satisfying the recurrence of `P` with a forcing of
size `√s + 1/4`, where `s n = ∑_{i<m} b (n + i) → ∞`, is `L R^n + O(R^(n/2))` with `L > 0`. -/
private theorem analytic {m : ℕ} (hm : 0 < m) (P : ℝ[X]) (R : ℝ) (hR : 1 < R)
    (hmult : P.rootMultiplicity R = 1)
    (hother : ∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).IsRoot z → z ≠ (R : ℂ) → ‖z‖ < 1)
    {K K' c c' : ℝ} (hK1 : 1 < K) (hK'0 : 0 ≤ K') (hK'1 : K' < 1) (hc1 : 1 < c)
    (hcR : c < R ^ 2) (hcc' : c < c' ^ 2) (hc'0 : 0 < c')
    (hcK : K * ∑ i ∈ Finset.range m, c ^ i ≤ c ^ m)
    (hc'K' : c' ^ m ≤ K' * ∑ i ∈ Finset.range m, c' ^ i)
    (b : ℕ → ℝ) (hb0 : ∀ n, 0 ≤ b n)
    (hsum : ∀ j, ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * b (j + k) =
      b (j + m) - ∑ i ∈ Finset.range m, b (j + i))
    (herr : ∀ n, |b (n + m) - ∑ i ∈ Finset.range m, b (n + i)| ≤
      Real.sqrt (∑ i ∈ Finset.range m, b (n + i)) + 1 / 4)
    (hinf : Tendsto (fun n => ∑ i ∈ Finset.range m, b (n + i)) atTop atTop)
    (hpos : ∀ᶠ n in atTop, 0 < b n) :
    ∃ L : ℝ, 0 < L ∧ (fun n => b n - L * R ^ n) =O[atTop] (fun n => Real.sqrt R ^ n) := by
  set s : ℕ → ℝ := fun n => ∑ i ∈ Finset.range m, b (n + i) with hsdef
  have hs0 : ∀ n, 0 ≤ s n := fun n => Finset.sum_nonneg fun i _ => hb0 _
  have hR0 : 0 < R := by linarith
  -- eventually the rounding error is a small fraction of `s`
  set ε := min (K - 1) (1 - K') with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  have hεK : ε ≤ K - 1 := min_le_left _ _
  have hεK' : ε ≤ 1 - K' := min_le_right _ _
  have hsq : Tendsto (fun n => Real.sqrt (s n)) atTop atTop := Real.tendsto_sqrt_atTop.comp hinf
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (hsq.eventually_ge_atTop (max 1 (2 / ε)))
  have hsmall : ∀ n, N0 ≤ n → Real.sqrt (s n) + 1 / 4 ≤ ε * s n := by
    intro n hn
    have hu := hN0 n hn
    have hu1 : 1 ≤ Real.sqrt (s n) := le_of_max_le_left hu
    have hu2 : 2 / ε ≤ Real.sqrt (s n) := le_of_max_le_right hu
    have hss : Real.sqrt (s n) ^ 2 = s n := Real.sq_sqrt (hs0 n)
    have h2 : 2 ≤ ε * Real.sqrt (s n) := by
      rw [div_le_iff₀ hε0] at hu2
      linarith
    nlinarith
  have hup : ∀ n, N0 ≤ n → b (n + m) ≤ K * s n := by
    intro n hn
    have h1 := (abs_le.mp (herr n)).2
    have h2 := hsmall n hn
    have h4 := hs0 n
    simp only [hsdef] at h2 h4 ⊢
    nlinarith
  have hdown : ∀ n, N0 ≤ n → K' * s n ≤ b (n + m) := by
    intro n hn
    have h1 := (abs_le.mp (herr n)).1
    have h2 := hsmall n hn
    have h4 := hs0 n
    simp only [hsdef] at h2 h4 ⊢
    nlinarith
  obtain ⟨M, hM⟩ := upper_compare (by linarith) (by linarith) hcK N0 hup
  -- the forcing is `O((√c)^n)`
  set q := Real.sqrt c with hqdef
  have hq0 : 0 < q := Real.sqrt_pos.mpr (by linarith)
  have hq1 : 1 < q := by
    rw [hqdef, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one hc1
  have hqR : q < R := (Real.sqrt_lt' hR0).mpr hcR
  have hqc' : q < c' := (Real.sqrt_lt' hc'0).mpr hcc'
  set e : ℕ → ℝ := fun j => ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * b (j + k)
    with hedef
  have he_le : ∀ n, |e n| ≤ Real.sqrt (s n) + 1 / 4 := fun n => by
    simp only [hedef, hsum]
    exact herr n
  set A := |M| * ∑ i ∈ Finset.range m, c ^ i with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hsA : ∀ n, N0 ≤ n → s n ≤ A * c ^ n := by
    intro n hn
    calc s n = ∑ i ∈ Finset.range m, b (n + i) := rfl
      _ ≤ ∑ i ∈ Finset.range m, |M| * c ^ (n + i) := Finset.sum_le_sum fun i _ =>
          (hM (n + i) (by omega)).trans (by gcongr; exact le_abs_self M)
      _ = A * c ^ n := by
          rw [hAdef, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
  have he : e =O[atTop] (fun j => q ^ j) := by
    refine IsBigO.of_bound (Real.sqrt A + 1 / 4) (eventually_atTop.mpr ⟨N0, fun n hn => ?_⟩)
    have h1 := sqrt_le_of_le_pow n hA0 (by linarith) (hsA n hn)
    have hq1n : 1 ≤ q ^ n := one_le_pow₀ hq1.le
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hq0 n)]
    have := he_le n
    nlinarith
  have hother_q : ∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).IsRoot z → z ≠ (R : ℂ) → ‖z‖ < q :=
    fun z hz hne => (hother z hz hne).trans hq1
  obtain ⟨L, hL⟩ := (D5.S1.Recurrence.Asymptotic.DominantRootForcing.result).1 P R q hmult hq0
    (by rwa [abs_of_pos hR0]) hother_q b e (fun j => rfl) he
  obtain ⟨C, hC⟩ := hL.bound
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hC
  have hbL : ∀ n, N1 ≤ n → |b n - L * R ^ n| ≤ |C| * q ^ n := by
    intro n hn
    have h := hN1 n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hq0 n)] at h
    exact h.trans (by gcongr; exact le_abs_self C)
  have hlo : (fun n => b n - L * R ^ n) =o[atTop] (fun n => R ^ n) :=
    hL.trans_isLittleO (isLittleO_pow_pow_of_lt_left hq0.le hqR)
  -- the forcing is `O((√R)^n)`
  set p := Real.sqrt R with hpdef
  have hp0 : 0 < p := Real.sqrt_pos.mpr hR0
  have hp1 : 1 < p := by
    rw [hpdef, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one hR
  have hpR : p < |R| := by
    rw [abs_of_pos hR0]
    exact (Real.sqrt_lt' hR0).mpr (by nlinarith)
  set B := (|L| + |C|) * ∑ i ∈ Finset.range m, R ^ i with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hbR : ∀ n, N1 ≤ n → b n ≤ (|L| + |C|) * R ^ n := by
    intro n hn
    have h := (abs_le.mp (hbL n hn)).2
    have hqn : q ^ n ≤ R ^ n := pow_le_pow_left₀ hq0.le hqR.le n
    have hLn : L * R ^ n ≤ |L| * R ^ n := by gcongr; exact le_abs_self L
    nlinarith [abs_nonneg C, pow_pos hR0 n]
  have he2 : e =O[atTop] (fun j => p ^ j) := by
    refine IsBigO.of_bound (Real.sqrt B + 1 / 4) (eventually_atTop.mpr ⟨N1, fun n hn => ?_⟩)
    have hsB : s n ≤ B * R ^ n := by
      calc s n = ∑ i ∈ Finset.range m, b (n + i) := rfl
        _ ≤ ∑ i ∈ Finset.range m, (|L| + |C|) * R ^ (n + i) :=
            Finset.sum_le_sum fun i _ => hbR (n + i) (by omega)
        _ = B * R ^ n := by
            rw [hBdef, Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
    have h1 := sqrt_le_of_le_pow n hB0 hR0.le hsB
    have hp1n : 1 ≤ p ^ n := one_le_pow₀ hp1.le
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hp0 n)]
    have := he_le n
    nlinarith
  have hmain := (D5.S1.Recurrence.Asymptotic.DominantRootForcing.result).2 P R p hmult hp0 hpR
    (fun z hz hne => (hother z hz hne).trans hp1) b e L (fun j => rfl) hlo he2
  -- positivity of `L`
  obtain ⟨N2, hN2⟩ := eventually_atTop.mp hpos
  obtain ⟨M', hM'0, hM'⟩ := lower_compare hm hK'0 hc'0 hc'K' (max N0 N2)
    (fun i _ => hN2 _ (by omega)) (fun n hn => hdown n (by omega))
  refine ⟨L, ?_, hmain⟩
  by_contra hL0
  push Not at hL0
  have hρ : Tendsto (fun n : ℕ => (q / c') ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((div_lt_one hc'0).mpr hqc')
  obtain ⟨N3, hN3⟩ := eventually_atTop.mp
    (hρ.eventually (gt_mem_nhds (show 0 < M' / (|C| + 1) by positivity)))
  set n := max (max N1 N3) (max N0 N2) with hn
  have h1 := hM' n (by omega)
  have h2 := (abs_le.mp (hbL n (by omega))).2
  have h3 := hN3 n (by omega)
  have hc'n : 0 < c' ^ n := pow_pos hc'0 n
  have h4 : L * R ^ n ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hL0 (pow_nonneg hR0.le n)
  have h5 : (q / c') ^ n * c' ^ n = q ^ n := by rw [div_pow]; field_simp
  rw [lt_div_iff₀ (by positivity)] at h3
  nlinarith [abs_nonneg C, pow_pos hq0 n]

end D5.S1.Recurrence.RoundedNormBoundedError
