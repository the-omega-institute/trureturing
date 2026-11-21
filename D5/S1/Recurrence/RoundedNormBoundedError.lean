/- GID: D5/S1/Recurrence/RoundedNormBoundedError
   generality: I
   mirror-B: D5/B/S1/Recurrence/RoundedNormBoundedError
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.NumberTheory.Real.GoldenRatio]
   utility: none
   digest: Rounded two- and three-norm sequences satisfy x_n = C R^(n/2) + O(1), C > 0, exactly for the seeds that do not stall. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#352)
escape_witness: analytic (a nonnegative sequence satisfying the characteristic recurrence with
  forcing √s + 1/4, s → ∞, is L R^n + O(R^(n/2)) with L > 0: comparison bounds b = O(2^n), dominant-
  root forcing at q = √2 and then at q = √R, and a lower comparison with ratio 3/2 rules out
  L <= 0), upper_compare and lower_compare (window comparison of linear recurrent inequalities),
  step_up and tendsto_atTop (the rounded norm strictly exceeds the window start past a
  threshold, so the sequence is unbounded), finish (rationalizing the squared expansion into
  the bounded error and the ratio rate), P2_other and P3_other (the non-dominant roots of
  X^2 - X - 1 and X^3 - X^2 - X - 1 have modulus below one), and two_case and three_case (the
  seed conditions are also necessary: otherwise the sequence stays at most one).
proof_shape:
  rad, P2, P3: definitions; consumers: the lemmas below.
  sqrt_le_of_le_pow: bind-only helper; consumer: analytic.
  rad_nonneg: bind-only helper; consumer: sq_err.
  round_err: bind-only helper; consumers: sq_err, le_next, step_up, two_case.
  sq_err: bind-only helper; consumer: generic.
  P2_natDegree: bind-only helper; consumers: P2_sum, P2_rootMultiplicity.
  P3_natDegree: bind-only helper; consumers: P3_sum, P3_rootMultiplicity.
  P2_sum, P2_rootMultiplicity: bind-only helpers; consumer: two_case.
  P3_sum, P3_rootMultiplicity: bind-only helpers; consumer: three_case.
  trib_gt: bind-only helper; consumers: P3_other, three_case.
  not_bounded_geom: bind-only helper; consumers: two_case, three_case,
    D5/S1/Recurrence/OEISA400645LargeSeeds.result.
  comparisons: content (eventual window comparisons from a rounding error √s + 1/4 with
    s → ∞); consumer: generic.
  le_next: bind-only helper (instantiation of the rounding bound); consumers: mono, two_case,
    three_case.
  mono: bind-only helper (induction over le_next); consumers: step_up, tendsto_atTop.
  generic: bind-only helper (assembles analytic and finish); consumers: two_case, three_case.
  upper_compare, lower_compare, step_up, tendsto_atTop, analytic, finish, P2_other, P3_other,
    two_case, three_case: content; consumers: generic, two_case, three_case, result; analytic
    and finish also D5/S1/Recurrence/OEISA400645LargeSeeds.asymptotic.
  result: content (after inlining the helpers added here, its live proof path runs through
    two_case, three_case and the lemmas above).
Direct frozen dependencies (module statement_id):
  D5/S1/Recurrence/Asymptotic/DominantRootForcing (result),
    sha256:1d9580e02dfd6fc17ce8d9039a9444783c195aa2b491d01ec9b830fd96091820;
  D5/S0/Tower/Tribonacci/Values (tribonacciConstant, one_lt_tribonacciConstant,
    tribonacciConstant_lt_two, tribonacciConstant_cubic),
    sha256:f0e84eed265aa226b9c3573b615c900dd052f29b0606f05c018db2a9cb665a5f.
Search record (§3.1): D5/S1/Recurrence/OEISA400644 proves the ratio limit for the fixed
  three-term seed (0, 0, 1) only; no D5 declaration treats general seeds, the two-term rule or a
  bounded-error rate; pinned Mathlib has no rounded-norm recurrences.
-/

import D5.S1.Recurrence.Asymptotic.DominantRootForcing
import D5.S0.Tower.Tribonacci.Values
import Mathlib.NumberTheory.Real.GoldenRatio

set_option autoImplicit false

noncomputable section

/-! # Rounded two- and three-norm sequences

For `x (n + m) = round √(x n² + ⋯ + x (n + m - 1)²)` with `m = 2` or `m = 3`, let `R` be the
dominant root of `y^m - y^(m-1) - ⋯ - 1` (the golden ratio, resp. the Tribonacci constant). There
is `C > 0` with `x n = C R^(n/2) + O(1)` and `x (n+1)/x n = √R + O(R^(-n/2))` exactly when the seed
does not stall: `max (x 0) (x 1) ≥ 2` for `m = 2`, and a nonzero seed for `m = 3`. The squares
satisfy the characteristic recurrence up to the rounding error `√s + 1/4`; dominant-root forcing
gives `x n² = L R^n + O(R^(n/2))` with `L > 0`, and rationalizing gives the bounded error.
-/

namespace D5.S1.Recurrence.RoundedNormBoundedError

open Polynomial Asymptotics Filter Real

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

/-- Eventual comparisons from a rounding error of size `√s + 1/4` with `s → ∞`. -/
private theorem comparisons {m : ℕ} {K K' : ℝ} (hK1 : 1 < K) (hK'1 : K' < 1) (b : ℕ → ℝ)
    (hb0 : ∀ n, 0 ≤ b n)
    (herr : ∀ n, |b (n + m) - ∑ i ∈ Finset.range m, b (n + i)| ≤
      Real.sqrt (∑ i ∈ Finset.range m, b (n + i)) + 1 / 4)
    (hinf : Tendsto (fun n => ∑ i ∈ Finset.range m, b (n + i)) atTop atTop) :
    (∀ᶠ n in atTop, b (n + m) ≤ K * ∑ i ∈ Finset.range m, b (n + i)) ∧
      (∀ᶠ n in atTop, K' * ∑ i ∈ Finset.range m, b (n + i) ≤ b (n + m)) := by
  set s : ℕ → ℝ := fun n => ∑ i ∈ Finset.range m, b (n + i) with hsdef
  have hs0 : ∀ n, 0 ≤ s n := fun n => Finset.sum_nonneg fun i _ => hb0 _
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
  refine ⟨eventually_atTop.mpr ⟨N0, fun n hn => ?_⟩, eventually_atTop.mpr ⟨N0, fun n hn => ?_⟩⟩
  · have h1 := (abs_le.mp (herr n)).2
    have h2 := hsmall n hn
    have h4 := hs0 n
    simp only [hsdef] at h2 h4 ⊢
    nlinarith
  · have h1 := (abs_le.mp (herr n)).1
    have h2 := hsmall n hn
    have h4 := hs0 n
    simp only [hsdef] at h2 h4 ⊢
    nlinarith

/-- The analytic core. Let `b` satisfy the recurrence of `P` with forcing `e`, where `P` has
the simple root `R > 1` and all other roots below `√c`. If eventually
`b (n + m₁) ≤ K ∑_{i<m₁} b (n + i)` with `K ∑ c^i ≤ c^m₁`, eventually
`K' ∑_{i<m₂} b (n + i) ≤ b (n + m₂)` with `c'^m₂ ≤ K' ∑ c'^i`, `1 < c < min (R^2) (c'^2)`, `b`
is eventually positive, and eventually `|e n| ≤ √(∑_{i<w} b (n + i)) + 1/4`, then
`b n = L R^n + O(R^(n/2))` with `L > 0`. -/
theorem analytic (P : ℝ[X]) (R : ℝ) (hR : 1 < R) (hmult : P.rootMultiplicity R = 1)
    {m₁ m₂ w : ℕ} (hm₂ : 0 < m₂) {K K' c c' : ℝ} (hK0 : 0 ≤ K) (hK'0 : 0 ≤ K')
    (hc1 : 1 < c) (hcR : c < R ^ 2) (hcc' : c < c' ^ 2) (hc'0 : 0 < c')
    (hother : ∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).IsRoot z → z ≠ (R : ℂ) →
      ‖z‖ < Real.sqrt c ∧ ‖z‖ < Real.sqrt R)
    (hcK : K * ∑ i ∈ Finset.range m₁, c ^ i ≤ c ^ m₁)
    (hc'K' : c' ^ m₂ ≤ K' * ∑ i ∈ Finset.range m₂, c' ^ i)
    (b : ℕ → ℝ)
    (hup : ∀ᶠ n in atTop, b (n + m₁) ≤ K * ∑ i ∈ Finset.range m₁, b (n + i))
    (hdown : ∀ᶠ n in atTop, K' * ∑ i ∈ Finset.range m₂, b (n + i) ≤ b (n + m₂))
    (hpos : ∀ᶠ n in atTop, 0 < b n) (e : ℕ → ℝ)
    (hsum : ∀ j, ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * b (j + k) = e j)
    (he : ∀ᶠ n in atTop, |e n| ≤ Real.sqrt (∑ i ∈ Finset.range w, b (n + i)) + 1 / 4) :
    ∃ L : ℝ, 0 < L ∧ (fun n => b n - L * R ^ n) =O[atTop] (fun n => Real.sqrt R ^ n) := by
  have hR0 : 0 < R := by linarith
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hup
  obtain ⟨Ne, hNe⟩ := eventually_atTop.mp he
  obtain ⟨M, hM⟩ := upper_compare hK0 (by linarith) hcK N0 hN0
  set T : ℕ → ℝ := fun n => ∑ i ∈ Finset.range w, b (n + i) with hTdef
  -- the forcing is `O((√c)^n)`
  set q := Real.sqrt c with hqdef
  have hq0 : 0 < q := Real.sqrt_pos.mpr (by linarith)
  have hq1 : 1 < q := by
    rw [hqdef, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one hc1
  have hqR : q < R := (Real.sqrt_lt' hR0).mpr hcR
  have hqc' : q < c' := (Real.sqrt_lt' hc'0).mpr hcc'
  set A := |M| * ∑ i ∈ Finset.range w, c ^ i with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hTA : ∀ n, N0 ≤ n → T n ≤ A * c ^ n := by
    intro n hn
    calc T n = ∑ i ∈ Finset.range w, b (n + i) := rfl
      _ ≤ ∑ i ∈ Finset.range w, |M| * c ^ (n + i) := Finset.sum_le_sum fun i _ =>
          (hM (n + i) (by omega)).trans (by gcongr; exact le_abs_self M)
      _ = A * c ^ n := by
          rw [hAdef, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
  have he1 : e =O[atTop] (fun j => q ^ j) := by
    refine IsBigO.of_bound (Real.sqrt A + 1 / 4)
      (eventually_atTop.mpr ⟨max N0 Ne, fun n hn => ?_⟩)
    have h1 := sqrt_le_of_le_pow n hA0 (by linarith) (hTA n (le_of_max_le_left hn))
    have hq1n : 1 ≤ q ^ n := one_le_pow₀ hq1.le
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hq0 n)]
    have := hNe n (le_of_max_le_right hn)
    nlinarith
  obtain ⟨L, hL⟩ := (D5.S1.Recurrence.Asymptotic.DominantRootForcing.result).1 P R q hmult hq0
    (by rwa [abs_of_pos hR0]) (fun z hz hne => (hother z hz hne).1) b e hsum he1
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
  set B := (|L| + |C|) * ∑ i ∈ Finset.range w, R ^ i with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hbR : ∀ n, N1 ≤ n → b n ≤ (|L| + |C|) * R ^ n := by
    intro n hn
    have h := (abs_le.mp (hbL n hn)).2
    have hqn : q ^ n ≤ R ^ n := pow_le_pow_left₀ hq0.le hqR.le n
    have hLn : L * R ^ n ≤ |L| * R ^ n := by gcongr; exact le_abs_self L
    nlinarith [abs_nonneg C, pow_pos hR0 n]
  have he2 : e =O[atTop] (fun j => p ^ j) := by
    refine IsBigO.of_bound (Real.sqrt B + 1 / 4)
      (eventually_atTop.mpr ⟨max N1 Ne, fun n hn => ?_⟩)
    have hTB : T n ≤ B * R ^ n := by
      calc T n = ∑ i ∈ Finset.range w, b (n + i) := rfl
        _ ≤ ∑ i ∈ Finset.range w, (|L| + |C|) * R ^ (n + i) :=
            Finset.sum_le_sum fun i _ => hbR (n + i) (by omega)
        _ = B * R ^ n := by
            rw [hBdef, Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
    have h1 := sqrt_le_of_le_pow n hB0 hR0.le hTB
    have hp1n : 1 ≤ p ^ n := one_le_pow₀ hp1.le
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hp0 n)]
    have := hNe n (le_of_max_le_right hn)
    nlinarith
  have hmain := (D5.S1.Recurrence.Asymptotic.DominantRootForcing.result).2 P R p hmult hp0 hpR
    (fun z hz hne => (hother z hz hne).2) b e L hsum hlo he2
  -- positivity of `L`
  obtain ⟨N2, hN2⟩ := eventually_atTop.mp hpos
  obtain ⟨N3, hN3⟩ := eventually_atTop.mp hdown
  obtain ⟨M', hM'0, hM'⟩ := lower_compare hm₂ hK'0 hc'0 hc'K' (max N2 N3)
    (fun i _ => hN2 _ (by omega)) (fun n hn => hN3 n (by omega))
  refine ⟨L, ?_, hmain⟩
  by_contra hL0
  push Not at hL0
  have hρ : Tendsto (fun n : ℕ => (q / c') ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((div_lt_one hc'0).mpr hqc')
  obtain ⟨N4, hN4⟩ := eventually_atTop.mp
    (hρ.eventually (gt_mem_nhds (show 0 < M' / (|C| + 1) by positivity)))
  set n := max (max N1 N4) (max N2 N3) with hn
  have h1 := hM' n (by omega)
  have h2 := (abs_le.mp (hbL n (by omega))).2
  have h3 := hN4 n (by omega)
  have hc'n : 0 < c' ^ n := pow_pos hc'0 n
  have h4 : L * R ^ n ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hL0 (pow_nonneg hR0.le n)
  have h5 : (q / c') ^ n * c' ^ n = q ^ n := by rw [div_pow]; field_simp
  rw [lt_div_iff₀ (by positivity)] at h3
  nlinarith [abs_nonneg C, pow_pos hq0 n]

section Sequence

variable {m : ℕ} {x : ℕ → ℕ}

/-- The radicand `∑_{i<m} x (n + i)^2`. -/
private def rad (m : ℕ) (x : ℕ → ℕ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range m, (x (n + i) : ℝ) ^ 2

private theorem rad_nonneg (n : ℕ) : 0 ≤ rad m x n :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem round_err
    (hrec : ∀ n, (x (n + m) : ℤ) = round (Real.sqrt (rad m x n))) (n : ℕ) :
    |(x (n + m) : ℝ) - Real.sqrt (rad m x n)| ≤ 1 / 2 := by
  have h := abs_sub_round (Real.sqrt (rad m x n))
  rw [← hrec n, abs_sub_comm] at h
  exact_mod_cast h

private theorem sq_err
    (hrec : ∀ n, (x (n + m) : ℤ) = round (Real.sqrt (rad m x n))) (n : ℕ) :
    |(x (n + m) : ℝ) ^ 2 - rad m x n| ≤ Real.sqrt (rad m x n) + 1 / 4 := by
  have h := round_err hrec n
  have hs := Real.sq_sqrt (rad_nonneg (m := m) (x := x) n)
  have hs0 := Real.sqrt_nonneg (rad m x n)
  obtain ⟨h1, h2⟩ := abs_le.mp h
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg ((x (n + m) : ℝ) - Real.sqrt (rad m x n))]

/-- Every earlier entry of the window is at most the new entry. -/
private theorem le_next
    (hrec : ∀ n, (x (n + m) : ℤ) = round (Real.sqrt (rad m x n))) (n i : ℕ) (hi : i < m) :
    x (n + i) ≤ x (n + m) := by
  have h := (abs_le.mp (round_err hrec n)).1
  have hsq : (x (n + i) : ℝ) ^ 2 ≤ rad m x n :=
    Finset.single_le_sum (f := fun i => (x (n + i) : ℝ) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_range.mpr hi)
  have hle : (x (n + i) : ℝ) ≤ Real.sqrt (rad m x n) :=
    Real.le_sqrt_of_sq_le hsq
  have : (x (n + i) : ℝ) < x (n + m) + 1 := by linarith
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)

/-- From index `m - 1` on, the sequence is nondecreasing. -/
private theorem mono (hm : 0 < m)
    (hrec : ∀ n, (x (n + m) : ℤ) = round (Real.sqrt (rad m x n))) {j k : ℕ} (hj : m - 1 ≤ j)
    (hjk : j ≤ k) : x j ≤ x k := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    have := le_next hrec (k + 1 - m) (m - 1) (by omega)
    rw [show k + 1 - m + (m - 1) = k by omega, show k + 1 - m + m = k + 1 by omega] at this
    exact ih.trans this

/-- If the window starts at `k` with `k + 1/4 < (m - 1) k^2`, the new entry exceeds `k`. -/
private theorem step_up (hm : 0 < m)
    (hrec : ∀ n, (x (n + m) : ℤ) = round (Real.sqrt (rad m x n))) (n : ℕ) (hn : m - 1 ≤ n)
    (hk : (x n : ℝ) + 1 / 4 < (m - 1 : ℝ) * (x n : ℝ) ^ 2) : x n + 1 ≤ x (n + m) := by
  have hwin : (m : ℝ) * (x n : ℝ) ^ 2 ≤ rad m x n := by
    have : ∑ i ∈ Finset.range m, (x n : ℝ) ^ 2 ≤ rad m x n :=
      Finset.sum_le_sum fun i _ => by
        have := mono hm hrec hn (show n ≤ n + i by omega)
        have : (x n : ℝ) ≤ x (n + i) := by exact_mod_cast this
        nlinarith [(Nat.cast_nonneg (x n) : (0 : ℝ) ≤ x n)]
    simpa using this
  have hlt : ((x n : ℝ) + 1 / 2) ^ 2 < rad m x n := by nlinarith
  have hsq : (x n : ℝ) + 1 / 2 < Real.sqrt (rad m x n) :=
    Real.lt_sqrt_of_sq_lt hlt
  have h := (abs_le.mp (round_err hrec n)).1
  have : (x n : ℝ) < x (n + m) := by linarith
  exact_mod_cast this

/-- Once an entry from index `m - 1` on reaches a threshold `k₀` with `k + 1/4 < (m - 1) k^2`
for all `k ≥ k₀`, the sequence tends to infinity. -/
private theorem tendsto_atTop (hm : 0 < m)
    (hrec : ∀ n, (x (n + m) : ℤ) = round (Real.sqrt (rad m x n))) (k₀ : ℕ)
    (hk : ∀ k : ℕ, k₀ ≤ k → (k : ℝ) + 1 / 4 < (m - 1 : ℝ) * (k : ℝ) ^ 2)
    (N : ℕ) (hN : m - 1 ≤ N) (hxN : k₀ ≤ x N) :
    Tendsto (fun n => (x n : ℝ)) atTop atTop := by
  have hgrow : ∀ j, x N + j ≤ x (N + m * j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hge : k₀ ≤ x (N + m * j) := hxN.trans
        ((Nat.le_add_right _ _).trans ih)
      have := step_up hm hrec (N + m * j) (by omega)
        (hk _ hge)
      rw [show N + m * j + m = N + m * (j + 1) by ring] at this
      omega
  rw [tendsto_atTop_atTop]
  intro B
  refine ⟨N + m * ⌈B⌉₊, fun n hn => ?_⟩
  have h1 := hgrow ⌈B⌉₊
  have h2 := mono hm hrec (show m - 1 ≤ N + m * ⌈B⌉₊ by omega) hn
  have h3 : (⌈B⌉₊ : ℝ) ≤ x n := by exact_mod_cast (by omega : ⌈B⌉₊ ≤ x n)
  exact (Nat.le_ceil B).trans h3

end Sequence

/-- Rationalizing: `x^2 = L R^n + O(R^(n/2))` gives `x = √L √R^n + O(1)` and the ratio rate. -/
theorem finish (x : ℕ → ℕ) (R : ℝ) (hR : 1 < R) (L : ℝ) (hL : 0 < L)
    (h : (fun n => (x n : ℝ) ^ 2 - L * R ^ n) =O[atTop] (fun n => Real.sqrt R ^ n)) :
    (fun n => (x n : ℝ) - Real.sqrt L * Real.sqrt R ^ n) =O[atTop] (fun _ => (1 : ℝ)) ∧
      (fun n => (x (n + 1) : ℝ) / x n - Real.sqrt R) =O[atTop]
        (fun n => (Real.sqrt R ^ n)⁻¹) := by
  set lam := Real.sqrt R with hlam
  have hR0 : 0 < R := by linarith
  have hs0 : 0 < lam := Real.sqrt_pos.mpr hR0
  have hs1 : 1 < lam := by
    rw [hlam, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one hR
  have hspow : ∀ j : ℕ, (lam ^ j) ^ 2 = R ^ j := fun j => by
    rw [← pow_mul, mul_comm, pow_mul, hlam, Real.sq_sqrt hR0.le]
  have hc0 : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  obtain ⟨C, hC⟩ := h.bound
  obtain ⟨M, hM⟩ := eventually_atTop.mp hC
  set B := |C| / Real.sqrt L with hBdef
  have hdev : ∀ n, M ≤ n → |(x n : ℝ) - Real.sqrt L * lam ^ n| ≤ B := by
    intro n hn
    have hb := hM n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hs0 n)] at hb
    set u : ℝ := (x n : ℝ)
    set y : ℝ := Real.sqrt L * lam ^ n
    have hu : 0 ≤ u := Nat.cast_nonneg _
    have hy : 0 < y := by positivity
    have hdiff : u ^ 2 - L * R ^ n = (u - y) * (u + y) := by
      have : y ^ 2 = L * R ^ n := by rw [mul_pow, Real.sq_sqrt hL.le, hspow]
      nlinarith [this]
    rw [hdiff, abs_mul, abs_of_pos (by linarith : 0 < u + y)] at hb
    rw [hBdef, le_div_iff₀ hc0]
    have hpos : 0 < lam ^ n := pow_pos hs0 n
    have h3 : |u - y| * y ≤ |C| * lam ^ n := by
      have := abs_nonneg (u - y)
      nlinarith [le_abs_self C]
    have h4 : |u - y| * Real.sqrt L * lam ^ n ≤ |C| * lam ^ n := by
      simpa [y, mul_assoc] using h3
    nlinarith
  have hB0 : 0 ≤ B := by positivity
  refine ⟨IsBigO.of_bound B (eventually_atTop.mpr ⟨M, fun n hn => ?_⟩), ?_⟩
  · rw [Real.norm_eq_abs, norm_one, mul_one]
    exact hdev n hn
  have hgrow : Tendsto (fun n : ℕ => lam ^ n) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hs1
  obtain ⟨P, hP⟩ := eventually_atTop.mp
    (hgrow.eventually_ge_atTop (2 * B / Real.sqrt L))
  refine IsBigO.of_bound (2 * B * (1 + lam) / Real.sqrt L)
    (eventually_atTop.mpr ⟨max M P, fun n hn => ?_⟩)
  have hn1 : M ≤ n := le_of_max_le_left hn
  have hn2 : P ≤ n := le_of_max_le_right hn
  have hpow : 0 < lam ^ n := pow_pos hs0 n
  have hd0 := hdev n hn1
  have hd1 := hdev (n + 1) (by omega)
  have hbig : 2 * B ≤ Real.sqrt L * lam ^ n := by
    have := hP n hn2
    rw [div_le_iff₀ hc0] at this
    linarith
  have hlow : Real.sqrt L * lam ^ n / 2 ≤ (x n : ℝ) := by
    have := (abs_le.mp hd0).1
    linarith
  have hxpos : 0 < (x n : ℝ) := by
    have : 0 < Real.sqrt L * lam ^ n := by positivity
    linarith
  have hnum : |(x (n + 1) : ℝ) - lam * x n| ≤ B * (1 + lam) := by
    have hsplit : (x (n + 1) : ℝ) - lam * x n =
        ((x (n + 1) : ℝ) - Real.sqrt L * lam ^ (n + 1)) -
          lam * ((x n : ℝ) - Real.sqrt L * lam ^ n) := by ring
    rw [hsplit]
    calc _ ≤ |(x (n + 1) : ℝ) - Real.sqrt L * lam ^ (n + 1)| +
          |lam * ((x n : ℝ) - Real.sqrt L * lam ^ n)| := abs_sub _ _
      _ = |(x (n + 1) : ℝ) - Real.sqrt L * lam ^ (n + 1)| +
          lam * |(x n : ℝ) - Real.sqrt L * lam ^ n| := by
          rw [abs_mul, abs_of_pos hs0]
      _ ≤ B + lam * B := by gcongr
      _ = B * (1 + lam) := by ring
  have hratio : (x (n + 1) : ℝ) / x n - lam = ((x (n + 1) : ℝ) - lam * x n) / x n := by
    field_simp
  rw [hratio, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_of_pos hxpos,
    abs_of_pos (inv_pos.mpr hpow), div_le_iff₀ hxpos]
  calc |(x (n + 1) : ℝ) - lam * x n| ≤ B * (1 + lam) := hnum
    _ = 2 * B * (1 + lam) / Real.sqrt L * (lam ^ n)⁻¹ * (Real.sqrt L * lam ^ n / 2) := by
        field_simp
    _ ≤ 2 * B * (1 + lam) / Real.sqrt L * (lam ^ n)⁻¹ * (x n : ℝ) := by
        gcongr

/-- The generic statement for window length `m`, characteristic polynomial `P`, dominant root `R`
and comparison data. -/
private theorem generic {m : ℕ} (hm : 0 < m) (P : ℝ[X]) (R : ℝ) (hR : 1 < R)
    (hmult : P.rootMultiplicity R = 1)
    (hother : ∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).IsRoot z → z ≠ (R : ℂ) → ‖z‖ < 1)
    (hP : ∀ (b : ℕ → ℝ) (j : ℕ), ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * b (j + k) =
      b (j + m) - ∑ i ∈ Finset.range m, b (j + i))
    {K K' c c' : ℝ} (hK1 : 1 < K) (hK'0 : 0 ≤ K') (hK'1 : K' < 1) (hc1 : 1 < c)
    (hcR : c < R ^ 2) (hcc' : c < c' ^ 2) (hc'0 : 0 < c')
    (hcK : K * ∑ i ∈ Finset.range m, c ^ i ≤ c ^ m)
    (hc'K' : c' ^ m ≤ K' * ∑ i ∈ Finset.range m, c' ^ i)
    (k₀ : ℕ) (hk : ∀ k : ℕ, k₀ ≤ k → (k : ℝ) + 1 / 4 < (m - 1 : ℝ) * (k : ℝ) ^ 2)
    (x : ℕ → ℕ) (hrec : ∀ n, (x (n + m) : ℤ) = round (Real.sqrt (rad m x n)))
    (N : ℕ) (hN : m - 1 ≤ N) (hxN : k₀ ≤ x N) :
    ∃ C : ℝ, 0 < C ∧
      (fun n => (x n : ℝ) - C * Real.sqrt R ^ n) =O[atTop] (fun _ => (1 : ℝ)) ∧
      (fun n => (x (n + 1) : ℝ) / x n - Real.sqrt R) =O[atTop]
        (fun n => (Real.sqrt R ^ n)⁻¹) := by
  have hx := tendsto_atTop hm hrec k₀ hk N hN hxN
  set b : ℕ → ℝ := fun n => (x n : ℝ) ^ 2 with hbdef
  have hrad : ∀ n, rad m x n = ∑ i ∈ Finset.range m, b (n + i) := fun n => rfl
  have hb : Tendsto b atTop atTop := (tendsto_pow_atTop two_ne_zero).comp hx
  have hinf : Tendsto (fun n => ∑ i ∈ Finset.range m, b (n + i)) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) hb
    have := Finset.single_le_sum (f := fun i => b (n + i)) (fun i _ => sq_nonneg _)
      (Finset.mem_range.mpr hm)
    simpa using this
  have hpos : ∀ᶠ n in atTop, 0 < b n :=
    (hb.eventually_gt_atTop 0)
  have herr : ∀ n, |b (n + m) - ∑ i ∈ Finset.range m, b (n + i)| ≤
      Real.sqrt (∑ i ∈ Finset.range m, b (n + i)) + 1 / 4 := fun n => by
    rw [← hrad]; exact sq_err hrec n
  obtain ⟨hup, hdown⟩ := comparisons hK1 hK'1 b (fun n => sq_nonneg _) herr hinf
  have hsqc : 1 < Real.sqrt c := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one hc1
  have hsqR : 1 < Real.sqrt R := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one hR
  obtain ⟨L, hL, hO⟩ := analytic P R hR hmult hm (by linarith) hK'0 hc1 hcR hcc' hc'0
    (fun z hz hne => ⟨(hother z hz hne).trans hsqc, (hother z hz hne).trans hsqR⟩) hcK hc'K' b hup hdown
    hpos _ (fun j => (hP b j).trans rfl) (Eventually.of_forall herr)
  obtain ⟨h1, h2⟩ := finish x R hR L hL hO
  exact ⟨Real.sqrt L, Real.sqrt_pos.mpr hL, h1, h2⟩

/-- A positive multiple of an unbounded geometric sequence is not within `O(1)` of a bounded
sequence. -/
theorem not_bounded_geom (x : ℕ → ℕ) (B₀ : ℕ) (hx : ∀ n, x n ≤ B₀) {C lam : ℝ}
    (hC : 0 < C) (hlam : 1 < lam)
    (h : (fun n => (x n : ℝ) - C * lam ^ n) =O[atTop] (fun _ => (1 : ℝ))) : False := by
  obtain ⟨B, hB⟩ := h.bound
  obtain ⟨N, hN⟩ := eventually_atTop.mp hB
  have hgrow : Tendsto (fun n : ℕ => C * lam ^ n) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hlam).const_mul_atTop hC
  obtain ⟨n, hn⟩ := eventually_atTop.mp (hgrow.eventually_gt_atTop (B + B₀))
  have h1 := hN (max N n) (le_max_left _ _)
  have h2 := hn (max N n) (le_max_right _ _)
  have h3 : (x (max N n) : ℝ) ≤ B₀ := by exact_mod_cast hx _
  rw [Real.norm_eq_abs, norm_one, mul_one] at h1
  have := (abs_le.mp h1).1
  linarith [(Nat.cast_nonneg (x (max N n)) : (0 : ℝ) ≤ _)]

/-! ### Two-term rounded norm -/

private def P2 : ℝ[X] := X ^ 2 - X - 1

private theorem P2_natDegree : P2.natDegree = 2 := by
  unfold P2
  compute_degree!

private theorem P2_sum (b : ℕ → ℝ) (j : ℕ) :
    ∑ k ∈ Finset.range (P2.natDegree + 1), P2.coeff k * b (j + k) =
      b (j + 2) - ∑ i ∈ Finset.range 2, b (j + i) := by
  rw [P2_natDegree]
  simp [Finset.sum_range_succ, P2, coeff_X_pow, coeff_X, coeff_one]
  ring

private theorem P2_rootMultiplicity : P2.rootMultiplicity goldenRatio = 1 := by
  have hP0 : P2 ≠ 0 := by
    intro h
    have := P2_natDegree
    rw [h, natDegree_zero] at this
    omega
  have hroot : P2.IsRoot goldenRatio := by
    simp only [IsRoot, P2, eval_sub, eval_pow, eval_X, eval_one]
    linear_combination goldenRatio_sq
  have hpos := (rootMultiplicity_pos hP0).mpr hroot
  have hnot : ¬ 1 < P2.rootMultiplicity goldenRatio := by
    rw [one_lt_rootMultiplicity_iff_isRoot hP0]
    rintro ⟨-, hd⟩
    simp [IsRoot, P2] at hd
    linarith [one_lt_goldenRatio]
  omega

private theorem P2_other (z : ℂ) (hz : (P2.map (algebraMap ℝ ℂ)).IsRoot z)
    (hne : z ≠ (goldenRatio : ℂ)) : ‖z‖ < 1 := by
  have hz' : z ^ 2 - z - 1 = 0 := by simpa [IsRoot, P2] using hz
  have hsum : (goldenRatio : ℂ) + goldenConj = 1 := by exact_mod_cast goldenRatio_add_goldenConj
  have hprod : (goldenRatio : ℂ) * goldenConj = -1 := by exact_mod_cast goldenRatio_mul_goldenConj
  have hfac : (z - goldenRatio) * (z - goldenConj) = 0 := by
    linear_combination hz' - z * hsum + hprod
  have hzψ : z = (goldenConj : ℂ) := by
    have := (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hne)
    exact sub_eq_zero.mp this
  rw [hzψ, Complex.norm_real, Real.norm_eq_abs, abs_of_neg goldenConj_neg]
  linarith [neg_one_lt_goldenConj]

private theorem two_case (x : ℕ → ℕ)
    (hrec : ∀ n, (x (n + 2) : ℤ) = round (Real.sqrt ((x n : ℝ) ^ 2 + (x (n + 1) : ℝ) ^ 2))) :
    (∃ C : ℝ, 0 < C ∧
      (fun n => (x n : ℝ) - C * Real.sqrt goldenRatio ^ n) =O[atTop] (fun _ => (1 : ℝ)) ∧
      (fun n => (x (n + 1) : ℝ) / x n - Real.sqrt goldenRatio) =O[atTop]
        (fun n => (Real.sqrt goldenRatio ^ n)⁻¹)) ↔ 2 ≤ max (x 0) (x 1) := by
  have hrec' : ∀ n, (x (n + 2) : ℤ) = round (Real.sqrt (rad 2 x n)) := fun n => by
    rw [hrec n]
    simp [rad, Finset.sum_range_succ]
  have hlam1 : 1 < Real.sqrt goldenRatio := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one one_lt_goldenRatio
  constructor
  · rintro ⟨C, hC, hO, -⟩
    by_contra hlt
    push Not at hlt
    have hsmall : ∀ n, x n ≤ 1 ∧ x (n + 1) ≤ 1 := by
      intro n
      induction n with
      | zero =>
        have h0 := le_max_left (x 0) (x 1)
        have h1 := le_max_right (x 0) (x 1)
        exact ⟨by omega, by simp only [zero_add]; omega⟩
      | succ n ih =>
        refine ⟨ih.2, ?_⟩
        show x (n + 2) ≤ 1
        have h := (abs_le.mp (round_err hrec' n)).2
        have hs : rad 2 x n ≤ 2 := by
          have h0 : (x n : ℝ) ≤ 1 := by exact_mod_cast ih.1
          have h1 : (x (n + 1) : ℝ) ≤ 1 := by exact_mod_cast ih.2
          simp only [rad, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero]
          nlinarith [(Nat.cast_nonneg (x n) : (0 : ℝ) ≤ _),
            (Nat.cast_nonneg (x (n + 1)) : (0 : ℝ) ≤ _)]
        have hsq : Real.sqrt (rad 2 x n) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt hs
        have h2 : Real.sqrt 2 < 3 / 2 := by
          rw [Real.sqrt_lt' (by norm_num)]
          norm_num
        have : (x (n + 2) : ℝ) < 2 := by linarith
        have : x (n + 2) < 2 := by exact_mod_cast this
        omega
    exact not_bounded_geom x 1 (fun n => (hsmall n).1) hC hlam1 hO
  · intro h2
    obtain ⟨N, hN, hxN⟩ : ∃ N, 1 ≤ N ∧ 2 ≤ x N := by
      rcases le_max_iff.mp h2 with h | h
      · exact ⟨2, by norm_num, h.trans (le_next hrec' 0 0 (by norm_num))⟩
      · exact ⟨1, le_rfl, h⟩
    have hφ := one_lt_goldenRatio
    exact generic (m := 2) (by norm_num) P2 goldenRatio hφ P2_rootMultiplicity P2_other P2_sum
      (K := 4 / 3) (K' := 9 / 10) (c := 2) (c' := 3 / 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by rw [goldenRatio_sq]; linarith) (by norm_num)
      (by norm_num) (by simp [Finset.sum_range_succ]; norm_num)
      (by simp [Finset.sum_range_succ]; norm_num) 2
      (fun k hk => by
        have : (2 : ℝ) ≤ k := by exact_mod_cast hk
        push_cast
        nlinarith)
      x hrec' N (by omega) hxN

/-! ### Three-term rounded norm -/

open D5.S0.Tower.Tribonacci.Values (tribonacciConstant one_lt_tribonacciConstant
  tribonacciConstant_lt_two tribonacciConstant_cubic)

private def P3 : ℝ[X] := X ^ 3 - X ^ 2 - X - 1

private theorem P3_natDegree : P3.natDegree = 3 := by
  unfold P3
  compute_degree!

private theorem P3_sum (b : ℕ → ℝ) (j : ℕ) :
    ∑ k ∈ Finset.range (P3.natDegree + 1), P3.coeff k * b (j + k) =
      b (j + 3) - ∑ i ∈ Finset.range 3, b (j + i) := by
  rw [P3_natDegree]
  simp [Finset.sum_range_succ, P3, coeff_X_pow, coeff_X, coeff_one]
  ring

private theorem trib_gt : 5 / 3 < tribonacciConstant := by
  have h1 := one_lt_tribonacciConstant
  have h2 := tribonacciConstant_lt_two
  have hc := tribonacciConstant_cubic
  nlinarith [sq_nonneg (tribonacciConstant - 5 / 3)]

private theorem P3_rootMultiplicity : P3.rootMultiplicity tribonacciConstant = 1 := by
  have hP0 : P3 ≠ 0 := by
    intro h
    have := P3_natDegree
    rw [h, natDegree_zero] at this
    omega
  have hroot : P3.IsRoot tribonacciConstant := by
    simp only [IsRoot, P3, eval_sub, eval_pow, eval_X, eval_one]
    linear_combination tribonacciConstant_cubic
  have hpos := (rootMultiplicity_pos hP0).mpr hroot
  have hnot : ¬ 1 < P3.rootMultiplicity tribonacciConstant := by
    rw [one_lt_rootMultiplicity_iff_isRoot hP0]
    rintro ⟨-, hd⟩
    simp [IsRoot, P3] at hd
    nlinarith [one_lt_tribonacciConstant]
  omega

private theorem P3_other (z : ℂ) (hz : (P3.map (algebraMap ℝ ℂ)).IsRoot z)
    (hne : z ≠ (tribonacciConstant : ℂ)) : ‖z‖ < 1 := by
  set t := tribonacciConstant with htdef
  have h1 := one_lt_tribonacciConstant
  have h2 := tribonacciConstant_lt_two
  have h53 := trib_gt
  have hz' : z ^ 3 - z ^ 2 - z - 1 = 0 := by simpa [IsRoot, P3] using hz
  have hcC : (t : ℂ) ^ 3 = t ^ 2 + t + 1 := by exact_mod_cast tribonacciConstant_cubic
  have hfac : (z - t) * (z ^ 2 + ((t - 1 : ℝ) : ℂ) * z + ((t ^ 2 - t - 1 : ℝ) : ℂ)) = 0 := by
    push_cast
    linear_combination hz' - hcC
  have hq := (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hne)
  have hre := congrArg Complex.re hq
  have him := congrArg Complex.im hq
  simp [sq, Complex.mul_re, Complex.mul_im] at hre him
  have hy : z.im ≠ 0 := by
    intro h0
    rw [h0] at hre
    nlinarith [sq_nonneg (z.re + (t - 1) / 2)]
  have hx : z.re = -(t - 1) / 2 := by
    have : z.im * (2 * z.re + (t - 1)) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hy
    linarith
  have hsq : Complex.normSq z < 1 := by
    rw [Complex.normSq_apply]
    rw [hx] at hre
    nlinarith
  rw [Complex.norm_def, show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_lt_sqrt (Complex.normSq_nonneg z) hsq

private theorem three_case (x : ℕ → ℕ)
    (hrec : ∀ n, (x (n + 3) : ℤ) =
      round (Real.sqrt ((x n : ℝ) ^ 2 + (x (n + 1) : ℝ) ^ 2 + (x (n + 2) : ℝ) ^ 2))) :
    (∃ C : ℝ, 0 < C ∧
      (fun n => (x n : ℝ) - C * Real.sqrt tribonacciConstant ^ n) =O[atTop]
        (fun _ => (1 : ℝ)) ∧
      (fun n => (x (n + 1) : ℝ) / x n - Real.sqrt tribonacciConstant) =O[atTop]
        (fun n => (Real.sqrt tribonacciConstant ^ n)⁻¹)) ↔ 0 < x 0 + x 1 + x 2 := by
  have hrec' : ∀ n, (x (n + 3) : ℤ) = round (Real.sqrt (rad 3 x n)) := fun n => by
    rw [hrec n]
    simp [rad, Finset.sum_range_succ]
  have ht1 := one_lt_tribonacciConstant
  have hlam1 : 1 < Real.sqrt tribonacciConstant := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one ht1
  constructor
  · rintro ⟨C, hC, hO, -⟩
    by_contra h0
    push Not at h0
    have hzero : ∀ n, x n = 0 ∧ x (n + 1) = 0 ∧ x (n + 2) = 0 := by
      intro n
      induction n with
      | zero => exact ⟨by omega, by simp only [zero_add]; omega, by simp only [zero_add]; omega⟩
      | succ n ih =>
        refine ⟨ih.2.1, ih.2.2, ?_⟩
        show x (n + 3) = 0
        have h := hrec' n
        have hs : rad 3 x n = 0 := by
          simp [rad, Finset.sum_range_succ, ih.1, ih.2.1, ih.2.2]
        rw [hs, Real.sqrt_zero, round_zero] at h
        exact_mod_cast h
    exact not_bounded_geom x 0 (fun n => (hzero n).1.le) hC hlam1 hO
  · intro hpos
    obtain ⟨i, hi, hxi⟩ : ∃ i, i < 3 ∧ 1 ≤ x i := by
      by_cases h0 : 1 ≤ x 0
      · exact ⟨0, by norm_num, h0⟩
      by_cases h1 : 1 ≤ x 1
      · exact ⟨1, by norm_num, h1⟩
      exact ⟨2, by norm_num, by omega⟩
    have hle := le_next hrec' 0 i hi
    simp only [zero_add] at hle
    have h53 := trib_gt
    have h2 := tribonacciConstant_lt_two
    exact generic (m := 3) (by norm_num) P3 tribonacciConstant ht1 P3_rootMultiplicity
      P3_other P3_sum (K := 8 / 7) (K' := 3 / 4) (c := 2) (c' := 3 / 2) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by nlinarith) (by norm_num) (by norm_num)
      (by simp [Finset.sum_range_succ]; norm_num) (by simp [Finset.sum_range_succ]; norm_num) 1
      (fun k hk => by
        have : (1 : ℝ) ≤ k := by exact_mod_cast hk
        push_cast
        nlinarith)
      x hrec' 3 (by norm_num) (hxi.trans hle)

/-- Rounded two- and three-norm sequences. For `x (n + 2) = round √(x n² + x (n+1)²)` there is
`C > 0` with `x n = C φ^(n/2) + O(1)` and `x (n+1)/x n = √φ + O(φ^(-n/2))` exactly when
`max (x 0) (x 1) ≥ 2`; for `x (n + 3) = round √(x n² + x (n+1)² + x (n+2)²)` the same holds with
the Tribonacci constant exactly when the seed is not all zero. -/
theorem result :
    (∀ x : ℕ → ℕ,
      (∀ n, (x (n + 2) : ℤ) = round (Real.sqrt ((x n : ℝ) ^ 2 + (x (n + 1) : ℝ) ^ 2))) →
      ((∃ C : ℝ, 0 < C ∧
        (fun n => (x n : ℝ) - C * Real.sqrt goldenRatio ^ n) =O[atTop] (fun _ => (1 : ℝ)) ∧
        (fun n => (x (n + 1) : ℝ) / x n - Real.sqrt goldenRatio) =O[atTop]
          (fun n => (Real.sqrt goldenRatio ^ n)⁻¹)) ↔ 2 ≤ max (x 0) (x 1))) ∧
    (∀ x : ℕ → ℕ,
      (∀ n, (x (n + 3) : ℤ) =
        round (Real.sqrt ((x n : ℝ) ^ 2 + (x (n + 1) : ℝ) ^ 2 + (x (n + 2) : ℝ) ^ 2))) →
      ((∃ C : ℝ, 0 < C ∧
        (fun n => (x n : ℝ) - C * Real.sqrt tribonacciConstant ^ n) =O[atTop]
          (fun _ => (1 : ℝ)) ∧
        (fun n => (x (n + 1) : ℝ) / x n - Real.sqrt tribonacciConstant) =O[atTop]
          (fun n => (Real.sqrt tribonacciConstant ^ n)⁻¹)) ↔ 0 < x 0 + x 1 + x 2)) :=
  ⟨two_case, three_case⟩

end D5.S1.Recurrence.RoundedNormBoundedError
