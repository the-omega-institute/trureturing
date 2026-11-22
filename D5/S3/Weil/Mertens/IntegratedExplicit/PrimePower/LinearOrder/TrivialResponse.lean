/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/TrivialResponse
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/TrivialResponse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Abel summation of the Möbius-weighted trivial-root response. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder.MoebiusPrefixes

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder

open Real ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta ArithmeticFunction.vonMangoldt

private theorem monotone_finite_abel_bound {N : ℕ} {a g : ℕ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hg0 : 0 ≤ g 0) (hg : Monotone g)
    (ha : ∀ n ≤ N+1, |∑ i ∈ Finset.range n, a i| ≤ L) :
    |∑ i ∈ Finset.range (N+1), a i * g i| ≤ 2*L*g N := by
  have hvar (M : ℕ) : ∑ i ∈ Finset.range M, (g (i+1)-g i) = g M-g 0 := by
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  have hlast : 0 ≤ g N := hg0.trans (hg (Nat.zero_le _))
  rw [show (∑ i ∈ Finset.range (N+1), a i * g i) =
      (∑ i ∈ Finset.range (N+1), a i) * g N -
        ∑ i ∈ Finset.range N, (∑ j ∈ Finset.range (i+1), a j) * (g (i+1) - g i) from
      by simpa only [Nat.add_sub_cancel, smul_eq_mul] using Finset.sum_range_by_parts' a g (N+1)]
  calc
    _ ≤ |(∑ i ∈ Finset.range (N+1), a i) * g N| +
        |∑ i ∈ Finset.range N, (∑ j ∈ Finset.range (i+1), a j) * (g (i+1) - g i)| := abs_sub _ _
    _ ≤ L * g N + L * (g N-g 0) := by
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg hlast]
        exact mul_le_mul_of_nonneg_right (ha _ le_rfl) hlast
      · rw [← hvar, Finset.mul_sum]
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro i hi
        have hd : 0 ≤ g (i+1)-g i := sub_nonneg.mpr (hg (Nat.le_succ _))
        rw [abs_mul, abs_of_nonneg hd]
        exact mul_le_mul_of_nonneg_right (ha _ (by have := Finset.mem_range.mp hi; omega)) hd
    _ ≤ _ := by nlinarith only [mul_nonneg hL hg0]

private def activeMoebius (i : ℕ) : ℝ := if 2 ≤ i then (μ i : ℝ) else 0

private theorem active_moebius_range (n : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range (n+1), activeMoebius i * f i =
      ∑ i ∈ Finset.Icc 2 n, (μ i : ℝ) * f i := by
  unfold activeMoebius
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  omega

private theorem active_moebius_prefix_log (hRH : RiemannHypothesis) :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ, 2 ≤ N → ∀ n ≤ N+1,
      |∑ i ∈ Finset.range n, activeMoebius i| * Real.log N ≤ D*N := by
  obtain ⟨C, hC, hM⟩ := moebius_uniform_prefix_log_saving hRH
  refine ⟨C+1, by positivity, fun N hN n hn => ?_⟩
  have hN₂ : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  cases n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, abs_zero, zero_mul]
    positivity
  | succ k =>
    have hk : k ≤ N := by omega
    rcases lt_or_ge k 2 with hl | hl
    · have hzero : ∀ i ∈ Finset.range (k+1), activeMoebius i = 0 := by
        intro i hi
        have hi' := Finset.mem_range.mp hi
        exact ite_eq_right (by omega)
      rw [Finset.sum_eq_zero hzero, abs_zero, zero_mul]
      positivity
    · have hI : insert 1 (Finset.Icc 2 k) = Finset.Ioc 0 k := by
        ext i
        simp only [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Ioc]
        omega
      have he : (∑ i ∈ Finset.Ioc 0 k, (μ i : ℝ)) =
          1 + ∑ i ∈ Finset.Icc 2 k, (μ i : ℝ) := by
        rw [← hI, Finset.sum_insert (by simp)]
        simp
      have hs := active_moebius_range k (fun _ => 1)
      simp only [mul_one] at hs
      rw [hs, show (∑ i ∈ Finset.Icc 2 k, (μ i : ℝ)) =
        (∑ i ∈ Finset.Ioc 0 k, (μ i : ℝ))-1 by linarith only [he]]
      calc
        _ ≤ (|(∑ i ∈ Finset.Ioc 0 k, (μ i : ℝ))| + 1) * Real.log N := by
          apply mul_le_mul_of_nonneg_right _ hlog
          simpa using abs_sub (∑ i ∈ Finset.Ioc 0 k, (μ i : ℝ)) 1
        _ ≤ _ := by
          rw [add_mul, one_mul, add_mul, one_mul]
          exact add_le_add (hM N hN k hk) (Real.log_le_self (by linarith))

private theorem moebius_monotone_log_weight_bound (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ), 2 ≤ N → ∀ g : ℕ → ℝ,
      0 ≤ g 0 → Monotone g → g N ≤ (1 + Real.log N) / 2 →
      |∑ i ∈ Finset.Icc 2 N, (μ i : ℝ) * g i| ≤ K*N := by
  obtain ⟨D, hD, hpre⟩ := active_moebius_prefix_log hRH
  let d := Real.log 2
  have hd : 0 < d := Real.log_pos (by norm_num)
  refine ⟨D*(1+1/d), by positivity, fun N hN g hg0 hg hgn => ?_⟩
  have hN₂ : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hld : d ≤ Real.log (N : ℝ) := Real.log_le_log (by norm_num) hN₂
  have hl : 0 < Real.log (N : ℝ) := hd.trans_le hld
  let L := D * (N : ℝ) / Real.log N
  have hL : 0 ≤ L := by
    dsimp [L]
    exact div_nonneg (by positivity) hl.le
  have hP : ∀ n ≤ N+1, |∑ i ∈ Finset.range n, activeMoebius i| ≤ L :=
    fun n hn => (le_div_iff₀ hl).mpr (hpre N hN n hn)
  rw [← active_moebius_range]
  calc
    _ ≤ 2 * L * g N := monotone_finite_abel_bound hL hg0 hg hP
    _ ≤ 2 * L * ((1 + Real.log N) / 2) :=
      mul_le_mul_of_nonneg_left hgn (by positivity)
    _ = D * (N : ℝ) * (1+1/Real.log N) := by
      dsimp [L]
      field_simp
      ring
    _ ≤ _ := by
      have ht := add_le_add_right (one_div_le_one_div_of_le hd hld) (1 : ℝ)
      exact (mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ D * (N : ℝ))).trans_eq (by ring)

open D5.S3.Weil.Mertens.IntegratedExplicit

private def trivialRootResponse (u : ℝ) (n : ℕ) : ℝ :=
  ∑' k : ℕ, (n : ℝ) / (trivialHeight k * ((n : ℝ)+trivialHeight k)) *
    Real.exp (-(trivialHeight k) * (u / (n : ℝ)))

private theorem trivialRootResponse_nonneg (u : ℝ) (n : ℕ) : 0 ≤ trivialRootResponse u n := by
  unfold trivialRootResponse
  exact tsum_nonneg fun k => by unfold trivialHeight; positivity

private theorem trivialRootMass_summable (n : ℕ) :
    Summable (fun k : ℕ => (n : ℝ) / (trivialHeight k * ((n : ℝ)+trivialHeight k))) := by
  cases n with
  | zero => simp
  | succ n =>
    have hnonneg (k : ℕ) : 0 ≤ ((n.succ : ℕ) : ℝ) /
        (trivialHeight k * (((n.succ : ℕ) : ℝ) + trivialHeight k)) := by
      unfold trivialHeight
      positivity
    apply Summable.of_nonneg_of_le hnonneg _
      (trivialCoeff_hasSum.summable.mul_left ((n.succ : ℕ) : ℝ))
    intro k
    have hn : (1 : ℝ) ≤ (n.succ : ℕ) := by exact_mod_cast Nat.succ_pos n
    have hk : 0 < trivialHeight k := by unfold trivialHeight; positivity
    change _ ≤ _ * (1 / (trivialHeight k * (trivialHeight k + 1)))
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left (by linarith) hk.le)

private theorem trivialRootResponse_monotone {u : ℝ} (hu : 0 ≤ u) :
    Monotone (trivialRootResponse u) := by
  let term (n k : ℕ) := (n : ℝ) / (trivialHeight k * ((n : ℝ)+trivialHeight k)) *
    Real.exp (-(trivialHeight k) * (u / (n : ℝ)))
  have ht (n k : ℕ) : 0 ≤ term n k := by dsimp [term]; unfold trivialHeight; positivity
  have hs (n : ℕ) : Summable (term n) := by
    apply Summable.of_nonneg_of_le (ht _) _ (trivialRootMass_summable n)
    intro k
    have hk : 0 < trivialHeight k := by unfold trivialHeight; positivity
    exact mul_le_of_le_one_right (by positivity)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr hk.le) (div_nonneg hu (by positivity))))
  intro n m hnm
  apply (hs n).tsum_le_tsum _ (hs m)
  intro k
  by_cases hn : n = 0
  · simpa [term, hn] using ht m k
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have ht0 : 0 < trivialHeight k := by unfold trivialHeight; positivity
  dsimp only [term]
  apply mul_le_mul _ _ (Real.exp_nonneg _) (by positivity)
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_nonneg ht0.le
      (mul_nonneg ht0.le (sub_nonneg.mpr hnm'))]
  · apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (div_le_div_of_nonneg_left hu hn0 hnm') (neg_nonpos.mpr ht0.le)

private theorem trivialRootResponse_upper {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    trivialRootResponse u n ≤ (1+Real.log n)/2 := by
  unfold trivialRootResponse
  apply (Real.tsum_le_of_sum_range_le (fun k => by unfold trivialHeight; positivity) _)
  intro N
  have hheight (k : ℕ) : 0 < trivialHeight k := by unfold trivialHeight; positivity
  have hpos (k : ℕ) : 0 ≤ (n : ℝ) / (trivialHeight k * ((n : ℝ)+trivialHeight k)) := by
    unfold trivialHeight
    positivity
  calc
    _ ≤ ∑ k ∈ Finset.range N, (n : ℝ) / (trivialHeight k * ((n : ℝ)+trivialHeight k)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_of_le_one_right (hpos k) (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (by linarith [hheight k])
          (div_nonneg hu (by positivity))))
    _ ≤ _ := ((trivialRootMass_summable n).sum_le_tsum _ (fun k _ => hpos k)).trans (trivial_mode_bound n)


open MeasureTheory Set
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open D5.S3.Arith.Robin.CompleteMertensPeak (Q U)
open D5.S3.Weil.Mertens.WeightedPrimeLimit (chebyshev_error_kernel_integrable)
open D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity (finite_error_integral normalized_error_integral)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope (G_split_nonneg)

private theorem root_centered_response {n : ℕ} (hn : 2 ≤ n)
    {v : ℝ} (hv : 0 ≤ v) :
    centered (n : ℝ) (Real.exp ((n : ℝ) * v)) - rootDensity (n : ℝ) ((n : ℝ) * v) =
      Real.exp (-((n : ℝ)*v)/2) * (trivialRootResponse ((n : ℝ)*v) n - Real.log (2*Real.pi)) := by
  let r := (n : ℝ)
  have hr : 1 < r := by dsimp [r]; exact_mod_cast (show 1 < n by omega)
  let y := Real.exp v
  let x := Real.exp (r * v)
  let s := Real.exp ((1 - r / 2) * v)
  let w := Real.exp ((r - 1) * v)
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : 1 ≤ x := (Real.exp_zero : Real.exp (0 : ℝ) = 1) ▸
    Real.exp_le_exp.mpr (mul_nonneg hr0.le hv)
  have hroot : x ^ r⁻¹ = y := by
    dsimp only [x, y]
    rw [← Real.exp_mul]
    congr 1
    field_simp
  have hscale₁ : Real.sqrt x * y ^ (1 - r) = s := by
    rw [Real.sqrt_eq_rpow]
    dsimp only [x, y, s]
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  have hscale₂ : s * w = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    dsimp only [s, w, x]
    rw [← Real.exp_add, ← Real.exp_mul]
    congr 1
    ring
  have hcut := centered_root_tail (r := r) hr.le (zero_lt_one.trans_le hx1)
  dsimp only at hcut
  change centered r x = _ at hcut
  rw [hroot] at hcut
  have h := root_spectral_transform hr v
  dsimp only at h
  change r * s * (-(zeroTail (Real.log y)).re + (r - 1) * w *
      (∫ t in Ioi y, t ^ (-r) * (zeroTail (Real.log t)).re)) = _ at h
  have he := (q_weighted_transport hr hv).1
  have hZ := (weighted_zero_tail hr v).1
  have hz : IntegrableOn (fun t => t ^ (-r) * (zeroTail (Real.log t)).re) (Ioi y) := by
    have hRe := hZ.re
    change IntegrableOn (fun t : ℝ => ((t ^ (-r)) • zeroTail (Real.log t)).re) (Ioi y) at hRe
    simpa only [Complex.real_smul, Complex.re_ofReal_mul] using hRe
  have hsplit : (∫ t in Ioi y, t ^ (-r) * Q t) =
      (∫ t in Ioi y, t ^ (-r) * qError t) -
        (∫ t in Ioi y, t ^ (-r) * (zeroTail (Real.log t)).re) := by
    rw [← integral_sub (f := fun t => t ^ (-r) * qError t)
      (g := fun t => t ^ (-r) * (zeroTail (Real.log t)).re) he hz]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by unfold qError; ring)
  have hdiff : centered r x - rootDensity r (r * v) =
      r * s * (qError y - (r - 1) * w * (∫ t in Ioi y, t ^ (-r) * qError t)) := by
    rw [hcut, ← h, hsplit]
    change _ = r * s * (Q y + (zeroTail (Real.log y)).re - (r - 1) * w *
      (∫ t in Ioi y, t ^ (-r) * qError t))
    linear_combination r * Q y * hscale₁ + r * (r - 1) *
      ((∫ t in Ioi y, t ^ (-r) * qError t) -
        (∫ t in Ioi y, t ^ (-r) * (zeroTail (Real.log t)).re)) * hscale₂
  have hscale : s = Real.exp (-(r * v) / 2) * Real.exp v := by
    dsimp only [s]
    rw [← Real.exp_add]
    congr 1
    ring
  change centered r x - rootDensity r (r * v) = _
  rw [hdiff, hscale, show r * (Real.exp (-(r * v) / 2) * Real.exp v) =
    Real.exp (-(r * v) / 2) * (r * Real.exp v) by ring, mul_assoc]
  rw [(q_weighted_transport hr hv).2]
  unfold trivialRootResponse
  rw [mul_div_cancel_left₀ _ hr0.ne']

private theorem trivial_response_split {m : ℕ} {u : ℝ} (hu : 0 ≤ u) :
    (∑ n ∈ Finset.Icc 2 m, -(μ n : ℝ) *
      (centered (n : ℝ) (Real.exp u) - rootDensity (n : ℝ) u)) =
      -Real.exp (-u/2) * (∑ n ∈ Finset.Icc 2 m, (μ n : ℝ)*trivialRootResponse u n) +
        Real.exp (-u/2)*Real.log (2*Real.pi)*∑ n ∈ Finset.Icc 2 m, (μ n : ℝ) := by
  let E := Real.exp (-u/2)
  let g := trivialRootResponse u
  let l := Real.log (2*Real.pi)
  have hcase (n : ℕ) (hn : n ∈ Finset.Icc 2 m) :
      centered (n : ℝ) (Real.exp u) - rootDensity (n : ℝ) u = E*(g n-l) := by
    have hn₂ := (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have h := root_centered_response hn₂ (v := u/(n : ℝ)) (div_nonneg hu hn0.le)
    rwa [mul_div_cancel₀ _ hn0.ne'] at h
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [hcase n hn]
  ring

theorem trivial_response_signed_bound (hRH : RiemannHypothesis) :
    ∃ D : ℝ, 0 < D ∧ ∀ (m : ℕ) (u : ℝ), 0 ≤ u →
      |∑ n ∈ Finset.Icc 2 m, -(μ n : ℝ) *
        (centered (n : ℝ) (Real.exp u) - rootDensity (n : ℝ) u)| ≤
      D*(m : ℝ)*Real.exp (-u/2) := by
  obtain ⟨C, hC, hM⟩ := moebius_monotone_log_weight_bound hRH
  let l := Real.log (2*Real.pi)
  refine ⟨C + |l|, by positivity, fun m u hu => ?_⟩
  by_cases hm : 2 ≤ m
  · let E := Real.exp (-u/2)
    let g := trivialRootResponse u
    have hsum := trivial_response_split (m := m) hu
    have habs : |∑ n ∈ Finset.Icc 2 m, (μ n : ℝ)| ≤ m := by
      calc
        _ ≤ ∑ n ∈ Finset.Icc 2 m, |(μ n : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _n ∈ Finset.Icc 2 m, (1 : ℝ) := Finset.sum_le_sum fun n _ => by
          exact_mod_cast abs_moebius_le_one (n := n)
        _ ≤ _ := by simp [Nat.card_Icc, nsmul_eq_mul]
    have hE : 0 ≤ E := Real.exp_nonneg _
    have hG := hM m hm g (trivialRootResponse_nonneg _ _) (trivialRootResponse_monotone hu)
      (trivialRootResponse_upper hu _)
    rw [hsum]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg hE]
    exact (add_le_add (mul_le_mul_of_nonneg_left hG hE)
      (mul_le_mul_of_nonneg_left habs (mul_nonneg hE (abs_nonneg _)))).trans_eq (by
      change _ = (C+|l|)*(m : ℝ)*E
      ring)
  · rw [Finset.Icc_eq_empty_of_lt (lt_of_not_ge hm), Finset.sum_empty, abs_zero]
    positivity

private theorem active_moebius_range_abs_le {P : ℝ} (hP : 0 ≤ P) {m n : ℕ} (hn : n ≤ m+1)
    (hprefix : ∀ k ≤ m, |∑ i ∈ Finset.Ioc 0 k, (μ i : ℝ)| ≤ P) :
    |∑ i ∈ Finset.range n, activeMoebius i| ≤ P+1 := by
  cases n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, abs_zero]
    positivity
  | succ k =>
    by_cases hk₂ : 2 ≤ k
    · have hI : insert 1 (Finset.Icc 2 k) = Finset.Ioc 0 k := by
        ext i
        simp only [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Ioc]
        omega
      have hs := active_moebius_range k (fun _ => 1)
      simp only [mul_one] at hs
      have he : (∑ i ∈ Finset.Ioc 0 k, (μ i : ℝ)) =
          1 + ∑ i ∈ Finset.Icc 2 k, (μ i : ℝ) := by
        rw [← hI, Finset.sum_insert (by simp)]
        simp
      rw [hs, show (∑ i ∈ Finset.Icc 2 k, (μ i : ℝ)) =
        (∑ i ∈ Finset.Ioc 0 k, (μ i : ℝ))-1 by linarith only [he]]
      have h := add_le_add (hprefix k (by omega)) (le_refl (1 : ℝ))
      exact (abs_sub _ (1 : ℝ)).trans (by simpa only [abs_one] using h)
    · have hzero : ∀ i ∈ Finset.range (k+1), activeMoebius i = 0 := by
        intro i hi
        have hi' := Finset.mem_range.mp hi
        exact ite_eq_right (by omega)
      rw [Finset.sum_eq_zero hzero, abs_zero]
      positivity

private theorem active_moebius_prefix_sublinear (hRH : RiemannHypothesis) :
    ∀ δ > (0 : ℝ), ∃ M : ℕ, 2 ≤ M ∧ ∀ m ≥ M, ∀ n ≤ m+1,
      |∑ i ∈ Finset.range n, activeMoebius i| ≤ δ * (m : ℝ) / Real.log m := by
  intro δ hδ
  obtain ⟨J, hJ⟩ := moebius_uniform_prefix_log_sublinear_of_rh hRH (δ/2) (by positivity)
  obtain ⟨K, hK⟩ := exists_nat_ge ((4/δ)^2)
  let M := max 2 (max J K)
  refine ⟨M, le_max_left _ _, fun m hm n hn => ?_⟩
  have hm₂ : 2 ≤ m := (le_max_left 2 _).trans hm
  have hm₂' : (2 : ℝ) ≤ m := by exact_mod_cast hm₂
  have hm0 : (0 : ℝ) < m := by linarith
  have hmlog : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
  have hJm : J ≤ m := (le_max_left _ K).trans ((le_max_right 2 _).trans hm)
  have hKm : K ≤ m := (le_max_right J _).trans ((le_max_right 2 _).trans hm)
  have hsmall : Real.log (m : ℝ) ≤ (δ/2) * m := by
    have hroot : 4/δ ≤ Real.sqrt (m : ℝ) := by
      have hx : (4/δ)^2 ≤ (m : ℝ) := hK.trans (by exact_mod_cast hKm)
      simpa only [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 4/δ)] using Real.sqrt_le_sqrt hx
    have hcoef : 2 ≤ (δ/2)*Real.sqrt (m : ℝ) := by
      linarith only [(div_le_iff₀ hδ).mp hroot]
    have hl := Real.log_le_rpow_div hm0.le (show (0 : ℝ) < 1/2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at hl
    refine hl.trans ?_
    have h := mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg (m : ℝ))
    calc
      _ = 2 * Real.sqrt (m : ℝ) := by ring
      _ ≤ _ := h.trans_eq (by rw [mul_assoc, ← pow_two, Real.sq_sqrt hm0.le])
  apply (le_div_iff₀ hmlog).mpr
  have hP : 0 ≤ (δ/2) * (m : ℝ) / Real.log m := by positivity
  have hpref (k : ℕ) (hk : k ≤ m) := (le_div_iff₀ hmlog).mpr (hJ m hJm k hk)
  have hA := active_moebius_range_abs_le hP hn hpref
  calc
    _ ≤ ((δ/2) * (m : ℝ) / Real.log m + 1) * Real.log m :=
      mul_le_mul_of_nonneg_right hA hmlog.le
    _ ≤ _ := by
      rw [add_mul, div_mul_cancel₀ _ hmlog.ne', one_mul]
      linarith only [hsmall]

private theorem trivial_response_of_active_prefix {B : ℝ} (hB : 0 ≤ B) (m : ℕ) {u : ℝ}
    (hu : 0 ≤ u) (hpref : ∀ n ≤ m+1, |∑ i ∈ Finset.range n, activeMoebius i| ≤ B) :
    |∑ n ∈ Finset.Icc 2 m, -(μ n : ℝ) *
      (centered (n : ℝ) (Real.exp u) - rootDensity (n : ℝ) u)| ≤
      (B * (1 + Real.log m + |Real.log (2*Real.pi)|)) * Real.exp (-u/2) := by
  let E := Real.exp (-u/2)
  let l := Real.log (2*Real.pi)
  let g := trivialRootResponse u
  have hG : |∑ n ∈ Finset.Icc 2 m, (μ n : ℝ)*g n| ≤ 2*B*g m := by
    rw [← active_moebius_range]
    exact monotone_finite_abel_bound hB (trivialRootResponse_nonneg _ _)
      (trivialRootResponse_monotone hu) hpref
  have hμ : |∑ n ∈ Finset.Icc 2 m, (μ n : ℝ)| ≤ B := by
    have hsum := active_moebius_range m (fun _ => 1)
    simp only [mul_one] at hsum
    rw [← hsum]
    exact hpref (m+1) le_rfl
  have hcoef : 2 * B * g m + |l| * B ≤ B * (1 + Real.log m + |l|) := by
    have hg := trivialRootResponse_upper hu m
    change g m ≤ (1+Real.log (m : ℝ))/2 at hg
    nlinarith only [mul_le_mul_of_nonneg_left hg hB]
  rw [trivial_response_split (m := m) hu]
  have hE : 0 ≤ E := Real.exp_nonneg _
  refine (abs_add_le _ _).trans ?_
  change |-E * (∑ n ∈ Finset.Icc 2 m, (μ n : ℝ)*g n)| +
    |E*l*(∑ n ∈ Finset.Icc 2 m, (μ n : ℝ))| ≤ _
  rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg hE]
  exact (add_le_add (mul_le_mul_of_nonneg_left hG hE)
    (mul_le_mul_of_nonneg_left hμ (mul_nonneg hE (abs_nonneg _)))).trans
    (by nlinarith only [mul_le_mul_of_nonneg_left hcoef hE])

/-- For large truncation orders, the signed trivial-root response is uniformly sublinear. -/
theorem trivial_response_signed_sublinear (hRH : RiemannHypothesis) :
    ∀ ε > (0 : ℝ), ∃ M : ℕ, 2 ≤ M ∧ ∀ m ≥ M, ∀ u : ℝ, 0 ≤ u →
      |∑ n ∈ Finset.Icc 2 m, -(μ n : ℝ) *
        (centered (n : ℝ) (Real.exp u) - rootDensity (n : ℝ) u)| ≤
      ε * (m : ℝ) * Real.exp (-u/2) := by
  intro ε hε
  let l := Real.log (2*Real.pi)
  let d := Real.log 2
  let C := 1 + (1 + |l|) / d
  have hd : 0 < d := Real.log_pos (by norm_num)
  have hC : 0 < C := by
    dsimp [C]
    exact add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (by positivity) hd.le)
  let δ := ε / C
  have hδ : 0 < δ := div_pos hε hC
  obtain ⟨M, hM₂, hM⟩ := active_moebius_prefix_sublinear hRH δ hδ
  refine ⟨M, hM₂, fun m hm u hu => ?_⟩
  let B := δ * (m : ℝ) / Real.log m
  have hm₂ := hM₂.trans hm
  have hm₂' : (2 : ℝ) ≤ m := by exact_mod_cast hm₂
  have hdlog : d ≤ Real.log (m : ℝ) := Real.log_le_log (by norm_num) hm₂'
  have hlog : 0 < Real.log (m : ℝ) := hd.trans_le hdlog
  have hB : 0 ≤ B := div_nonneg (mul_nonneg hδ.le (Nat.cast_nonneg m)) hlog.le
  have hpref := hM m hm
  have hcoef : B*(1+Real.log (m : ℝ)+|l|) ≤ ε * (m : ℝ) := by
    have hratio := one_div_le_one_div_of_le hd hdlog
    have hmain : 1 + (1 + |l|)/Real.log (m : ℝ) ≤ C := by
      dsimp only [C]
      simp_rw [div_eq_mul_inv, one_mul] at hratio ⊢
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hratio (by positivity))
    calc
      _ = (δ*(m : ℝ)) * (1 + (1+|l|)/Real.log (m : ℝ)) := by
        dsimp only [B]
        field_simp
        ring
      _ ≤ (δ*(m : ℝ)) * C := mul_le_mul_of_nonneg_left hmain (by positivity)
      _ = ε*(m : ℝ) := by dsimp only [δ]; field_simp
  exact (trivial_response_of_active_prefix hB m hu hpref).trans
    (mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _))

/-- The signed trivial-zero response inherits the logarithmic power saving. -/
theorem trivial_response_signed_log_power_saving (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ m → 2 ≤ Real.log m →
      ∀ k ≤ m, ∀ u : ℝ, 0 ≤ u →
        |∑ n ∈ Finset.Icc 2 k, -(μ n : ℝ) *
          (centered (n : ℝ) (Real.exp u) - rootDensity (n : ℝ) u)| ≤
          C * ((m : ℝ) / (Real.log m)^(1/5 : ℝ)) * Real.exp (-u/2) := by
  obtain ⟨D, hD, hprefix⟩ := moebius_uniform_prefix_log_power_saving hRH
  let A := 2 + |Real.log (2*Real.pi)|
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨(D+4)*A, by positivity, fun m hm ht k hk u hu => ?_⟩
  let t := Real.log (m : ℝ)
  let Q := (m : ℝ) / t^(1/5 : ℝ)
  let B := (D+4)*Q/t
  have hm0 : (0 : ℝ) < m := by positivity
  have ht1 : 1 ≤ t := by change 2 ≤ t at ht; linarith
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hB : 0 ≤ B := by dsimp [B, Q]; positivity
  have htp : 0 < t^(1/5 : ℝ) := Real.rpow_pos_of_pos ht0 _
  have hlog := Real.log_le_rpow_div (ε := (1/2 : ℝ)) hm0.le (by norm_num)
  rw [← Real.sqrt_eq_rpow] at hlog
  have hts : t ≤ 2*Real.sqrt (m : ℝ) := by change t ≤ _ at hlog; linarith
  have htpow : t^(1/5 : ℝ) ≤ t := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le ht1
      (by norm_num : (1/5 : ℝ) ≤ 1)
  have hprod : t * t^(1/5 : ℝ) ≤ 4 * (m : ℝ) := by
    calc
      _ ≤ t ^ 2 := (mul_le_mul_of_nonneg_left htpow ht0.le).trans_eq (by ring)
      _ ≤ (2*Real.sqrt (m : ℝ))^2 := pow_le_pow_left₀ ht0.le hts 2
      _ = _ := by rw [mul_pow, Real.sq_sqrt hm0.le]; ring
  have hQfour : t ≤ 4*Q := by
    dsimp only [Q]
    rw [← mul_div_assoc, le_div_iff₀ htp]
    exact hprod
  have hpb (j : ℕ) (hj : j ≤ m) :
      |∑ n ∈ Finset.Ioc 0 j, (μ n : ℝ)| ≤ D*Q/t :=
    (le_div_iff₀ ht0).mpr (hprefix m hm ht j hj)
  have hpref (n : ℕ) (hn : n ≤ k+1) : |∑ i ∈ Finset.range n, activeMoebius i| ≤ B := by
    have h := active_moebius_range_abs_le (by positivity : 0 ≤ D*Q/t)
      (hn.trans (Nat.succ_le_succ hk)) hpb
    apply h.trans
    dsimp only [B]
    apply (le_div_iff₀ ht0).mpr
    rw [add_mul, div_mul_cancel₀ _ ht0.ne', one_mul]
    linarith only [hQfour]
  by_cases hk2 : 2 ≤ k
  · have hk0 : (0 : ℝ) < k := by positivity
    have hklog : Real.log (k : ℝ) ≤ t := Real.log_le_log hk0 (by exact_mod_cast hk)
    have hcoef : 1 + Real.log (k : ℝ) + |Real.log (2*Real.pi)| ≤ A*t := by
      dsimp [A]
      linarith only [hklog, mul_nonneg (abs_nonneg (Real.log (2*Real.pi))) (sub_nonneg.mpr ht1), ht1]
    refine (trivial_response_of_active_prefix hB k hu hpref).trans ?_
    refine mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hcoef hB).trans_eq ?_)
      (Real.exp_nonneg _)
    dsimp only [B, Q]
    field_simp
    rfl
  · rw [Finset.Icc_eq_empty_of_lt (lt_of_not_ge hk2), Finset.sum_empty, abs_zero]
    positivity

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder
