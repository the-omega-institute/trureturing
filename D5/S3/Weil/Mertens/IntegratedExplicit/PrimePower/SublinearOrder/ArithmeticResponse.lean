/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/ArithmeticResponse
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/ArithmeticResponse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed Chebyshev truncation and short-range root response with logarithmic savings. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder.TrivialResponse

/-! Signed finite Abel summation for the arithmetic tail and nearby root response. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open Real ArithmeticFunction Finset Chebyshev MeasureTheory
open Set (Ioi)
open scoped ArithmeticFunction.Moebius
open D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder
private theorem weighted_antitone_finite_abel
    {N : ℕ} {a g : ℕ → ℝ} {q C : ℝ}
    (hg0 : ∀ n, 0 ≤ g n) (hg : Antitone g)
    (ha : ∀ n ≤ N, |∑ i ∈ Finset.range (n+1), a i| ≤ C * (q+n)) :
    |∑ i ∈ Finset.range (N+1), a i*g i| ≤
      C * (q*g 0 + ∑ i ∈ Finset.range N, g (i+1)) := by
  have htel (M : ℕ) :
      (q+M)*g M + ∑ i ∈ Finset.range M, (q+i)*(g i-g (i+1)) =
        q*g 0 + ∑ i ∈ Finset.range M, g (i+1) := by
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp only [Nat.cast_succ]
      linarith only [ih]
  rw [show (∑ i ∈ Finset.range (N+1), a i * g i) =
      (∑ i ∈ Finset.range (N+1), a i) * g N +
        ∑ i ∈ Finset.range N, (∑ j ∈ Finset.range (i+1), a j) * (g i - g (i+1)) from by
      rw [show (∑ i ∈ Finset.range (N+1), a i * g i) =
          (∑ i ∈ Finset.range (N+1), a i) * g N -
            ∑ i ∈ Finset.range N, (∑ j ∈ Finset.range (i+1), a j) * (g (i+1) - g i) from
          by simpa only [Nat.add_sub_cancel, smul_eq_mul] using Finset.sum_range_by_parts' a g (N+1)]
      rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
      exact congrArg (_ + ·) (Finset.sum_congr rfl (fun _ _ => by ring))]
  calc
    _ ≤ |(∑ i ∈ Finset.range (N+1), a i) * g N| +
        |∑ i ∈ Finset.range N, (∑ j ∈ Finset.range (i+1), a j) * (g i - g (i+1))| :=
      abs_add_le _ _
    _ ≤ C*(q+N)*g N + ∑ i ∈ Finset.range N, C*(q+i)*(g i-g (i+1)) := by
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg (hg0 _)]
        exact mul_le_mul_of_nonneg_right (ha _ le_rfl) (hg0 _)
      · apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro i hi
        have hd : 0 ≤ g i-g (i+1) := sub_nonneg.mpr (hg (Nat.le_succ _))
        rw [abs_mul, abs_of_nonneg hd]
        exact mul_le_mul_of_nonneg_right (ha i (Finset.mem_range.mp hi).le) hd
    _ = _ := by
      rw [← htel, mul_add C ((q + (N : ℝ))*g N), Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl (fun _ _ => by ring)

private theorem interval_moebius_prefix_le_of_log_saving {D : ℝ} (hD : 0 ≤ D)
    (hM : ∀ M : ℕ, 2 ≤ M →
      |∑ n ∈ Finset.Ioc 0 M, (μ n : ℝ)| * Real.log M ≤ D*(M : ℝ))
    {q j : ℕ} (hq : 3 ≤ q) :
    |∑ i ∈ Finset.range (j+1), (μ (q+i) : ℝ)| ≤
      (3*D / Real.log q) * ((q : ℝ)+j) := by
  have hq₂ : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hq₀ : (0 : ℝ) < q := by linarith
  have hp₂ : 2 ≤ q-1 := by omega
  have hp₀ : (0 : ℝ) < (q-1 : ℕ) := by exact_mod_cast (show 0 < q-1 by omega)
  have hqlog := Real.log_pos (show (1 : ℝ) < q by linarith)
  have hsub : (∑ i ∈ Finset.range (j+1), (μ (q+i) : ℝ)) =
      (∑ i ∈ Finset.Ioc 0 (q+j), (μ i : ℝ)) - ∑ i ∈ Finset.Ioc 0 (q-1), (μ i : ℝ) := by
    have hsplit : (∑ i ∈ Finset.Ioc 0 (q-1), (μ i : ℝ)) +
        ∑ i ∈ Finset.Ioc (q-1) (q+j), (μ i : ℝ) =
          ∑ i ∈ Finset.Ioc 0 (q+j), (μ i : ℝ) :=
      Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (by omega)
    have hshift : (∑ i ∈ Finset.range (j+1), (μ (q+i) : ℝ)) =
        ∑ i ∈ Finset.Ioc (q-1) (q+j), (μ i : ℝ) := by
      apply Finset.sum_bij (fun i _ => q+i)
      · intro i hi
        exact Finset.mem_Ioc.mpr ⟨by omega, by have := Finset.mem_range.mp hi; omega⟩
      · intro i hi k hk h
        omega
      · intro i hi
        obtain ⟨hil, hir⟩ := Finset.mem_Ioc.mp hi
        exact ⟨i-q, Finset.mem_range.mpr (by omega), by omega⟩
      · intro i hi
        rfl
    linarith
  have hqj : (q : ℝ) ≤ (q+j : ℕ) := by exact_mod_cast Nat.le_add_right q j
  have hMlarge : |∑ n ∈ Finset.Ioc 0 (q+j), (μ n : ℝ)| ≤
      D*(q+j : ℕ)/Real.log q := by
    apply (le_div_iff₀ hqlog).mpr
    exact (mul_le_mul_of_nonneg_left (Real.log_le_log hq₀ hqj) (abs_nonneg _)).trans
      (hM _ (by omega))
  have hMsmall : |∑ n ∈ Finset.Ioc 0 (q-1), (μ n : ℝ)| ≤
      2*D*(q : ℝ)/Real.log q := by
    have hsq : (q : ℝ) ≤ ((q-1 : ℕ) : ℝ)^2 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
      have hq₃ : (3 : ℝ) ≤ q := by exact_mod_cast hq
      nlinarith only [sq_nonneg ((q : ℝ)-3), hq₃]
    have hlogrel := Real.log_le_log hq₀ hsq
    rw [Real.log_pow] at hlogrel
    norm_num at hlogrel
    apply (le_div_iff₀ hqlog).mpr
    have h := mul_le_mul_of_nonneg_left hlogrel
      (abs_nonneg (∑ n ∈ Finset.Ioc 0 (q-1), (μ n : ℝ)))
    have hpq : ((q-1 : ℕ) : ℝ) ≤ q := by exact_mod_cast Nat.sub_le q 1
    have hb := hM (q-1) hp₂
    nlinarith only [h, hb, mul_le_mul_of_nonneg_left hpq hD]
  rw [hsub]
  apply (abs_sub _ _).trans
  have hqj' : (q : ℝ) ≤ (q : ℝ)+j := le_add_of_nonneg_right (Nat.cast_nonneg j)
  apply (add_le_add hMlarge hMsmall).trans
  push_cast
  rw [← add_div, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (by nlinarith only [mul_le_mul_of_nonneg_left hqj' hD]) hqlog.le



private theorem chebyshev_signed_tail_one_log (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), 2 ≤ m → ∀ t ≥ (2 : ℝ),
      |Chebyshev.theta t - Chebyshev.psi t - ∑ d ∈ Icc 2 m, (μ d : ℝ) *
        Chebyshev.psi (t ^ (1 / (d : ℝ)))| ≤
      C * (((m+1 : ℕ) : ℝ) / Real.log ((m+1 : ℕ) : ℝ)) * t ^ (1 / (m+1 : ℝ)) := by
  obtain ⟨D, hD, hM⟩ := moebius_log_saving_of_rh hRH
  let P : ℝ := (Real.log 4 + 4)*2
  let J : ℝ := 2+1/Real.log 2
  have hP : 0 < P := by dsimp [P]; positivity
  have hJ : 0 < J := by dsimp [J]; positivity
  refine ⟨3*D*P*J, by positivity, fun m hm t ht => ?_⟩
  let q := m+1
  let R := max m ⌊Real.log t/Real.log 2⌋₊
  let g (i : ℕ) := Chebyshev.psi (t ^ (1/((q+i : ℕ) : ℝ)))
  let a (i : ℕ) := (μ (q+i) : ℝ)
  let b : ℝ := (2 : ℝ)^(-(1/(q : ℝ)))
  let x := t^(1/(q : ℝ))
  have hq : 3 ≤ q := by dsimp [q]; omega
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast (show 0 < q from by omega)
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q from by omega)
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hDq : 0 ≤ 3*D/Real.log (q : ℝ) := div_nonneg (by positivity) hlog.le
  have hxp : 0 ≤ x := by dsimp [x]; positivity
  have hb₀ : 0 ≤ b := by dsimp [b]; positivity
  have hb₁ : b < 1 := by
    dsimp [b]
    exact rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos (by positivity))
  have he : Chebyshev.theta t - Chebyshev.psi t -
      ∑ d ∈ Icc 2 m, (μ d : ℝ) * Chebyshev.psi (t ^ (1 / (d : ℝ))) =
      ∑ d ∈ Icc q R, (μ d : ℝ) * Chebyshev.psi (t ^ (1 / (d : ℝ))) := by
    rw [chebyshev_mobius_cutoff ht (show ⌊Real.log t/Real.log 2⌋₊ ≤ R from le_max_right _ _)]
    have hsplit : (∑ d ∈ Icc 2 m, (μ d : ℝ) * Chebyshev.psi (t ^ (1 / (d : ℝ)))) +
        ∑ d ∈ Icc q R, (μ d : ℝ) * Chebyshev.psi (t ^ (1 / (d : ℝ))) =
          ∑ d ∈ Icc 2 R, (μ d : ℝ) * Chebyshev.psi (t ^ (1 / (d : ℝ))) := by
      dsimp [q]
      simp only [← Ico_add_one_right_eq_Icc]
      exact sum_Ico_consecutive _ (by omega) (Nat.succ_le_succ (le_max_left _ _))
    linarith
  rw [he]
  by_cases hr : q ≤ R
  · let N := R-q
    have hshift : (∑ d ∈ Icc q R, (μ d : ℝ) * Chebyshev.psi (t ^ (1 / (d : ℝ)))) =
        ∑ i ∈ range (N+1), a i*g i := by
      symm
      apply Finset.sum_bij (fun i _ => q+i)
      · intro i hi
        have ht := Finset.mem_range.mp hi
        exact Finset.mem_Icc.mpr ⟨by omega, by dsimp [N] at ht; omega⟩
      · intro i hi j hj hij
        omega
      · intro d hd
        obtain ⟨hl, hh⟩ := Finset.mem_Icc.mp hd
        exact ⟨d-q, Finset.mem_range.mpr (by dsimp [N]; omega), by omega⟩
      · intro i hi
        rfl
    have hg0 (i : ℕ) : 0 ≤ g i := Chebyshev.psi_nonneg _
    have hg : Antitone g := by
      intro i j hij
      apply Chebyshev.psi_mono
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      exact one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.add_le_add_left hij q)
    have hg_le (i : ℕ) : g i ≤ (P*x) * b^i := by
      have h := psi_root_geometric (show 1 ≤ t by linarith) (show 0 < q by omega)
        (Nat.le_add_right q i)
      change g i ≤ P*b^(q+i)*x at h
      have hh := pow_le_pow_left₀ hb₀ (show b ≤ 1 from hb₁.le) q
      simp only [one_pow] at hh
      rw [pow_add] at h
      apply h.trans
      have hbpos := pow_nonneg hb₀ i
      have hPx := mul_nonneg hP.le hxp
      nlinarith only [mul_nonneg hPx (mul_nonneg (sub_nonneg.mpr hh) hbpos)]
    have hg_head : g 0 ≤ P*x := by simpa using hg_le 0
    have hg_tail : ∑ i ∈ range N, g (i+1) ≤ (P*x) * (1+(q : ℝ)/Real.log 2) := by
      have hpoint : ∀ i ∈ range N, g (i+1) ≤ (P*x)*b^i := by
        intro i hi
        apply (hg_le (i+1)).trans
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_left
          (mul_le_of_le_one_right (pow_nonneg hb₀ i) hb₁.le) (mul_nonneg hP.le hxp)
      refine (Finset.sum_le_sum hpoint).trans ?_
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hP.le hxp)
      have hgeom := (summable_geometric_of_lt_one hb₀ hb₁).sum_le_tsum
        (range N) (fun i _ => pow_nonneg hb₀ i)
      rw [tsum_geometric_of_lt_one hb₀ hb₁] at hgeom
      exact hgeom.trans (geometric_root_factor (show 0 < q by omega))
    rw [hshift]
    have hA := weighted_antitone_finite_abel hg0 hg
      (a := a) (N := N) (q := (q : ℝ))
      (fun i _ => interval_moebius_prefix_le_of_log_saving hD.le hM (j := i) hq)
    calc
      _ ≤ (3*D/Real.log (q : ℝ)) * ((q : ℝ)*g 0 + ∑ i ∈ range N, g (i+1)) := hA
      _ ≤ (3*D/Real.log (q : ℝ)) * ((P*x) * ((q : ℝ)*J)) := by
        apply mul_le_mul_of_nonneg_left _ hDq
        have hdiff : (q : ℝ) + (1+(q : ℝ)/Real.log 2) ≤ (q : ℝ)*J := by
          dsimp [J]
          simp only [div_eq_mul_inv, one_mul]
          linarith only [hq₁]
        exact (add_le_add (mul_le_mul_of_nonneg_left hg_head hq₀.le) hg_tail).trans (by
          have h := mul_le_mul_of_nonneg_left hdiff (mul_nonneg hP.le hxp)
          linarith only [h])
      _ = _ := by
        have hx : t ^ (1/(m+1 : ℝ)) = x := by simp [x, q]
        rw [hx]
        ring
  · rw [Finset.Icc_eq_empty_of_lt (lt_of_not_ge hr), Finset.sum_empty, abs_zero]
    positivity

open MeasureTheory Set
open D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

theorem normalized_mobius_tail_one_log (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ m → ∀ u : ℝ, 2 ≤ Real.exp u →
      |Real.sqrt (Real.exp u) * (primeTail (Real.exp u) - Q (Real.exp u)) -
        ∑ n ∈ Finset.Icc 2 m, (μ n : ℝ) * (Real.sqrt (Real.exp u) *
          (∫ t in Ioi (Real.exp u), psi (t ^ (n : ℝ)⁻¹) / t ^ 2))| ≤
        C * ((m : ℝ) / Real.log ((m : ℝ) + 1)) *
          Real.exp (-(orderRate m) * u) := by
  obtain ⟨C, hC, hpoint⟩ := chebyshev_signed_tail_one_log hRH
  refine ⟨4 * C, by positivity, fun m hm u hx => ?_⟩
  simp only [Nat.cast_add, Nat.cast_one] at hpoint
  let p : ℝ := 1 / (m + 1 : ℝ)
  let x := Real.exp u
  let c := C * ((m + 1 : ℝ) / Real.log (m + 1 : ℝ))
  have h := integrated_mobius_of_pointwise hm hx (C := c) (fun t ht => hpoint m hm t (hx.trans ht.le))
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : 0 < Real.log (m + 1 : ℝ) := Real.log_pos (by linarith)
  have hp : p ≤ 1 / 2 := by
    dsimp [p]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hcoef : c / (1 - p) ≤ 4 * C * ((m : ℝ) / Real.log (m + 1 : ℝ)) := by
    have hc : 0 ≤ c := by dsimp [c]; positivity
    calc
      _ ≤ 2 * c := by
        apply (div_le_iff₀ (by linarith : 0 < 1 - p)).mpr
        nlinarith only [mul_nonneg hc (sub_nonneg.mpr hp)]
      _ ≤ _ := by
        dsimp only [c]
        simp only [mul_div_assoc', mul_assoc]
        apply div_le_div_of_nonneg_right _ hlog.le
        nlinarith only [mul_nonneg hC.le (show 0 ≤ (m : ℝ) - 1 by linarith)]
  change |Real.sqrt x * (primeTail x - Q x) -
      ∑ n ∈ Finset.Icc 2 m, (μ n : ℝ) * (Real.sqrt x *
        (∫ t in Ioi x, psi (t ^ (n : ℝ)⁻¹) / t ^ 2))| ≤ _
  change |Real.sqrt x * (primeTail x - Q x - ∑ n ∈ Finset.Icc 2 m, (μ n : ℝ) *
    (∫ t in Ioi x, psi (t ^ (1 / (n : ℝ))) / t ^ 2))| ≤ c / (1 - p) * x ^ (p - 1 / 2) at h
  rw [mul_sub, Finset.mul_sum] at h
  simp only [one_div, mul_left_comm (Real.sqrt x)] at h
  have hpower : x ^ (p - 1 / 2) = Real.exp (-(orderRate m) * u) := by
    dsimp [x, p, orderRate]
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, hpower] at h
  exact h.trans (mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _))



private theorem sum_moebius_antitone_Icc_bound {m p : ℕ} (hp : 1 ≤ p) (hpm : p ≤ m)
    {g : ℕ → ℝ} (hg0 : ∀ n, 0 ≤ g n) (hg : Antitone g)
    {D : ℝ} (hprefix : ∀ k ≤ m, |∑ n ∈ Ioc 0 k, (μ n : ℝ)| ≤ D) :
    |∑ n ∈ Icc p m, (μ n : ℝ) * g n| ≤ 2 * D * g p := by
  have hI : Finset.Icc p m = Finset.Ioc (p-1) m := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hI]
  have h := abs_sum_mul_antitone_Ioc_le (a := fun n => (μ n : ℝ)) (w := g) (B := D)
    (m := p-1) (N := m) (by omega) (by
      intro k hk
      have hset : Finset.range (k+1) = insert 0 (Finset.Ioc 0 k) := by
        ext n
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
        omega
      rw [hset, Finset.sum_insert (by simp), ArithmeticFunction.map_zero, Int.cast_zero, zero_add]
      exact hprefix k hk)
    (fun _ _ => hg0 _) (hg.antitoneOn _)
  simpa only [Nat.sub_add_cancel hp] using h

open MeasureTheory Chebyshev
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower (root_kernel_integrable root_tail_main normalized_tail_bound)

private theorem bounded_centered_response {x : ℝ} (hx : 1 ≤ x)
    {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ Real.sqrt x * (∫ t in Ioi x, ψ (t ^ (n : ℝ)⁻¹) / t ^ 2) ∧
      Real.sqrt x * (∫ t in Ioi x, ψ (t ^ (n : ℝ)⁻¹) / t ^ 2) ≤
        (2 * (Real.log 4 + 4)) * x ^ ((n : ℝ)⁻¹ - 1/2) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hP : (n : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hn'
  norm_num at hP
  have hI := root_kernel_integrable (hP.trans_lt (by norm_num)) hx0
  have h0 : 0 ≤ Real.sqrt x * (∫ t in Ioi x, ψ (t ^ (n : ℝ)⁻¹) / t ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (integral_nonneg fun t => div_nonneg (psi_nonneg _) (sq_nonneg _))
  have h := normalized_tail_bound hx0 (hP.trans_lt (by norm_num)) hI.aestronglyMeasurable
    (g := fun t => ψ (t ^ (n : ℝ)⁻¹)) (fun t ht => by
      rw [abs_of_nonneg (psi_nonneg _)]
      exact psi_le_const_mul_self (rpow_nonneg (hx0.trans ht).le _))
  rw [abs_of_nonneg h0] at h
  refine ⟨h0, h.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (rpow_nonneg hx0.le _)
  apply (div_le_iff₀ (by linarith : 0 < 1 - (n : ℝ)⁻¹)).mpr
  have hK : 0 ≤ Real.log 4 + 4 := by positivity
  nlinarith only [mul_nonneg hK (show 0 ≤ 1 - 2 * (n : ℝ)⁻¹ by linarith)]

private theorem uncentered_response_antitone {x : ℝ} (hx : 1 ≤ x)
    {n k : ℕ} (hn : 2 ≤ n) (hnk : n ≤ k) :
    Real.sqrt x * (∫ t in Ioi x, ψ (t ^ (k : ℝ)⁻¹) / t ^ 2) ≤
      Real.sqrt x * (∫ t in Ioi x, ψ (t ^ (n : ℝ)⁻¹) / t ^ 2) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hnk' : (n : ℝ) ≤ k := by exact_mod_cast hnk
  have hp := inv_anti₀ (zero_lt_one.trans hn') hnk'
  have hnI := (inv_lt_one₀ (zero_lt_one.trans hn')).mpr hn'
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply setIntegral_mono_on (root_kernel_integrable (hp.trans_lt hnI) hx0)
    (root_kernel_integrable hnI hx0) measurableSet_Ioi
  intro t ht
  exact div_le_div_of_nonneg_right
    (psi_mono (rpow_le_rpow_of_exponent_le (hx.trans (show x < t from ht).le) hp)) (sq_nonneg _)

private theorem uncentered_main_antitone {x : ℝ} (hx : 1 ≤ x)
    {n k : ℕ} (hn : 2 ≤ n) (hnk : n ≤ k) :
    (k : ℝ) / ((k : ℝ)-1) * x ^ ((k : ℝ)⁻¹ - 1/2) ≤
      (n : ℝ) / ((n : ℝ)-1) * x ^ ((n : ℝ)⁻¹ - 1/2) := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hnk' : (n : ℝ) ≤ k := by exact_mod_cast hnk
  have hk' := hn'.trans_le hnk'
  have hcoef : (k : ℝ) / ((k : ℝ)-1) ≤ (n : ℝ) / ((n : ℝ)-1) := by
    apply (div_le_div_iff₀ (by linarith : 0 < (k : ℝ)-1) (by linarith : 0 < (n : ℝ)-1)).mpr
    nlinarith only [hnk']
  have hp := inv_anti₀ (zero_lt_one.trans hn') hnk'
  exact mul_le_mul hcoef (rpow_le_rpow_of_exponent_le hx (sub_le_sub_right hp _))
    (rpow_nonneg (by linarith) _) (by positivity)

theorem omitted_centered_near_moebius_bound (hRH : RiemannHypothesis) {L : ℝ} (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m p : ℕ) (u : ℝ), 2 ≤ p → p ≤ m → m+1 ≤ 2*p →
      0 ≤ u → u ≤ L * ((m : ℝ)+1) →
      |∑ n ∈ Icc p m, (μ n : ℝ) * (Real.sqrt (Real.exp u) *
        (∫ t in Ioi (Real.exp u), (ψ (t ^ (n : ℝ)⁻¹) - t ^ (n : ℝ)⁻¹) / t ^ 2))| ≤
        C * ((m : ℝ) / Real.log (m : ℝ)) * Real.exp (-u/2) := by
  obtain ⟨D, hD, hpre⟩ := moebius_uniform_prefix_log_saving hRH
  let K : ℝ := 2 * (Real.log 4+4)
  refine ⟨2*D*(K+2)*Real.exp (2*L), by dsimp [K]; positivity, ?_⟩
  intro m p u hp hpm hhalf hu huL
  let x := Real.exp u
  let P (n : ℕ) := (n : ℝ) / ((n : ℝ)-1) * x ^ ((n : ℝ)⁻¹ - 1/2)
  let T (n : ℕ) := Real.sqrt x * (∫ t in Ioi x, ψ (t ^ (n : ℝ)⁻¹) / t ^ 2)
  let F (n : ℕ) := Real.sqrt x * (∫ t in Ioi x, (ψ (t ^ (n : ℝ)⁻¹) - t ^ (n : ℝ)⁻¹) / t ^ 2)
  let H := D * (m : ℝ) / Real.log (m : ℝ)
  have hx : 1 ≤ x := Real.one_le_exp_iff.mpr hu
  have hm : 2 ≤ m := hp.trans hpm
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : 0 < Real.log m := Real.log_pos (by linarith)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hpre' (k : ℕ) (hk : k ≤ m) : |∑ n ∈ Ioc 0 k, (μ n : ℝ)| ≤ H :=
    (le_div_iff₀ hlog).mpr (hpre m hm k hk)
  have hTa : Antitone (fun n => T (max p n)) := by
    intro i j hij
    exact uncentered_response_antitone hx (hp.trans (le_max_left _ _))
      (max_le_max_left p hij)
  have hPa : Antitone (fun n => P (max p n)) := by
    intro i j hij
    exact uncentered_main_antitone hx (hp.trans (le_max_left _ _))
      (max_le_max_left p hij)
  have hT0 (n : ℕ) : 0 ≤ T (max p n) :=
    (bounded_centered_response hx (hp.trans (le_max_left _ _))).1
  have hP0 (n : ℕ) : 0 ≤ P (max p n) := by
    have h : (2 : ℝ) ≤ max p n := by exact_mod_cast hp.trans (le_max_left p n)
    dsimp [P]
    exact mul_nonneg (div_nonneg (by linarith) (by linarith)) (rpow_nonneg (by linarith) _)
  have hT := sum_moebius_antitone_Icc_bound (show 1 ≤ p by omega) hpm hT0 hTa hpre'
  have hP := sum_moebius_antitone_Icc_bound (show 1 ≤ p by omega) hpm hP0 hPa hpre'
  rw [max_self] at hT hP
  have hTsum : (∑ n ∈ Icc p m, (μ n : ℝ) * T (max p n)) =
      ∑ n ∈ Icc p m, (μ n : ℝ) * T n :=
    Finset.sum_congr rfl fun n hn => by rw [max_eq_right (Finset.mem_Icc.mp hn).1]
  have hPsum : (∑ n ∈ Icc p m, (μ n : ℝ) * P (max p n)) =
      ∑ n ∈ Icc p m, (μ n : ℝ) * P n :=
    Finset.sum_congr rfl fun n hn => by rw [max_eq_right (Finset.mem_Icc.mp hn).1]
  rw [hTsum] at hT
  rw [hPsum] at hP
  have hf : (∑ n ∈ Icc p m, (μ n : ℝ) * F n) =
      (∑ n ∈ Icc p m, (μ n : ℝ) * T n) - ∑ n ∈ Icc p m, (μ n : ℝ) * P n := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hn1 : (1 : ℝ) < n := by
      exact_mod_cast (show 1 < n by have := (Finset.mem_Icc.mp hn).1; omega)
    have he : T n = P n + F n := root_tail_main hn1 (zero_lt_one.trans_le hx)
    rw [he]
    ring
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hhalf' : (m : ℝ)+1 ≤ 2*(p : ℝ) := by exact_mod_cast hhalf
  have hu' : u / (p : ℝ) ≤ 2*L := by
    apply (div_le_iff₀ (by linarith : 0 < (p : ℝ))).mpr
    exact huL.trans ((mul_le_mul_of_nonneg_left hhalf' hL).trans_eq (by ring))
  have hpower : x ^ ((p : ℝ)⁻¹ - 1/2) ≤ Real.exp (2*L) * Real.exp (-u/2) := by
    dsimp [x]
    rw [← Real.exp_mul, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by rw [div_eq_mul_inv] at hu'; nlinarith only [hu'])
  have hTval : T p ≤ K * (Real.exp (2*L) * Real.exp (-u/2)) :=
    (bounded_centered_response hx hp).2.trans (mul_le_mul_of_nonneg_left hpower (show 0 ≤ K by dsimp [K]; positivity))
  have hPval : P p ≤ 2 * (Real.exp (2*L) * Real.exp (-u/2)) := by
    dsimp [P]
    have hpp : 0 < (p : ℝ)-1 := by linarith
    apply mul_le_mul ((div_le_iff₀ hpp).mpr (by linarith)) hpower (rpow_nonneg (by linarith) _) (by norm_num)
  change |∑ n ∈ Icc p m, (μ n : ℝ)*F n| ≤ _
  rw [hf]
  refine (abs_sub _ _).trans ((add_le_add hT hP).trans ?_)
  calc
    _ ≤ 2*H * (K * (Real.exp (2*L)*Real.exp (-u/2))) +
        2*H * (2 * (Real.exp (2*L)*Real.exp (-u/2))) :=
      add_le_add (mul_le_mul_of_nonneg_left hTval (by positivity))
        (mul_le_mul_of_nonneg_left hPval (by positivity))
    _ = _ := by dsimp [H]; ring



end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
