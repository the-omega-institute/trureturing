/- GID: D5/S3/Weil/ZetaPntBounds/ZetaBoundsDerivative
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaPntBounds/ZetaBoundsDerivative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Port the zeta and derivative upper bounds. -/

/- Ported from anthropics/zeta-23-lean commit 3635e74826a4c1fcece7d1cd2b6fa75e43a00510.
   Modified by trureturing on 2026-08-14: repository routing and module splitting. -/
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/ZetaBounds.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
blueprint_comment blocks, @[blueprint ...] attributes), redirected intra-project
imports to routed D5.S3.Weil modules, and added a (name := ...) tag to local notation.
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/
import D5.S3.Weil.ZetaPntBounds.ZetaBoundsUpper

set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta
local notation (name := riemannzeta0) "ζ₀" => riemannZeta0

lemma ZetaBnd_aux2 {n : ℕ} {t A σ : ℝ} (Apos : 0 < A) (σpos : 0 < σ) (n_le_t : n ≤ |t|)
    (σ_ge : (1 : ℝ) - A / Real.log |t| ≤ σ) :
    ‖(n : ℂ) ^ (-(σ + t * I))‖ ≤ (n : ℝ)⁻¹ * Real.exp A := by
  set s := σ + t * I
  by_cases n0 : n = 0
  · simp_rw [n0, CharP.cast_eq_zero, inv_zero, zero_mul]
    rw [Complex.zero_cpow ?_]
    · simp
    · exact fun h ↦ σpos.ne' <| zero_eq_neg.mp <| zero_re ▸ h ▸ (by simp [s])
  have n_gt_0 : 0 < n := Nat.pos_of_ne_zero n0
  have n_gt_0' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr n_gt_0
  have n_ge_1 : 1 ≤ (n : ℝ) := Nat.one_le_cast.mpr <| Nat.succ_le_of_lt n_gt_0
  calc
    _ = |((n : ℝ) ^ (-σ))| := ?_
    _ ≤ Real.exp (Real.log n * -σ) := Real.abs_rpow_le_exp_log_mul (n : ℝ) (-σ)
    _ ≤ Real.exp (Real.log n *  -(1 - A / Real.log t)) := ?_
    _ ≤ Real.exp (- Real.log n + A) := Real.exp_le_exp_of_le ?_
    _ ≤ _ := by rw [Real.exp_add, Real.exp_neg, Real.exp_log n_gt_0']
  · have : ‖(n : ℂ) ^ (-s)‖ = n ^ (-s.re) := norm_cpow_eq_rpow_re_of_pos n_gt_0' (-s)
    rw [this, abs_eq_self.mpr <| Real.rpow_nonneg n_gt_0'.le _]; simp [s]
  · apply Real.exp_le_exp_of_le <| mul_le_mul_of_nonneg_left _ <| Real.log_nonneg n_ge_1
    rw [neg_sub, neg_le_sub_iff_le_add, add_comm, ← Real.log_abs]; linarith
  · simp only [neg_sub, le_neg_add_iff_add_le]
    ring_nf
    conv => rw [mul_comm, ← mul_assoc, ← Real.log_abs]; rhs; rw [← one_mul A]
    gcongr
    by_cases ht1 : |t| = 1
    · simp [ht1]
    apply (inv_mul_le_iff₀ ?_).mpr
    · convert! Real.log_le_log n_gt_0' n_le_t using 1; rw [mul_one]
    · exact Real.log_pos <| lt_of_le_of_ne (le_trans n_ge_1 n_le_t) <| fun t ↦ ht1 (t.symm)

lemma logt_gt_one {t : ℝ} (t_ge : 3 ≤ t) : 1 < Real.log t :=
  (Real.lt_log_iff_exp_lt (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])

lemma UpperBnd_aux {A σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
    (σ_ge : 1 - A / Real.log |t| ≤ σ) :
    let N := ⌊|t|⌋₊;
    0 < N ∧ N ≤ |t| ∧ 1 < Real.log |t| ∧ 1 - A < σ ∧ 0 < σ ∧ σ + t * I ≠ 1 := by
  intro N
  have Npos : 0 < N := Nat.floor_pos.mpr (by linarith)
  have N_le_t : N ≤ |t| := Nat.floor_le <| abs_nonneg _
  have logt_gt := logt_gt_one t_gt.le
  have σ_gt : 1 - A < σ := by
    apply lt_of_lt_of_le ((sub_lt_sub_iff_left (a := 1)).mpr ?_) σ_ge
    exact (div_lt_iff₀ (by linarith)).mpr <| lt_mul_right hA.1 logt_gt
  refine ⟨Npos, N_le_t, logt_gt, σ_gt, by linarith [hA.2], ?_⟩
  contrapose! t_gt
  simp only [Complex.ext_iff, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, one_re, add_im, mul_im, zero_add, one_im] at t_gt
  norm_num [t_gt.2]

lemma UpperBnd_aux2 {A σ t : ℝ} (t_ge : 3 < |t|) (σ_ge : 1 - A / Real.log |t| ≤ σ) :
      |t| ^ (1 - σ) ≤ Real.exp A := by
  have : |t| ^ (1 - σ) ≤ |t| ^ (A / Real.log |t|) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  apply le_trans this ?_
  conv => lhs; lhs; rw [← Real.exp_log (by linarith : 0 < |t|)]
  rw [div_eq_mul_inv, Real.rpow_mul (by positivity), ← Real.exp_mul, ← Real.exp_mul, mul_comm,
    ← mul_assoc, inv_mul_cancel₀, one_mul]
  apply Real.log_ne_zero.mpr; split_ands <;> linarith

lemma riemannZeta0_zero_aux (N : ℕ) (Npos : 0 < N) :
    ∑ x ∈ Finset.Ico 0 N, ((x : ℝ))⁻¹ = ∑ x ∈ Finset.Ico 1 N, ((x : ℝ))⁻¹ := by
  have : Finset.Ico 1 N ⊆ Finset.Ico 0 N := by
    intro x hx
    simp only [Finset.mem_Ico, Nat.Ico_zero_eq_range, Finset.mem_range] at hx ⊢
    exact hx.2
  rw [← Finset.sum_sdiff (s₁ := Finset.Ico 1 N) (s₂ := Finset.Ico 0 N) this]
  have : Finset.Ico 0 N \ Finset.Ico 1 N = Finset.range 1 := by
    ext a
    simp only [Nat.Ico_zero_eq_range, Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico, not_and,
      not_lt, Finset.range_one, Finset.mem_singleton]
    exact ⟨fun _ ↦ by omega, fun ha ↦ ⟨by simp [ha, Npos], by omega⟩⟩
  rw [this]; simp

lemma UpperBnd_aux3 {A C σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2))
    (σ_ge : 1 - A / Real.log |t| ≤ σ) (t_gt : 3 < |t|) (hC : 2 ≤ C) : let N := ⌊|t|⌋₊;
    ‖∑ n ∈ Finset.range (N + 1), (n : ℂ) ^ (-(σ + t * I))‖ ≤
      Real.exp A * C * Real.log |t| := by
  intro N
  obtain ⟨Npos, N_le_t, _, _, σPos, _⟩ := UpperBnd_aux hA t_gt σ_ge
  have logt_gt := logt_gt_one t_gt.le
  have (n : ℕ) (hn : n ∈ Finset.range (N + 1)) := ZetaBnd_aux2 (n := n) hA.1 σPos ?_ σ_ge
  · replace := norm_sum_le_of_le (Finset.range (N + 1)) this
    rw [← Finset.sum_mul, mul_comm _ (Real.exp A)] at this
    rw [mul_assoc]
    apply le_trans this <| (mul_le_mul_iff_right₀ A.exp_pos).mpr ?_
    have : 1 + Real.log (N : ℝ) ≤ C * Real.log |t| := by
      by_cases hN : N = 1
      · simp only [hN, Nat.cast_one, Real.log_one, add_zero]
        have : 2 * 1 ≤ C * Real.log |t| := mul_le_mul hC logt_gt.le (by linarith) (by linarith)
        linarith
      · rw [(by ring : C * Real.log |t| = Real.log |t| + (C - 1) * Real.log |t|),
          ← one_mul <| Real.log (N: ℝ)]
        apply add_le_add logt_gt.le
        refine mul_le_mul (by linarith) ?_ (by positivity) (by linarith)
        exact Real.log_le_log (by positivity) N_le_t
    refine le_trans ?_ this
    convert! harmonic_eq_sum_Icc ▸ harmonic_le_one_add_log N
    · simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Finset.range_eq_Ico]
      rw [riemannZeta0_zero_aux (N + 1) (by linarith)]; congr! 1
  · simp only [Finset.mem_range] at hn
    linarith [(by exact_mod_cast (by omega : n ≤ N) : (n : ℝ) ≤ N)]

lemma Nat.self_div_floor_bound {t : ℝ} (t_ge : 1 ≤ |t|) : let N := ⌊|t|⌋₊;
    (|t| / N) ∈ Icc 1 2 := by
  intro N
  have Npos : 0 < N := Nat.floor_pos.mpr (by linarith)
  have N_le_t : N ≤ |t| := Nat.floor_le <| abs_nonneg _
  constructor
  · apply le_div_iff₀ (by simp [Npos]) |>.mpr; simp [N_le_t]
  · apply div_le_iff₀ (by positivity) |>.mpr
    suffices |t| < N + 1 by linarith [(by exact_mod_cast (by omega) : 1 ≤ (N : ℝ))]
    apply Nat.lt_floor_add_one

lemma UpperBnd_aux5 {σ t : ℝ} (t_ge : 3 < |t|) (σ_le : σ ≤ 2) : (|t| / ⌊|t|⌋₊) ^ σ ≤ 4 := by
  obtain ⟨h₁, h₂⟩ := Nat.self_div_floor_bound (by linarith)
  calc _ ≤ ((|t| / ↑⌊|t|⌋₊) ^ (2 : ℝ)) := by gcongr
       _ ≤ (2 : ℝ) ^ (2 : ℝ) := by gcongr
       _ = 4 := by norm_num

lemma UpperBnd_aux6 {σ t : ℝ} (t_ge : 3 < |t|) (hσ : σ ∈ Ioc (1 / 2) 2)
    (neOne : σ + t * I ≠ 1) (Npos : 0 < ⌊|t|⌋₊) (N_le_t : ⌊|t|⌋₊ ≤ |t|) :
    ⌊|t|⌋₊ ^ (1 - σ) / ‖1 - (σ + t * I)‖ ≤ |t| ^ (1 - σ) * 2 ∧
    ⌊|t|⌋₊ ^ (-σ) / 2 ≤ |t| ^ (1 - σ) ∧ ⌊|t|⌋₊ ^ (-σ) / σ ≤ 8 * |t| ^ (-σ) := by
  have bnd := UpperBnd_aux5 t_ge hσ.2
  have bnd' : (|t| / ⌊|t|⌋₊) ^ σ ≤ 2 * |t| := by linarith
  split_ands
  · apply (div_le_iff₀ <| norm_pos_iff.mpr <| sub_ne_zero_of_ne neOne.symm).mpr
    conv => rw [mul_assoc]; rhs; rw [mul_comm]
    apply (div_le_iff₀ <| Real.rpow_pos_of_pos (by linarith) _).mp
    rw [div_rpow_eq_rpow_div_neg (by positivity) (by positivity), neg_sub]
    refine le_trans₄ ?_ bnd' ?_
    · exact Real.rpow_le_rpow_of_exponent_le (one_le_div (by positivity) |>.mpr N_le_t) (by simp)
    · apply (mul_le_mul_iff_right₀ (by norm_num)).mpr; simpa using abs_im_le_norm (1 - (σ + t * I))
  · apply div_le_iff₀ (by norm_num) |>.mpr
    rw [Real.rpow_sub (by linarith), Real.rpow_one, div_mul_eq_mul_div, mul_comm]
    apply div_le_iff₀ (by positivity) |>.mp
    convert! bnd' using 1
    rw [← Real.rpow_neg (by linarith), div_rpow_neg_eq_rpow_div (by positivity) (by positivity)]
  · apply div_le_iff₀ (by linarith [hσ.1]) |>.mpr
    rw [mul_assoc, mul_comm, mul_assoc]
    apply div_le_iff₀' (by positivity) |>.mp
    apply le_trans ?_ (by linarith [hσ.1] : 4 ≤ σ * 8)
    convert! bnd using 1; exact div_rpow_neg_eq_rpow_div (by positivity) (by positivity)

lemma ZetaUpperBnd' {A σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
    (hσ : σ ∈ Icc (1 - A / Real.log |t|) 2) :
    let C := Real.exp A * (5 + 8 * 2); -- the 2 comes from ZetaBnd_aux1
    let N := ⌊|t|⌋₊;
    let s := σ + t * I;
    ‖∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s‖ + ‖(N : ℂ) ^ (1 - s) / (1 - s)‖
    + ‖(N : ℂ) ^ (-s) / 2‖
    + ‖s * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
    ≤ C * Real.log |t| := by
  intros C N s
  obtain ⟨Npos, N_le_t, logt_gt, σ_gt, σPos, neOne⟩ := UpperBnd_aux hA t_gt hσ.1
  replace σ_gt : 1 / 2 < σ := by linarith [hA.2]
  calc
    _ ≤ Real.exp A * 2 * Real.log |t| + ‖N ^ (1 - s) / (1 - s)‖ + ‖(N : ℂ) ^ (-s) / 2‖ +
      ‖s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ := ?_
    _ ≤ Real.exp A * 2 * Real.log |t| + ‖N ^ (1 - s) / (1 - s)‖ + ‖(N : ℂ) ^ (-s) / 2‖ +
      2 * |t| * N ^ (-σ) / σ  := ?_
    _ = Real.exp A * 2 * Real.log |t| + N ^ (1 - σ) / ‖(1 - s)‖ + N ^ (-σ) / 2 +
      2 * |t| * N ^ (-σ) / σ  := ?_
    _ ≤ Real.exp A * 2 * Real.log |t| + |t| ^ (1 - σ) * 2 +
        |t| ^ (1 - σ) + 2 * |t| * (8 * |t| ^ (-σ)) := ?_
    _ = Real.exp A * 2 * Real.log |t| + (3 + 8 * 2) * |t| ^ (1 - σ) := ?_
    _ ≤ Real.exp A * 2 * Real.log |t| + (3 + 8 * 2) * Real.exp A * 1 := ?_
    _ ≤ Real.exp A * 2 * Real.log |t| + (3 + 8 * 2) * Real.exp A * Real.log |t| := ?_
    _ = _ := by ring
  · simp only [add_le_add_iff_right, one_div_cpow_eq_cpow_neg]
    convert UpperBnd_aux3 (C := 2) hA hσ.1 t_gt le_rfl using 1
  · simp only [add_le_add_iff_left]; exact ZetaBnd_aux1 N (by linarith) ⟨σPos, hσ.2⟩ (by linarith)
  · simp only [norm_div, RCLike.norm_ofNat, s]
    congr <;> (convert norm_natCast_cpow_of_pos Npos _; simp)
  · have ⟨h₁, h₂, h₃⟩ := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t
    gcongr
    rw [mul_div_assoc]
    gcongr
  · ring_nf; conv => lhs; rhs; lhs; rw [mul_comm |t|]
    rw [← Real.rpow_add_one (by positivity)]; ring_nf
  · simp only [Real.log_abs, add_le_add_iff_left, mul_one]
    exact mul_le_mul_iff_right₀ (by positivity) |>.mpr <| UpperBnd_aux2 t_gt hσ.1
  · simp only [add_le_add_iff_left]
    apply mul_le_mul_iff_right₀ (by norm_num [Real.exp_pos]) |>.mpr <| logt_gt.le

lemma ZetaUpperBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Icc (1 - A / Real.log |t|) 2), ‖ζ (σ + t * I)‖ ≤ C * Real.log |t| := by
  let A := (1 / 2 : ℝ)
  let C := Real.exp A * (5 + 8 * 2) -- the 2 comes from ZetaBnd_aux1
  refine ⟨A, ⟨by norm_num, by norm_num⟩, C, (by positivity), ?_⟩
  intro σ t t_gt ⟨σ_ge, σ_le⟩
  obtain ⟨Npos, _, _, _, σPos, neOne⟩ := UpperBnd_aux ⟨by norm_num, by norm_num⟩ t_gt σ_ge
  rw [← Zeta0EqZeta Npos (by simp [σPos]) neOne]
  apply le_trans (by apply norm_add₄_le) ?_
  convert! ZetaUpperBnd' ⟨by norm_num, le_rfl⟩ t_gt ⟨σ_ge, σ_le⟩ using 1; simp

lemma norm_complex_log_ofNat (n : ℕ) : ‖(n : ℂ).log‖ = (n : ℝ).log := by
  have := Complex.ofReal_log (x := (n : ℝ)) (Nat.cast_nonneg n)
  rw [(by simp : ((n : ℝ) : ℂ) = (n : ℂ))] at this
  rw [← this, Complex.norm_of_nonneg]
  exact Real.log_natCast_nonneg n

lemma Real.log_natCast_monotone : Monotone (fun (n : ℕ) ↦ Real.log n) := by
  intro n m hnm
  cases n
  · simp only [CharP.cast_eq_zero, Real.log_zero, Real.log_natCast_nonneg]
  · apply Real.log_le_log <;> simp only [Nat.cast_add, Nat.cast_one]
    · exact Nat.cast_add_one_pos _
    · exact_mod_cast hnm

lemma Finset.Icc0_eq (N : ℕ) : Finset.Icc 0 N = {0} ∪ Finset.Icc 1 N := by
  refine Finset.ext_iff.mpr ?_
  intro a
  cases a
  · simp only [Finset.mem_Icc, le_refl, zero_le, and_self, Finset.mem_union, Finset.mem_singleton,
    nonpos_iff_eq_zero, one_ne_zero, and_true, or_false]
  · simp only [Finset.mem_Icc, le_add_iff_nonneg_left, zero_le, true_and, Finset.mem_union,
    Finset.mem_singleton, add_eq_zero, one_ne_zero, and_false, false_or]

lemma harmonic_eq_sum_Icc0_aux (N : ℕ) :
    ∑ i ∈ Finset.Icc 0 N, (i : ℝ)⁻¹ = ∑ i ∈ Finset.Icc 1 N, (i : ℝ)⁻¹ := by
  rw [Finset.Icc0_eq, Finset.sum_union]
  · simp only [Finset.sum_singleton, CharP.cast_eq_zero, inv_zero, zero_add]
  · simp only [Finset.disjoint_singleton_left, Finset.mem_Icc, nonpos_iff_eq_zero, one_ne_zero,
    zero_le, and_true, not_false_eq_true]

lemma harmonic_eq_sum_Icc0 (N : ℕ) : ∑ i ∈ Finset.Icc 0 N, (i : ℝ)⁻¹ = (harmonic N : ℝ) := by
  rw [harmonic_eq_sum_Icc0_aux, harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

lemma DerivUpperBnd_aux1 {A C σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2))
    (σ_ge : 1 - A / Real.log |t| ≤ σ) (t_gt : 3 < |t|) (hC : 2 ≤ C) : let N := ⌊|t|⌋₊;
    ‖∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ (σ + t * I) * (Real.log n)‖
      ≤ Real.exp A * C * (Real.log |t|) ^ 2 := by
  intro N
  obtain ⟨Npos, N_le_t, _, _, σPos, _⟩ := UpperBnd_aux hA t_gt σ_ge
  have logt_gt := logt_gt_one t_gt.le
  have logN_pos : 0 ≤ Real.log N := Real.log_nonneg (by norm_cast)
  have fact0 {n : ℕ} (hn : n ≤ N) : n ≤ |t| := by linarith [(by exact_mod_cast hn : (n : ℝ) ≤ N)]
  have fact1 {n : ℕ} (hn : n ≤ N) :
    ‖(n : ℂ) ^ (-(σ + t * I))‖ ≤ (n : ℝ)⁻¹ * A.exp := ZetaBnd_aux2 hA.1 σPos (fact0 hn) σ_ge
  have fact2 {n : ℕ} (hn : n ≤ N) : Real.log n ≤ Real.log |t| := by
    cases n
    · simp only [CharP.cast_eq_zero, Real.log_zero]; linarith
    · exact Real.log_le_log (by exact_mod_cast Nat.add_one_pos _) (fact0 hn)
  have fact3 (n : ℕ) (hn : n ≤ N) :
    ‖-1 / (n : ℂ) ^ (σ + t * I) * (Real.log n)‖ ≤ (n : ℝ)⁻¹ * Real.exp A * (Real.log |t|) := by
    convert! mul_le_mul (fact1 hn) (fact2 hn) (Real.log_natCast_nonneg n) (by positivity)
    simp only [norm_mul, norm_div, norm_neg, norm_one, one_div, natCast_log, ← norm_inv, cpow_neg]
    congr; exact norm_complex_log_ofNat n
  have := norm_sum_le_of_le (Finset.range (N + 1))
    (by simp only [Finset.mem_range, Nat.lt_succ_iff]; exact fact3)
  rw [← Finset.sum_mul, ← Finset.sum_mul, mul_comm _ A.exp, mul_assoc] at this
  rw [mul_assoc]
  apply le_trans this <| (mul_le_mul_iff_right₀ A.exp_pos).mpr ?_
  rw [pow_two, ← mul_assoc, Finset.range_eq_Ico, ← Finset.Icc_eq_Ico, harmonic_eq_sum_Icc0]
  apply le_trans (mul_le_mul (h₁ := harmonic_le_one_add_log (n := N)) (le_refl (Real.log |t|))
    (by linarith) (by linarith))
  apply (mul_le_mul_iff_left₀ (by linarith)).mpr
  rw [(by ring : C * Real.log |t| = Real.log |t| + (C - 1) * Real.log |t|),
      ← one_mul <| Real.log (N: ℝ)]
  refine add_le_add logt_gt.le <| mul_le_mul (by linarith) ?_ (by positivity) (by linarith)
  exact Real.log_le_log (by positivity) N_le_t

lemma DerivUpperBnd_aux2 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 →
    1 / 2 < σ → ‖-↑N ^ (1 - s) / (1 - s) ^ 2‖ ≤ A.exp * 2 * (1 / 3) := by
  intro N s Npos N_le_t neOne σ_gt
  dsimp only [s]
  simp_rw [norm_div, norm_neg, norm_pow, norm_natCast_cpow_of_pos Npos _,
    sub_re, one_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, sub_self, add_zero]
  have h := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t |>.1
  rw [(by ring_nf : N ^ (1 - σ) / ‖1 - (↑σ + ↑t * I)‖ ^ 2 =
          N ^ (1 - σ) / ‖1 - (↑σ + ↑t * I)‖ * 1 / ‖1 - (↑σ + ↑t * I)‖)]
  apply mul_le_mul ?_ ?_ (inv_nonneg.mpr <| norm_nonneg _) ?_
  · rw [mul_one]; exact le_trans h (by gcongr; exact UpperBnd_aux2 t_gt hσ.1)
  · rw [inv_eq_one_div, div_le_iff₀ <| norm_pos_iff.mpr <| sub_ne_zero_of_ne neOne.symm,
        mul_comm, ← mul_div_assoc, mul_one, le_div_iff₀ (by norm_num), one_mul]
    apply le_trans t_gt.le ?_
    rw [← abs_neg]; convert! abs_im_le_norm (1 - (σ + t * I)); simp
  · exact mul_nonneg (Real.exp_nonneg _) (by norm_num)

theorem DerivUpperBnd_aux3 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 → 1 / 2 < σ →
    ‖↑(N : ℝ).log * ↑N ^ (1 - s) / (1 - s)‖ ≤ A.exp * 2 * |t|.log := by
  intro N s Npos N_le_t neOne σ_gt
  rw [norm_div, norm_mul, mul_div_assoc, mul_comm]
  apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · have h := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t |>.1
    convert le_trans h ?_ using 1
    · simp [s, norm_natCast_cpow_of_pos Npos _, N]
    · gcongr; exact UpperBnd_aux2 t_gt hσ.1
  · rw [natCast_log, norm_complex_log_ofNat]
    exact Real.log_le_log (by positivity) N_le_t

theorem DerivUpperBnd_aux4 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 → 1 / 2 < σ →
    ‖↑(N : ℝ).log * (N : ℂ) ^ (-s) / 2‖ ≤ A.exp * |t|.log := by
  intro N s Npos N_le_t neOne σ_gt
  rw [norm_div, norm_mul, mul_div_assoc, mul_comm, RCLike.norm_ofNat]
  apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · have h := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t |>.2.1
    convert le_trans h (UpperBnd_aux2 t_gt hσ.1) using 1
    simp [s, norm_natCast_cpow_of_pos Npos _, N]
  · rw [natCast_log, norm_complex_log_ofNat]
    exact Real.log_le_log (by positivity) N_le_t

theorem DerivUpperBnd_aux5 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → 1 / 2 < σ →
    ‖1 * ∫ (x : ℝ) in Ioi (N : ℝ), (↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1)‖ ≤
    1 / 3 * (2 * |t| * ↑N ^ (-σ) / σ) := by
  intro N s Npos σ_gt
  have neZero : s ≠ 0 := by
    contrapose! σ_gt
    simp only [Complex.ext_iff, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, zero_re, add_im, mul_im, zero_add, zero_im, s] at σ_gt
    linarith
  have : 1 = 1 / s * s := by field_simp
  nth_rewrite 1 [this]
  rw [mul_assoc, norm_mul]
  apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · simp only [s, norm_div, norm_one]
    apply one_div_le_one_div (norm_pos_iff.mpr neZero) (by norm_num) |>.mpr
    apply le_trans t_gt.le ?_
    convert! abs_im_le_norm (σ + t * I); simp
  · have hσ : σ ∈ Ioc 0 2 := ⟨(by linarith), hσ.2⟩
    simp only [s]
    have := ZetaBnd_aux1 N (by omega) hσ (by linarith)
    simp only [div_cpow_eq_cpow_neg] at this
    convert! this using 1; congr; funext x; ring_nf

theorem DerivUpperBnd_aux6 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    0 < N → ↑N ≤ |t| → ↑σ + ↑t * I ≠ 1 → 1 / 2 < σ →
    2 * |t| * ↑N ^ (-σ) / σ ≤ 2 * (8 * A.exp) := by
  intro N Npos N_le_t neOne σ_gt
  rw [mul_div_assoc, mul_assoc]
  apply mul_le_mul_iff_right₀ (by norm_num) |>.mpr
  have h := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t |>.2.2
  apply le_trans (mul_le_mul_iff_right₀ (a := |t|) (by positivity) |>.mpr h) ?_
  rw [← mul_assoc, mul_comm _ 8, mul_assoc]
  gcongr
  convert! UpperBnd_aux2 t_gt hσ.1 using 1
  rw [mul_comm, ← Real.rpow_add_one (by positivity)]; ring_nf

lemma DerivUpperBnd_aux7_1 {x σ t : ℝ} (hx : 1 ≤ x) :
    let s := ↑σ + ↑t * I;
    ‖(↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖ = |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log := by
  have xpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have : ‖(x.log : ℂ)‖ = x.log := Complex.norm_of_nonneg <| Real.log_nonneg hx
  simp [← norm_real, this, Complex.norm_cpow_eq_rpow_re_of_pos xpos, ← Real.norm_eq_abs, ← ofReal_ofNat,
    ← ofReal_inv, ← ofReal_add, ← ofReal_sub, ← ofReal_intCast, one_div]

lemma DerivUpperBnd_aux7_2 {x σ : ℝ} (hx : 1 ≤ x) :
    |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log ≤ x ^ (-σ - 1) * x.log := by
  rw [← one_mul (x ^ (-σ - 1) * Real.log x), mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (by bound)
  exact le_trans (ZetaSum_aux1_3 x) (by norm_num)

lemma DerivUpperBnd_aux7_3 {x σ : ℝ} (xpos : 0 < x) (σnz : σ ≠ 0) :
    HasDerivAt (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t))
      (x ^ (-σ - 1) * Real.log x) x := by
  have h1 := Real.hasDerivAt_rpow_const (p := -σ) (Or.inl xpos.ne.symm)
  have h2 := h1.const_mul (1 / σ^2)
  have cancel : 1 / σ^2 * σ = 1 / σ := by field_simp
  rw [neg_mul, mul_neg, ← mul_assoc, cancel] at h2
  have h3 := Real.hasDerivAt_log xpos.ne.symm
  have h4 := HasDerivAt.mul (h1.const_mul (1 / σ)) h3
  have cancel := Real.rpow_add xpos (-σ) (-1)
  have : -σ + -1 = -σ - 1 := by rfl
  rw [← Real.rpow_neg_one x, mul_assoc (1 / σ) (x ^ (-σ)), ← cancel, this] at h4
  convert! h2.add h4 |>.neg using 1
  field_simp; ring

lemma DerivUpperBnd_aux7_3' {a σ : ℝ} (apos : 0 < a) (σnz : σ ≠ 0) :
    ∀ x ∈ Ici a, HasDerivAt (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t))
      (x ^ (-σ - 1) * Real.log x) x := by
  intro x hx
  simp at hx
  exact DerivUpperBnd_aux7_3 (by linarith) σnz

lemma DerivUpperBnd_aux7_nonneg {a σ : ℝ} (ha : 1 ≤ a) :
    ∀ x ∈ Ioi a, 0 ≤ x ^ (-σ - 1) * Real.log x := by
  intro x hx
  simp at hx
  bound

lemma DerivUpperBnd_aux7_tendsto {σ : ℝ} (σpos : 0 < σ) :
    Tendsto (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t)) atTop (nhds 0) := by
  have h1 := tendsto_rpow_neg_atTop σpos
  have h2 := h1.const_mul (1 / σ^2)
  have h3 : Tendsto (fun t : ℝ ↦ t ^ (-σ) * Real.log t) atTop (nhds 0) := by
    have := Real.tendsto_pow_log_div_pow_atTop σ 1 σpos
    simp only [Real.rpow_one] at this
    apply Tendsto.congr' _ this
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [mul_comm]
    apply div_rpow_eq_rpow_neg _ _ _ hx
  have h4 := h3.const_mul (1 / σ)
  have h5 := (h2.add h4).neg
  convert h5 using 1
  · ext; ring
  simp

open MeasureTheory in
lemma DerivUpperBnd_aux7_4 {a σ : ℝ} (σpos : 0 < σ) (ha : 1 ≤ a) :
    IntegrableOn (fun x ↦ x ^ (-σ - 1) * Real.log x) (Ioi a) volume := by
  apply integrableOn_Ioi_deriv_of_nonneg' (l := 0)
  · exact DerivUpperBnd_aux7_3' (by linarith) (by linarith)
  · exact DerivUpperBnd_aux7_nonneg ha
  · exact DerivUpperBnd_aux7_tendsto σpos

open MeasureTheory in
lemma DerivUpperBnd_aux7_5 {a σ : ℝ} (σpos : 0 < σ) (ha : 1 ≤ a) :
    IntegrableOn (fun x ↦ |(↑⌊x⌋ + (1 : ℝ) / 2 - x)| * x ^ (-σ - 1) * Real.log x)
      (Ioi a) volume := by
  simp_rw [mul_assoc]
  apply Integrable.bdd_mul (c := 1 / 2) <| DerivUpperBnd_aux7_4 σpos ha
  · exact Measurable.aestronglyMeasurable <| Measurable.abs measurable_floor_add_half_sub
  apply ae_of_all
  intro x
  simp only [Real.norm_eq_abs, _root_.abs_abs]
  exact  ZetaSum_aux1_3 x

open MeasureTheory in
lemma DerivUpperBnd_aux7_integral_eq {a σ : ℝ} (ha : 1 ≤ a) (σpos : 0 < σ) :
    ∫ (x : ℝ) in Ioi a, x ^ (-σ - 1) * Real.log x =
      1 / σ^2 * a ^ (-σ) + 1 / σ * a ^ (-σ) * Real.log a := by
  convert integral_Ioi_of_hasDerivAt_of_nonneg'
    (DerivUpperBnd_aux7_3' (by linarith) (by linarith))
    (DerivUpperBnd_aux7_nonneg ha) (DerivUpperBnd_aux7_tendsto σpos) using 1
  ring

open MeasureTheory in
theorem DerivUpperBnd_aux7 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 → 1 / 2 < σ →
    ‖s * ∫ (x : ℝ) in Ioi (N : ℝ), (↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖ ≤
      6 * |t| * ↑N ^ (-σ) / σ * |t|.log := by
  intro N s Npos N_le_t neOne σ_gt
  have σpos : 0 < σ := lt_trans (by norm_num) σ_gt
  rw [norm_mul, (by ring : 6 * |t| * ↑N ^ (-σ) / σ * Real.log |t| = (2 * |t|) * (3 * ↑N ^ (-σ) / σ * Real.log |t|))]
  apply mul_le_mul _ _ (by positivity) (by positivity)
  · apply le_trans (by apply norm_add_le)
    simp [abs_of_pos σpos]
    linarith [hσ.2]
  apply le_trans (by apply norm_integral_le_integral_norm)
  calc ∫ (x : ℝ) in Ioi (N : ℝ), ‖(↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖
    _ = ∫ (x : ℝ) in Ioi (N : ℝ), |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log := by
      apply setIntegral_congr_fun (by measurability)
      intro x hx
      simp only [mem_Ioi] at hx
      exact DerivUpperBnd_aux7_1 (lt_of_le_of_lt (mod_cast Npos) hx).le
    _ ≤ ∫ (x : ℝ) in Ioi (N : ℝ), x ^ (-σ - 1) * x.log := by
      apply setIntegral_mono_on _ _ (by measurability)
      · intro x hx
        exact DerivUpperBnd_aux7_2 (lt_of_le_of_lt (mod_cast Npos) hx).le
      · apply DerivUpperBnd_aux7_5 σpos (mod_cast Npos)
      apply DerivUpperBnd_aux7_4 σpos (mod_cast Npos)
    _ = 1 / σ^2 * N ^ (-σ) + 1 / σ * N ^ (-σ) * Real.log N :=
      DerivUpperBnd_aux7_integral_eq (mod_cast Npos) σpos
    _ ≤ 3 * ↑N ^ (-σ) / σ * |t|.log := by
      have h2 : 1 / σ * ↑N ^ (-σ) * Real.log ↑N ≤ ↑N ^ (-σ) / σ * Real.log |t| := calc
        _ = ↑N ^ (-σ) / σ * Real.log N := by ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.log_le_log (mod_cast Npos) N_le_t
      have : 2 ≤ 2 * Real.log |t| := by
        nth_rewrite 1  [← mul_one 2]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact logt_gt_one t_gt.le |>.le
      have h1 : 1 / σ^2 * ↑N ^ (-σ) ≤ 2 * ↑N ^ (-σ) / σ * Real.log |t| := calc
        1 / σ^2 * ↑N ^ (-σ) = (↑N ^ (-σ) / σ) * (1 / σ) := by ring
        _ ≤ ↑N ^ (-σ) / σ * (2 * Real.log |t|):= by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply le_trans _ this
          exact (one_div_le σpos (by norm_num)).mpr σ_gt.le
        _ = _ := by ring
      convert! add_le_add h1 h2 using 1
      ring

lemma ZetaDerivUpperBnd' {A σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
    (hσ : σ ∈ Icc (1 - A / Real.log |t|) 2) :
    let C := Real.exp A * 59;
    let N := ⌊|t|⌋₊;
    let s := σ + t * I;
    ‖∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * (Real.log n)‖ +
      ‖-(N : ℂ) ^ (1 - s) / (1 - s) ^ 2‖ +
      ‖(Real.log N) * (N : ℂ) ^ (1 - s) / (1 - s)‖ +
      ‖(Real.log N) * (N : ℂ) ^ (-s) / 2‖ +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖
        ≤ C * Real.log |t| ^ 2 := by
  intros C N s
  obtain ⟨Npos, N_le_t, logt_gt, σ_gt, _, neOne⟩ := UpperBnd_aux hA t_gt hσ.1
  replace σ_gt : 1 / 2 < σ := by linarith [hA.2]
  calc _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      ‖-(N : ℂ) ^ (1 - s) / (1 - s) ^ 2‖ +
      ‖(Real.log N) * (N : ℂ) ^ (1 - s) / (1 - s)‖ +
      ‖(Real.log N) * (N : ℂ) ^ (-s) / 2‖ +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux1 hA hσ.1 t_gt (by simp : (2 : ℝ) ≤ 2)
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      ‖(Real.log N) * (N : ℂ) ^ (1 - s) / (1 - s)‖ +
      ‖(Real.log N) * (N : ℂ) ^ (-s) / 2‖ +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux2 t_gt hσ Npos N_le_t neOne σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      ‖(Real.log N) * (N : ℂ) ^ (-s) / 2‖ +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux3 t_gt hσ Npos N_le_t neOne σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      Real.exp A * (Real.log |t|) +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux4 t_gt hσ Npos N_le_t neOne σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      Real.exp A * (Real.log |t|) +
      1 / 3 * (2 * |t| * N ^ (-σ) / σ) +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux5 t_gt hσ Npos σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      Real.exp A * (Real.log |t|) +
      1 / 3 * (2 * (8 * Real.exp A)) +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux6 t_gt hσ Npos N_le_t neOne σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      Real.exp A * (Real.log |t|) +
      1 / 3 * (2 * (8 * Real.exp A)) +
      (6 * |t| * N ^ (-σ) / σ) * (Real.log |t|) := by
        gcongr; exact DerivUpperBnd_aux7 t_gt hσ Npos N_le_t neOne σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      Real.exp A * (Real.log |t|) +
      1 / 3 * (2 * (8 * Real.exp A)) +
      (6 * (8 * Real.exp A)) * (Real.log |t|) := by
        gcongr; convert mul_le_mul_of_nonneg_left (DerivUpperBnd_aux6 t_gt hσ Npos N_le_t neOne σ_gt) (by norm_num : (0 : ℝ) ≤ 3) using 1 <;> ring
    _ ≤ _ := by
      simp only [C]
      ring_nf
      rw [(by ring : A.exp * |t|.log ^ 2 * 59 = A.exp * |t|.log ^ 2 * 6 + A.exp * |t|.log ^ 2 * 51 +
        A.exp * |t|.log ^ 2 * 2)]
      nth_rewrite 1 [← mul_one A.exp]
      gcongr
      swap
      · nth_rewrite 1 [← mul_one |t|.log, (by ring : |t|.log ^ 2 = |t|.log * |t|.log)]
        gcongr
      nlinarith

lemma ZetaDerivUpperBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Icc (1 - A / Real.log |t|) 2),
    ‖ζ' (σ + t * I)‖ ≤ C * Real.log |t| ^ 2 := by
  obtain ⟨A, hA, _, _, _⟩ := ZetaUpperBnd
  let C := Real.exp A * 59
  refine ⟨A, hA, C, by positivity, ?_⟩
  intro σ t t_gt ⟨σ_ge, σ_le⟩
  obtain ⟨Npos, N_le_t, _, _, σPos, neOne⟩ := UpperBnd_aux hA t_gt σ_ge
  rw [← DerivZeta0EqDerivZeta Npos (by simp [σPos]) neOne]
  set N : ℕ := ⌊|t|⌋₊
  rw [(HasDerivAtZeta0 Npos (s := σ + t * I) (by simp [σPos]) neOne).deriv]
  dsimp only [ζ₀']
  rw [← add_assoc]
  set aa := ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ (σ + t * I) * (Real.log n)
  set bb := -(N : ℂ) ^ (1 - (σ + t * I)) / (1 - (σ + t * I)) ^ 2
  set cc := (Real.log N) * (N : ℂ) ^ (1 - (σ + t * I)) / (1 - (σ + t * I))
  set dd := (Real.log N) * (N : ℂ) ^ (-(σ + t * I)) / 2
  set ee := 1 * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(σ + t * I) - 1)
  set ff := (σ + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(σ + t * I) - 1) * -(Real.log x)
  rw [(by ring : aa + (bb + cc) + dd + ee + ff = aa + bb + cc + dd + ee + ff)]
  apply le_trans (by apply norm_add₆_le) ?_
  convert ZetaDerivUpperBnd' hA t_gt ⟨σ_ge, σ_le⟩

