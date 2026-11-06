/- GID: D5/S3/Analytic/Laplace/PairedPoleRegularity
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/PairedPoleRegularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Paired pole subtraction preserves holomorphy and polynomial boundary bounds. -/

import D5.S3.Analytic.Oscillation.OrdinateCounting
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Liouville

/-! Regularity and polynomial boundary bounds for paired spectral pole expansions. -/

namespace D5.S3.Analytic.Laplace.PairedPoleRegularity

open D5.S3.Analytic.Oscillation.OrdinateCounting
open Set Filter MeasureTheory Metric
open scoped Topology BigOperators

noncomputable section

noncomputable def laplace (f : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ u in Set.Ici (0 : ℝ), (f u : ℂ) * Complex.exp (-s * (u : ℂ))

noncomputable def poleTerm (S : Spectrum) (j : S.index) (s : ℂ) : ℂ :=
  (S.mult j : ℂ) * (1 / (s - (S.gamma j : ℂ) * Complex.I) +
    1 / (s + (S.gamma j : ℂ) * Complex.I))

structure PairedLaplaceData (S : Spectrum) (f : ℝ → ℝ) (k : ℕ) where
  measurable : Measurable f
  local_bound : ∀ A : ℝ, 0 ≤ A → ∃ B : ℝ, 0 ≤ B ∧ ∀ u ∈ Set.Icc (0 : ℝ) A, |f u| ≤ B
  initial_convergence : ∀ σ : ℝ, 1 / 2 < σ →
    IntegrableOn (fun u => f u * Real.exp (-σ * u)) (Set.Ici (0 : ℝ))
  eta : ℝ
  eta_pos : 0 < eta
  eta_lt : eta < 1 / 5
  J : ℂ → ℂ
  holomorphic : DifferentiableOn ℂ J {s | -eta < s.re ∧ s.re < 1}
  growth : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, |s.re| ≤ eta / 2 →
    ‖J s‖ ≤ C * (1 + |s.im|) ^ k
  identity : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
    laplace f s = -(1 / 2 : ℂ) * (∑' j : S.index, poleTerm S j s) + J s

/-- The part of the transform left after removing the poles with γ ≤ 2M. -/
noncomputable def regularPart (S : Spectrum) (J : ℂ → ℂ) (M : ℝ) (s : ℂ) : ℂ :=
  J s - (1 / 2 : ℂ) * ∑' j : {j : S.index // 2 * M < S.gamma j}, poleTerm S j.val s

private lemma pole_separation (S : Spectrum) (j : S.index) {s : ℂ}
    (hs : ‖s‖ ≤ 3 * S.gamma j / 4) :
    S.gamma j / 4 ≤ ‖s - (S.gamma j : ℂ) * Complex.I‖ ∧
      S.gamma j / 4 ≤ ‖s + (S.gamma j : ℂ) * Complex.I‖ := by
  have hn : ‖(S.gamma j : ℂ) * Complex.I‖ = S.gamma j := by
    simp [abs_of_pos (S.gamma_pos j)]
  have hm := norm_sub_norm_le ((S.gamma j : ℂ) * Complex.I) s
  have hp := norm_sub_norm_le (-((S.gamma j : ℂ) * Complex.I)) s
  rw [hn, norm_sub_rev] at hm
  rw [norm_neg, hn, norm_sub_rev, sub_neg_eq_add] at hp
  constructor <;> linarith

private lemma pole_bound (S : Spectrum) (j : S.index) {s : ℂ}
    (hs : ‖s‖ ≤ 3 * S.gamma j / 4) :
    ‖poleTerm S j s‖ ≤ 32 * ‖s‖ * ((S.mult j : ℝ) / (S.gamma j) ^ 2) := by
  obtain ⟨hm, hp⟩ := pole_separation S j hs
  have hg := S.gamma_pos j
  have hm0 : s - (S.gamma j : ℂ) * Complex.I ≠ 0 :=
    norm_pos_iff.mp (by linarith)
  have hp0 : s + (S.gamma j : ℂ) * Complex.I ≠ 0 :=
    norm_pos_iff.mp (by linarith)
  have heq : poleTerm S j s = (S.mult j : ℂ) * (2 * s) /
      ((s - (S.gamma j : ℂ) * Complex.I) * (s + (S.gamma j : ℂ) * Complex.I)) := by
    unfold poleTerm
    field_simp
    ring
  rw [heq, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_natCast]
  norm_num only [Complex.norm_ofNat]
  have hd : 0 < ‖s - (S.gamma j : ℂ) * Complex.I‖ *
      ‖s + (S.gamma j : ℂ) * Complex.I‖ := mul_pos (by linarith) (by linarith)
  have hprod := mul_le_mul hm hp (by positivity : 0 ≤ S.gamma j / 4) (norm_nonneg _)
  apply (div_le_iff₀ hd).mpr
  have hgamma2 : 0 < (S.gamma j) ^ 2 := sq_pos_of_pos hg
  have he : 32 * ‖s‖ * ((S.mult j : ℝ) / (S.gamma j) ^ 2) *
      ((S.gamma j / 4) * (S.gamma j / 4)) = (S.mult j : ℝ) * (2 * ‖s‖) := by
    field_simp
    ring
  rw [← he]
  exact mul_le_mul_of_nonneg_left hprod (by positivity)

private lemma tail_small (S : Spectrum) (hN : CountAsymptotic S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T →
      Summable (fun j : {j : S.index // T < S.gamma j} =>
        (S.mult j.val : ℝ) / (S.gamma j.val) ^ 2) ∧
      (∑' j : {j : S.index // T < S.gamma j},
        (S.mult j.val : ℝ) / (S.gamma j.val) ^ 2) ≤ C := by
  obtain ⟨C, hC, htail⟩ := inverse_square_tail S hN
  refine ⟨C, hC, fun T hT => ⟨(htail T hT).1, (htail T hT).2.trans ?_⟩⟩
  apply (div_le_iff₀ (by linarith : 0 < T)).mpr
  exact mul_le_mul_of_nonneg_left (Real.log_le_self (by linarith)) hC


private lemma rectangle_open (a M : ℝ) :
    IsOpen {s : ℂ | |s.re| < a ∧ |s.im| < M + 1} :=
  (isOpen_lt Complex.continuous_re.abs continuous_const).inter
    (isOpen_lt Complex.continuous_im.abs continuous_const)

private lemma rectangle_norm {a M : ℝ} (ha : a < 1 / 5)
    {s : ℂ} (hs : |s.re| < a ∧ |s.im| < M + 1) : ‖s‖ ≤ M + 2 := by
  have := Complex.norm_le_abs_re_add_abs_im s
  linarith [hs.1, hs.2]

private lemma tail_comparison {M g : ℝ} (hM : 4 ≤ M) (hg : 2 * M < g)
    {s : ℂ} (hs : ‖s‖ ≤ M + 2) : ‖s‖ ≤ 3 * g / 4 := by
  linarith

private lemma tail_summable (S : Spectrum) (hN : CountAsymptotic S)
    {T : ℝ} (hT : 4 ≤ T) {s : ℂ} (hs : ‖s‖ ≤ 3 * T / 4) :
    Summable (fun j : {j : S.index // T < S.gamma j} => poleTerm S j.val s) := by
  obtain ⟨C, _, hC⟩ := tail_small S hN
  apply Summable.of_norm_bounded ((hC T hT).1.mul_left (32 * ‖s‖))
  intro j
  exact pole_bound S j.val (hs.trans (by linarith [j.property]))

/-- Removing the low poles leaves a holomorphic function on the stated rectangle. -/
theorem regularPart_differentiableOn (S : Spectrum) (hN : CountAsymptotic S)
    {f : ℝ → ℝ} {k : ℕ} (D : PairedLaplaceData S f k) {M : ℝ} (hM : 4 ≤ M) :
    DifferentiableOn ℂ (regularPart S D.J M) {s | |s.re| < D.eta ∧ |s.im| < M + 1} := by
  obtain ⟨C, _, hC⟩ := tail_small S hN
  have hsum : DifferentiableOn ℂ
      (fun s => ∑' j : {j : S.index // 2 * M < S.gamma j}, poleTerm S j.val s)
      {s | |s.re| < D.eta ∧ |s.im| < M + 1} := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      ((hC (2 * M) (by linarith)).1.mul_left (32 * (M + 2)))
      ?_ (rectangle_open D.eta M) ?_
    · intro j s hs
      have hb := tail_comparison hM j.property (rectangle_norm D.eta_lt hs)
      obtain ⟨hm, hp⟩ := pole_separation S j.val hb
      have hg := S.gamma_pos j.val
      have hm0 : s - (S.gamma j.val : ℂ) * Complex.I ≠ 0 :=
        norm_pos_iff.mp (by linarith)
      have hp0 : s + (S.gamma j.val : ℂ) * Complex.I ≠ 0 :=
        norm_pos_iff.mp (by linarith)
      have hid : DifferentiableAt ℂ (fun z : ℂ => z) s := differentiableAt_id
      have hminus : DifferentiableAt ℂ
          (fun z : ℂ => z - (S.gamma j.val : ℂ) * Complex.I) s :=
        hid.sub (differentiableAt_const _)
      have hplus : DifferentiableAt ℂ
          (fun z : ℂ => z + (S.gamma j.val : ℂ) * Complex.I) s :=
        hid.add (differentiableAt_const _)
      exact (((differentiableAt_const (1 : ℂ)).div hminus hm0).add
        ((differentiableAt_const (1 : ℂ)).div hplus hp0)).const_mul
          (S.mult j.val : ℂ) |>.differentiableWithinAt
    · intro j s hs
      exact (pole_bound S j.val
        (tail_comparison hM j.property (rectangle_norm D.eta_lt hs))).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (rectangle_norm D.eta_lt hs) (by norm_num))
          (by positivity))
  apply (D.holomorphic.mono ?_).sub (hsum.const_mul (1 / 2 : ℂ))
  intro s hs
  have hr := abs_lt.mp hs.1
  exact ⟨hr.1, by linarith [hr.2, D.eta_lt]⟩


private def cutoff_complement (S : Spectrum) (T : ℝ) :
    {j : S.index // j ∉ S.cut T} ≃ {j : S.index // T < S.gamma j} :=
  Equiv.subtypeEquivRight (fun j => by classical simp [Spectrum.cut])

private lemma poles_summable (S : Spectrum) (hN : CountAsymptotic S) (s : ℂ) :
    Summable (fun j : S.index => poleTerm S j s) := by
  classical
  let T : ℝ := max 4 (2 * ‖s‖)
  have hT : 4 ≤ T := le_max_left _ _
  have hs : ‖s‖ ≤ 3 * T / 4 := by
    have := le_max_right 4 (2 * ‖s‖)
    dsimp [T]
    nlinarith [norm_nonneg s]
  apply (S.cut T).summable_compl_iff.mp
  exact (cutoff_complement S T).symm.summable_iff.mp (tail_summable S hN hT hs)

/-- The transform splits into its finitely many low poles and the regular part. -/
theorem laplace_eq_finite_poles_add_regular (S : Spectrum) (hN : CountAsymptotic S)
    {f : ℝ → ℝ} {k : ℕ} (D : PairedLaplaceData S f k) {M : ℝ} (hM : 4 ≤ M)
    {s : ℂ} (hs1 : 1 / 2 < s.re) (hs2 : s.re < 1) :
    laplace f s = -(1 / 2 : ℂ) * (∑ j ∈ S.cut (2 * M), poleTerm S j s) +
      regularPart S D.J M s := by
  classical
  have hsplit := (poles_summable S hN s).sum_add_tsum_subtype_compl (S.cut (2 * M))
  have heq : (∑' j : {j : S.index // j ∉ S.cut (2 * M)}, poleTerm S j.val s) =
      ∑' j : {j : S.index // 2 * M < S.gamma j}, poleTerm S j.val s :=
    (cutoff_complement S (2 * M)).tsum_eq (fun j => poleTerm S j.val s)
  rw [heq] at hsplit
  rw [D.identity s hs1 hs2, ← hsplit, regularPart]
  ring

private lemma regular_bound (S : Spectrum) (hN : CountAsymptotic S)
    {f : ℝ → ℝ} {k : ℕ} (D : PairedLaplaceData S f k) :
    ∃ B : ℝ, 0 < B ∧ ∀ M : ℝ, 4 ≤ M → ∀ s : ℂ,
      |s.re| ≤ D.eta / 2 → |s.im| ≤ M + 1 / 2 →
      ‖regularPart S D.J M s‖ ≤ B * M ^ (max k 1) := by
  obtain ⟨C, hC, htail⟩ := tail_small S hN
  obtain ⟨CJ, hCJ, hJ⟩ := D.growth
  refine ⟨CJ * 2 ^ k + 24 * C + 1, by positivity, ?_⟩
  intro M hM s hre him
  have hM0 : 0 ≤ M := by linarith
  have hnorm : ‖s‖ ≤ M + 2 := by
    have := Complex.norm_le_abs_re_add_abs_im s
    linarith [D.eta_lt]
  have ht := tsum_of_norm_bounded
    (((htail (2 * M) (by linarith)).1.mul_left (32 * ‖s‖)).hasSum)
    (fun j => pole_bound S j.val (tail_comparison hM j.property hnorm))
  rw [tsum_mul_left] at ht
  have ht' : ‖∑' j : {j : S.index // 2 * M < S.gamma j}, poleTerm S j.val s‖ ≤
      32 * (M + 2) * C := ht.trans (by
    apply mul_le_mul
    · nlinarith
    · exact (htail (2 * M) (by linarith)).2
    · exact tsum_nonneg (fun _ => by positivity)
    · positivity)
  have hpow : (1 + |s.im|) ^ k ≤ 2 ^ k * M ^ k := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hk : M ^ k ≤ M ^ (max k 1) :=
    pow_le_pow_right₀ (by linarith) (le_max_left _ _)
  have h1 : M ≤ M ^ (max k 1) := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ (by linarith : 1 ≤ M) (le_max_right k 1))
  have hj : ‖D.J s‖ ≤ CJ * 2 ^ k * M ^ (max k 1) := by
    calc
      _ ≤ CJ * (1 + |s.im|) ^ k := hJ s hre
      _ ≤ CJ * (2 ^ k * M ^ k) := mul_le_mul_of_nonneg_left hpow hCJ
      _ ≤ CJ * 2 ^ k * M ^ (max k 1) := by rw [← mul_assoc]; gcongr
  have hreg := norm_sub_le (D.J s)
    ((1 / 2 : ℂ) * ∑' j : {j : S.index // 2 * M < S.gamma j}, poleTerm S j.val s)
  change ‖regularPart S D.J M s‖ ≤ _ at hreg
  simp only [norm_mul, norm_div, norm_one, Complex.norm_ofNat] at hreg
  have htailbound : 1 / 2 *
      ‖∑' j : {j : S.index // 2 * M < S.gamma j}, poleTerm S j.val s‖ ≤
        24 * C * M ^ (max k 1) := by
    have hlinear : 1 / 2 * (32 * (M + 2) * C) ≤ 24 * C * M := by
      nlinarith
    exact (mul_le_mul_of_nonneg_left ht' (by norm_num)).trans
      (hlinear.trans (mul_le_mul_of_nonneg_left h1 (by positivity)))
  have hpow0 : 0 ≤ M ^ (max k 1) := pow_nonneg hM0 _
  nlinarith

/-- The regular part and its first derivative have uniform polynomial boundary bounds. -/
theorem regularized_boundary_bound (S : Spectrum) (hN : CountAsymptotic S)
    {f : ℝ → ℝ} {k : ℕ} (D : PairedLaplaceData S f k) :
    ∃ A : ℝ, 0 < A ∧ ∀ M t : ℝ, 4 ≤ M → |t| ≤ M →
      ‖regularPart S D.J M ((t : ℂ) * Complex.I)‖ +
      ‖deriv (regularPart S D.J M) ((t : ℂ) * Complex.I)‖ ≤ A * M ^ (max k 1) := by
  obtain ⟨B, hB, hbound⟩ := regular_bound S hN D
  let r : ℝ := D.eta / 4
  have hr : 0 < r := by dsimp [r]; linarith [D.eta_pos]
  have hr_eta : r < D.eta := by dsimp [r]; linarith [D.eta_pos]
  have hr_half : r < 1 / 2 := by dsimp [r]; linarith [D.eta_lt]
  refine ⟨B + B / r, by positivity, ?_⟩
  intro M t hM ht
  let c : ℂ := (t : ℂ) * Complex.I
  have hc_re : c.re = 0 := by simp [c]
  have hc_im : c.im = t := by simp [c]
  have hcoords (z : ℂ) (hz : z ∈ closedBall c r) :
      |z.re| ≤ D.eta / 2 ∧ |z.im| ≤ M + 1 / 2 := by
    have hz' : ‖z - c‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hz
    have hre := (Complex.abs_re_le_norm (z - c)).trans hz'
    have him := (Complex.abs_im_le_norm (z - c)).trans hz'
    simp only [Complex.sub_re, hc_re, sub_zero] at hre
    simp only [Complex.sub_im, hc_im] at him
    have him' := abs_add_le (z.im - t) t
    constructor
    · dsimp [r] at hre; linarith [D.eta_pos]
    · rw [sub_add_cancel] at him'
      linarith
  have hrect : closedBall c r ⊆ {s : ℂ | |s.re| < D.eta ∧ |s.im| < M + 1} := by
    intro z hz
    have hz' : ‖z - c‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hz
    have hre := (Complex.abs_re_le_norm (z - c)).trans hz'
    have him := (Complex.abs_im_le_norm (z - c)).trans hz'
    simp only [Complex.sub_re, hc_re, sub_zero] at hre
    simp only [Complex.sub_im, hc_im] at him
    refine ⟨hre.trans_lt hr_eta, ?_⟩
    have hh := abs_add_le (z.im - t) t
    rw [sub_add_cancel] at hh
    linarith
  have hder := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    ((regularPart_differentiableOn S hN D hM).diffContOnCl_ball hrect)
    (fun z hz => hbound M hM z (hcoords z (sphere_subset_closedBall hz)).1
      (hcoords z (sphere_subset_closedBall hz)).2)
  have hval : ‖regularPart S D.J M c‖ ≤ B * M ^ (max k 1) :=
    hbound M hM c (by rw [hc_re, abs_zero]; linarith [D.eta_pos])
      (by rw [hc_im]; linarith)
  change ‖regularPart S D.J M c‖ + ‖deriv (regularPart S D.J M) c‖ ≤ _
  calc
    _ ≤ B * M ^ (max k 1) + B * M ^ (max k 1) / r := add_le_add hval hder
    _ = (B + B / r) * M ^ (max k 1) := by ring

#print axioms regularPart_differentiableOn
#print axioms laplace_eq_finite_poles_add_regular
#print axioms regularized_boundary_bound

end
end D5.S3.Analytic.Laplace.PairedPoleRegularity
