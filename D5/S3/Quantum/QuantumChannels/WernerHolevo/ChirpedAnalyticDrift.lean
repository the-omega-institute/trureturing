/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedAnalyticDrift
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedAnalyticDrift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact correlation residual has a derivative with global sup-norm drift constant 16. -/

import D5.S3.Quantum.QuantumChannels.WernerHolevo.ChirpedCirculantGram
import D5.S3.Quantum.QuantumChannels.WernerHolevo.ChirpedReplaySoundness
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The analytic derivative and global derivative drift of the chirped replay residual. -/

open scoped BigOperators ComplexConjugate InnerProductSpace ZMod
open ContinuousLinearMap

namespace ChirpedAnalyticDrift

noncomputable section

private abbrev divisor (t : ℝ) : ℂ := 1 - Complex.I * (t : ℂ)

private theorem divisor_ne (t : ℝ) : divisor t ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp [divisor, Complex.sub_re, Complex.mul_re] at hr

private theorem one_le_norm_divisor (t : ℝ) : 1 ≤ ‖divisor t‖ := by
  have h : ‖divisor t‖ ^ 2 = 1 + t ^ 2 := by
    rw [Complex.sq_norm]
    simp [divisor, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, pow_two]
  apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (norm_nonneg _)).mp
  nlinarith [sq_nonneg t]

private theorem hasDerivAt_it (t : ℝ) :
    HasDerivAt (fun v : ℝ => Complex.I * (v : ℂ)) Complex.I t := by
  simpa only [mul_one] using
    ((hasDerivAt_id' (↑t : ℂ)).const_mul Complex.I).comp_ofReal

theorem hasDerivAt_cayley (s : ℤ) (t : ℝ) :
    HasDerivAt (fun v => ChirpedReplay.cayley v s) (ChirpedReplay.cayleySlope t s) t := by
  have h := (((hasDerivAt_it t).const_add 1).const_mul (s : ℂ)).fun_div
    ((hasDerivAt_it t).const_sub 1) (divisor_ne t)
  unfold ChirpedReplay.cayley
  convert h using 1
  unfold ChirpedReplay.cayleySlope
  ring

private def cayleySecond (s : ℤ) (t : ℝ) : ℂ := -4 * (s : ℂ) / divisor t ^ 3

private theorem hasDerivAt_cayleySlope (s : ℤ) (t : ℝ) :
    HasDerivAt (fun v => ChirpedReplay.cayleySlope v s) (cayleySecond s t) t := by
  have h := (hasDerivAt_const t (2 * (s : ℂ) * Complex.I)).fun_div
    (((hasDerivAt_it t).const_sub 1).fun_pow 2) (pow_ne_zero 2 (divisor_ne t))
  unfold ChirpedReplay.cayleySlope
  convert h using 1
  have hi : Complex.I * Complex.I = -1 := Complex.I_mul_I
  change (-4 : ℂ) * s / divisor t ^ 3 =
    (0 * divisor t ^ 2 - (2 * (s : ℂ) * Complex.I) *
      ((2 : ℂ) * divisor t ^ (2 - 1) * -Complex.I)) / (divisor t ^ 2) ^ 2
  calc
    _ = (4 : ℂ) * s * (Complex.I * Complex.I) * divisor t / (divisor t ^ 2) ^ 2 := by
      rw [hi]
      field_simp [divisor_ne t]
    _ = _ := by simp only [Nat.reduceSub, pow_one, zero_mul, zero_sub]; ring

private theorem cayleySecond_bound (s : ℤ) (hs : s = 1 ∨ s = -1) (t : ℝ) :
    ‖cayleySecond s t‖ ≤ 4 := by
  have hs' : ‖(s : ℂ)‖ = 1 := by rcases hs with rfl | rfl <;> simp
  rw [cayleySecond, norm_div, norm_mul, hs', mul_one, norm_neg, norm_pow]
  have hn : ‖(4 : ℂ)‖ = 4 := Complex.norm_natCast 4
  rw [hn]
  exact div_le_self (by norm_num) (one_le_pow₀ (one_le_norm_divisor t))

private theorem cayley_diff (s : ℤ) (hs : s = 1 ∨ s = -1) (x y : ℝ) :
    ‖ChirpedReplay.cayley x s - ChirpedReplay.cayley y s‖ ≤ 2 * ‖x - y‖ :=
  (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hasDerivAt_cayley s t).hasDerivWithinAt)
    (fun t _ => (ChirpedReplay.cayley_norm_bounds t s hs).2)
    (Set.mem_univ y) (Set.mem_univ x)

private theorem slope_diff (s : ℤ) (hs : s = 1 ∨ s = -1) (x y : ℝ) :
    ‖ChirpedReplay.cayleySlope x s - ChirpedReplay.cayleySlope y s‖ ≤ 4 * ‖x - y‖ :=
  (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hasDerivAt_cayleySlope s t).hasDerivWithinAt)
    (fun t _ => cayleySecond_bound s hs t)
    (Set.mem_univ y) (Set.mem_univ x)

section Fourier

variable {n : ℕ} [NeZero n]

private abbrev phase (a : ZMod n) : ℂ := ZMod.stdAddChar a

private theorem phase_add (a b : ZMod n) : phase (a + b) = phase a * phase b :=
  AddChar.map_add_eq_mul ZMod.stdAddChar a b

private theorem phase_conj (a : ZMod n) : conj (phase a) = phase (-a) :=
  (AddChar.map_neg_eq_conj ZMod.stdAddChar a).symm

theorem phase_sum (a : ZMod n) :
    ∑ x : ZMod n, ZMod.stdAddChar (a * x) = if a = 0 then (n : ℂ) else 0 := by
  by_cases ha : a = 0 <;>
    simpa [ha, mul_comm a, ZMod.card] using
      AddChar.sum_mulShift a (ZMod.isPrimitive_stdAddChar n)

private def fourierSum (a : ZMod n → ℂ) (d : ZMod n) : ℂ :=
  ∑ j, phase (j * d) * a j

private theorem fourierSum_pairing (a b : ZMod n → ℂ) :
    (∑ d, conj (fourierSum a d) * fourierSum b d) =
      (n : ℂ) * ∑ j, conj (a j) * b j := by
  classical
  calc
    _ = ∑ d : ZMod n, ∑ j : ZMod n, ∑ k : ZMod n,
        (conj (a j) * b k) * phase ((k - j) * d) := by
      apply Finset.sum_congr rfl
      intro d _
      simp only [fourierSum, map_sum]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [map_mul, phase_conj, sub_mul, sub_eq_neg_add, phase_add]
      ac_rfl
    _ = ∑ j : ZMod n, ∑ k : ZMod n, ∑ d : ZMod n,
        (conj (a j) * b k) * phase ((k - j) * d) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = _ := by
      simp only [← Finset.mul_sum, phase_sum, sub_eq_zero, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- A unit chirp applied after the inverse DFT, with columns read through a permutation. -/
def transform (chirp : ZMod n) (p : Equiv.Perm (ZMod n)) (a : ZMod n → ℂ)
    (d : ZMod n) : ℂ :=
  phase (chirp * (p d) ^ 2) * ChirpedCirculantGram.kernel a (p d)

theorem transform_eq_sum (chirp : ZMod n) (p : Equiv.Perm (ZMod n)) (a : ZMod n → ℂ)
    (d : ZMod n) :
    transform chirp p a d =
      (n : ℂ)⁻¹ * ∑ j, ZMod.stdAddChar (chirp * (p d) ^ 2 + j * p d) * a j := by
  change phase (chirp * (p d) ^ 2) *
    ((n : ℂ)⁻¹ * ∑ j : ZMod n, phase (j * p d) * a j) = _
  rw [mul_left_comm (phase (chirp * (p d) ^ 2)) ((n : ℂ)⁻¹), Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  change _ = phase (chirp * (p d) ^ 2 + j * p d) * a j
  rw [phase_add (chirp * (p d) ^ 2) (j * p d)]
  exact (mul_assoc _ _ _).symm

private theorem transform_sub (k : ZMod n) (p : Equiv.Perm (ZMod n))
    (a b : ZMod n → ℂ) :
    transform k p (a - b) = transform k p a - transform k p b := by
  funext d
  simp only [transform_eq_sum, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem transform_parseval (k : ZMod n) (p : Equiv.Perm (ZMod n))
    (a : ZMod n → ℂ) :
    ‖WithLp.toLp 2 (transform k p a)‖ ^ 2 = (n : ℝ)⁻¹ * ∑ j, ‖a j‖ ^ 2 := by
  have hn : (n : ℂ) ≠ 0 := NeZero.ne _
  have hentry (d : ZMod n) :
      conj (transform k p a d) * transform k p a d =
        (n : ℂ)⁻¹ ^ 2 * (conj (fourierSum a (p d)) * fourierSum a (p d)) := by
    change conj (phase (k * (p d)^2) * ((n : ℂ)⁻¹ * fourierSum a (p d))) *
      (phase (k * (p d)^2) * ((n : ℂ)⁻¹ * fourierSum a (p d))) = _
    have hu : conj (phase (k * (p d)^2)) * phase (k * (p d)^2) = 1 := by
      rw [Complex.conj_mul', AddChar.norm_apply]
      norm_num
    simp only [map_mul, map_inv₀, map_natCast]
    calc
      _ = (conj (phase (k * (p d)^2)) * phase (k * (p d)^2)) *
          ((n : ℂ)⁻¹ ^ 2 * (conj (fourierSum a (p d)) * fourierSum a (p d))) := by ring
      _ = _ := by rw [hu, one_mul]
  have hp : (∑ d, conj (fourierSum a (p d)) * fourierSum a (p d)) =
      ∑ d, conj (fourierSum a d) * fourierSum a d :=
    Fintype.sum_equiv p _ _ (fun _ => rfl)
  have h : (∑ d, conj (transform k p a d) * transform k p a d) =
      (n : ℂ)⁻¹ * ∑ j, conj (a j) * a j := by
    simp only [hentry, ← Finset.mul_sum]
    rw [hp, fourierSum_pairing]
    field_simp [hn]
  rw [EuclideanSpace.norm_sq_eq]
  simpa only [Complex.conj_mul', ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    ← Complex.ofReal_pow, ← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
    using congrArg Complex.re h

theorem transform_norm_le (k : ZMod n) (p : Equiv.Perm (ZMod n)) (a : ZMod n → ℂ)
    {M : ℝ} (hM : 0 ≤ M) (ha : ∀ j, ‖a j‖ ≤ M) :
    ‖WithLp.toLp 2 (transform k p a)‖ ≤ M := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [← sq_le_sq₀ (norm_nonneg _) hM, transform_parseval]
  calc
    _ ≤ (n : ℝ)⁻¹ * (∑ _ : ZMod n, M ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun j _ => (sq_le_sq₀ (norm_nonneg _) hM).2 (ha j))
        (inv_nonneg.mpr hn.le)
    _ = M ^ 2 := by
      simp [ZMod.card, nsmul_eq_mul, hn.ne']

private theorem transform_diff_le (k : ZMod n) (p : Equiv.Perm (ZMod n)) (a b : ZMod n → ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hab : ∀ j, ‖a j - b j‖ ≤ M) :
    ‖WithLp.toLp 2 (transform k p a) - WithLp.toLp 2 (transform k p b)‖ ≤ M := by
  rw [← WithLp.toLp_sub, ← transform_sub]
  exact transform_norm_le k p (a - b) hM hab

end Fourier

section System

variable {n : ℕ} [NeZero n] {ι : Type*} [Fintype ι]

abbrev Parameters (ι : Type*) := ι → ℝ

/-- A frequency carries a fixed 1 or pulls back one Cayley parameter. The chirp
is the quadratic coefficient in the seed, including the factor of one half. -/
structure Seed (n : ℕ) (ι : Type*) where
  chirp : ZMod n
  coord : ZMod n → Option ι

def spectrum (sign : ι → ℤ) (S : Seed n ι) (x : Parameters ι) (j : ZMod n) : ℂ :=
  match S.coord j with
  | none => 1
  | some a => ChirpedReplay.cayley (x a) (sign a)

def spectrumD (sign : ι → ℤ) (S : Seed n ι) (x : Parameters ι) (j : ZMod n) :
    Parameters ι →L[ℝ] ℂ :=
  match S.coord j with
  | none => 0
  | some a => (proj a).smulRight (ChirpedReplay.cayleySlope (x a) (sign a))

theorem hasFDerivAt_spectrum (sign : ι → ℤ) (S : Seed n ι) (x : Parameters ι) (j : ZMod n) :
    HasFDerivAt (fun y => spectrum sign S y j) (spectrumD sign S x j) x := by
  cases h : S.coord j with
  | none => simpa only [spectrum, spectrumD, h] using (hasFDerivAt_const (1 : ℂ) x)
  | some a =>
    let ev : Parameters ι →L[ℝ] ℝ := proj (R := ℝ) (φ := fun _ : ι => ℝ) a
    have hd := (hasDerivAt_cayley (sign a) (x a)).hasFDerivAt.comp x ev.hasFDerivAt
    simp only [spectrum, spectrumD, h]
    change HasFDerivAt ((fun t : ℝ => ChirpedReplay.cayley t (sign a)) ∘ ev)
      (ev.smulRight (ChirpedReplay.cayleySlope (x a) (sign a))) x
    simpa only [toSpanSingleton_comp] using hd

def seedValue (sign : ι → ℤ) (S : Seed n ι) (p : Equiv.Perm (ZMod n)) (x : Parameters ι) :
    ZMod n → ℂ :=
  transform S.chirp p (spectrum sign S x)

def seedD (sign : ι → ℤ) (S : Seed n ι) (p : Equiv.Perm (ZMod n))
    (x : Parameters ι) (d : ZMod n) : Parameters ι →L[ℝ] ℂ :=
  ((n : ℂ)⁻¹) • ∑ j, phase (S.chirp * (p d) ^ 2 + j * p d) • spectrumD sign S x j

theorem seedD_apply (sign : ι → ℤ) (S : Seed n ι) (p : Equiv.Perm (ZMod n))
    (x u : Parameters ι) :
    (fun d => seedD sign S p x d u) = transform S.chirp p (fun j => spectrumD sign S x j u) := by
  funext d
  simp only [transform_eq_sum, seedD, _root_.smul_apply, _root_.sum_apply, smul_eq_mul]

theorem hasFDerivAt_seedValue (sign : ι → ℤ) (S : Seed n ι) (p : Equiv.Perm (ZMod n))
    (x : Parameters ι) (d : ZMod n) :
    HasFDerivAt (fun y => seedValue sign S p y d) (seedD sign S p x d) x := by
  simp only [seedValue, transform_eq_sum, seedD]
  exact (HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (hasFDerivAt_spectrum sign S x j).const_mul _)).const_mul _

private theorem spectrum_norm (sign : ι → ℤ) (hs : ∀ j, sign j = 1 ∨ sign j = -1)
    (S : Seed n ι) (x : Parameters ι) (j : ZMod n) :
    ‖spectrum sign S x j‖ ≤ 1 := by
  cases h : S.coord j with
  | none => simp [spectrum, h]
  | some a =>
    simpa only [spectrum, h] using
      (ChirpedReplay.cayley_norm_bounds (x a) (sign a) (hs a)).1.le

private theorem spectrumD_norm (sign : ι → ℤ) (hs : ∀ j, sign j = 1 ∨ sign j = -1)
    (S : Seed n ι) (x u : Parameters ι) (j : ZMod n) :
    ‖spectrumD sign S x j u‖ ≤ 2 * ‖u‖ := by
  cases h : S.coord j with
  | none => simpa [spectrumD, h] using (show 0 ≤ 2 * ‖u‖ by positivity)
  | some a =>
    simp only [spectrumD, h, smulRight_apply, proj_apply, norm_smul]
    calc
      _ ≤ ‖u a‖ * 2 := mul_le_mul_of_nonneg_left
        (ChirpedReplay.cayley_norm_bounds (x a) (sign a) (hs a)).2 (norm_nonneg _)
      _ ≤ 2 * ‖u‖ := by
        rw [mul_comm ‖u a‖]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm u a) (by norm_num)

private theorem spectrum_diff (sign : ι → ℤ) (hs : ∀ j, sign j = 1 ∨ sign j = -1)
    (S : Seed n ι) (x y : Parameters ι) (j : ZMod n) :
    ‖spectrum sign S x j - spectrum sign S y j‖ ≤ 2 * ‖x - y‖ := by
  cases h : S.coord j with
  | none => simpa [spectrum, h] using (show 0 ≤ 2 * ‖x - y‖ by positivity)
  | some a =>
    simpa only [spectrum, h] using
      (cayley_diff (sign a) (hs a) (x a) (y a)).trans
        (mul_le_mul_of_nonneg_left (norm_le_pi_norm (x - y) a) (by norm_num))

private theorem spectrumD_diff (sign : ι → ℤ) (hs : ∀ j, sign j = 1 ∨ sign j = -1)
    (S : Seed n ι) (x y u : Parameters ι) (j : ZMod n) :
    ‖spectrumD sign S x j u - spectrumD sign S y j u‖ ≤ (4 * ‖x - y‖) * ‖u‖ := by
  cases h : S.coord j with
  | none => simpa [spectrumD, h] using (show 0 ≤ (4 * ‖x - y‖) * ‖u‖ by positivity)
  | some a =>
    simp only [spectrumD, h, smulRight_apply, proj_apply, ← smul_sub, norm_smul]
    rw [mul_comm]
    exact mul_le_mul
      ((slope_diff (sign a) (hs a) (x a) (y a)).trans
        (mul_le_mul_of_nonneg_left (norm_le_pi_norm (x - y) a) (by norm_num)))
      (norm_le_pi_norm u a) (norm_nonneg _) (by positivity)

def projection (imag : Bool) : ℂ →L[ℝ] ℝ :=
  if imag then Complex.imCLM else Complex.reCLM

@[simp] theorem projection_apply (imag : Bool) (z : ℂ) :
    projection imag z = ChirpedReplay.project imag z := by
  cases imag <;> rfl

private theorem norm_projection_le (imag : Bool) (z : ℂ) : ‖projection imag z‖ ≤ ‖z‖ := by
  cases imag
  · simpa [projection, Real.norm_eq_abs] using Complex.abs_re_le_norm z
  · simpa [projection, Real.norm_eq_abs] using Complex.abs_im_le_norm z

/-- The two seed views for a retained row and its real or imaginary projection. -/
structure Row (n : ℕ) (ι : Type*) where
  left : Seed n ι
  right : Seed n ι
  perm : Equiv.Perm (ZMod n)
  imag : Bool

private abbrev leftValue (sign : ι → ℤ) (r : Row n ι) := seedValue sign r.left r.perm
private abbrev rightValue (sign : ι → ℤ) (r : Row n ι) := seedValue sign r.right (Equiv.refl _)
private abbrev leftD (sign : ι → ℤ) (r : Row n ι) := seedD sign r.left r.perm
private abbrev rightD (sign : ι → ℤ) (r : Row n ι) := seedD sign r.right (Equiv.refl _)

private abbrev conjCLM : ℂ →L[ℝ] ℂ := (Complex.conjCLE : ℂ →L[ℝ] ℂ)

def rowValue (sign : ι → ℤ) (r : Row n ι) (x : Parameters ι) : ℝ :=
  projection r.imag (∑ d, conj (leftValue sign r x d) * rightValue sign r x d)

def rowD (sign : ι → ℤ) (r : Row n ι) (x : Parameters ι) : Parameters ι →L[ℝ] ℝ :=
  (projection r.imag).comp
    (∑ d : ZMod n, (conj (leftValue sign r x d) • rightD sign r x d +
      rightValue sign r x d • (conjCLM.comp (leftD sign r x d))))

theorem rowD_apply (sign : ι → ℤ) (r : Row n ι) (x u : Parameters ι) :
    rowD sign r x u = projection r.imag
      ((∑ d, conj (leftD sign r x d u) * rightValue sign r x d) +
        ∑ d, conj (leftValue sign r x d) * rightD sign r x d u) := by
  simp only [rowD, comp_apply, _root_.sum_apply, add_apply, _root_.smul_apply, smul_eq_mul]
  apply congrArg (fun z : ℂ => projection r.imag z)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  change conj (leftValue sign r x d) * rightD sign r x d u +
      rightValue sign r x d * conj (leftD sign r x d u) =
    conj (leftD sign r x d u) * rightValue sign r x d +
      conj (leftValue sign r x d) * rightD sign r x d u
  ac_rfl

theorem hasFDerivAt_rowValue (sign : ι → ℤ) (r : Row n ι) (x : Parameters ι) :
    HasFDerivAt (rowValue sign r) (rowD sign r x) x := by
  have hleft (d : ZMod n) : HasFDerivAt (fun y => conj (leftValue sign r y d))
      (conjCLM.comp (leftD sign r x d)) x :=
    conjCLM.hasFDerivAt.comp x (hasFDerivAt_seedValue sign r.left r.perm x d)
  unfold rowValue rowD
  exact (projection r.imag).hasFDerivAt.comp x
    (HasFDerivAt.fun_sum (u := Finset.univ) (fun d _ =>
      (hleft d).fun_mul (hasFDerivAt_seedValue sign r.right (Equiv.refl _) x d)))

private def euclideanSeed (sign : ι → ℤ) (S : Seed n ι) (p : Equiv.Perm (ZMod n))
    (x : Parameters ι) : EuclideanSpace ℂ (ZMod n) :=
  WithLp.toLp 2 (seedValue sign S p x)

private def euclideanSeedD (sign : ι → ℤ) (S : Seed n ι) (p : Equiv.Perm (ZMod n))
    (x u : Parameters ι) : EuclideanSpace ℂ (ZMod n) :=
  WithLp.toLp 2 (fun d => seedD sign S p x d u)

private theorem euclideanSeed_bounds (sign : ι → ℤ) (hs : ∀ j, sign j = 1 ∨ sign j = -1)
    (S : Seed n ι) (p : Equiv.Perm (ZMod n)) (x y u : Parameters ι) :
    ‖euclideanSeed sign S p x‖ ≤ 1 ∧
    ‖euclideanSeedD sign S p x u‖ ≤ 2 * ‖u‖ ∧
    ‖euclideanSeed sign S p x - euclideanSeed sign S p y‖ ≤ 2 * ‖x - y‖ ∧
    ‖euclideanSeedD sign S p x u - euclideanSeedD sign S p y u‖ ≤ (4 * ‖x - y‖) * ‖u‖ := by
  simp only [euclideanSeed, euclideanSeedD, seedValue, seedD_apply]
  exact ⟨transform_norm_le _ _ _ zero_le_one (spectrum_norm sign hs S x),
    transform_norm_le _ _ _ (by positivity) (spectrumD_norm sign hs S x u),
    transform_diff_le _ _ _ _ (by positivity) (spectrum_diff sign hs S x y),
    transform_diff_le _ _ _ _ (by positivity) (spectrumD_diff sign hs S x y u)⟩

/-- The pointwise bounds used by the replay's rounding-error lemmas. -/
theorem seed_entry_bounds [DecidableEq ι] (sign : ι → ℤ)
    (hs : ∀ j, sign j = 1 ∨ sign j = -1)
    (S : Seed n ι) (p : Equiv.Perm (ZMod n)) (x : Parameters ι) (d : ZMod n) (j : ι) :
    ‖seedValue sign S p x d‖ ≤ 1 ∧ ‖seedD sign S p x d (Pi.single j 1)‖ ≤ 2 := by
  let u : Parameters ι := Pi.single (M := fun _ : ι => ℝ) j 1
  obtain ⟨hv, hd, _, _⟩ := euclideanSeed_bounds sign hs S p x x u
  constructor
  · exact (PiLp.norm_apply_le (euclideanSeed sign S p x) d).trans hv
  · have hunit : ‖u‖ = 1 := by
      change ‖Pi.single (M := fun _ : ι => ℝ) j 1‖ = 1
      rw [Pi.norm_single, norm_one]
    rw [hunit, mul_one] at hd
    exact (PiLp.norm_apply_le (euclideanSeedD sign S p x u) d).trans hd

private theorem inner_diff_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a b c d : H) :
    ‖⟪a, b⟫_ℂ - ⟪c, d⟫_ℂ‖ ≤ ‖a - c‖ * ‖b‖ + ‖c‖ * ‖b - d‖ := by
  rw [show ⟪a, b⟫_ℂ - ⟪c, d⟫_ℂ = ⟪a - c, b⟫_ℂ + ⟪c, b - d⟫_ℂ by
    rw [inner_sub_left, inner_sub_right]; abel]
  exact (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))

private theorem pairing_eq (a b : ZMod n → ℂ) :
    (∑ d, conj (a d) * b d) = ⟪WithLp.toLp 2 a, WithLp.toLp 2 b⟫_ℂ := by
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct]
  exact Finset.sum_congr rfl fun d _ => mul_comm _ _

theorem rowD_drift (sign : ι → ℤ) (hs : ∀ j, sign j = 1 ∨ sign j = -1)
    (r : Row n ι) (x y u : Parameters ι) :
    ‖rowD sign r x u - rowD sign r y u‖ ≤ (16 * ‖x - y‖) * ‖u‖ := by
  obtain ⟨_, _, hLxy, hDLxy⟩ := euclideanSeed_bounds sign hs r.left r.perm x y u
  obtain ⟨hLy, hDLy, _, _⟩ := euclideanSeed_bounds sign hs r.left r.perm y x u
  obtain ⟨hRx, hDRx, hRxy, hDRxy⟩ :=
    euclideanSeed_bounds sign hs r.right (Equiv.refl _) x y u
  rw [rowD_apply, rowD_apply, ← map_sub]
  refine (norm_projection_le _ _).trans ?_
  simp only [pairing_eq, add_sub_add_comm]
  change ‖(⟪euclideanSeedD sign r.left r.perm x u,
              euclideanSeed sign r.right (Equiv.refl _) x⟫_ℂ -
            ⟪euclideanSeedD sign r.left r.perm y u,
              euclideanSeed sign r.right (Equiv.refl _) y⟫_ℂ) +
          (⟪euclideanSeed sign r.left r.perm x,
              euclideanSeedD sign r.right (Equiv.refl _) x u⟫_ℂ -
            ⟪euclideanSeed sign r.left r.perm y,
              euclideanSeedD sign r.right (Equiv.refl _) y u⟫_ℂ)‖ ≤ _
  refine (norm_add_le _ _).trans
    ((add_le_add (inner_diff_le _ _ _ _) (inner_diff_le _ _ _ _)).trans ?_)
  calc
    _ ≤ (4 * ‖x - y‖) * ‖u‖ * 1 + (2 * ‖u‖) * (2 * ‖x - y‖) +
        ((2 * ‖x - y‖) * (2 * ‖u‖) + 1 * ((4 * ‖x - y‖) * ‖u‖)) := by
      exact add_le_add
        (add_le_add (mul_le_mul hDLxy hRx (norm_nonneg _) (by positivity))
          (mul_le_mul hDLy hRxy (norm_nonneg _) (by positivity)))
        (add_le_add (mul_le_mul hLxy hDRx (norm_nonneg _) (by positivity))
          (mul_le_mul hLy hDRxy (norm_nonneg _) zero_le_one))
    _ = _ := by ring

def residual (sign : ι → ℤ) (rows : ι → Row n ι) (x : Parameters ι) : Parameters ι :=
  fun i => rowValue sign (rows i) x

def derivative (sign : ι → ℤ) (rows : ι → Row n ι) (x : Parameters ι) :
    Parameters ι →L[ℝ] Parameters ι :=
  ContinuousLinearMap.pi fun i => rowD sign (rows i) x

theorem hasFDerivAt_residual (sign : ι → ℤ) (rows : ι → Row n ι) (x : Parameters ι) :
    HasFDerivAt (residual sign rows) (derivative sign rows x) x :=
  hasFDerivAt_pi.mpr fun i => hasFDerivAt_rowValue sign (rows i) x

/-- Uniform drift in the operator norm induced by the two coordinate sup norms. -/
theorem derivative_drift (sign : ι → ℤ) (hs : ∀ j, sign j = 1 ∨ sign j = -1)
    (rows : ι → Row n ι) (x y : Parameters ι) :
    ‖derivative sign rows x - derivative sign rows y‖ ≤ 16 * ‖x - y‖ := by
  apply opNorm_le_bound _ (by positivity)
  intro u
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  exact fun i => rowD_drift sign hs (rows i) x y u

end System

end

end ChirpedAnalyticDrift
