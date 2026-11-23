/- GID: D5/S3/Quantum/Measurement/Auric/FairProjectiveRecord
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/FairProjectiveRecord
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Quantum.Measurement.Auric.OriginalInstrument, lake/module/D5.S3.Entropy.Forgetting.PushforwardComposition, mathlib/module/Mathlib.NumberTheory.Real.GoldenRatio, mathlib/module/Mathlib.RingTheory.AdjoinRoot, mathlib/module/Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective, mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse]
   utility: none
   digest: The actual fixed-horizon AURIC record and its real projective endpoint law. -/

import D5.S3.Quantum.Measurement.Auric.OriginalInstrument
import D5.S3.Entropy.Forgetting.PushforwardComposition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.RingTheory.AdjoinRoot

namespace D5.S3.Quantum.Measurement.Auric.FairProjectiveRecord

open Matrix Polynomial
open scoped Matrix MatrixGroups Kronecker
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.Forgetting.PushforwardComposition
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open OriginalInstrument SimulatorUpper ProjectiveTree

noncomputable section

private noncomputable def sine : ℝ := (Real.sqrt 5 - 1) / 2
noncomputable def angle : ℝ := Real.arcsin sine
private noncomputable def cosine : ℝ := Real.cos angle
private noncomputable def parameter : ℂ := Complex.I * (Real.tan angle : ℂ)

private theorem sqrt_five_sq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)

private theorem sine_pos : 0 < sine := by
  have := Real.sqrt_nonneg 5
  unfold sine
  nlinarith only [sqrt_five_sq, this, sq_nonneg (Real.sqrt 5 - 1)]

private theorem sine_lt_one : sine < 1 := by
  have := Real.sqrt_nonneg 5
  unfold sine
  nlinarith only [sqrt_five_sq, this, sq_nonneg (Real.sqrt 5 - 3)]

private theorem sine_sq : sine ^ 2 = 1 - sine := by
  unfold sine
  nlinarith only [sqrt_five_sq]

private theorem sin_angle : Real.sin angle = sine :=
  Real.sin_arcsin (by linarith [sine_pos]) sine_lt_one.le

private theorem cosine_sq : cosine ^ 2 = sine := by
  rw [cosine, angle, Real.cos_arcsin, Real.sq_sqrt (by rw [sine_sq]; linarith [sine_pos]),
    sine_sq]
  ring

private theorem cosine_pos : 0 < cosine := by
  have h := Real.cos_arcsin_nonneg sine
  change 0 ≤ cosine at h
  by_contra! he
  have hc : cosine = 0 := le_antisymm he h
  have hsq := cosine_sq
  rw [hc] at hsq
  nlinarith [hsq, sine_pos]

private theorem tan_angle : Real.tan angle = cosine := by
  rw [Real.tan_eq_sin_div_cos, sin_angle]
  change sine / cosine = cosine
  rw [div_eq_iff (ne_of_gt cosine_pos), ← cosine_sq, pow_two]

private theorem parameter_sq : parameter ^ 2 = -(sine : ℂ) := by
  rw [parameter, tan_angle, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, cosine_sq]
  ring

private theorem parameter_four : parameter ^ 4 = parameter ^ 2 + 1 := by
  rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, parameter_sq, neg_pow, even_two.neg_one_pow,
    one_mul, ← Complex.ofReal_pow, sine_sq]
  push_cast
  ring

private theorem sine_irrational : Irrational sine := by
  have h : Irrational (Real.sqrt 5) := by
    simpa using (show Nat.Prime 5 by norm_num).irrational_sqrt
  convert (h.sub_ratCast (1 : ℚ)).div_ratCast (show (2 : ℚ) ≠ 0 by norm_num) using 1
  norm_num [sine]

/-- The coefficient basis evaluated at the distinguished parameter. -/
private structure QuarticCoefficients where
  constant : ℤ
  linear : ℤ
  quadratic : ℤ
  cubic : ℤ
  

namespace QuarticCoefficients

private def zero : QuarticCoefficients := ⟨0, 0, 0, 0⟩
private def one : QuarticCoefficients := ⟨1, 0, 0, 0⟩

private def add (x y : QuarticCoefficients) : QuarticCoefficients :=
  ⟨x.constant + y.constant, x.linear + y.linear, x.quadratic + y.quadratic,
    x.cubic + y.cubic⟩

private def shift (x : QuarticCoefficients) : QuarticCoefficients :=
  ⟨x.cubic, x.constant, x.linear + x.cubic, x.quadratic⟩

private noncomputable def eval (x : QuarticCoefficients) : ℂ :=
  x.constant + x.linear * parameter + x.quadratic * parameter ^ 2 + x.cubic * parameter ^ 3

@[simp] private theorem eval_zero : eval zero = 0 := by simp [eval, zero]
@[simp] private theorem eval_one : eval one = 1 := by simp [eval, one]

@[simp] private theorem eval_add (x y : QuarticCoefficients) : eval (x.add y) = eval x + eval y := by
  simp only [eval, add, Int.cast_add]
  ring

@[simp] private theorem eval_shift (x : QuarticCoefficients) : eval x.shift = parameter * eval x := by
  simp only [eval, shift, Int.cast_add]
  linear_combination -(x.cubic : ℂ) * parameter_four

private theorem int_pair_injective {a b c d : ℤ}
    (h : (a : ℝ) - b * sine = c - d * sine) : a = c ∧ b = d := by
  have hb : b = d := by
    by_contra hne
    have hden : ((b - d : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hne
    have heq : sine = (((a - c : ℤ) : ℝ) / ((b - d : ℤ) : ℝ)) := by
      apply (eq_div_iff hden).2
      push_cast
      linarith only [h]
    apply sine_irrational
    refine ⟨((a - c : ℤ) : ℚ) / ((b - d : ℤ) : ℚ), ?_⟩
    simpa using heq.symm
  subst d
  exact ⟨by exact_mod_cast (show (a : ℝ) = c by linarith only [h]), rfl⟩

/-- Integer coefficients of degree below four are recovered from their complex value. -/
private theorem eval_injective : Function.Injective eval := by
  intro x y h
  have cub : parameter ^ 3 = -(sine : ℂ) * parameter := by
    rw [pow_succ, parameter_sq]
  rw [eval, eval, cub, parameter_sq, parameter, tan_angle] at h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.mul_im, Complex.neg_im] at hr hi
  obtain ⟨hc, hq⟩ := int_pair_injective (a := x.constant) (b := x.quadratic)
    (c := y.constant) (d := y.quadratic) (by linarith only [hr])
  obtain ⟨hl, hb⟩ := int_pair_injective (a := x.linear) (b := x.cubic)
    (c := y.linear) (d := y.cubic) (by
      apply mul_right_cancel₀ (ne_of_gt cosine_pos)
      linarith only [hi])
  cases x
  cases y
  cases hc
  cases hq
  cases hl
  cases hb
  rfl

end QuarticCoefficients

abbrev Qutrit := Matrix (Fin 3) (Fin 3) ℂ

/-- The unrotated letters in the (u,v,z) source basis, given by their row permutations. -/
private def row₀ (i : Fin 3) : Fin 3 := ![0, 2, 1] i
private def row₁ (i : Fin 3) : Fin 3 := ![1, 2, 0] i

private def U₀ : Qutrit := of fun i j => if row₀ i = j then 1 else 0
private def U₁ : Qutrit := of fun i j => if row₁ i = j then 1 else 0

/-- The actual normalized qutrit branches of Record Memory Theorem 2.2. -/
noncomputable def letter (b : Bool) : Qutrit :=
  (cosine : ℂ) • (if b then U₁ else U₀) +
    (Complex.I * (sine : ℂ)) • (if b then U₀ else U₁)

private noncomputable def unscaledLetter (b : Bool) : Qutrit :=
  (if b then U₁ else U₀) + parameter • (if b then U₀ else U₁)

private theorem letter_eq_scale (b : Bool) : letter b = (cosine : ℂ) • unscaledLetter b := by
  have h : (cosine : ℂ) * parameter = Complex.I * (sine : ℂ) := by
    rw [parameter, tan_angle, ← cosine_sq, Complex.ofReal_pow]
    ring
  rw [letter, unscaledLetter, smul_add, smul_smul, h]

/-- Products are indexed latest outcome first as in the source's chronological convention. -/
noncomputable def word : List Bool → Qutrit
  | [] => 1
  | b :: w => letter b * word w

private abbrev CoefficientMatrix := Matrix (Fin 3) (Fin 3) QuarticCoefficients

private def recurrence : List Bool → CoefficientMatrix
  | [] => of fun i j => if i = j then QuarticCoefficients.one else QuarticCoefficients.zero
  | b :: w => of fun i j =>
    let x := recurrence w (row₀ i) j
    let y := recurrence w (row₁ i) j
    if b then y.add x.shift else x.add y.shift

private theorem word_eq_recurrence (w : List Bool) :
    word w = (cosine : ℂ) ^ w.length • (recurrence w).map QuarticCoefficients.eval := by
  induction w with
  | nil =>
    ext i j
    by_cases h : i = j <;> simp [word, recurrence, Matrix.one_apply, h]
  | cons b w ih =>
    rw [word, letter_eq_scale, ih, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    simp only [List.length_cons, pow_succ, mul_comm ((cosine : ℂ) ^ w.length)]
    congr 1
    cases b <;> ext i j <;>
      simp [unscaledLetter, recurrence, Matrix.mul_apply, U₀, U₁, add_mul, ite_mul, Finset.sum_add_distrib]

private theorem cosine_complex_ne : (cosine : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt cosine_pos

private theorem word_eq_iff_recurrence_eq {v w : List Bool} (h : v.length = w.length) :
    word v = word w ↔ recurrence v = recurrence w := by
  rw [word_eq_recurrence, word_eq_recurrence, h]
  constructor
  · intro he
    ext i j
    apply QuarticCoefficients.eval_injective
    exact mul_left_cancel₀ (pow_ne_zero _ cosine_complex_ne) (congrArg (fun m : Qutrit => m i j) he)
  · intro he
    rw [he]

private noncomputable def commonEigenvalue : ℂ := (cosine : ℂ) + Complex.I * (sine : ℂ)

private theorem commonEigenvalue_ne : commonEigenvalue ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp [commonEigenvalue, Complex.add_re, Complex.mul_re] at hr
  exact (ne_of_gt cosine_pos) hr

private theorem letter_common_line (b : Bool) :
    letter b *ᵥ (fun _ => 1) = fun _ => commonEigenvalue := by
  cases b <;> funext i <;>
    simp [letter, Matrix.mulVec, dotProduct, U₀, U₁, commonEigenvalue, Finset.sum_add_distrib]

private theorem word_common_line (w : List Bool) :
    word w *ᵥ (fun _ => 1) = fun _ => commonEigenvalue ^ w.length := by
  induction w with
  | nil => simp [word]
  | cons b w ih =>
    rw [word, ← Matrix.mulVec_mulVec, ih]
    have h : (fun _ : Fin 3 => commonEigenvalue ^ w.length) =
        commonEigenvalue ^ w.length • (fun _ : Fin 3 => (1 : ℂ)) := by
      ext i
      simp
    rw [h, Matrix.mulVec_smul, letter_common_line]
    ext i
    simp [pow_succ]

/-- Same-horizon projective equality of full qutrit products is exact equality. -/
private theorem projective_iff_word_eq {v w : List Bool} (hlen : v.length = w.length) :
    (∃ scalar : ℂ, word v = scalar • word w) ↔ word v = word w := by
  constructor
  · rintro ⟨scalar, hs⟩
    have h := congrArg (fun m : Qutrit => (m *ᵥ (fun _ => 1)) 0) hs
    simp only [Matrix.smul_mulVec, word_common_line, Pi.smul_apply, smul_eq_mul, hlen] at h
    have he : scalar = 1 := mul_right_cancel₀ (pow_ne_zero _ commonEigenvalue_ne) (by simpa using h.symm)
    simpa [he] using hs
  · intro h
    exact ⟨1, by simpa using h⟩

section Specialization

variable {R : Type*} [CommRing R]

private def QuarticCoefficients.specialize (t : R) (x : QuarticCoefficients) : R :=
  x.constant + x.linear * t + x.quadratic * t ^ 2 + x.cubic * t ^ 3

@[simp] private theorem QuarticCoefficients.specialize_zero (t : R) :
    specialize t zero = 0 := by simp [specialize, zero]

@[simp] private theorem QuarticCoefficients.specialize_one (t : R) :
    specialize t one = 1 := by simp [specialize, one]

@[simp] private theorem QuarticCoefficients.specialize_add (t : R) (x y : QuarticCoefficients) :
    specialize t (x.add y) = specialize t x + specialize t y := by
  simp only [specialize, QuarticCoefficients.add, Int.cast_add]
  ring

private theorem QuarticCoefficients.specialize_shift {t : R} (ht : t ^ 4 = t ^ 2 + 1)
    (x : QuarticCoefficients) : specialize t x.shift = t * specialize t x := by
  simp only [specialize, shift, Int.cast_add]
  linear_combination -(x.cubic : R) * ht

private def specializedLetter (t : R) (b : Bool) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun i j =>
    (if (if b then row₁ i else row₀ i) = j then 1 else 0) +
      t * (if (if b then row₀ i else row₁ i) = j then 1 else 0)

private def specializedWord (t : R) : List Bool → Matrix (Fin 3) (Fin 3) R
  | [] => 1
  | b :: w => specializedLetter t b * specializedWord t w

private theorem specializedWord_eq_recurrence {t : R} (ht : t ^ 4 = t ^ 2 + 1) (w : List Bool) :
    specializedWord t w = (recurrence w).map (QuarticCoefficients.specialize t) := by
  induction w with
  | nil =>
    ext i j
    by_cases h : i = j <;> simp [specializedWord, recurrence, Matrix.one_apply, h]
  | cons b w ih =>
    rw [specializedWord, ih]
    cases b <;> ext i j <;>
      simp [specializedLetter, recurrence, Matrix.mul_apply, add_mul, ite_mul,
        Finset.sum_add_distrib, QuarticCoefficients.specialize_shift ht]

/-- Projective collisions of the actual equal-length qutrit words survive
every specialization of the source quartic, including the real root. -/
private theorem specializedWord_eq_of_projective {t : R} (ht : t ^ 4 = t ^ 2 + 1) {v w : List Bool}
    (hlen : v.length = w.length) (h : ∃ scalar : ℂ, word v = scalar • word w) :
    specializedWord t v = specializedWord t w := by
  rw [specializedWord_eq_recurrence ht, specializedWord_eq_recurrence ht,
    (word_eq_iff_recurrence_eq hlen).mp ((projective_iff_word_eq hlen).mp h)]

end Specialization

private noncomputable def realRoot : ℝ := -Real.sqrt (1 + sine)

private theorem realRoot_sq : realRoot ^ 2 = 1 + sine := by
  rw [realRoot, neg_sq, Real.sq_sqrt (by linarith only [sine_pos])]

private theorem realRoot_quartic : realRoot ^ 4 = realRoot ^ 2 + 1 := by
  rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, realRoot_sq]
  nlinarith only [sine_sq]

private abbrev RealPlaneMatrix := Matrix (Fin 2) (Fin 2) ℝ



/-- The positive square root of the golden ratio. The qutrit specialization uses its negative. -/
def d : ℝ := Real.sqrt (1 + sine)

private theorem d_ne_zero : d ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.2 (by linarith [sine_pos]))

private theorem d_quartic : d ^ 4 = d ^ 2 + 1 := by
  simpa only [show realRoot = -d from rfl, (show Even (4 : ℕ) by decide).neg_pow, even_two.neg_pow] using
    realRoot_quartic


/-- The common modulus of the integral, rational and characteristic-three coordinates. -/
private def quartic (R : Type*) [CommRing R] : R[X] := X ^ 4 - X ^ 2 - 1

private theorem quartic_eval₂ {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (t : S) :
    (quartic R).eval₂ f t = t ^ 4 - t ^ 2 - 1 := by
  simp [quartic, eval₂_sub, eval₂_pow]

private theorem quartic_monic (R : Type*) [CommRing R] [Nontrivial R] : (quartic R).Monic := by
  have h : (X ^ 2 : R[X]).degree < (X ^ 4 : R[X]).degree := by
    simp
    norm_num
  apply (Monic.sub_of_left (monic_X_pow 4) h).sub_of_left
  rw [degree_sub_eq_left_of_degree_lt h]
  simp

private theorem quartic_natDegree (R : Type*) [CommRing R] [Nontrivial R] :
    (quartic R).natDegree = 4 := by
  have h : (X ^ 2 : R[X]).natDegree < (X ^ 4 : R[X]).natDegree := by simp
  unfold quartic
  rw [natDegree_sub_eq_left_of_natDegree_lt, natDegree_sub_eq_left_of_natDegree_lt h]
  · simp
  · rw [natDegree_sub_eq_left_of_natDegree_lt h]
    simp

private theorem rational_pair_zero {x : ℝ} (hx : Irrational x) {a b : ℚ}
    (h : (a : ℝ) + (b : ℝ) * x = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst b
    exact ⟨by exact_mod_cast (show (a : ℝ) = 0 by simpa using h), rfl⟩
  · exfalso
    apply hx
    refine ⟨-a / b, ?_⟩
    push_cast
    exact (div_eq_iff (by exact_mod_cast hb)).2 (by linarith only [h])

private theorem sq_eq_goldenRatio {t : ℝ} (h : t ^ 4 = t ^ 2 + 1) : t ^ 2 = Real.goldenRatio := by
  have hfactor : (t ^ 2 - Real.goldenRatio) * (t ^ 2 - Real.goldenConj) = 0 := by
    calc
      _ = t ^ 4 - (Real.goldenRatio + Real.goldenConj) * t ^ 2 +
          Real.goldenRatio * Real.goldenConj := by ring
      _ = 0 := by rw [Real.goldenRatio_add_goldenConj, Real.goldenRatio_mul_goldenConj]; linarith only [h]
  rcases mul_eq_zero.mp hfactor with he | he
  · exact sub_eq_zero.mp he
  · linarith only [he, sq_nonneg t, Real.goldenConj_neg]

/-- A rational relation between the first four powers vanishes coefficientwise.
Squaring the even and odd parts and conjugating in the golden-ratio field changes
the square multiplier from the positive golden ratio to its negative conjugate. -/
private theorem rational_coefficients_zero {t : ℝ} (ht : t ^ 4 = t ^ 2 + 1) {a b c e : ℚ}
    (h : (a : ℝ) + (b : ℝ) * t + (c : ℝ) * t ^ 2 + (e : ℝ) * t ^ 3 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0 := by
  have hs := sq_eq_goldenRatio ht
  have he : (a : ℝ) + (c : ℝ) * Real.goldenRatio =
      -t * ((b : ℝ) + (e : ℝ) * Real.goldenRatio) := by
    rw [← hs]
    linear_combination h
  have hsq : ((a : ℝ) + (c : ℝ) * Real.goldenRatio) ^ 2 -
      Real.goldenRatio * ((b : ℝ) + (e : ℝ) * Real.goldenRatio) ^ 2 = 0 := by
    rw [he, mul_pow, neg_sq, hs, sub_self]
  have expand (x : ℝ) (hx : x ^ 2 = x + 1) :
      ((a : ℝ) + (c : ℝ) * x) ^ 2 - x * ((b : ℝ) + (e : ℝ) * x) ^ 2 =
        ((a ^ 2 + c ^ 2 - 2 * b * e - e ^ 2 : ℚ) : ℝ) +
        ((2 * a * c + c ^ 2 - b ^ 2 - 2 * b * e - 2 * e ^ 2 : ℚ) : ℝ) * x := by
    push_cast
    linear_combination
      ((c : ℝ) ^ 2 - 2 * b * e - (e : ℝ) ^ 2 * (x + 1)) * hx
  rw [expand _ Real.goldenRatio_sq] at hsq
  obtain ⟨h₀, h₁⟩ := rational_pair_zero Real.goldenRatio_irrational hsq
  have hc : ((a : ℝ) + (c : ℝ) * Real.goldenConj) ^ 2 -
      Real.goldenConj * ((b : ℝ) + (e : ℝ) * Real.goldenConj) ^ 2 = 0 := by
    rw [expand _ Real.goldenConj_sq, h₀, h₁]
    simp
  have hb : (b : ℝ) + (e : ℝ) * Real.goldenConj = 0 := by
    by_contra hn
    have hp := mul_pos (neg_pos.mpr Real.goldenConj_neg) (sq_pos_of_ne_zero hn)
    linarith only [hc, hp, sq_nonneg ((a : ℝ) + (c : ℝ) * Real.goldenConj)]
  have ha : (a : ℝ) + (c : ℝ) * Real.goldenConj = 0 := by
    simpa [hb] using hc
  obtain ⟨ha, hc⟩ := rational_pair_zero Real.goldenConj_irrational ha
  obtain ⟨hb, he⟩ := rational_pair_zero Real.goldenConj_irrational hb
  exact ⟨ha, hb, hc, he⟩

private theorem polynomial_eq_zero_of_aeval {t : ℝ} (ht : t ^ 4 = t ^ 2 + 1)
    {p : ℚ[X]} (hdeg : p.natDegree < 4) (he : aeval t p = 0) : p = 0 := by
  have hrepr := p.as_sum_range_C_mul_X_pow' hdeg
  have h := congrArg (aeval t : ℚ[X] →ₐ[ℚ] ℝ) hrepr
  rw [he] at h
  simp [Finset.sum_range_succ] at h
  obtain ⟨h₀, h₁, h₂, h₃⟩ := rational_coefficients_zero ht h.symm
  rw [hrepr]
  simp [Finset.sum_range_succ, h₀, h₁, h₂, h₃]

private abbrev IntegralQuartic := AdjoinRoot (quartic ℤ)
private abbrev ModThreeQuartic := AdjoinRoot (quartic (ZMod 3))

private theorem root_quartic (R : Type*) [CommRing R] :
    AdjoinRoot.root (quartic R) ^ 4 = AdjoinRoot.root (quartic R) ^ 2 + 1 := by
  have h := AdjoinRoot.eval₂_root (f := quartic R)
  rw [quartic_eval₂] at h
  exact sub_eq_zero.mp (by linear_combination h)

private noncomputable def realEvaluation (t : ℝ) (ht : t ^ 4 = t ^ 2 + 1) :
    IntegralQuartic →+* ℝ :=
  AdjoinRoot.lift (Int.castRingHom ℝ) t (by rw [quartic_eval₂, ht]; ring)

@[simp] private theorem realEvaluation_root (t : ℝ) (ht : t ^ 4 = t ^ 2 + 1) :
    realEvaluation t ht (AdjoinRoot.root (quartic ℤ)) = t := AdjoinRoot.lift_root _

private theorem realEvaluation_injective (t : ℝ) (ht : t ^ 4 = t ^ 2 + 1) :
    Function.Injective (realEvaluation t ht) := by
  apply (injective_iff_map_eq_zero _).2
  intro x hx
  induction x using AdjoinRoot.induction_on with
  | ih p =>
    let r := p %ₘ quartic ℤ
    have hr : AdjoinRoot.mk (quartic ℤ) r = AdjoinRoot.mk (quartic ℤ) p :=
      by simpa only [r, AdjoinRoot.modByMonicHom_mk] using
        AdjoinRoot.mk_leftInverse (quartic_monic ℤ) (AdjoinRoot.mk (quartic ℤ) p)
    have hdeg : r.natDegree < 4 := by
      have h := natDegree_modByMonic_lt p (quartic_monic ℤ) (by
        intro he
        have := quartic_natDegree ℤ
        simp [he] at this)
      rwa [quartic_natDegree] at h
    have he : aeval t (r.map (Int.castRingHom ℚ)) = 0 := by
      rw [aeval_def, eval₂_map]
      have hc : (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ := by
        ext n
        simp
      rw [hc]
      rw [← hr, realEvaluation, AdjoinRoot.lift_mk] at hx
      exact hx
    have hz := polynomial_eq_zero_of_aeval ht ((natDegree_map_le).trans_lt hdeg) he
    have hzero : r = 0 := Polynomial.map_injective _ Int.cast_injective (by simpa using hz)
    rw [← hr, hzero, map_zero]

instance : Nontrivial ModThreeQuartic :=
  (AdjoinRoot.nontrivial_iff_of_monic (quartic_monic (ZMod 3))).2 (by
    rw [degree_eq_natDegree (quartic_monic (ZMod 3)).ne_zero, quartic_natDegree]
    decide)

private def modThree : IntegralQuartic →+* ModThreeQuartic :=
  AdjoinRoot.lift (Int.castRingHom _) (AdjoinRoot.root _) (by
    rw [quartic_eval₂, root_quartic]
    ring)

@[simp] private theorem modThree_root : modThree (AdjoinRoot.root (quartic ℤ)) =
    AdjoinRoot.root (quartic (ZMod 3)) := AdjoinRoot.lift_root _

section Matrices

variable {R : Type*} [CommRing R]

private def swap : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]

private def directRotation (t : R) : Matrix (Fin 2) (Fin 2) R :=
  !![t, -t ^ 2; t ^ 2 - t, t ^ 2 - t]

def directLetter (t : R) (b : Bool) : Matrix (Fin 2) (Fin 2) R :=
  directRotation t * (if b then swap else 1)

private def matrixWord {M : Type*} [Monoid M] (letter : Bool → M) (w : List Bool) : M :=
  (w.map letter).prod

private abbrev directWord (t : R) := matrixWord (directLetter t)

private theorem directLetter_det {t : R} (ht : t ^ 4 = t ^ 2 + 1) (b : Bool) :
    (directLetter t b).det = if b then -1 else 1 := by
  have h : (directRotation t).det = 1 := by
    simp [directRotation, det_fin_two]
    linear_combination ht
  cases b <;> simp [directLetter, det_mul, h, swap, det_fin_two]

private theorem directWord_det {t : R} (ht : t ^ 4 = t ^ 2 + 1) (w : List Bool) :
    (directWord t w).det = 1 ∨ (directWord t w).det = -1 := by
  induction w with
  | nil => simp [matrixWord]
  | cons b w ih =>
    change (directLetter t b * directWord t w).det = 1 ∨
      (directLetter t b * directWord t w).det = -1
    rcases ih with ih | ih <;> cases b <;> simp [det_mul, directLetter_det ht, ih]

private theorem directWord_map {S : Type*} [CommRing S] (f : R →+* S) (t : R) (w : List Bool) :
    (directWord t w).map f = directWord (f t) w := by
  induction w with
  | nil => exact (f.mapMatrix (m := Fin 2)).map_one
  | cons b w ih =>
    change (directLetter t b * directWord t w).map f =
      directLetter (f t) b * directWord (f t) w
    rw [← RingHom.mapMatrix_apply, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ih]
    congr 1
    unfold directLetter
    rw [← RingHom.mapMatrix_apply, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply]
    congr 1
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [directRotation]
    · cases b
      · exact (f.mapMatrix (m := Fin 2)).map_one
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [swap]

end Matrices

private abbrev modRoot : ModThreeQuartic := AdjoinRoot.root (quartic (ZMod 3))

private theorem modThree_three : (3 : ModThreeQuartic) = 0 := by
  simpa only [map_ofNat, map_zero] using
    congrArg (AdjoinRoot.of (quartic (ZMod 3))) (by decide : (3 : ZMod 3) = 0)

private abbrev modEigenvalue : ModThreeQuartic := modRoot - modRoot ^ 2

private theorem modEigenvalue_isUnit : IsUnit modEigenvalue := by
  apply IsUnit.of_mul_eq_one (-(modRoot ^ 2 + modRoot))
  linear_combination root_quartic (ZMod 3)

private theorem modThree_letter_line (b : Bool) :
    directLetter modRoot b *ᵥ (fun _ => 1) = fun _ => modEigenvalue := by
  have hw : swap *ᵥ (fun _ => (1 : ModThreeQuartic)) = fun _ => 1 := by
    funext i
    fin_cases i <;> simp [swap, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  cases b <;> simp only [directLetter, Bool.false_eq_true, ↓reduceIte,
    ← Matrix.mulVec_mulVec, Matrix.one_mulVec, hw]
  all_goals
    funext i
    fin_cases i <;> simp [directRotation, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination (modRoot ^ 2 - modRoot) * modThree_three

private theorem modThree_word_line (w : List Bool) :
    directWord modRoot w *ᵥ (fun _ => 1) = modEigenvalue ^ w.length • (fun _ => 1) := by
  induction w with
  | nil => simp [matrixWord]
  | cons b w ih =>
    change (directLetter modRoot b * directWord modRoot w) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, modThree_letter_line]
    ext i
    simp [pow_succ]

/-- Equal-length real words cannot differ by a minus sign. -/
private theorem directWord_ne_neg {t : ℝ} (ht : t ^ 4 = t ^ 2 + 1) {v w : List Bool}
    (hlen : v.length = w.length) : directWord t v ≠ -directWord t w := by
  intro h
  let z := AdjoinRoot.root (quartic ℤ)
  have hi : directWord z v = -directWord z w := by
    apply Matrix.map_injective (realEvaluation_injective t ht)
    change (realEvaluation t ht).mapMatrix (directWord z v) =
      (realEvaluation t ht).mapMatrix (-directWord z w)
    simp only [map_neg, RingHom.mapMatrix_apply, directWord_map, z, realEvaluation_root]
    exact h
  have hm := congrArg (modThree.mapMatrix (m := Fin 2)) hi
  simp only [map_neg, RingHom.mapMatrix_apply, directWord_map, z, modThree_root] at hm
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ModThreeQuartic =>
    (M *ᵥ (fun _ => 1)) 0) hm
  simp only [Matrix.neg_mulVec, Pi.neg_apply, modThree_word_line, Pi.smul_apply,
    smul_eq_mul, mul_one, hlen] at he
  have hz : modEigenvalue ^ w.length * 2 = modEigenvalue ^ w.length * 0 := by
    linear_combination he
  have h₂ := (modEigenvalue_isUnit.pow w.length).mul_right_inj.mp hz
  exact one_ne_zero (show (1 : ModThreeQuartic) = 0 by linear_combination modThree_three - h₂)

private theorem scalar_eq_one_or_neg_one {M N : Matrix (Fin 2) (Fin 2) ℝ} {s : ℝ}
    (hm : M.det = 1 ∨ M.det = -1) (hn : N.det = 1 ∨ N.det = -1) (h : M = s • N) :
    s = 1 ∨ s = -1 := by
  have hd := congrArg Matrix.det h
  rw [det_smul, Fintype.card_fin] at hd
  have hs : s ^ 2 = 1 := by
    rcases hm with hm | hm <;> rcases hn with hn | hn <;>
      rw [hm, hn] at hd <;> nlinarith only [hd, sq_nonneg s]
  exact sq_eq_one_iff.mp hs

private abbrev RealQutrit := Matrix (Fin 3) (Fin 3) ℝ

private def directBasis : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 1; -1, -1]

private theorem scaledLetter_mul_directBasis (b : Bool) :
    d • (specializedLetter realRoot b * directBasis) = directBasis * directLetter d b := by
  have he : realRoot = -d := by simp [d]
  cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [he, specializedLetter, directBasis, directLetter, directRotation, swap, Matrix.vecMul, dotProduct, row₀,
      row₁, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;> ring

private theorem scaledWord_mul_directBasis (w : List Bool) :
    d ^ w.length • (specializedWord realRoot w * directBasis) = directBasis * directWord d w := by
  induction w with
  | nil => simp [specializedWord, matrixWord]
  | cons b w ih =>
    change d ^ (w.length + 1) •
        ((specializedLetter realRoot b * specializedWord realRoot w) * directBasis) =
      directBasis * (directLetter d b * directWord d w)
    rw [pow_succ', ← smul_smul, Matrix.mul_assoc, ← Matrix.mul_smul, ih,
      ← Matrix.mul_assoc, ← Matrix.smul_mul, scaledLetter_mul_directBasis, Matrix.mul_assoc]

private theorem specializedLetter_trivialLine (t : ℝ) (b : Bool) :
    specializedLetter t b *ᵥ (fun _ => 1) = fun _ => 1 + t := by
  cases b <;> funext i <;>
    simp [specializedLetter, Matrix.mulVec, dotProduct, Finset.sum_add_distrib]

private theorem specializedWord_trivialLine (t : ℝ) (w : List Bool) :
    specializedWord t w *ᵥ (fun _ => 1) = fun _ => (1 + t) ^ w.length := by
  induction w with
  | nil => simp [specializedWord]
  | cons b w ih =>
    rw [specializedWord, ← Matrix.mulVec_mulVec, ih]
    have h : (fun _ : Fin 3 => (1 + t) ^ w.length) =
        (1 + t) ^ w.length • (fun _ => (1 : ℝ)) := by
      ext i
      simp
    rw [h, Matrix.mulVec_smul, specializedLetter_trivialLine]
    ext i
    simp [pow_succ]

private theorem ext_plane_and_line {M N : RealQutrit}
    (hp : M * directBasis = N * directBasis)
    (hl : M *ᵥ (fun _ => 1) = N *ᵥ (fun _ => 1)) : M = N := by
  ext i j
  have h₀ := congrArg (fun C => C i 0) hp
  have h₁ := congrArg (fun C => C i 1) hp
  have h₂ := congrFun hl i
  norm_num [directBasis, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h₀ h₁ h₂
  fin_cases j
  · change M i 0 = N i 0
    linarith only [h₀, h₁, h₂]
  · change M i 1 = N i 1
    linarith only [h₀, h₁, h₂]
  · change M i 2 = N i 2
    linarith only [h₀, h₁, h₂]

private theorem realSpecialize_injective : Function.Injective (QuarticCoefficients.specialize realRoot) := by
  intro x y h
  have he : (((x.constant - y.constant : ℤ) : ℚ) : ℝ) +
      (((x.linear - y.linear : ℤ) : ℚ) : ℝ) * realRoot +
      (((x.quadratic - y.quadratic : ℤ) : ℚ) : ℝ) * realRoot ^ 2 +
      (((x.cubic - y.cubic : ℤ) : ℚ) : ℝ) * realRoot ^ 3 = 0 := by
    simp only [QuarticCoefficients.specialize] at h
    push_cast
    linear_combination h
  obtain ⟨hc, hl, hq, hb⟩ := rational_coefficients_zero realRoot_quartic he
  have hc' : x.constant = y.constant := sub_eq_zero.mp (by exact_mod_cast hc)
  have hl' : x.linear = y.linear := sub_eq_zero.mp (by exact_mod_cast hl)
  have hq' : x.quadratic = y.quadratic := sub_eq_zero.mp (by exact_mod_cast hq)
  have hb' : x.cubic = y.cubic := sub_eq_zero.mp (by exact_mod_cast hb)
  cases x
  cases y
  cases hc'
  cases hl'
  cases hq'
  cases hb'
  rfl

/-- At a fixed horizon, the actual qutrit classes are exactly the ordinary plane products. -/
private theorem qutrit_projective_iff_directWord_eq {v w : List Bool} (hlen : v.length = w.length) :
    (∃ s : ℂ, word v = s • word w) ↔ directWord d v = directWord d w := by
  constructor
  · intro h
    have hr := specializedWord_eq_of_projective realRoot_quartic hlen h
    have hp : directBasis * directWord d v = directBasis * directWord d w := by
      rw [← scaledWord_mul_directBasis, ← scaledWord_mul_directBasis, hlen, hr]
    ext i j
    fin_cases i
    · simpa [directBasis, Matrix.mul_apply, Fin.sum_univ_two] using congrArg (fun M => M 0 j) hp
    · simpa [directBasis, Matrix.mul_apply, Fin.sum_univ_two] using congrArg (fun M => M 1 j) hp
  · intro h
    have he : specializedWord realRoot v = specializedWord realRoot w := by
      apply ext_plane_and_line
      · have hp : d ^ v.length • (specializedWord realRoot v * directBasis) =
            d ^ w.length • (specializedWord realRoot w * directBasis) := by
          rw [scaledWord_mul_directBasis, scaledWord_mul_directBasis, h]
        rw [hlen] at hp
        ext i j
        apply mul_left_cancel₀ (pow_ne_zero w.length d_ne_zero)
        exact congrArg (fun M : Matrix (Fin 3) (Fin 2) ℝ => M i j) hp
      · rw [specializedWord_trivialLine, specializedWord_trivialLine, hlen]
    rw [specializedWord_eq_recurrence realRoot_quartic,
      specializedWord_eq_recurrence realRoot_quartic] at he
    exact (projective_iff_word_eq hlen).mpr ((word_eq_iff_recurrence_eq hlen).mpr
      (Matrix.map_injective realSpecialize_injective he))

private theorem directWord_det_ne_zero (w : List Bool) : (directWord d w).det ≠ 0 := by
  rcases directWord_det d_quartic w with h | h <;> rw [h] <;> norm_num

private noncomputable def directGL (w : List Bool) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero _ (directWord_det_ne_zero w)

/-- The projective group value of a history in the direct plane coordinates. -/
noncomputable def projectiveWord (w : List Bool) : PGL(2, ℝ) :=
  ProjGenLinGroup.mk (directGL w)

private theorem mul_scalar_matrix (M : RealPlaneMatrix) (r : ℝ) :
    M * Matrix.scalar (Fin 2) r = r • M := by
  have hs : Matrix.scalar (Fin 2) r = r • (1 : RealPlaneMatrix) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [hs, Matrix.mul_smul, mul_one]

private theorem pgl_eq_iff_directWord_eq {v w : List Bool} (hlen : v.length = w.length) :
    projectiveWord v = projectiveWord w ↔ directWord d v = directWord d w := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h.symm
    have hm := congrArg (fun g : GL (Fin 2) ℝ => (g : RealPlaneMatrix)) hu
    change directWord d w * Matrix.scalar (Fin 2) (u : ℝ) = directWord d v at hm
    rw [mul_scalar_matrix] at hm
    rcases scalar_eq_one_or_neg_one (directWord_det d_quartic v) (directWord_det d_quartic w)
      hm.symm with h₁ | h₁
    · simpa [h₁] using hm.symm
    · exact (directWord_ne_neg d_quartic hlen (by simpa [h₁] using hm.symm)).elim
  · intro h
    exact congrArg ProjGenLinGroup.mk (Units.ext h)

private theorem projectiveWord_eq_iff {v w : List Bool} (hlen : v.length = w.length) :
    projectiveWord v = projectiveWord w ↔ ∃ s : ℂ, word v = s • word w := by
  exact (pgl_eq_iff_directWord_eq hlen).trans (qutrit_projective_iff_directWord_eq hlen).symm

/-- The code columns are the symmetric pairs of source levels and the middle level. -/
def code : Matrix Level (Fin 3) ℂ :=
  let q : ℂ := (Real.sqrt 2 / 2 : ℝ)
  !![q, 0, 0; 0, q, 0; 0, 0, 1; q, 0, 0; 0, q, 0]

private def q : ℂ := (Real.sqrt 2 / 2 : ℝ)

private theorem q_sq : q * q = 1 / 2 := by
  have h : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  exact_mod_cast (show (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = (1 / 2 : ℝ) by nlinarith)

private theorem star_q : star q = q := Complex.conj_ofReal _

private theorem code_isometry : codeᴴ * code = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [code, ← show ((Real.sqrt 2 / 2 : ℝ) : ℂ) = q from rfl, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, Fin.sum_univ_succ]
  all_goals change star q * q + (star q * q + 0) = 1 <;> rw [star_q, q_sq] <;> norm_num

private def flagOf (b : Bool) : Flag := if b then 1 else 0

private def kraus (b : Bool) : Matrix Level Level ℂ :=
  (Real.cos angle : ℂ) • baseKraus (flagOf b) +
    (Complex.I * (Real.sin angle : ℂ)) • baseKraus (1 - flagOf b)

private theorem base_on_code (b : Bool) :
    baseKraus (flagOf b) * code = q • (code * (if b then U₁ else U₀)) := by
  have hq : ((Real.sqrt 2 / 2 : ℝ) : ℂ) = q := rfl
  cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [baseKraus, flagOf, code, U₀, U₁, row₀, row₁, Matrix.mul_apply, Fin.sum_univ_succ,
      hq, q_sq] <;> first | rfl | exact q_sq.symm

private theorem kraus_on_code (b : Bool) : kraus b * code = q • (code * letter b) := by
  have hc : flagOf (!b) = 1 - flagOf b := by cases b <;> decide
  unfold kraus
  rw [← hc]
  simp only [Matrix.add_mul, Matrix.smul_mul, base_on_code, letter, Matrix.mul_add,
    Matrix.mul_smul, smul_add, smul_smul, ← sin_angle, cosine]
  cases b <;> simp [mul_comm q]

private theorem letter_isometry (b : Bool) : (letter b)ᴴ * letter b = 1 := by
  have hc : (cosine : ℂ) ^ 2 = (sine : ℂ) := by exact_mod_cast cosine_sq
  have hs : (sine : ℂ) ^ 2 = 1 - (sine : ℂ) := by exact_mod_cast sine_sq
  have hi := Complex.I_sq
  cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [letter, U₀, U₁, row₀, row₁, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fin.sum_univ_succ, star_add, star_mul, Complex.conj_I, Complex.conj_ofReal] <;>
    first | ring | linear_combination hc + hs - (sine : ℂ) ^ 2 * hi

private theorem original_block (b : Bool) (X : Matrix Level Level ℂ) (i j : Level) :
    originalInstrument angle X (flagOf b, i) (flagOf b, j) =
      (kraus b * X * (kraus b)ᴴ) i j := by
  simp only [originalInstrument, flagged, MatrixMap.of_kraus, LinearMap.coe_sum,
    LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Matrix.sum_apply]
  rw [Finset.sum_eq_single (flagOf b)]
  · simp [flagKraus, Matrix.mul_apply, Matrix.conjTranspose_apply, kraus]
  · intro k _ hk
    simp [flagKraus, Matrix.mul_apply, Matrix.conjTranspose_apply, Ne.symm hk]
  · simp

variable {s : Type*} [Fintype s] [DecidableEq s]

/-- Select the measured flag block of the original instrument tensored with the spectator identity. -/
def measuredStep (b : Bool) (X : Matrix (Level × s) (Level × s) ℂ) :
    Matrix (Level × s) (Level × s) ℂ :=
  let includeFlag (i : Level × s) : (Flag × Level) × s := ((flagOf b, i.1), i.2)
  (MatrixMap.kron (originalInstrument angle) LinearMap.id X).submatrix includeFlag includeFlag

private theorem measuredStep_eq (b : Bool) (X : Matrix (Level × s) (Level × s) ℂ) :
    measuredStep b X = (kraus b ⊗ₖ (1 : Matrix s s ℂ)) * X *
      (kraus b ⊗ₖ (1 : Matrix s s ℂ))ᴴ := by
  ext ⟨i, r⟩ ⟨j, t⟩
  simp only [measuredStep, Matrix.submatrix_apply, MatrixMap.kron_def, original_block,
    LinearMap.id_apply]
  simp only [Matrix.mul_assoc (kraus b), Matrix.mul_apply, Matrix.single,
    Matrix.conjTranspose_apply, Matrix.of_apply, ite_mul, zero_mul, one_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Matrix.one_apply, Matrix.kronecker_apply, mul_ite, mul_zero, mul_one,
    Fintype.sum_prod_type, ite_mul, zero_mul, map_ite, map_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr! 4
  ring

/-- Apply fresh measured branches, with the most recent outcome at the head of the list. -/
def measuredHistory : List Bool → Matrix (Level × s) (Level × s) ℂ →
    Matrix (Level × s) (Level × s) ℂ
  | [], X => X
  | b :: w, X => measuredStep b (measuredHistory w X)

private theorem code_word_effect (w : List Bool) :
    (code * word w)ᴴ * (code * word w) = 1 := by
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc codeᴴ,
    code_isometry, one_mul]
  induction w with
  | nil => simp [word]
  | cons b w ih =>
    rw [word, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (letter b)ᴴ,
      letter_isometry, one_mul, ih]

private theorem measuredHistory_eq (w : List Bool) (ρ : Matrix (Fin 3 × s) (Fin 3 × s) ℂ) :
    let embed := code ⊗ₖ (1 : Matrix s s ℂ)
    let out := (code * word w) ⊗ₖ (1 : Matrix s s ℂ)
    measuredHistory w (embed * ρ * embedᴴ) = (1 / 2 : ℂ) ^ w.length • (out * ρ * outᴴ) := by
  induction w with
  | nil => simp [measuredHistory, word]
  | cons b w ih =>
    dsimp only at ih ⊢
    let K := kraus b ⊗ₖ (1 : Matrix s s ℂ)
    let F := (code * word w) ⊗ₖ (1 : Matrix s s ℂ)
    let G := (code * word (b :: w)) ⊗ₖ (1 : Matrix s s ℂ)
    have hKF : K * F = q • G := by
      dsimp only [K, F, G]
      rw [← Matrix.mul_kronecker_mul, one_mul, ← Matrix.mul_assoc, kraus_on_code,
        Matrix.smul_mul, Matrix.mul_assoc, ← word, Matrix.smul_kronecker]
    rw [measuredHistory, ih, measuredStep_eq]
    change K * ((1 / 2 : ℂ) ^ w.length • (F * ρ * Fᴴ)) * Kᴴ =
      (1 / 2 : ℂ) ^ (w.length + 1) • (G * ρ * Gᴴ)
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc K, ← Matrix.mul_assoc K,
      Matrix.mul_assoc (K * F * ρ), ← Matrix.conjTranspose_mul, hKF]
    simp only [Matrix.conjTranspose_smul, star_q, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, pow_succ]
    congr 1
    rw [← mul_assoc q q, q_sq]

/-- Every measured history has fair trace weight on the code, even with a finite spectator. -/
theorem measuredHistory_trace (w : List Bool) (ρ : Matrix (Fin 3 × s) (Fin 3 × s) ℂ)
    (hρ : ρ.trace = 1) :
    let embed := code ⊗ₖ (1 : Matrix s s ℂ)
    (measuredHistory w (embed * ρ * embedᴴ)).trace = (1 / 2 : ℂ) ^ w.length := by
  dsimp only
  rw [measuredHistory_eq, Matrix.trace_smul, Matrix.trace_mul_cycle]
  simp [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, code_word_effect,
    Matrix.one_kronecker_one, hρ]

/-- Time is read from the first coordinate of a tuple to the last. -/
abbrev History (n : ℕ) := Fin n → Bool

/-- The physical product in a chronological tuple, with later factors multiplying on the left. -/
def chronologicalWord {n : ℕ} (w : History n) : Qutrit := word (List.ofFn w).reverse

/-- The finite image of the normalized physical products at a fixed horizon. -/
def RecordClass (n : ℕ) := Set.range (@chronologicalWord n)

noncomputable instance (n : ℕ) : Fintype (RecordClass n) :=
  Fintype.ofFinite _

noncomputable instance (n : ℕ) : DecidableEq (RecordClass n) := Classical.decEq _

def classOf {n : ℕ} (w : History n) : RecordClass n :=
  ⟨chronologicalWord w, ⟨w, rfl⟩⟩

/-- The physical projective relation and the real endpoint have exactly the same fibers. -/
theorem chronological_fibers {n : ℕ} (v w : History n) :
    (∃ z : ℂ, chronologicalWord v = z • chronologicalWord w) ↔
      projectiveWord (List.ofFn v).reverse = projectiveWord (List.ofFn w).reverse :=
  (projectiveWord_eq_iff (by simp)).symm

/-- Embed each actual finite record class as a real projective endpoint. -/
def classProjective (n : ℕ) : RecordClass n ↪ PGL(2, ℝ) where
  toFun k := projectiveWord (List.ofFn k.property.choose).reverse
  inj' := by
    intro k l he
    apply Subtype.ext
    rw [← k.property.choose_spec, ← l.property.choose_spec]
    exact (projective_iff_word_eq (by simp)).mp ((chronological_fibers _ _).mpr he)

private theorem classProjective_classOf {n : ℕ} (w : History n) :
    classProjective n (classOf w) = projectiveWord (List.ofFn w).reverse := by
  apply (chronological_fibers _ _).mp
  exact ⟨1, by simpa [classOf] using (classOf w).property.choose_spec⟩

/-- The measured mass uses the trace of the actual five-level output of each history. -/
def measuredLaw {n : ℕ} (ρ : Matrix (Fin 3 × s) (Fin 3 × s) ℂ) : RecordClass n → ℝ :=
  let embed := code ⊗ₖ (1 : Matrix s s ℂ)
  pushforward classOf fun w : History n =>
    ((measuredHistory (List.ofFn w).reverse (embed * ρ * embedᴴ)).trace).re

/-- The fair endpoint law uses the ordinary left-to-right matrix product of a fair tuple. -/
def projectiveLaw (n : ℕ) : PGL(2, ℝ) → ℝ :=
  pushforward (fun w : History n => projectiveWord (List.ofFn w)) fun _ => ((2 : ℝ) ^ n)⁻¹

private def reverseHistory (n : ℕ) : History n ≃ History n where
  toFun w i := w i.rev
  invFun w i := w i.rev
  left_inv w := by funext i; simp
  right_inv w := by funext i; simp

private theorem ofFn_reverseHistory {n : ℕ} (w : History n) :
    List.ofFn (reverseHistory n w) = (List.ofFn w).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [List.getElem_reverse hj, reverseHistory, Fin.rev, Fin.revPerm]

/-- The measured class law is the counted projective law on its finite support. -/
theorem fair_projective_record (n : ℕ) (ρ : Matrix (Fin 3 × s) (Fin 3 × s) ℂ) (hρ : ρ.trace = 1) :
    pushforward (classProjective n) (measuredLaw (n := n) ρ) = projectiveLaw n ∧
      ∀ k : RecordClass n, projectiveLaw n (classProjective n k) =
        ((Finset.univ.filter (fun w : History n => classOf w = k)).card : ℝ) / (2 : ℝ) ^ n := by
  classical
  have hw (w : History n) :
      let embed := code ⊗ₖ (1 : Matrix s s ℂ)
      ((measuredHistory (List.ofFn w).reverse (embed * ρ * embedᴴ)).trace).re =
        ((2 : ℝ) ^ n)⁻¹ := by
    dsimp only
    rw [measuredHistory_trace _ _ hρ, List.length_reverse, List.length_ofFn]
    norm_cast
    rw [one_div, inv_pow]
  have hl : measuredLaw (n := n) ρ = pushforward classOf (fun _ : History n => ((2 : ℝ) ^ n)⁻¹) := by
    unfold measuredLaw
    congr 1
    funext w
    exact hw w
  have he : pushforward (classProjective n) (measuredLaw (n := n) ρ) = projectiveLaw n := by
    rw [hl, pushforward_comp]
    funext g
    simp only [pushforward, Function.comp_apply, classProjective_classOf, projectiveLaw]
    simpa only [ofFn_reverseHistory] using
      ((reverseHistory n).sum_comp (fun w : History n =>
        if projectiveWord (List.ofFn w) = g then ((2 : ℝ) ^ n)⁻¹ else 0))
  refine ⟨he, fun k => ?_⟩
  rw [← he, hl]
  simp only [pushforward, (classProjective n).injective.eq_iff, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

end

end D5.S3.Quantum.Measurement.Auric.FairProjectiveRecord
