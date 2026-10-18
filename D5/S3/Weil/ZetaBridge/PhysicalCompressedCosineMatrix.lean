/- GID: D5/S3/Weil/ZetaBridge/PhysicalCompressedCosineMatrix
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/PhysicalCompressedCosineMatrix
   mirror-E: none(waiver:physical-Ioc-compression-and-finite-prime-form)
   anchors: []
   utility: none
   digest: Exact Ioc zero-extension cosine compression and finite complex prime-power quadratic form. -/

import D5.S3.Weil.ZetaBridge.PrimeJumpDecomposition
import D5.S3.Weil.ZetaBridge.WeilMellinPrimeIntertwining
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Physical compressed cosine matrix

The original Ioc zero extension is compressed before every translation.  The
finite cosine matrix and the exact finite complex prime-power quadratic form
below retain every mode, shift, conjugated cross term, and signed Weil action.
-/

noncomputable section
namespace PhysicalCompressedCosineMatrix

open MeasureTheory Set
open scoped BigOperators ComplexConjugate
open D5.S3.Weil.ZetaBridge.PrimeJumpDecomposition (primeWeight)
open D5.S3.Weil.ZetaBridge.WeilMellinPrimeIntertwining (primeSymmetric)

def window (a : ℝ) : Set ℝ := Ioc (-a) a

def zeroExtension {E : Type*} [Zero E] (a : ℝ) (f : ℝ → E) : ℝ → E :=
  (window a).indicator f

/-- Compress the whole-line translation of the original zero extension. -/
def compression {E : Type*} [Zero E] (a s : ℝ) (f : ℝ → E) : ℝ → E :=
  zeroExtension a (fun x => zeroExtension a f (x + s))

def overlap (a s : ℝ) : Set ℝ :=
  Ioc (max (-a) (-a - s)) (min a (a - s))

lemma overlap_mem (a s x : ℝ) :
    x ∈ overlap a s ↔ x ∈ window a ∧ x + s ∈ window a := by
  simp only [overlap, window, mem_Ioc, max_lt_iff, le_min_iff]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
    exact ⟨⟨h₁, h₃⟩, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
    exact ⟨⟨h₁, by linarith⟩, ⟨h₂, by linarith⟩⟩

section Scalar
variable {𝕜 : Type*} [RCLike 𝕜]

def pairing (a s : ℝ) (f g : ℝ → 𝕜) : 𝕜 :=
  ∫ x : ℝ, f x * compression a s g x

/-- Exact pointwise support geometry; it also covers an empty overlap. -/
lemma compression_product (a s : ℝ) (f g : ℝ → 𝕜) :
    (fun x => f x * compression a s g x) =
      (overlap a s).indicator (fun x => f x * g (x + s)) := by
  classical
  funext x
  by_cases h : x ∈ overlap a s
  · obtain ⟨hx, hxs⟩ := (overlap_mem a s x).mp h
    simp [compression, zeroExtension, h, hx, hxs]
  · have hn : x ∉ window a ∨ x + s ∉ window a :=
      not_and_or.mp (fun hh => h ((overlap_mem a s x).mpr hh))
    rcases hn with hx | hxs
    · simp [compression, zeroExtension, h, hx]
    · by_cases hx : x ∈ window a <;>
        simp [compression, zeroExtension, h, hx, hxs]

/-- The first analytic bridge is a set integral on the actual overlap.
No continuity, trace, or endpoint equality is needed for this identity. -/
theorem pairing_overlap (a s : ℝ) (f g : ℝ → 𝕜) :
    pairing a s f g = ∫ x in overlap a s, f x * g (x + s) := by
  rw [pairing, compression_product, overlap, integral_indicator measurableSet_Ioc]

lemma integrable_compression_product (a s : ℝ) {f g : ℝ → 𝕜}
    (hf : Continuous f) (hg : Continuous g) :
    Integrable (fun x => f x * compression a s g x) := by
  rw [compression_product]
  apply IntegrableOn.integrable_indicator _ measurableSet_Ioc
  have hc : Continuous (fun x : ℝ => f x * g (x + s)) :=
    hf.mul (hg.comp (continuous_id.add continuous_const))
  exact hc.integrableOn_Ioc

lemma pairing_nonneg (a s : ℝ) (f g : ℝ → 𝕜)
    (hs : 0 ≤ s) (hcap : s ≤ 2 * a) :
    pairing a s f g = ∫ x in (-a)..(a - s), f x * g (x + s) := by
  rw [pairing_overlap, overlap, max_eq_left (by linarith : -a - s ≤ -a),
    min_eq_right (by linarith : a - s ≤ a),
    intervalIntegral.integral_of_le (by linarith : -a ≤ a - s)]

lemma pairing_nonpos (a s : ℝ) (f g : ℝ → 𝕜)
    (hs : s ≤ 0) (hcap : -(2 * a) ≤ s) :
    pairing a s f g = ∫ x in (-a - s)..a, f x * g (x + s) := by
  rw [pairing_overlap, overlap, max_eq_right (by linarith : -a ≤ -a - s),
    min_eq_left (by linarith : a ≤ a - s),
    intervalIntegral.integral_of_le (by linarith : -a - s ≤ a)]

lemma compression_zero_right (a s : ℝ) (f : ℝ → 𝕜) (hs : 2 * a ≤ s) :
    compression a s f = 0 := by
  classical
  funext x
  by_cases hx : x ∈ window a
  · have hxs : x + s ∉ window a := by
      intro h
      have hx' := hx.1
      have h' := h.2
      linarith
    simp [compression, zeroExtension, hx, hxs]
  · simp [compression, zeroExtension, hx]

lemma compression_zero_left (a s : ℝ) (f : ℝ → 𝕜) (hs : s ≤ -(2 * a)) :
    compression a s f = 0 := by
  classical
  funext x
  by_cases hx : x ∈ window a
  · have hxs : x + s ∉ window a := by
      intro h
      have hx' := hx.2
      have h' := h.1
      linarith
    simp [compression, zeroExtension, hx, hxs]
  · simp [compression, zeroExtension, hx]

lemma pairing_zero_right (a s : ℝ) (f g : ℝ → 𝕜) (hs : 2 * a ≤ s) :
    pairing a s f g = 0 := by
  simp [pairing, compression_zero_right a s g hs]

lemma pairing_zero_left (a s : ℝ) (f g : ℝ → 𝕜) (hs : s ≤ -(2 * a)) :
    pairing a s f g = 0 := by
  simp [pairing, compression_zero_left a s g hs]

/-- Reflection is proved on ordinary interval integrals. The underlying
Ioc reflection changes endpoint convention only on a Lebesgue null set;
`integral_comp_neg` incorporates precisely that fact. No reflected zero
extension is asserted to agree pointwise at the two endpoints. -/
theorem pairing_neg_even (a s : ℝ) (f g : ℝ → 𝕜) (hs : 0 ≤ s)
    (hf : ∀ x, f (-x) = f x) (hg : ∀ x, g (-x) = g x) :
    pairing a (-s) f g = pairing a s f g := by
  by_cases hcap : s ≤ 2 * a
  · rw [pairing_nonpos a (-s) f g (by linarith) (by linarith),
      pairing_nonneg a s f g hs hcap]
    calc
      (∫ x in (-a - -s)..a, f x * g (x + -s)) =
          ∫ x in (-a - -s)..a, (fun y => f y * g (y + s)) (-x) := by
        apply intervalIntegral.integral_congr
        intro x _
        change f x * g (x + -s) = f (-x) * g (-x + s)
        rw [← hf x, show -x + s = -(x + -s) by ring, hg]
      _ = _ := by
        have hcomp := intervalIntegral.integral_comp_neg
          (a := -a - -s) (b := a) (fun y : ℝ => f y * g (y + s))
        convert hcomp using 1 <;> ring
  · rw [pairing_zero_right a s f g (le_of_not_ge hcap),
      pairing_zero_left a (-s) f g (by linarith [le_of_not_ge hcap])]

end Scalar

/-- Scaled Mathlib sinc. Its removable value is included in the definition. -/
def S (H r : ℝ) : ℝ := H * Real.sinc (r * H)

@[simp] lemma S_zero (H : ℝ) : S H 0 = H := by simp [S]
@[simp] lemma S_neg (H r : ℝ) : S H (-r) = S H r := by
  simp [S, neg_mul, Real.sinc_neg]

lemma S_of_ne (H r : ℝ) (hr : r ≠ 0) : S H r = Real.sin (r * H) / r := by
  by_cases hH : H = 0
  · simp [hH, S]
  · rw [S, Real.sinc_of_ne_zero (mul_ne_zero hr hH)]
    field_simp [hr, hH]
    <;> ring

/-- General affine cosine integral, including zero frequency. -/
theorem integral_cos_centered (H r t : ℝ) :
    (∫ y in (-H)..H, Real.cos (r * y + t)) = 2 * Real.cos t * S H r := by
  by_cases hr : r = 0
  · subst r
    simp only [zero_mul, zero_add, intervalIntegral.integral_const,
      smul_eq_mul, S_zero]
    ring
  · rw [intervalIntegral.integral_comp_mul_add Real.cos hr t, integral_cos,
      S_of_ne H r hr]
    simp only [smul_eq_mul, mul_neg, Real.sin_add, Real.sin_neg, Real.cos_neg]
    field_simp [hr]
    <;> ring

/-- Complete cosine product integral. Both r=u-v=0 and r=u+v=0
are genuinely included, as are H=0 and the simultaneous zero mode. -/
theorem integral_cos_product_centered (H u v s : ℝ) :
    (∫ y in (-H)..H, Real.cos (u * (y - s / 2)) *
      Real.cos (v * (y + s / 2))) =
      Real.cos ((u + v) * s / 2) * S H (u - v) +
      Real.cos ((u - v) * s / 2) * S H (u + v) := by
  have he : (fun y : ℝ => Real.cos (u * (y - s / 2)) *
      Real.cos (v * (y + s / 2))) =
      (fun y => (Real.cos ((u - v) * y + (-(u + v) * s / 2)) +
        Real.cos ((u + v) * y + (-(u - v) * s / 2))) / 2) := by
    funext y
    have hp := Real.two_mul_cos_mul_cos (u * (y - s / 2)) (v * (y + s / 2))
    rw [show u * (y - s / 2) - v * (y + s / 2) =
        (u - v) * y + (-(u + v) * s / 2) by ring,
      show u * (y - s / 2) + v * (y + s / 2) =
        (u + v) * y + (-(u - v) * s / 2) by ring] at hp
    linarith
  have h₁ : IntervalIntegrable (fun y : ℝ =>
      Real.cos ((u - v) * y + (-(u + v) * s / 2))) volume (-H) H :=
    (by fun_prop : Continuous (fun y : ℝ =>
      Real.cos ((u - v) * y + (-(u + v) * s / 2)))).intervalIntegrable _ _
  have h₂ : IntervalIntegrable (fun y : ℝ =>
      Real.cos ((u + v) * y + (-(u - v) * s / 2))) volume (-H) H :=
    (by fun_prop : Continuous (fun y : ℝ =>
      Real.cos ((u + v) * y + (-(u - v) * s / 2)))).intervalIntegrable _ _
  rw [he, intervalIntegral.integral_div, intervalIntegral.integral_add h₁ h₂,
    integral_cos_centered, integral_cos_centered]
  simp only [neg_mul, neg_div, Real.cos_neg]
  ring

/-- The midpoint substitution y=x+s/2 is an ordinary Lebesgue interval
change of variables; there is no circle or wrapped interval here. -/
theorem integral_cos_product_overlap (a s u v : ℝ) :
    (∫ x in (-a)..(a - s), Real.cos (u * x) * Real.cos (v * (x + s))) =
      Real.cos ((u + v) * s / 2) * S ((2 * a - s) / 2) (u - v) +
      Real.cos ((u - v) * s / 2) * S ((2 * a - s) / 2) (u + v) := by
  let H := (2 * a - s) / 2
  let F := fun y : ℝ => Real.cos (u * (y - s / 2)) *
    Real.cos (v * (y + s / 2))
  calc
    _ = ∫ x in (-a)..(a - s), F (x + s / 2) := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp [F]
      rw [show x + s / 2 - s / 2 = x by ring,
        show x + s / 2 + s / 2 = x + s by ring]
    _ = ∫ y in (-H)..H, F y := by
      rw [intervalIntegral.integral_comp_add_right]
      congr 1 <;> dsimp [H] <;> ring
    _ = _ := integral_cos_product_centered H u v s

def omega (a : ℝ) (n : ℕ) : ℝ := 2 * Real.pi * (n : ℝ) / (2 * a)

def amplitude (a : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 1 / Real.sqrt (2 * a) else Real.sqrt (2 / (2 * a))

/-- The unextended cosine profile. `compression` performs its original
zero extension, including the half-open physical endpoint convention. -/
def mode (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  amplitude a n * Real.cos (omega a n * x)

def matrixEntry (a : ℝ) (n m : ℕ) (s : ℝ) : ℝ :=
  pairing a s (mode a n) (mode a m)

/-- Explicit retained matrix, defined for every signed physical shift.
The equality branch at |s|=2a is harmless: S_0 is identically zero. -/
def matrix (a : ℝ) (n m : ℕ) (s : ℝ) : ℝ :=
  if |s| ≤ 2 * a then
    amplitude a n * amplitude a m *
      (Real.cos ((omega a n + omega a m) * |s| / 2) *
        S ((2 * a - |s|) / 2) (omega a n - omega a m) +
       Real.cos ((omega a n - omega a m) * |s| / 2) *
        S ((2 * a - |s|) / 2) (omega a n + omega a m))
  else 0

lemma mode_even (a : ℝ) (n : ℕ) (x : ℝ) : mode a n (-x) = mode a n x := by
  simp [mode, mul_neg, Real.cos_neg]

/-- The positive-shift physical matrix identity, including s=0 and s=2a.
Neither equality nor inequality of the two mode indices is assumed. -/
theorem matrixEntry_nonneg (a : ℝ) (n m : ℕ) (s : ℝ)
    (hs : 0 ≤ s) (hcap : s ≤ 2 * a) :
    matrixEntry a n m s = amplitude a n * amplitude a m *
      (Real.cos ((omega a n + omega a m) * s / 2) *
        S ((2 * a - s) / 2) (omega a n - omega a m) +
       Real.cos ((omega a n - omega a m) * s / 2) *
        S ((2 * a - s) / 2) (omega a n + omega a m)) := by
  rw [matrixEntry, pairing_nonneg a s _ _ hs hcap]
  have he : (fun x => mode a n x * mode a m (x + s)) =
      (fun x => (amplitude a n * amplitude a m) *
        (Real.cos (omega a n * x) * Real.cos (omega a m * (x + s)))) := by
    funext x
    unfold mode
    ring
  rw [he, intervalIntegral.integral_const_mul, integral_cos_product_overlap]

lemma matrixEntry_neg (a : ℝ) (n m : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    matrixEntry a n m (-s) = matrixEntry a n m s :=
  pairing_neg_even a s _ _ hs (mode_even a n) (mode_even a m)

/-- Every real shift and every pair of original modes, including both zero
modes and every resonance. This is the physical-compression theorem. -/
theorem matrixEntry_eq_matrix (a : ℝ) (ha : 0 < a) (n m : ℕ) (s : ℝ) :
    matrixEntry a n m s = matrix a n m s := by
  have hforward : ∀ t : ℝ, 0 ≤ t → matrixEntry a n m t = matrix a n m t := by
    intro t ht
    by_cases hc : t ≤ 2 * a
    · rw [matrix, abs_of_nonneg ht, if_pos hc, matrixEntry_nonneg a n m t ht hc]
    · rw [matrix, abs_of_nonneg ht, if_neg hc]
      exact pairing_zero_right a t _ _ (le_of_not_ge hc)
  rcases le_or_gt 0 s with hs | hs
  · exact hforward s hs
  · have he := matrixEntry_neg a n m (-s) (by linarith : 0 ≤ -s)
    rw [neg_neg] at he
    rw [he, hforward (-s) (by linarith)]
    simp [matrix, abs_neg]

theorem matrixEntry_symmetric (a : ℝ) (ha : 0 < a) (n m : ℕ) (s : ℝ) :
    matrixEntry a n m s = matrixEntry a m n s := by
  rw [matrixEntry_eq_matrix a ha, matrixEntry_eq_matrix a ha]
  unfold matrix
  split_ifs
  · rw [show omega a m - omega a n = -(omega a n - omega a m) by ring,
      show omega a m + omega a n = omega a n + omega a m by ring]
    simp only [S_neg, neg_mul, neg_div, Real.cos_neg]
    ring
  · rfl

/-! Finite complex profiles: every mixed term is retained. -/

lemma compression_ofReal (a s : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    compression a s (fun y => (g y : ℂ)) x =
      ((compression (E := ℝ) a s g x : ℝ) : ℂ) := by
  classical
  by_cases hx : x ∈ window a <;> by_cases hxs : x + s ∈ window a <;>
    simp [compression, zeroExtension, hx, hxs]

lemma pairing_ofReal (a s : ℝ) (f g : ℝ → ℝ) :
    pairing a s (fun x => (f x : ℂ)) (fun x => (g x : ℂ)) =
      ((pairing (𝕜 := ℝ) a s f g : ℝ) : ℂ) := by
  unfold pairing
  simp_rw [compression_ofReal, ← Complex.ofReal_mul]
  exact integral_ofReal

/-- A genuinely finite bilinear expansion with integrability derived from
the continuous factors and bounded physical overlap. -/
theorem pairing_finite (a s : ℝ) {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (c : ι → ℂ) (d : κ → ℂ) (f : ι → ℝ → ℂ) (g : κ → ℝ → ℂ)
    (hf : ∀ i ∈ A, Continuous (f i)) (hg : ∀ j ∈ B, Continuous (g j)) :
    pairing a s (fun x => ∑ i ∈ A, c i * f i x)
        (fun x => ∑ j ∈ B, d j * g j x) =
      ∑ i ∈ A, ∑ j ∈ B, (c i * d j) * pairing a s (f i) (g j) := by
  classical
  have hc (x : ℝ) :
      compression a s (fun y => ∑ j ∈ B, d j * g j y) x =
        ∑ j ∈ B, d j * compression a s (g j) x := by
    by_cases hx : x ∈ window a <;> by_cases hxs : x + s ∈ window a <;>
      simp [compression, zeroExtension, hx, hxs]
  have he : (fun x => (∑ i ∈ A, c i * f i x) *
      compression a s (fun y => ∑ j ∈ B, d j * g j y) x) =
      (fun x => ∑ i ∈ A, ∑ j ∈ B,
        (c i * d j) * (f i x * compression a s (g j) x)) := by
    funext x
    rw [hc, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hij (i : ι) (hi : i ∈ A) (j : κ) (hj : j ∈ B) :
      Integrable (fun x => (c i * d j) * (f i x * compression a s (g j) x)) :=
    (integrable_compression_product a s (hf i hi) (hg j hj)).const_mul _
  have hi (i : ι) (h : i ∈ A) :
      Integrable (fun x => ∑ j ∈ B,
        (c i * d j) * (f i x * compression a s (g j) x)) :=
    integrable_finsetSum B (hij i h)
  rw [pairing, he, integral_finsetSum A hi]
  apply Finset.sum_congr rfl
  intro i h
  rw [integral_finsetSum B (hij i h)]
  simp only [integral_const_mul, pairing]

def profile (a : ℝ) (A : Finset ℕ) (v : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ A, v n * (mode a n x : ℂ)

lemma profile_continuous (a : ℝ) (A : Finset ℕ) (v : ℕ → ℂ) :
    Continuous (profile a A v) := by
  unfold profile mode
  fun_prop

lemma profile_even (a : ℝ) (A : Finset ℕ) (v : ℕ → ℂ) (x : ℝ) :
    profile a A v (-x) = profile a A v x := by
  unfold profile
  simp only [mode_even]

theorem profile_pairing (a s : ℝ) (A : Finset ℕ) (v : ℕ → ℂ) :
    pairing a s (fun x => conj (profile a A v x)) (profile a A v) =
      ∑ n ∈ A, ∑ m ∈ A,
        (conj (v n) * v m) * (matrixEntry a n m s : ℂ) := by
  classical
  have he : (fun x => conj (profile a A v x)) =
      (fun x => ∑ n ∈ A, conj (v n) * (mode a n x : ℂ)) := by
    funext x
    simp [profile, map_sum, map_mul]
  rw [he]
  change pairing a s (fun x => ∑ n ∈ A, conj (v n) * (mode a n x : ℂ))
      (fun x => ∑ m ∈ A, v m * (mode a m x : ℂ)) = _
  rw [pairing_finite a s A A (fun n => conj (v n)) v
    (fun n x => (mode a n x : ℂ)) (fun m x => (mode a m x : ℂ))
    (by intro n _; unfold mode; fun_prop)
    (by intro m _; unfold mode; fun_prop)]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  rw [pairing_ofReal]
  rfl

/-- A complex even profile has a real compressed correlation. Reality is
proved by matrix symmetry, without deleting any conjugated cross term. -/
lemma profile_pairing_conj (a : ℝ) (ha : 0 < a) (s : ℝ)
    (A : Finset ℕ) (v : ℕ → ℂ) :
    conj (pairing a s (fun x => conj (profile a A v x)) (profile a A v)) =
      pairing a s (fun x => conj (profile a A v x)) (profile a A v) := by
  classical
  simp only [profile_pairing]
  simp only [map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  rw [matrixEntry_symmetric a ha m n s]
  ring

/-! The actual finite symmetric von Mangoldt action and its exact cutoff. -/

def primeCutoff (a : ℝ) : ℕ := ⌊Real.exp (2 * a)⌋₊

/-- Unsigned action. Its negative is the arithmetic translation term in
the Weil form. The factors 1/sqrt(n), all prime powers, and both shifts are
the original ones; each summand has its own physical compression. -/
def primeAction (a : ℝ) (M : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ r ∈ Finset.Icc 1 M, (primeWeight r : ℂ) *
    (compression a (Real.log (r : ℝ)) f x +
      compression a (-Real.log (r : ℝ)) f x)

/-- Reuse the existing actual prime action. Its outer Icc convention
agrees pointwise on our Ioc integration domain; no endpoint equality for
the inner zero extension is imposed or needed. -/
lemma primeAction_existing (a : ℝ) (M : ℕ) (f : ℝ → ℂ) (x : ℝ)
    (hx : x ∈ window a) :
    primeAction a M f x = primeSymmetric a M (zeroExtension a f) x := by
  classical
  have hxcc : x ∈ Icc (-a) a := ⟨hx.1.le, hx.2⟩
  have hc (s : ℝ) : compression a s f x = zeroExtension a f (x + s) :=
    by simp [compression, zeroExtension, hx]
  unfold primeAction primeSymmetric
  rw [Set.indicator_of_mem hxcc]
  apply Finset.sum_congr rfl
  intro r _
  rw [hc, hc]
  simp only [primeWeight, sub_eq_add_neg]

lemma log_beyond_cutoff (a : ℝ) {r : ℕ} (hr : primeCutoff a < r) :
    2 * a < Real.log (r : ℝ) := by
  have he : Real.exp (2 * a) < (r : ℝ) := Nat.lt_of_floor_lt hr
  calc
    2 * a = Real.log (Real.exp (2 * a)) := (Real.log_exp _).symm
    _ < Real.log (r : ℝ) := Real.log_lt_log (Real.exp_pos _) he

/-- All terms above floor(exp(2a)) vanish in the original compression.
At shift exactly 2a the Ioc overlap is empty as well. -/
theorem primeAction_cutoff (a : ℝ) (M : ℕ) (hM : primeCutoff a ≤ M)
    (f : ℝ → ℂ) : primeAction a M f = primeAction a (primeCutoff a) f := by
  classical
  funext x
  unfold primeAction
  symm
  apply Finset.sum_subset
  · intro r hr
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hr).1, (Finset.mem_Icc.mp hr).2.trans hM⟩
  · intro r hr hnot
    have ht : primeCutoff a < r := by
      have hr₁ := (Finset.mem_Icc.mp hr).1
      by_contra hn
      exact hnot (Finset.mem_Icc.mpr ⟨hr₁, le_of_not_gt hn⟩)
    have hl := log_beyond_cutoff a ht
    rw [compression_zero_right a _ f hl.le,
      compression_zero_left a _ f (by linarith)]
    simp

def primeQuadratic (a : ℝ) (M : ℕ) (f : ℝ → ℂ) : ℂ :=
  ∫ x : ℝ, conj (f x) * primeAction a M f x

lemma primeQuadratic_physical (a : ℝ) (M : ℕ) (f : ℝ → ℂ) :
    primeQuadratic a M f = ∫ x in window a, conj (f x) * primeAction a M f x := by
  classical
  have he : (fun x => conj (f x) * primeAction a M f x) =
      (window a).indicator (fun x => conj (f x) * primeAction a M f x) := by
    funext x
    by_cases hx : x ∈ window a
    · simp [hx]
    · simp [primeAction, compression, zeroExtension, hx]
  unfold primeQuadratic
  have hwin : MeasurableSet (window a) := measurableSet_Ioc
  calc
    (∫ x : ℝ, conj (f x) * primeAction a M f x) =
        ∫ x : ℝ, (window a).indicator
          (fun x => conj (f x) * primeAction a M f x) x := by
      exact congrArg (fun h : ℝ → ℂ => ∫ x : ℝ, h x) he
    _ = ∫ x in window a, conj (f x) * primeAction a M f x :=
      integral_indicator hwin

/-- Factor two is derived from physical reflection in the even sector.
The finite weighted action itself was defined with two independent shifts. -/
theorem primeQuadratic_even (a : ℝ) (M : ℕ) (f : ℝ → ℂ)
    (hf : Continuous f) (heven : ∀ x, f (-x) = f x) :
    primeQuadratic a M f =
      2 * ∑ r ∈ Finset.Icc 1 M, (primeWeight r : ℂ) *
        pairing a (Real.log (r : ℝ)) (fun x => conj (f x)) f := by
  classical
  have hconj : Continuous (fun x => conj (f x)) := by fun_prop
  have hp (r : ℕ) : Integrable
      (fun x => conj (f x) * compression a (Real.log (r : ℝ)) f x) :=
    integrable_compression_product a _ hconj hf
  have hm (r : ℕ) : Integrable
      (fun x => conj (f x) * compression a (-Real.log (r : ℝ)) f x) :=
    integrable_compression_product a _ hconj hf
  have hi (r : ℕ) : Integrable (fun x => (primeWeight r : ℂ) *
      (conj (f x) * compression a (Real.log (r : ℝ)) f x +
        conj (f x) * compression a (-Real.log (r : ℝ)) f x)) :=
    ((hp r).add (hm r)).const_mul _
  have hexp : (fun x => conj (f x) * primeAction a M f x) =
      (fun x => ∑ r ∈ Finset.Icc 1 M, (primeWeight r : ℂ) *
        (conj (f x) * compression a (Real.log (r : ℝ)) f x +
          conj (f x) * compression a (-Real.log (r : ℝ)) f x)) := by
    funext x
    unfold primeAction
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [primeQuadratic, hexp, integral_finsetSum _ (fun r _ => hi r), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [integral_const_mul, integral_add (hp r) (hm r)]
  change (primeWeight r : ℂ) *
      (pairing a (Real.log (r : ℝ)) (fun x => conj (f x)) f +
       pairing a (-Real.log (r : ℝ)) (fun x => conj (f x)) f) = _
  have hr₁ : (1 : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp hr).1
  rw [pairing_neg_even a _ _ _ (Real.log_nonneg hr₁)
    (by intro x; rw [heven x]) heven]
  ring

/-- Full complex physical finite-profile identity. The finite set A may
contain zero and is arbitrary; v is complex. No offdiagonal term is omitted.
The exact prime cutoff and the original half-density weights are retained. -/
theorem finite_prime_quadratic (a : ℝ) (ha : 0 < a) (M : ℕ)
    (hM : primeCutoff a ≤ M) (A : Finset ℕ) (v : ℕ → ℂ) :
    (∫ x in window a, conj (profile a A v x) * primeAction a M (profile a A v) x) =
      2 * ∑ r ∈ Finset.Icc 1 (primeCutoff a), (primeWeight r : ℂ) *
        (∑ n ∈ A, ∑ m ∈ A, (conj (v n) * v m) *
          (matrix a n m (Real.log (r : ℝ)) : ℂ)) := by
  rw [← primeQuadratic_physical]
  have hc : primeQuadratic a M (profile a A v) =
      primeQuadratic a (primeCutoff a) (profile a A v) := by
    unfold primeQuadratic
    rw [primeAction_cutoff a M hM]
  rw [hc, primeQuadratic_even a _ _ (profile_continuous a A v) (profile_even a A v)]
  apply congrArg (fun z : ℂ => 2 * z)
  apply Finset.sum_congr rfl
  intro r _
  rw [profile_pairing]
  simp_rw [matrixEntry_eq_matrix a ha]

/-- Exact real part; Re(conj(v_n)*v_m) retains all mixed complex terms. -/
theorem finite_prime_quadratic_re (a : ℝ) (ha : 0 < a) (M : ℕ)
    (hM : primeCutoff a ≤ M) (A : Finset ℕ) (v : ℕ → ℂ) :
    (∫ x in window a, conj (profile a A v x) *
      primeAction a M (profile a A v) x).re =
      2 * ∑ r ∈ Finset.Icc 1 (primeCutoff a), primeWeight r *
        (∑ n ∈ A, ∑ m ∈ A, (conj (v n) * v m).re *
          matrix a n m (Real.log (r : ℝ))) := by
  have h := congrArg Complex.re (finite_prime_quadratic a ha M hM A v)
  simpa only [Complex.re_sum, Complex.im_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, mul_zero, sub_zero] using h

/-- The full complex value is real, proved from the symmetric physical
matrix. This is an equality of quadratic forms, with no positivity claim. -/
theorem finite_prime_quadratic_real (a : ℝ) (ha : 0 < a) (M : ℕ)
    (hM : primeCutoff a ≤ M) (A : Finset ℕ) (v : ℕ → ℂ) :
    (∫ x in window a, conj (profile a A v x) *
      primeAction a M (profile a A v) x) =
      ((2 * ∑ r ∈ Finset.Icc 1 (primeCutoff a), primeWeight r *
        (∑ n ∈ A, ∑ m ∈ A, (conj (v n) * v m).re *
          matrix a n m (Real.log (r : ℝ))) : ℝ) : ℂ) := by
  have hreal : conj (primeQuadratic a M (profile a A v)) =
      primeQuadratic a M (profile a A v) := by
    rw [primeQuadratic_even a M _ (profile_continuous a A v) (profile_even a A v)]
    simp only [map_mul, map_sum, Complex.conj_ofReal, Complex.conj_ofNat,
      profile_pairing_conj a ha]
  have him : (primeQuadratic a M (profile a A v)).im = 0 := by
    have h := congrArg Complex.im hreal
    simp only [Complex.conj_im] at h
    linarith
  apply Complex.ext
  · simpa only [Complex.ofReal_re] using finite_prime_quadratic_re a ha M hM A v
  · rw [primeQuadratic_physical] at him
    simpa only [Complex.ofReal_im] using him

/-- Signed arithmetic component for the Weil form: negative twice the
weighted retained matrix quadratic form. This supplies neither Gamma nor
pole terms, and asserts no matrix positivity or Riemann hypothesis. -/
theorem finite_weil_prime_quadratic (a : ℝ) (ha : 0 < a) (M : ℕ)
    (hM : primeCutoff a ≤ M) (A : Finset ℕ) (v : ℕ → ℂ) :
    (∫ x in window a, conj (zeroExtension a (profile a A v) x) *
      (-primeSymmetric a M (zeroExtension a (profile a A v)) x)) =
      -((2 * ∑ r ∈ Finset.Icc 1 (primeCutoff a), primeWeight r *
        (∑ n ∈ A, ∑ m ∈ A, (conj (v n) * v m).re *
          matrix a n m (Real.log (r : ℝ))) : ℝ) : ℂ) := by
  calc
    _ = ∫ x in window a, conj (profile a A v x) *
        (-primeAction a M (profile a A v) x) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      have hF : zeroExtension a (profile a A v) x = profile a A v x :=
        Set.indicator_of_mem hx _
      change conj (zeroExtension a (profile a A v) x) *
        (-primeSymmetric a M (zeroExtension a (profile a A v)) x) = _
      rw [hF, ← primeAction_existing a M (profile a A v) x hx]
    _ = _ := by
      simp_rw [mul_neg]
      rw [integral_neg, finite_prime_quadratic_real a ha M hM A v]

end PhysicalCompressedCosineMatrix


