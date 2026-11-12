/- GID: D5/S3/Topology/JBSquareDefect
   generality: G
   mirror-B: D5/B/S3/Topology/JBSquareDefect
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Algebra.Jordan.Basic]
   utility: none
   digest: Spectral square defects force multiplicativity from spanning idempotents. -/

module

public import D5.S3.Topology.JBComplexification
public import Mathlib.LinearAlgebra.Span.Basic

/-! The square-defect step uses the actual six JB laws and finite spectral resolutions.
It does not supply the spectral resolution, support normalization or a PRE interface. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace D5.S3.Topology.JBSquareDefect

open JBAlgebra JBPositiveShift JBComplexification
open scoped BigOperators

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {S : X →ₗ[ℝ] X →ₗ[ℝ] X} {u : X}
  {T : Y →ₗ[ℝ] Y →ₗ[ℝ] Y} {v : Y}

/-- Finite spectral data in the original product. No map or multiplicativity
condition occurs in this predicate. Its existence is a separate supplier. -/
def HasFiniteSpectralResolutions (S : X →ₗ[ℝ] X →ₗ[ℝ] X) (u : X) : Prop :=
  ∀ a : X, ∃ (n : ℕ) (e : Fin n → X) (r : Fin n → ℝ),
    (∀ i, S (e i) (e i) = e i) ∧
    ∑ i, e i = u ∧ ∑ i, r i • e i = a ∧
    ∑ i, (r i * r i) • e i = S a a

private theorem add_squares (A : Data Y T v) {p q : Y}
    (hp : ∃ z, T z z = p) (hq : ∃ z, T z z = q) :
    ∃ z, T z z = p + q := by
  apply square_of_ambient_center A (p + q) (‖p‖ + ‖q‖) (by positivity)
  have hp' := (square_iff_center A p).mp hp
  have hq' := (square_iff_center A q).mp hq
  have he : p + q - (‖p‖ + ‖q‖) • v =
      (p - ‖p‖ • v) + (q - ‖q‖ • v) := by module
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hp' hq')

private theorem sum_squares (A : Data Y T v) {ι : Type*}
    (s : Finset ι) (f : ι → Y) (hf : ∀ i ∈ s, ∃ z, T z z = f i) :
    ∃ z, T z z = ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact add_squares A (hf i (by simp)) (ih (fun j hj => hf j (by simp [hj])))

/-- The explicit spectral sum identity for the same map, spectrum and target product. -/
theorem square_defect_identity (A : Data Y T v) {n : ℕ}
    (e : Fin n → X) (r : Fin n → ℝ) (Φ : X →ₗ[ℝ] Y)
    (hunit : Φ u = v) (heu : ∑ i, e i = u) {a : X}
    (hea : ∑ i, r i • e i = a)
    (heaa : ∑ i, (r i * r i) • e i = S a a) :
    ∑ i, quadratic T (r i • v - Φ a) (Φ (e i)) =
      Φ (S a a) - T (Φ a) (Φ a) := by
  let z : Fin n → Y := fun i => Φ (e i)
  let b := Φ a
  have hz : ∑ i, z i = v := by
    simpa only [z, ← map_sum, heu] using hunit
  have hrz : ∑ i, r i • z i = b := by
    simp only [z, b, ← map_smul, ← map_sum, hea]
  have hrrz : ∑ i, (r i * r i) • z i = Φ (S a a) := by
    simp only [z, ← map_smul, ← map_sum, heaa]
  have hsum : ∑ i, quadratic T (r i • v - b) (z i) =
      Φ (S a a) - T b b := by
    have hright (x : Y) : T x v = x := (A.symm x v).trans (A.unit_mul x)
    have hquad (i : Fin n) : quadratic T (r i • v - b) (z i) =
        (r i * r i) • z i - (2 : ℝ) • (r i • T b (z i)) +
          quadratic T b (z i) := by
      simp only [quadratic, map_sub, map_smul, LinearMap.sub_apply,
        LinearMap.smul_apply, A.unit_mul, hright]
      module
    have hcross : ∑ i, r i • T b (z i) = T b b := by
      simpa only [map_sum, map_smul] using congrArg (T b) hrz
    have hp : ∑ i, quadratic T b (z i) = T b b := by
      simp only [quadratic, Finset.sum_sub_distrib, ← Finset.smul_sum, ← map_sum,
        hz, hright]
      module
    simp only [hquad, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.smul_sum, hrrz, hcross, hp]
    module
  exact hsum

/-- Positivity of the square defect is derived from finite spectral data and
the original all-argument quadratic-positivity theorem. -/
theorem square_defect_of_spectral (A : Data Y T v)
    (hspec : HasFiniteSpectralResolutions S u) (Φ : X →ₗ[ℝ] Y)
    (hunit : Φ u = v) (hpos : ∀ x, ∃ y, T y y = Φ (S x x)) (a : X) :
    ∃ z, T z z = Φ (S a a) - T (Φ a) (Φ a) := by
  obtain ⟨n, e, r, he, heu, hea, heaa⟩ := hspec a
  have hsum := square_defect_identity A e r Φ hunit heu hea heaa
  rw [← hsum]
  apply sum_squares A
  intro i _
  obtain ⟨w, hw⟩ := hpos (e i)
  rw [he i] at hw
  obtain ⟨q, hq⟩ := quadratic_preserves_squares A (r i • v - Φ a) w
  exact ⟨q, by simpa only [hw] using hq.symm⟩

omit [CompleteSpace Y] in
theorem zero_defect_cross (A : Data Y T v)
    (hsymm : ∀ x y, S x y = S y x) (Φ : X →ₗ[ℝ] Y)
    (hdef : ∀ a, ∃ z, T z z = Φ (S a a) - T (Φ a) (Φ a))
    (a : X) (ha : Φ (S a a) - T (Φ a) (Φ a) = 0) (x : X) :
    Φ (S a x) = T (Φ a) (Φ x) := by
  let d := Φ (S x x) - T (Φ x) (Φ x)
  let c := Φ (S a x) - T (Φ a) (Φ x)
  let g (t : ℝ) := Φ (S (t • a + x) (t • a + x)) -
    T (Φ (t • a + x)) (Φ (t • a + x))
  have hexp (t : ℝ) : g t = (2 * t) • c + d := by
    have he : Φ (S a a) = T (Φ a) (Φ a) := sub_eq_zero.mp ha
    dsimp [g, c, d]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      hsymm x a, A.symm (Φ x) (Φ a), he]
    module
  have hsum (t : ℝ) : g t + g (-t) = (2 : ℝ) • d := by
    rw [hexp, hexp]
    module
  have hdiff (t : ℝ) : g t - g (-t) = (4 * t) • c := by
    rw [hexp, hexp]
    module
  have hbound (t : ℝ) : ‖g t‖ ≤ 2 * ‖d‖ := by
    obtain ⟨q, hq⟩ := hdef (t • a + x)
    obtain ⟨r, hr⟩ := hdef ((-t) • a + x)
    have hb := A.square_mono q r
    change T q q = g t at hq
    change T r r = g (-t) at hr
    rw [hq, hr, hsum, norm_smul,
      Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hb
    exact hb
  have hlinear (t : ℝ) : |t| * ‖c‖ ≤ ‖d‖ := by
    have hb := norm_sub_le (g t) (g (-t))
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hb
    nlinarith [hbound t, hbound (-t)]
  have hc : c = 0 := by
    by_contra hc
    have hn : 0 < ‖c‖ := norm_pos_iff.mpr hc
    let t := (‖d‖ + 1) / ‖c‖
    have ht : 0 ≤ t := (div_pos (by positivity) hn).le
    have hb := hlinear t
    rw [abs_of_nonneg ht] at hb
    have he : t * ‖c‖ = ‖d‖ + 1 := div_mul_cancel₀ _ hn.ne'
    linarith
  exact sub_eq_zero.mp hc

/-- Preserving idempotence on any real spanning set forces multiplicativity.
Square positivity and spectral resolutions are genuine inputs; neither a
Jordan-map certificate nor cross-product preservation is assumed. -/
theorem multiplicative_of_spanning_idempotents (A : Data Y T v)
    (hsymm : ∀ x y, S x y = S y x)
    (hspec : HasFiniteSpectralResolutions S u) (Φ : X →ₗ[ℝ] Y)
    (hunit : Φ u = v) (hpos : ∀ x, ∃ y, T y y = Φ (S x x))
    (s : Set X) (hspan : Submodule.span ℝ s = ⊤)
    (hid : ∀ e ∈ s, S e e = e ∧ T (Φ e) (Φ e) = Φ e) :
    ∀ a x, Φ (S a x) = T (Φ a) (Φ x) := by
  have hdef := square_defect_of_spectral A hspec Φ hunit hpos
  intro a x
  have ha : a ∈ Submodule.span ℝ s := by rw [hspan]; trivial
  induction ha using Submodule.span_induction with
  | mem e he =>
    apply zero_defect_cross A hsymm Φ hdef e _ x
    rw [(hid e he).1, (hid e he).2, sub_self]
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | smul r a _ ha => simp only [map_smul, LinearMap.smul_apply, ha]

#print axioms multiplicative_of_spanning_idempotents

end D5.S3.Topology.JBSquareDefect
