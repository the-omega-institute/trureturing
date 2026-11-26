/- GID: D5/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/SpinorHelicityDoubleCopy4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Four-dimensional spinor kinematics, four-point consistency and the tree double copy. -/

import D5.S3.Geometry.Lorentz.WeylNullScreen
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Tactic.LinearCombination

/-! Spinor kinematics and the algebra of constructible four-point amplitudes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Geometry.Lorentz.SpinorHelicityDoubleCopy4D

open Matrix BigOperators Module
open WeylNullScreen (minkowski nullGenerator)

abbrev Spinor := Fin 2 → ℂ
abbrev Momentum := Matrix (Fin 2) (Fin 2) ℂ

def bracket (u v : Spinor) : ℂ := u 0 * v 1 - u 1 * v 0

def momentum (l r : Spinor) : Momentum := Matrix.vecMulVec l r

def mandelstam (p q : Momentum) : ℂ := -(p + q).det

theorem bracket_antisymm (u v : Spinor) : bracket u v = -bracket v u := by
  unfold bracket
  ring

@[simp] theorem bracket_self (u : Spinor) : bracket u u = 0 := by simp [bracket, mul_comm]

private theorem bracket_smul (a b : ℂ) (u v : Spinor) :
    bracket (a • u) (b • v) = a * b * bracket u v := by
  simp [bracket, Pi.smul_apply, smul_eq_mul]
  ring

theorem bracket_zero_iff_dependent (u v : Spinor) :
    bracket u v = 0 ↔ u = 0 ∨ ∃ a : ℂ, v = a • u := by
  constructor
  · intro h
    by_cases h0 : u 0 = 0
    · by_cases h1 : u 1 = 0
      · left
        funext i
        fin_cases i
        · exact h0
        · exact h1
      · have hv : v 0 = 0 := by
          simpa [bracket, h0, h1] using h
        right
        refine ⟨v 1 / u 1, ?_⟩
        funext i
        fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, h0, hv, h1]
    · right
      refine ⟨v 0 / u 0, ?_⟩
      funext i
      fin_cases i
      · simp [Pi.smul_apply, smul_eq_mul, h0]
      · change v 1 = (v 0 / u 0) * u 1
        field_simp
        unfold bracket at h
        linear_combination h
  · rintro (rfl | ⟨a, rfl⟩)
    · simp [bracket]
    · simpa using bracket_smul 1 a u u

theorem spinor_det_null (l r : Spinor) : (momentum l r).det = 0 := by
  simp only [momentum, det_fin_two, vecMulVec_apply]
  ring

theorem null_iff_rankOne (p : Momentum) : p.det = 0 ↔ ∃ l r, p = momentum l r := by
  constructor
  · intro h
    rw [det_fin_two] at h
    by_cases h0 : p 0 0 = 0
    · by_cases h1 : p 1 0 = 0
      · refine ⟨fun i => p i 1, ![0, 1], Matrix.ext fun i j => ?_⟩
        fin_cases j
        · fin_cases i <;> simp [momentum, vecMulVec_apply, h0, h1]
        · change p i 1 = p i 1 * 1
          rw [mul_one]
      · have hp : p 0 1 = 0 := by simpa [h0, h1] using h
        refine ⟨fun i => p i 0, fun j => p 1 j / p 1 0, Matrix.ext fun i j => ?_⟩
        fin_cases i
        · change p 0 j = p 0 0 * (p 1 j / p 1 0)
          fin_cases j <;> simp [h0, hp]
        · change p 1 j = p 1 0 * (p 1 j / p 1 0)
          field_simp
    · refine ⟨fun i => p i 0, fun j => p 0 j / p 0 0, Matrix.ext fun i j => ?_⟩
      fin_cases i
      · change p 0 j = p 0 0 * (p 0 j / p 0 0)
        field_simp
      · fin_cases j
        · change p 1 0 = p 1 0 * (p 0 0 / p 0 0)
          simp [h0]
        · change p 1 1 = p 1 0 * (p 0 1 / p 0 0)
          field_simp
          linear_combination h
  · rintro ⟨l, r, rfl⟩
    exact spinor_det_null l r

theorem schouten (a b c d : Spinor) :
    bracket a b * bracket c d + bracket a c * bracket d b +
      bracket a d * bracket b c = 0 := by
  unfold bracket
  ring

theorem mandelstam_brackets (a b c d : Spinor) :
    mandelstam (momentum a c) (momentum b d) = bracket a b * bracket d c := by
  simp only [mandelstam, momentum, det_fin_two, Matrix.add_apply, vecMulVec_apply, bracket]
  ring

def sigma (x : Fin 4 → ℝ) : Momentum :=
  !![(x 0 : ℂ) + x 3, (x 1 : ℂ) - Complex.I * x 2;
     (x 1 : ℂ) + Complex.I * x 2, (x 0 : ℂ) - x 3]

theorem det_sigma (x : Fin 4 → ℝ) : -(sigma x).det = ((minkowski x x : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [sigma, det_fin_two, minkowski, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im] <;> ring

theorem nullGenerator_spinor_factor (z : ℂ) :
    sigma (nullGenerator (some z)) = (2 : ℂ) • momentum ![1, z] ![1, star z] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [sigma, nullGenerator, momentum, Complex.normSq_apply, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im] <;> ring

theorem nullGenerator_south_factor :
    sigma (nullGenerator none) = (2 : ℂ) • momentum ![0, 1] ![0, 1] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [sigma, nullGenerator, momentum]

private theorem oriented_three_point (a b c u v w : Spinor)
    (h : momentum a u + momentum b v + momentum c w = 0) (hab : bracket a b ≠ 0) :
    bracket u v = 0 ∧ bracket u w = 0 ∧ bracket v w = 0 := by
  have hentry (i j : Fin 2) : a i * u j + b i * v j + c i * w j = 0 :=
    congrFun (congrFun h i) j
  have hu : u = (bracket b c / bracket a b) • w := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    unfold bracket
    linear_combination b 1 * hentry 0 j - b 0 * hentry 1 j
  have hv : v = (-bracket a c / bracket a b) • w := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    unfold bracket
    linear_combination a 0 * hentry 1 j - a 1 * hentry 0 j
  rw [hu, hv]
  have hw (d : ℂ) : bracket (d • w) w = 0 := by
    simpa [bracket_smul] using bracket_smul d 1 w w
  exact ⟨by simp [bracket_smul], hw _, hw _⟩

theorem three_point_branches (l r : Fin 3 → Spinor)
    (h : ∑ i, momentum (l i) (r i) = 0) :
    (∀ i j, bracket (r i) (r j) = 0) ∨ (∀ i j, bracket (l i) (l j) = 0) := by
  have all_pairs (v : Fin 3 → Spinor) (h01 : bracket (v 0) (v 1) = 0)
      (h02 : bracket (v 0) (v 2) = 0) (h12 : bracket (v 1) (v 2) = 0) :
      ∀ i j, bracket (v i) (v j) = 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      first | exact bracket_self _ | exact h01 | exact h02 | exact h12 |
        rw [bracket_antisymm]; simp [h01, h02, h12]
  rw [Fin.sum_univ_three] at h
  by_cases h01 : bracket (l 0) (l 1) = 0
  · by_cases h02 : bracket (l 0) (l 2) = 0
    · by_cases h12 : bracket (l 1) (l 2) = 0
      · exact Or.inr (all_pairs l h01 h02 h12)
      · have hc : momentum (l 1) (r 1) + momentum (l 2) (r 2) + momentum (l 0) (r 0) = 0 := by
          rwa [add_comm _ (momentum (l 0) (r 0)), ← add_assoc]
        obtain ⟨h₁₂, h₁₀, h₂₀⟩ := oriented_three_point _ _ _ _ _ _ hc h12
        exact Or.inl (all_pairs r (by rw [bracket_antisymm, h₁₀, neg_zero])
          (by rw [bracket_antisymm, h₂₀, neg_zero]) h₁₂)
    · have hc : momentum (l 0) (r 0) + momentum (l 2) (r 2) + momentum (l 1) (r 1) = 0 := by
        rwa [add_right_comm]
      obtain ⟨h₀₂, h₀₁, h₂₁⟩ := oriented_three_point _ _ _ _ _ _ hc h02
      exact Or.inl (all_pairs r h₀₁ h₀₂ (by rw [bracket_antisymm, h₂₁, neg_zero]))
  · obtain ⟨h₀₁, h₀₂, h₁₂⟩ := oriented_three_point _ _ _ _ _ _ h h01
    exact Or.inl (all_pairs r h₀₁ h₀₂ h₁₂)

/-- The two cleared BCFW shift numerators, with the crossed contraction supplied explicitly. -/
def channelPolynomial (s : ℕ) (x y U V W V' : ℂ) : ℂ :=
  y ^ (s - 1) * ((x + y) * U - y * V) - x ^ (s - 1) * ((x + y) * W - x * V')

/-- The difference of the two rational shifts vanishes exactly when the cleared test does. -/
theorem bcfw_iff_cleared (s : ℕ) (x y P K U V W V' : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : x + y ≠ 0) (hP : P ≠ 0) (hK : K ≠ 0) :
    P * (K / x) ^ (s - 1) * (U - y * V / (x + y)) =
      P * (K / y) ^ (s - 1) * (W - x * V' / (x + y)) ↔
      channelPolynomial s x y U V W V' = 0 := by
  have hxp := pow_ne_zero (s - 1) hx
  have hyp := pow_ne_zero (s - 1) hy
  have hkp := pow_ne_zero (s - 1) hK
  rw [← sub_eq_zero]
  have hc : P * (K / x) ^ (s - 1) * (U - y * V / (x + y)) -
      P * (K / y) ^ (s - 1) * (W - x * V' / (x + y)) =
      (P * K ^ (s - 1) / (x ^ (s - 1) * y ^ (s - 1) * (x + y))) *
        channelPolynomial s x y U V W V' := by
    simp only [div_pow, channelPolynomial]
    field_simp
  rw [hc, mul_eq_zero]
  simp [hP, hkp, hxp, hyp, hz]

private def channelU {ι : Type*} [Fintype ι] (f : ι → ι → ι → ℂ) (a b c d : ι) :=
  ∑ e, f a d e * f e c b

private def channelV {ι : Type*} [Fintype ι] (f : ι → ι → ι → ℂ) (a b c d : ι) :=
  ∑ e, f a c e * f e d b

private def channelW {ι : Type*} [Fintype ι] (f : ι → ι → ι → ℂ) (a b c d : ι) :=
  ∑ e, f a b e * f e c d

/-- Every generic pair of channels occurs on a conserved complex four-spinor chart. -/
theorem generic_channel_chart (x y : ℂ) (hz : x + y ≠ 0) :
    ∃ l r : Fin 4 → Spinor,
      (∑ i, momentum (l i) (r i) = 0) ∧
      bracket (l 0) (l 1) * bracket (l 2) (l 3) = x ∧
      bracket (l 0) (l 3) * bracket (l 1) (l 2) = y ∧
      bracket (l 0) (l 2) * bracket (l 1) (l 3) = x + y ∧
      bracket (l 1) (l 3) ^ 3 * bracket (r 0) (r 2) ≠ 0 := by
  refine ⟨![![1, 0], ![0, 1], ![1, 1], ![-x - y, -y]],
    ![![-1, x + y], ![-1, y], ![1, 0], ![0, 1]], ?_, ?_, ?_, ?_, ?_⟩
  · apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_four, momentum]
  · simp [bracket]
    ring
  · simp [bracket]
  · simp [bracket]
    ring
  · have hzy : y + x ≠ 0 := by simpa [add_comm] using hz
    have hneg : -y + -x ≠ 0 := by rwa [← neg_add, neg_ne_zero]
    simpa [bracket] using And.intro hzy hneg

/-- Equality of the two shifts throughout the generic two-channel chart. -/
def Consistent {ι : Type*} [Fintype ι] (s : ℕ) (f : ι → ι → ι → ℂ) : Prop :=
  ∀ a b c d x y, x ≠ 0 → y ≠ 0 → x + y ≠ 0 →
    channelPolynomial s x y (channelU f a b c d) (channelV f a b c d)
      (channelW f a b c d) ((-1 : ℂ) ^ s * channelV f a b c d) = 0

theorem spin_one_consistency_iff_jacobi {ι : Type*} [Fintype ι] (f : ι → ι → ι → ℂ)
    (h₁ : ∀ a b c, f a b c = -f b a c) (h₂ : ∀ a b c, f a b c = -f a c b) :
    Consistent 1 f ↔ ∀ a b c d,
      (∑ e, (f a b e * f c d e + f b c e * f a d e + f c a e * f b d e)) = 0 := by
  have hc (a b c : ι) : f a b c = f b c a := by rw [h₁ a b c, h₂ b a c, neg_neg]
  have hfactor (a b c d : ι) (x y : ℂ) :
      channelPolynomial 1 x y (channelU f a b c d) (channelV f a b c d)
          (channelW f a b c d) ((-1 : ℂ) ^ 1 * channelV f a b c d) =
        -(x + y) * (∑ e, (f a b e * f c d e + f b c e * f a d e + f c a e * f b d e)) := by
    have hs : channelU f a b c d - channelW f a b c d - channelV f a b c d =
        -(∑ e, (f a b e * f c d e + f b c e * f a d e + f c a e * f b d e)) := by
      simp only [channelU, channelW, channelV, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro e _
      rw [hc e c b, hc e c d, hc e d b, h₁ c b e, h₁ d b e, h₁ c a e]
      ring
    simp [channelPolynomial]
    linear_combination (x + y) * hs
  constructor
  · intro h a b c d
    have htest := h a b c d 1 1 one_ne_zero one_ne_zero (by norm_num)
    rw [hfactor] at htest
    exact (mul_eq_zero.mp htest).resolve_left (by norm_num)
  · intro h a b c d x y _ _ _
    rw [hfactor, h a b c d, mul_zero]

theorem spin_two_consistency_iff_associative {ι : Type*} [Fintype ι] (f : ι → ι → ι → ℂ)
    (h₁ : ∀ a b c, f a b c = f b a c) (h₂ : ∀ a b c, f a b c = f a c b) :
    Consistent 2 f ↔ ∀ a b c d, (∑ e, f a b e * f e c d) = ∑ e, f b c e * f a e d := by
  have hfactor (a b c d : ι) (x y : ℂ) :
      channelPolynomial 2 x y (channelU f a b c d) (channelV f a b c d)
          (channelW f a b c d) ((-1 : ℂ) ^ 2 * channelV f a b c d) =
        (x + y) * (y * (channelU f a b c d - channelV f a b c d) -
          x * (channelW f a b c d - channelV f a b c d)) := by
    norm_num [channelPolynomial]
    ring
  have hu (a b c d : ι) : channelU f a b c d = ∑ e, f b c e * f a e d := by
    apply Finset.sum_congr rfl
    intro e _
    rw [h₂ a e d, h₁ e c b, h₂ c e b, h₁ c b e, mul_comm]
  have hv (a b c d : ι) : channelV f a b c d = channelW f a c b d := by
    apply Finset.sum_congr rfl
    intro e _
    rw [h₂ e d b]
  have huv (a b c d : ι) : channelU f a c b d = channelU f a b c d := by
    apply Finset.sum_congr rfl
    intro e _
    rw [h₂ e b c]
  constructor
  · intro h a b c d
    have get (y : ℂ) (hy : y ≠ 0) (hz : 1 + y ≠ 0) :=
      (mul_eq_zero.mp ((hfactor a b c d 1 y).symm.trans
        (h a b c d 1 y one_ne_zero hy hz))).resolve_left hz
    have h11 := get 1 one_ne_zero (by norm_num)
    rw [← hu, ← show channelW f a b c d = (∑ e, f a b e * f e c d) from rfl]
    linear_combination -h11
  · intro h a b c d x y _ _ _
    have hc (a b c d : ι) : channelW f a b c d = channelU f a b c d :=
      (h a b c d).trans (hu a b c d).symm
    rw [hfactor, hv a b c d, hc a c b d, huv a b c d, hc a b c d]
    ring

theorem higher_spin_single_zero (s : ℕ) (hs : 3 ≤ s) (g : ℂ)
    (h : Consistent s (fun (_ _ _ : Unit) => g)) : g = 0 := by
  have hdiag := h () () () () 1 1 one_ne_zero one_ne_zero (by norm_num)
  simp only [channelU, channelV, channelW, Finset.univ_unique, Finset.sum_singleton,
    channelPolynomial, one_pow] at hdiag
  have hg : (-1 : ℂ) ^ s * (g * g) = g * g := by
    linear_combination hdiag
  have ht := h () () () () 1 2 one_ne_zero (by norm_num) (by norm_num)
  simp only [channelU, channelV, channelW, Finset.univ_unique, Finset.sum_singleton, hg] at ht
  simp only [channelPolynomial, one_pow] at ht
  have ht' : ((2 : ℂ) ^ (s - 1) - 2) * (g * g) = 0 := by
    linear_combination ht
  have hp : (2 : ℝ) < 2 ^ (s - 1) := by
    simpa using (pow_lt_pow_right₀ (show (1 : ℝ) < 2 by norm_num)
      (show 1 < s - 1 by omega))
  have hn : (2 : ℂ) ^ (s - 1) - 2 ≠ 0 := by
    intro he
    apply hp.ne'
    exact_mod_cast (sub_eq_zero.mp he)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp ht').resolve_left hn)).elim id id

open LinearMap Module.End InnerProductSpace in
/-- For a positive real species metric, the joint eigenbasis consists of independent products. -/
theorem spin_two_orthogonal_split {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (product : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (hcomm : ∀ x y, product x y = product y x)
    (hassoc : ∀ x y z, product (product x y) z = product x (product y z))
    (hsym : ∀ x, (product x).IsSymmetric) :
    ∃ B : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E, ∃ c : Fin (finrank ℝ E) → ℝ,
      (∀ i j, i ≠ j → product (B i) (B j) = 0) ∧
      ∀ i, product (B i) (B i) = c i • B i := by
  classical
  let A := stdOrthonormalBasis ℝ E
  let F := fun i => product (A i)
  have hp : Pairwise (fun a b => Commute (F a) (F b)) := by
    intro a b _
    ext z
    change product (A a) (product (A b) z) = product (A b) (product (A a) z)
    rw [← hassoc, ← hassoc, hcomm (A a) (A b)]
  let V (χ : Fin (finrank ℝ E) → ℝ) : Submodule ℝ E := ⨅ i, eigenspace (F i) (χ i)
  have hsym' i : (F i).IsSymmetric := hsym (A i)
  have hV : DirectSum.IsInternal V := IsSymmetric.directSum_isInternal_of_pairwise_commute hsym' hp
  let J := {χ // V χ ≠ ⊥}
  let _ : Fintype J := hV.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  have hVJ : DirectSum.IsInternal fun χ : J => V χ := DirectSum.isInternal_ne_bot_iff.mpr hV
  have hOJ := (IsSymmetric.orthogonalFamily_iInf_eigenspaces hsym').comp
    (Subtype.val_injective (p := fun χ => V χ ≠ ⊥))
  let B := hVJ.subordinateOrthonormalBasis rfl hOJ
  let χ (j : Fin (finrank ℝ E)) := (hVJ.subordinateOrthonormalBasisIndex rfl j hOJ).1
  have hB (i j : Fin (finrank ℝ E)) : F i (B j) = χ j i • B j := by
    have hm : B j ∈ V (χ j) := hVJ.subordinateOrthonormalBasis_subordinate rfl j hOJ
    exact mem_eigenspace_iff.mp (((Submodule.mem_iInf _).mp hm) i)
  let eigenvalue (x : E) j := ∑ i, A.toBasis.repr x i * χ j i
  have heig (x : E) (j : Fin (finrank ℝ E)) : product x (B j) = eigenvalue x j • B j := by
    conv_lhs => rw [← A.toBasis.sum_repr x]
    have hB' (i : Fin (finrank ℝ E)) : product (A.toBasis i) (B j) = χ j i • B j := hB i j
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hB',
      smul_smul, eigenvalue, Finset.sum_smul]
  refine ⟨B, fun i => eigenvalue (B i) i, ?_, fun i => heig (B i) i⟩
  intro i j hij
  have h := (heig (B i) j).symm.trans ((hcomm _ _).trans (heig (B j) i))
  have hcoef := congrArg (fun v => B.toBasis.repr v j) h
  simp [hij] at hcoef
  simp [heig, hcoef]

private theorem conservation_entries {n : ℕ} (l r : Fin n → Spinor)
    (h : ∑ i, momentum (l i) (r i) = 0) (a b : Fin 2) :
    ∑ i, l i a * r i b = 0 := by
  simpa [Matrix.sum_apply, momentum, vecMulVec_apply] using congrFun (congrFun h a) b

/-- Both complementary channels have the same invariant by momentum conservation. -/
theorem mandelstam_complement (l r : Fin 4 → Spinor)
    (h : ∑ i, momentum (l i) (r i) = 0) :
    mandelstam (momentum (l 0) (r 0)) (momentum (l 1) (r 1)) =
      mandelstam (momentum (l 2) (r 2)) (momentum (l 3) (r 3)) := by
  have hc : momentum (l 0) (r 0) + momentum (l 1) (r 1) =
      -(momentum (l 2) (r 2) + momentum (l 3) (r 3)) := by
    apply eq_neg_of_add_eq_zero_left
    simpa [Fin.sum_univ_four, add_assoc] using h
  unfold mandelstam
  rw [hc, det_neg]
  simp

private theorem mandelstam_sum (l r : Fin 4 → Spinor)
    (h : ∑ i, momentum (l i) (r i) = 0) :
    ∑ j, mandelstam (momentum (l 0) (r 0)) (momentum (l j) (r j)) = 0 := by
  simp only [Fin.sum_univ_four, mandelstam_brackets, bracket]
  have he (a b : Fin 2) := conservation_entries l r h a b
  simp only [Fin.sum_univ_four] at he
  linear_combination
    -l 0 0 * r 0 0 * he 1 1 +
    l 0 0 * r 0 1 * he 1 0 +
    l 0 1 * r 0 0 * he 0 1 -
    l 0 1 * r 0 1 * he 0 0

private theorem conservation_contraction (l r : Fin 4 → Spinor)
    (h : ∑ i, momentum (l i) (r i) = 0) (i k : Fin 4) :
    ∑ j, bracket (l i) (l j) * bracket (r j) (r k) = 0 := by
  simp only [Fin.sum_univ_four, bracket]
  have he (a b : Fin 2) := conservation_entries l r h a b
  simp only [Fin.sum_univ_four] at he
  linear_combination
    l i 0 * r k 1 * he 1 0 -
    l i 0 * r k 0 * he 1 1 -
    l i 1 * r k 1 * he 0 0 +
    l i 1 * r k 0 * he 0 1

/-- The mixed graviton–matter equation on the conserved generic chart of the two shifts. -/
theorem nonzero_graviton_matter_universal (l r : Fin 4 → Spinor)
    (h : ∑ i, momentum (l i) (r i) = 0)
    (hl : ∀ i j, i ≠ j → bracket (l i) (l j) ≠ 0)
    (hr : ∀ i j, i ≠ j → bracket (r i) (r j) ≠ 0)
    (n : ℤ) (κ κa : ℂ) (hκa : κa ≠ 0)
    (heq :
      let s := mandelstam (momentum (l 0) (r 0)) (momentum (l 1) (r 1))
      let t := mandelstam (momentum (l 0) (r 0)) (momentum (l 3) (r 3))
      let u := mandelstam (momentum (l 0) (r 0)) (momentum (l 2) (r 2))
      let B := bracket (l 0) (l 2) ^ 2 * bracket (r 1) (r 3) ^ (n + 2) /
        (bracket (r 0) (r 3) ^ 2 * bracket (r 1) (r 2) ^ (n - 2))
      (-κa ^ 2) * B *
        (bracket (r 0) (r 3) * bracket (r 1) (r 2) /
          (bracket (r 0) (r 1) * bracket (r 2) (r 3))) ^ 2 * (s / (t * u)) =
        κa * B * (κ / s + κa / u)) : κa = κ := by
  let s := mandelstam (momentum (l 0) (r 0)) (momentum (l 1) (r 1))
  let t := mandelstam (momentum (l 0) (r 0)) (momentum (l 3) (r 3))
  let u := mandelstam (momentum (l 0) (r 0)) (momentum (l 2) (r 2))
  let B := bracket (l 0) (l 2) ^ 2 * bracket (r 1) (r 3) ^ (n + 2) /
    (bracket (r 0) (r 3) ^ 2 * bracket (r 1) (r 2) ^ (n - 2))
  have hs : s ≠ 0 := by
    simp only [s, mandelstam_brackets]
    exact mul_ne_zero (hl 0 1 (by decide)) (hr 1 0 (by decide))
  have ht : t ≠ 0 := by
    simp only [t, mandelstam_brackets]
    exact mul_ne_zero (hl 0 3 (by decide)) (hr 3 0 (by decide))
  have hu : u ≠ 0 := by
    simp only [u, mandelstam_brackets]
    exact mul_ne_zero (hl 0 2 (by decide)) (hr 2 0 (by decide))
  have hB : B ≠ 0 := div_ne_zero
    (mul_ne_zero (pow_ne_zero _ (hl 0 2 (by decide))) (zpow_ne_zero _ (hr 1 3 (by decide))))
    (mul_ne_zero (pow_ne_zero _ (hr 0 3 (by decide))) (zpow_ne_zero _ (hr 1 2 (by decide))))
  have hsum : s + u + t = 0 := by
    simpa [Fin.sum_univ_four, mandelstam_brackets, s, u, t] using mandelstam_sum l r h
  have hratio : bracket (r 0) (r 3) * bracket (r 1) (r 2) /
        (bracket (r 0) (r 1) * bracket (r 2) (r 3)) = t / s := by
    have hc := conservation_contraction l r h 0 2
    simp [Fin.sum_univ_four, bracket_antisymm (r 3) (r 2)] at hc
    simp only [s, t, mandelstam_brackets, bracket_antisymm (r 1) (r 0),
      bracket_antisymm (r 3) (r 0)]
    field_simp [hl 0 1 (by decide), hr 0 1 (by decide), hr 2 3 (by decide)]
    linear_combination bracket (r 0) (r 3) * hc
  change -κa ^ 2 * B * (_ / _) ^ 2 * (s / (t * u)) = κa * B * (κ / s + κa / u) at heq
  rw [hratio] at heq
  have hreduce : -κa ^ 2 * B * (t / s) ^ 2 * (s / (t * u)) =
      κa * B * (κa / s + κa / u) := by
    field_simp
    linear_combination -hsum
  rw [hreduce] at heq
  have hc := (mul_left_cancel₀ (mul_ne_zero hκa hB) heq)
  exact (div_left_inj' hs).mp (add_right_cancel hc)

/-- The leading soft factor under the polarization shift q ⊗ ξ + ξ ⊗ q. -/
def softGaugeTerm {E : Type*} [AddCommGroup E] [Module ℂ E]
    (q ξ : E →ₗ[ℂ] ℂ) (p : E) : ℂ :=
  (q p * ξ p + ξ p * q p) / q p

/-- Gauge invariance of a conservative mixed process with nonzero total matter momentum. -/
theorem soft_ward_universal {E : Type*} [AddCommGroup E] [Module ℂ E]
    (g₁ g₂ m₁ m₂ : E) (κ κa : ℂ) (h : g₁ + g₂ + (m₁ + m₂) = 0)
    (hm : m₁ + m₂ ≠ 0) (q : E →ₗ[ℂ] ℂ)
    (hg₁ : q g₁ ≠ 0) (hg₂ : q g₂ ≠ 0) (hm₁ : q m₁ ≠ 0) (hm₂ : q m₂ ≠ 0)
    (ward : ∀ ξ : E →ₗ[ℂ] ℂ,
      κ * softGaugeTerm q ξ g₁ + κ * softGaugeTerm q ξ g₂ +
        κa * softGaugeTerm q ξ m₁ + κa * softGaugeTerm q ξ m₂ = 0) : κa = κ := by
  have hcancel (ξ : E →ₗ[ℂ] ℂ) (p : E) (hp : q p ≠ 0) :
      softGaugeTerm q ξ p = 2 * ξ p := by
    unfold softGaugeTerm
    field_simp
    ring
  have hw (ξ : E →ₗ[ℂ] ℂ) : (κa - κ) * ξ (m₁ + m₂) = 0 := by
    have hc := congrArg ξ h
    have hward := ward ξ
    rw [hcancel ξ g₁ hg₁, hcancel ξ g₂ hg₂, hcancel ξ m₁ hm₁, hcancel ξ m₂ hm₂] at hward
    simp only [map_add, map_zero] at hc ⊢
    linear_combination (1 / 2 : ℂ) * hward - κ * hc
  by_contra hne
  apply hm
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro ξ
  exact (mul_eq_zero.mp (hw ξ)).resolve_left (sub_ne_zero.mpr hne)

def parkeTaylor (l : Fin 4 → Spinor) : ℂ :=
  bracket (l 0) (l 1) ^ 4 /
    (bracket (l 0) (l 1) * bracket (l 1) (l 2) * bracket (l 2) (l 3) * bracket (l 3) (l 0))

def parkeTaylor1243 (l : Fin 4 → Spinor) : ℂ :=
  bracket (l 0) (l 1) ^ 4 /
    (bracket (l 0) (l 1) * bracket (l 1) (l 3) * bracket (l 3) (l 2) * bracket (l 2) (l 0))

/-- The stripped spin-two recursion value with negative helicities on legs one and two. -/
def gravityMHV4 (l r : Fin 4 → Spinor) : ℂ :=
  let x := bracket (l 2) (l 0) * bracket (l 3) (l 1)
  let y := bracket (l 2) (l 1) * bracket (l 0) (l 3)
  let z := bracket (l 2) (l 3) * bracket (l 0) (l 1)
  bracket (l 0) (l 1) ^ 7 * bracket (r 2) (r 3) / (x * y * z)

/-- Schouten identifies the independent rational amplitude with the single-species BCFW shift. -/
theorem gravityMHV4_bcfw (l r : Fin 4 → Spinor)
    (hl : ∀ i j, i ≠ j → bracket (l i) (l j) ≠ 0) :
    let x := bracket (l 2) (l 0) * bracket (l 3) (l 1)
    let y := bracket (l 2) (l 1) * bracket (l 0) (l 3)
    let z := bracket (l 2) (l 3) * bracket (l 0) (l 1)
    let K := bracket (l 0) (l 1) ^ 3 * bracket (r 2) (r 3)
    let P := -bracket (l 0) (l 1) ^ 4 / (x * y)
    gravityMHV4 l r = -P * (K / x) * (1 - y / z) := by
  dsimp only
  have hsch := schouten (l 2) (l 0) (l 3) (l 1)
  simp only [bracket_antisymm (l 1) (l 0)] at hsch
  unfold gravityMHV4
  field_simp [hl 2 0 (by decide), hl 3 1 (by decide), hl 2 1 (by decide),
    hl 0 3 (by decide), hl 2 3 (by decide), hl 0 1 (by decide)]
  linear_combination bracket (r 2) (r 3) * hsch

theorem klt_four_point (l r : Fin 4 → Spinor) (h : ∑ i, momentum (l i) (r i) = 0)
    (hl : ∀ i j, i ≠ j → bracket (l i) (l j) ≠ 0) :
    gravityMHV4 l r =
      -mandelstam (momentum (l 0) (r 0)) (momentum (l 1) (r 1)) *
        parkeTaylor l * parkeTaylor1243 l := by
  have hc := mandelstam_complement l r h
  simp only [mandelstam_brackets, bracket_antisymm (r 1) (r 0),
    bracket_antisymm (r 3) (r 2), mul_neg, neg_inj] at hc
  simp only [gravityMHV4, parkeTaylor, parkeTaylor1243, mandelstam_brackets,
    bracket_antisymm (r 1) (r 0), bracket_antisymm (l 3) (l 1),
    bracket_antisymm (l 2) (l 1), bracket_antisymm (l 3) (l 0),
    bracket_antisymm (l 3) (l 2)]
  field_simp [hl 0 1 (by decide), hl 0 3 (by decide), hl 1 2 (by decide),
    hl 1 3 (by decide), hl 2 3 (by decide), hl 2 0 (by decide)]
  linear_combination -hc

end D5.S3.Geometry.Lorentz.SpinorHelicityDoubleCopy4D
