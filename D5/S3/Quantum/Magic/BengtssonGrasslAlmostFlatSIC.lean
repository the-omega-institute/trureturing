/- GID: D5/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC
   generality: G
   mirror-B: D5/B/S3/Quantum/Magic/BengtssonGrasslAlmostFlatSIC
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Almost flat SIC fiducials satisfy the Bengtsson-Grassl X-overlap equation in every odd dimension. -/

import D5.S3.Quantum.Magic.ErewGoldsteinSICStabilizerRefutation
import D5.S3.Observer.MatrixUnitCertificate
import D5.S3.Quantum.Magic.ParitySectorMoments

namespace D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC

open Matrix Finset D5.S3.Observer.WindowRegister
open D5.S3.Quantum.Algebra.WeylDisplacement
open D5.S3.Quantum.Magic.ErewGoldsteinSICStabilizerRefutation
open scoped ComplexConjugate

noncomputable section

/-- Source eqs. (4)-(5): the almost flat ansatz with purely imaginary first coordinate. -/
def IsAlmostFlat (d : ℕ) [NeZero d] (v : ZMod d → ℂ) : Prop :=
  v 0 = Complex.I * (Real.sqrt (Real.sqrt (d + 1) + 2) : ℂ) ∧
  ∀ j : ZMod d, j ≠ 0 → ‖v j‖ = 1 ∧ v (-j) = -(starRingEnd ℂ) (v j)

/-- The squared norm of an almost flat vector: d + 1 + √(d+1) = 1/N². -/
noncomputable def almostFlatNorm (d : ℕ) : ℝ := d + 1 + Real.sqrt (d + 1)

variable {d : ℕ} [NeZero d] {v : ZMod d → ℂ}

/-- The cyclic shift convention, including arbitrary powers. -/
theorem shift_pow_mulVec (n : ℕ) (v : ZMod d → ℂ) (r : ZMod d) :
    (shiftMatrix d ^ n *ᵥ v) r = v (r - (n : ZMod d)) := by
  classical
  simp only [Matrix.mulVec, dotProduct,
    D5.S3.Observer.MatrixUnitCertificate.shift_matrix_pow_apply]
  have h (s : ZMod d) : r - s = (n : ZMod d) ↔ s = r - (n : ZMod d) := by
    constructor <;> intro h <;> linear_combination -h
  simp [h]

/-- Weyl overlaps in coordinates, with no additional Weyl scalar phase. -/
theorem displacement_overlap_sum (v : ZMod d → ℂ) (a b : ZMod d) :
    star v ⬝ᵥ (displacement d a b *ᵥ v) =
      ∑ r, conj (v (r + a)) * v r * ZMod.stdAddChar (b * r) := by
  classical
  have hc (r : ZMod d) : windowRoot d ^ r.val = ZMod.stdAddChar r := by
    by_cases hd : d = 1
    · subst d
      have hr : r = 0 := Subsingleton.elim _ _
      simp [hr]
    · simpa [ZMod.val_one'' hd, D5.S3.Fourier.FinitePoisson.character_apply] using
        (D5.S3.Observer.MatrixUnitCertificate.clock_phase_pow_eq_character r (1 : ZMod d))
  simp only [dotProduct, Pi.star_apply, Matrix.mulVec]
  simp_rw [D5.S3.Quantum.Magic.ParitySectorMoments.disp_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  have h (i : ZMod d) : i - r = a ↔ i = r + a := by
    constructor <;> intro h <;> linear_combination h
  simp only [h, ite_mul, zero_mul, mul_ite, mul_zero]
  simp [hc, mul_comm, mul_left_comm, mul_assoc]

/-- Character orthogonality turns a spectral square into an autocorrelation. -/
theorem spectral_autocorrelation (f : ZMod d → ℂ) (j : ZMod d) :
    (∑ b : ZMod d, ZMod.stdAddChar (-(b * j)) *
      (conj (∑ r, ZMod.stdAddChar (b * r) * f r) *
        (∑ r, ZMod.stdAddChar (b * r) * f r))) =
      (d : ℂ) * ∑ r, conj (f r) * f (r + j) := by
  classical
  have he (b t r : ZMod d) :
      ZMod.stdAddChar (-(b * j)) *
        (conj (ZMod.stdAddChar (b * t) * f t) *
          (ZMod.stdAddChar (b * r) * f r)) =
      ZMod.stdAddChar (b * (r - t - j)) * (conj (f t) * f r) := by
    rw [map_mul, ← AddChar.map_neg_eq_conj]
    calc
      _ = (ZMod.stdAddChar (-(b * j)) * ZMod.stdAddChar (-(b * t)) *
          ZMod.stdAddChar (b * r)) * (conj (f t) * f r) := by ring
      _ = _ := by
        rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
        congr 2
        ring
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  simp_rw [he]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext r
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar d), ZMod.card]
  have h (r t : ZMod d) : r - t - j = 0 ↔ r = t + j := by
    constructor <;> intro h <;> linear_combination h
  simp only [h, ite_mul, zero_mul]
  simp [Finset.mul_sum]

/-- The diagonal quartic contraction of constant nonidentity Weyl overlap squares. -/
theorem diagonal_quartic (v : ZMod d → ℂ) (K : ℝ)
    (h : ∀ a b : ZMod d,
      ‖star v ⬝ᵥ (displacement d a b *ᵥ v)‖ ^ 2 =
        K * (1 + if a = 0 ∧ b = 0 then (d : ℝ) else 0))
    (j : ZMod d) :
    ∑ r, conj (v (r + j)) ^ 2 * v r * v (r + 2 * j) =
      if j = 0 then (2 * K : ℂ) else 0 := by
  classical
  let f : ZMod d → ℂ := fun r => conj (v (r + j)) * v r
  have hs := spectral_autocorrelation f j
  have hp (b : ZMod d) :
      conj (∑ r, ZMod.stdAddChar (b * r) * f r) *
        (∑ r, ZMod.stdAddChar (b * r) * f r) =
      (K : ℂ) * (1 + if j = 0 ∧ b = 0 then (d : ℂ) else 0) := by
    have hh := h j b
    rw [displacement_overlap_sum] at hh
    have he : (∑ r, ZMod.stdAddChar (b * r) * f r) =
        ∑ r, conj (v (r + j)) * v r * ZMod.stdAddChar (b * r) := by
      apply Finset.sum_congr rfl
      intro r _
      dsimp [f]
      ring
    rw [he, Complex.conj_mul']
    have hhc := congrArg Complex.ofReal hh
    push_cast at hhc
    by_cases hcond : j = 0 ∧ b = 0 <;> simpa [hcond] using hhc
  simp_rw [hp] at hs
  have hleft : (∑ b : ZMod d, ZMod.stdAddChar (-(b * j)) *
      ((K : ℂ) * (1 + if j = 0 ∧ b = 0 then (d : ℂ) else 0))) =
      (d : ℂ) * (if j = 0 then (2 * K : ℂ) else 0) := by
    by_cases hj : j = 0
    · subst j
      simp [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
      ring
    · simp only [hj, false_and, ↓reduceIte, add_zero, mul_one]
      rw [← Finset.sum_mul]
      simp_rw [show ∀ b : ZMod d, -(b * j) = b * (-j) from fun b => by ring]
      rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar d)]
      simp [hj]
  rw [hleft] at hs
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hf := (mul_left_cancel₀ hd hs).symm
  have hconj := congrArg (starRingEnd ℂ) hf
  have hright : conj (if j = 0 then (2 * K : ℂ) else 0) =
      if j = 0 then (2 * K : ℂ) else 0 := by
    split_ifs <;> simp [Complex.conj_ofNat]
  rw [hright] at hconj
  simp only [map_sum, map_mul, Complex.conj_conj] at hconj
  calc
    _ = ∑ r, f r * conj (f (r + j)) := by
      apply Finset.sum_congr rfl
      intro r _
      dsimp [f]
      simp only [map_mul, Complex.conj_conj]
      rw [show r + j + j = r + 2 * j by ring]
      ring
    _ = _ := hconj



/-- The negative even shift has the source's explicit coordinate expression. -/
theorem overlap_sum (v : ZMod d → ℂ) (j : ZMod d) :
    star v ⬝ᵥ (shiftMatrix d ^ (-(2 * j)).val *ᵥ v) =
      ∑ r, conj (v r) * v (r + 2 * j) := by
  simp only [dotProduct, Pi.star_apply, shift_pow_mulVec, ZMod.natCast_zmod_val,
    sub_neg_eq_add, starRingEnd_apply]

/-- The purely imaginary zeroth coordinate extends the reflection law to every residue. -/
theorem conjugate_reflection (hv : IsAlmostFlat d v) (r : ZMod d) :
    conj (v r) = -v (-r) := by
  by_cases hr : r = 0
  · subst r
    simp [hv.1]
  · simpa using congrArg Neg.neg (hv.2 r hr).2.symm

/-- Squared coordinate norms, including the distinguished zeroth coordinate. -/
theorem coordinate_norm_sq (hv : IsAlmostFlat d v) (r : ZMod d) :
    ‖v r‖ ^ 2 = 1 + if r = 0 then Real.sqrt (d + 1) + 1 else 0 := by
  by_cases hr : r = 0
  · subst r
    rw [hv.1]
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (by positivity : 0 ≤ Real.sqrt (d + 1) + 2), ↓reduceIte]
    ring
  · simp [hr, (hv.2 r hr).1]

/-- The normalization denominator is the actual Hermitian squared norm. -/
theorem squared_norm (hv : IsAlmostFlat d v) :
    star v ⬝ᵥ v = (almostFlatNorm d : ℂ) := by
  classical
  have hh : ∑ r : ZMod d, ‖v r‖ ^ 2 = almostFlatNorm d := by
    simp_rw [coordinate_norm_sq hv]
    simp [Finset.sum_add_distrib, almostFlatNorm]
    ring
  change (∑ r, conj (v r) * v r) = _
  simp_rw [Complex.conj_mul', ← Complex.ofReal_pow]
  rw [← Complex.ofReal_sum, hh]

/-- Removing normalization from the SIC equations gives constant nonidentity overlap squares. -/
theorem sic_overlap_squares (hv : IsAlmostFlat d v)
    (hsic : IsSICFiducial d (((Real.sqrt (almostFlatNorm d) : ℝ) : ℂ)⁻¹ • v)) :
    ∀ a b : ZMod d,
      ‖star v ⬝ᵥ (displacement d a b *ᵥ v)‖ ^ 2 =
        (Real.sqrt (d + 1) + 1) ^ 2 *
          (1 + if a = 0 ∧ b = 0 then (d : ℝ) else 0) := by
  intro a b
  have hspos : 0 < Real.sqrt (d + 1) := Real.sqrt_pos.2 (by positivity)
  have hs : Real.sqrt (d + 1) ^ 2 = (d : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hL : 0 < almostFlatNorm d := by unfold almostFlatNorm; positivity
  have hLfactor : almostFlatNorm d = Real.sqrt (d + 1) * (Real.sqrt (d + 1) + 1) := by
    unfold almostFlatNorm
    nlinarith [hs]
  have hLsq : Real.sqrt (almostFlatNorm d) ^ 2 = almostFlatNorm d :=
    Real.sq_sqrt hL.le
  by_cases hab : a = 0 ∧ b = 0
  · rcases hab with ⟨rfl, rfl⟩
    simp only [displacement, ZMod.val_zero, pow_zero, mul_one, Matrix.one_mulVec,
      squared_norm hv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL,
      and_self, ↓reduceIte]
    rw [hLfactor, mul_pow, hs]
    ring
  · have hp : (a, b) ≠ (0, 0) := by
      intro heq
      exact hab ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
    have hm := hsic.2 a b hp
    have he : star (((Real.sqrt (almostFlatNorm d) : ℝ) : ℂ)⁻¹ • v) ⬝ᵥ
        (displacement d a b *ᵥ (((Real.sqrt (almostFlatNorm d) : ℝ) : ℂ)⁻¹ • v)) =
        ((almostFlatNorm d : ℂ)⁻¹) *
          (star v ⬝ᵥ (displacement d a b *ᵥ v)) := by
      rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
      simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
      rw [← mul_assoc, ← mul_inv, ← pow_two, ← Complex.ofReal_pow, hLsq]
    rw [he, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL] at hm
    have hn : ‖star v ⬝ᵥ (displacement d a b *ᵥ v)‖ =
        Real.sqrt (d + 1) + 1 := by
      have := (inv_mul_eq_iff_eq_mul₀ (ne_of_gt hL)).1 hm
      rw [hLfactor] at this
      convert this using 1
      field_simp [ne_of_gt hspos] <;> ring
    simp [hab, hn]

/-- Conjugate reflection identifies the autocorrelation with a negative convolution. -/
theorem overlap_convolution (hv : IsAlmostFlat d v) (j : ZMod d) :
    (∑ r, conj (v r) * v (r + 2 * j)) = -∑ r, v r * v (2 * j - r) := by
  classical
  calc
    _ = ∑ r : ZMod d, conj (v (-r)) * v (-r + 2 * j) :=
      (_root_.Equiv.sum_comp (Equiv.neg (ZMod d)) _).symm
    _ = _ := by
      simp_rw [conjugate_reflection hv, neg_neg, neg_mul]
      rw [Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      rw [show -r + 2 * j = 2 * j - r by ring]

/-- Reindexing the quartic diagonal by its midpoint. -/
theorem midpoint_contraction (hv : IsAlmostFlat d v) :
    (∑ j : ZMod d, ∑ r, conj (v (r + j)) ^ 2 * v r * v (r + 2 * j)) =
      -∑ k : ZMod d, conj (v k) ^ 2 * (∑ r, conj (v r) * v (r + 2 * k)) := by
  classical
  rw [Finset.sum_comm]
  calc
    _ = ∑ r : ZMod d, ∑ k : ZMod d, conj (v k) ^ 2 * v r * v (2 * k - r) := by
      apply Finset.sum_congr rfl
      intro r _
      apply Fintype.sum_equiv (Equiv.addRight r)
      intro j
      simp only [Equiv.coe_addRight]
      rw [show r + j = j + r by ring, show r + 2 * j = 2 * (j + r) - r by ring]
    _ = _ := by
      rw [Finset.sum_comm]
      have hc (k : ZMod d) := neg_eq_iff_eq_neg.mp (overlap_convolution hv k).symm
      simp_rw [mul_assoc, ← Finset.mul_sum, hc]
      simp [Finset.sum_neg_distrib]

/-- Equality in the aggregate bound fixes each individual unit phase. -/
theorem phase_saturation {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (z A : ι → ℂ) (C : ℝ)
    (hz : ∀ k ∈ S, ‖z k‖ = 1) (hA : ∀ k ∈ S, ‖A k‖ = C)
    (hsum : ∑ k ∈ S, conj (z k) ^ 2 * A k = (C * S.card : ℝ)) :
    ∀ k ∈ S, A k = (C : ℂ) * z k ^ 2 := by
  have he (k : ι) (hk : k ∈ S) :
      Complex.normSq (A k - (C : ℂ) * z k ^ 2) =
        2 * C ^ 2 - 2 * C * (conj (z k) ^ 2 * A k).re := by
    rw [Complex.normSq_sub, Complex.normSq_eq_norm_sq (A k), hA k hk,
      Complex.normSq_mul, map_pow, Complex.normSq_eq_norm_sq (z k), hz k hk]
    simp only [one_pow, mul_one, Complex.normSq_ofReal, map_mul, map_pow,
      Complex.conj_ofReal]
    have hprod : A k * ((C : ℂ) * conj (z k) ^ 2) =
        (C : ℂ) * (conj (z k) ^ 2 * A k) := by ring
    rw [hprod, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have hr := congrArg Complex.re hsum
  simp only [Complex.ofReal_re, Complex.re_sum] at hr
  have hzero : ∑ k ∈ S, Complex.normSq (A k - (C : ℂ) * z k ^ 2) = 0 := by
    rw [Finset.sum_congr rfl he]
    rw [Finset.sum_sub_distrib, Finset.sum_const]
    simp only [nsmul_eq_mul]
    rw [← Finset.mul_sum, hr]
    ring
  intro k hk
  have := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => Complex.normSq_nonneg (A k - (C : ℂ) * z k ^ 2))).1 hzero k hk
  exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp this)

/-- Bengtsson–Grassl 2025 conjecture: the X-overlap equation (8) holds for every
almost flat SIC fiducial in every odd dimension. -/
theorem result : ∀ (d : ℕ) [NeZero d], Odd d → ∀ v : ZMod d → ℂ, IsAlmostFlat d v →
    IsSICFiducial d (((Real.sqrt (almostFlatNorm d) : ℝ) : ℂ)⁻¹ • v) →
    ∀ j : ZMod d, j ≠ 0 →
      star v ⬝ᵥ (shiftMatrix d ^ (-(2 * j)).val *ᵥ v) =
        ((Real.sqrt (d + 1) + 1 : ℝ) : ℂ) * v j ^ 2 := by
  intro d _ hodd v hv hsic j hj
  classical
  let C : ℝ := Real.sqrt (d + 1) + 1
  let A : ZMod d → ℂ := fun k => ∑ r, conj (v r) * v (r + 2 * k)
  let S : Finset (ZMod d) := Finset.univ.erase 0
  have hspec := sic_overlap_squares hv hsic
  have hquartic : (∑ k : ZMod d, ∑ r,
      conj (v (r + k)) ^ 2 * v r * v (r + 2 * k)) = (2 * C ^ 2 : ℂ) := by
    simp_rw [diagonal_quartic v (C ^ 2) hspec]
    simp
  have htotal : ∑ k : ZMod d, conj (v k) ^ 2 * A k = -(2 * C ^ 2 : ℂ) := by
    rw [midpoint_contraction hv] at hquartic
    exact neg_eq_iff_eq_neg.mp hquartic
  have hA0 : A 0 = (almostFlatNorm d : ℂ) := by
    dsimp only [A]
    simp only [mul_zero, add_zero]
    exact squared_norm hv
  have hv0 : conj (v 0) ^ 2 = -((Real.sqrt (d + 1) + 2 : ℝ) : ℂ) := by
    have ht : (Real.sqrt (Real.sqrt (d + 1) + 2) : ℂ) ^ 2 =
        ((Real.sqrt (d + 1) + 2 : ℝ) : ℂ) := by
      exact_mod_cast Real.sq_sqrt (by positivity : 0 ≤ Real.sqrt (d + 1) + 2)
    rw [hv.1, map_mul, Complex.conj_I, Complex.conj_ofReal, mul_pow, neg_sq,
      Complex.I_sq, ht]
    ring
  have hScard : (S.card : ℝ) = (d : ℝ) - 1 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card,
      Nat.cast_sub (NeZero.pos d)]
    norm_num
  have hsum : ∑ k ∈ S, conj (v k) ^ 2 * A k = (C * S.card : ℝ) := by
    have he := Finset.sum_erase_add Finset.univ (fun k => conj (v k) ^ 2 * A k)
      (Finset.mem_univ 0)
    rw [htotal, hv0, hA0] at he
    have hs : Real.sqrt (d + 1) ^ 2 = (d : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have halg : (Real.sqrt (d + 1) + 2) * almostFlatNorm d - 2 * C ^ 2 =
        C * S.card := by
      rw [hScard]
      dsimp [almostFlatNorm, C]
      nlinarith
    have hc := congrArg Complex.ofReal halg
    push_cast at he hc ⊢
    dsimp [S]
    linear_combination he + hc
  have hnorm (k : ZMod d) (hk : k ∈ S) : ‖A k‖ = C := by
    have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
    have hu : IsUnit (2 : ZMod d) :=
      (ZMod.isUnit_iff_coprime 2 d).2 (Nat.coprime_two_left.mpr hodd)
    have ha : -(2 * k) ≠ 0 := by
      intro he
      exact hk0 (hu.mul_right_eq_zero.mp (neg_eq_zero.mp he))
    have hh := hspec (-(2 * k)) 0
    have hsumA : star v ⬝ᵥ (displacement d (-(2 * k)) 0 *ᵥ v) = A k := by
      simpa [displacement, A] using overlap_sum v k
    rw [hsumA] at hh
    simp only [ha, false_and, ↓reduceIte, add_zero, mul_one] at hh
    dsimp [C]
    nlinarith [norm_nonneg (A k), Real.sqrt_nonneg (d + 1)]
  rw [overlap_sum]
  exact phase_saturation S v A C (fun k hk => (hv.2 k (Finset.mem_erase.mp hk).1).1)
    hnorm hsum j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)

#print axioms result

end
end D5.S3.Quantum.Magic.BengtssonGrasslAlmostFlatSIC
