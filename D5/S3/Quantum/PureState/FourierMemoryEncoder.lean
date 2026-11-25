/- GID: D5/S3/Quantum/PureState/FourierMemoryEncoder
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/FourierMemoryEncoder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A common finite CPTP encoder attains certified profiles that are mixtures of translates. -/

import D5.S3.Quantum.PureState.QuantumMemoryBudget
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

namespace PhaseRecordDistillation

noncomputable section

open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.Recovery.KrausCompletion
open D5.S3.Quantum.Subentropy.GuessingProbability
open JointRecordDecoding PhaseRecordMemory

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Fourier character signals on the carrier. -/
def characterVector (t : G → ℝ) (χ : AddChar G ℂ) (i : G) : ℂ :=
  (t i : ℂ) * χ i

omit [DecidableEq G] in
theorem characterVector_norm (t : G → ℝ) (ht : ∑ i, t i ^ 2 = 1)
    (χ : AddChar G ℂ) :
    star (characterVector t χ) ⬝ᵥ characterVector t χ = 1 := by
  have h (i : G) : star (characterVector t χ i) * characterVector t χ i =
      ((t i ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    simp [characterVector, χ.norm_apply]
  simp only [dotProduct, Pi.star_apply, h, ← Complex.ofReal_sum, ht, Complex.ofReal_one]

/-- The normalized pure Fourier ensemble in the canonical density-state interface. -/
def characterState (t : G → ℝ) (ht : ∑ i, t i ^ 2 = 1) (χ : AddChar G ℂ) :
    DensityState G :=
  pureState (characterVector t χ) (characterVector_norm t ht χ)

omit [DecidableEq G] in
private theorem character_star_mul (χ : AddChar G ℂ) (x : G) : star (χ x) * χ x = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    χ.norm_apply, one_pow, Complex.ofReal_one]

/-- The restricted Fourier POVM has one outcome for every character. -/
def characterEffect (A : Finset G) (χ : AddChar G ℂ) : Matrix A A ℂ :=
  ((Fintype.card G : ℂ)⁻¹) • rankOneDensity (fun a : A => χ a)

omit [DecidableEq G] in
theorem characterEffect_posSemidef (A : Finset G) (χ : AddChar G ℂ) :
    (characterEffect A χ).PosSemidef :=
  (Matrix.posSemidef_vecMulVec_self_star _).smul
    (show (0 : ℂ) ≤ (Fintype.card G : ℂ)⁻¹ by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
      rw [Complex.nonneg_iff, Complex.ofReal_re, Complex.ofReal_im]
      exact ⟨by positivity, rfl⟩)

theorem sum_characterEffect (A : Finset G) :
    ∑ χ, characterEffect A χ = 1 := by
  classical
  ext a a'
  have hchar (χ : AddChar G ℂ) : χ a * star (χ a') = χ ((a : G) - a') := by
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
      AddChar.inv_apply_eq_conj]
    rfl
  simp only [Matrix.sum_apply, characterEffect, Matrix.smul_apply, smul_eq_mul,
    rankOneDensity, vecMulVec_apply, Pi.star_apply, ← Finset.mul_sum, hchar,
    AddChar.sum_apply_eq_ite, Matrix.one_apply]
  simp only [sub_eq_zero, Subtype.coe_inj]
  split_ifs
  · exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)
  · simp

/-- The part of the encoder indexed by the discarded translation coordinate `z`. -/
def translateKraus (A : Finset G) (b d : G → ℝ) (z : G) : Matrix A G ℂ :=
  Matrix.of fun a i =>
    if i = (a : G) + z then ((Real.sqrt (b z) / Real.sqrt (d i) : ℝ) : ℂ) else 0

/-- Projection onto positive profile coordinates. -/
def profileSupport (d : G → ℝ) : Matrix G G ℂ :=
  diagonal fun i => if d i = 0 then 0 else 1

private theorem translateKraus_gram (A : Finset G) (b d : G → ℝ)
    (hb : ∀ z, 0 ≤ b z) (hd : ∀ i, 0 ≤ d i)
    (htranslate : ∀ i, d i = ∑ a : A, b (i - a)) :
    ∑ z, (translateKraus A b d z)ᴴ * translateKraus A b d z = profileSupport d := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      translateKraus, Matrix.of_apply, profileSupport, diagonal_apply_eq]
    rw [Finset.sum_comm]
    have hterm (a : A) : (∑ z : G,
        star (if i = (a : G) + z then ((Real.sqrt (b z) / Real.sqrt (d i) : ℝ) : ℂ) else 0) *
        (if i = (a : G) + z then ((Real.sqrt (b z) / Real.sqrt (d i) : ℝ) : ℂ) else 0)) =
        ((b (i - a) / d i : ℝ) : ℂ) := by
      have hiff (z : G) : i = (a : G) + z ↔ z = i - a := by
        rw [eq_sub_iff_add_eq, add_comm z, eq_comm]
      simp only [hiff]
      rw [Finset.sum_eq_single (i - a)]
      · rw [ite_eq_left rfl, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
          ← pow_two, div_pow, Real.sq_sqrt (hb _), Real.sq_sqrt (hd _)]
      · intro z _ hz
        simp [hz]
      · simp
    rw [Finset.sum_congr rfl (fun a _ => hterm a),
      ← Complex.ofReal_sum, ← Finset.sum_div, ← htranslate i]
    split_ifs with h
    · simp [h]
    · simp [div_self h]
  · have hz (z : G) (a : A) :
        star (translateKraus A b d z a i) * translateKraus A b d z a j = 0 := by
      by_cases hi : i = (a : G) + z
      · have hj : j ≠ (a : G) + z := fun hj => hij (hi.trans hj.symm)
        simp [translateKraus, hj]
      · simp [translateKraus, hi]
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, hz,
      Finset.sum_const_zero, profileSupport, diagonal_apply_ne _ hij]

omit [DecidableEq G] in
private theorem sum_profile (A : Finset G) (b d : G → ℝ) (hb : ∑ z, b z = 1)
    (htranslate : ∀ i, d i = ∑ a : A, b (i - a)) :
    ∑ i, d i = Fintype.card A := by
  simp_rw [htranslate]
  rw [Finset.sum_comm]
  have h (a : A) : (∑ i : G, b (i - a)) = 1 := by
    rw [← hb]
    exact Equiv.sum_comp (Equiv.subRight (a : G)) b
  simp [h]

private theorem window_sum (A : Finset G) (b d r : G → ℝ) (c : ℝ)
    (hb : ∀ z, 0 ≤ b z) (hs : ∑ z, b z = 1)
    (hd : ∀ i, d i ≤ 1) (hclip : ∀ i, d i < 1 → r i = c)
    (htranslate : ∀ i, d i = ∑ a : A, b (i - a))
    (z : G) (hz : 0 < b z) :
    ∑ a : A, r ((a : G) + z) = ∑ i, d i * r i := by
  classical
  let e : A ↪ G := ⟨fun a => (a : G) + z, fun _ _ h => Subtype.ext (add_right_cancel h)⟩
  have hout (i : G) (hi : i ∉ Finset.univ.map e) : d i < 1 := by
    let f : A ↪ G :=
      ⟨fun a => i - (a : G), fun a a' h => Subtype.ext (sub_right_inj.mp h)⟩
    have hiz : z ∉ Finset.univ.map f := by
      intro h
      obtain ⟨a, _, ha⟩ := Finset.mem_map.mp h
      apply hi
      refine Finset.mem_map.mpr ⟨a, Finset.mem_univ _, ?_⟩
      change (a : G) + z = i
      rw [← ha]
      change (a : G) + (i - (a : G)) = i
      abel
    have hle : d i ≤ ∑ w ∈ Finset.univ.erase z, b w := by
      rw [htranslate i]
      change (∑ a : A, b (f a)) ≤ _
      rw [← Finset.sum_map]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact fun w hw => Finset.mem_erase.mpr
          ⟨fun h => hiz (h ▸ hw), Finset.mem_univ _⟩
      · exact fun w _ _ => hb w
    have hsplit := Finset.sum_erase_add Finset.univ b (Finset.mem_univ z)
    linarith
  have hsum : (∑ a : A, (r ((a : G) + z) - c)) = ∑ i, (r i - c) := by
    calc
      _ = ∑ i ∈ Finset.univ.map e, (r i - c) := (Finset.sum_map _ _ _).symm
      _ = _ := Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
        simp [hclip i (hout i hi)]
  have hprod (i : G) : d i * r i = (r i - c) + c * d i := by
    rcases (hd i).lt_or_eq with h | h
    · rw [hclip i h]; ring
    · rw [h]; ring
  simp_rw [hprod, Finset.sum_add_distrib, ← Finset.mul_sum, sum_profile A b d hs htranslate]
  rw [Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  linarith [mul_comm c (Fintype.card A : ℝ)]

private theorem kraus_apply_character (A : Finset G) (b d r t : G → ℝ)
    (ht : ∀ i, t i = Real.sqrt (d i) * r i)
    (hb : ∀ z, 0 ≤ b z) (htranslate : ∀ i, d i = ∑ a : A, b (i - a))
    (χ : AddChar G ℂ) (z : G) (a : A) :
    (translateKraus A b d z *ᵥ characterVector t χ) a =
      ((Real.sqrt (b z) * r ((a : G) + z) : ℝ) : ℂ) * χ ((a : G) + z) := by
  simp only [Matrix.mulVec, dotProduct, translateKraus, Matrix.of_apply]
  rw [Finset.sum_eq_single ((a : G) + z)]
  · simp only [ite_true, characterVector]
    by_cases hz : b z = 0
    · simp [hz]
    · have hd : 0 < d ((a : G) + z) := by
        have hle := Finset.single_le_sum (s := (Finset.univ : Finset A))
          (f := fun a' : A => b ((a : G) + z - (a' : G))) (fun a' _ => hb _) (Finset.mem_univ a)
        rw [← htranslate] at hle
        have he : (a : G) + z - a = z := by abel
        rw [he] at hle
        exact (lt_of_le_of_ne (hb z) (Ne.symm hz)).trans_le hle
      rw [ht ((a : G) + z), ← mul_assoc, ← Complex.ofReal_mul]
      have hcancel : Real.sqrt (b z) / Real.sqrt (d ((a : G) + z)) *
          (Real.sqrt (d ((a : G) + z)) * r ((a : G) + z)) =
          Real.sqrt (b z) * r ((a : G) + z) := by
        rw [← mul_assoc, div_mul_cancel₀ _ (Real.sqrt_pos.2 hd).ne']
      rw [hcancel]
  · intro i _ hi
    simp [hi]
  · simp

private theorem trace_character_branch (A : Finset G) (b d r t : G → ℝ)
    (ht : ∀ i, t i = Real.sqrt (d i) * r i)
    (hb : ∀ z, 0 ≤ b z) (htranslate : ∀ i, d i = ∑ a : A, b (i - a))
    (χ : AddChar G ℂ) (z : G) :
    (trace (characterEffect A χ *
      rankOneDensity (translateKraus A b d z *ᵥ characterVector t χ))).re =
      (Fintype.card G : ℝ)⁻¹ * b z * (∑ a : A, r ((a : G) + z)) ^ 2 := by
  have hamp : star (fun a : A => χ a) ⬝ᵥ (translateKraus A b d z *ᵥ characterVector t χ) =
      ((Real.sqrt (b z) * (∑ a : A, r ((a : G) + z)) : ℝ) : ℂ) * χ z := by
    simp only [dotProduct, Pi.star_apply, kraus_apply_character _ _ _ _ _ ht hb htranslate,
      Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [AddChar.map_add_eq_mul]
    calc
      _ = (↑(Real.sqrt (b z)) * ↑(r ((a : G) + z))) * (star (χ a) * χ a) * χ z := by ring
      _ = _ := by rw [character_star_mul, mul_one]
  rw [characterEffect, smul_mul_assoc, trace_smul, trace_rankOne_pair, hamp]
  simp only [smul_eq_mul, norm_mul, χ.norm_apply, mul_one, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hb z),
    mul_assoc]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- A single explicit CPTP encoder and the restricted Fourier POVM attain the
certified profile when the profile is a convex combination of translates of `A`.
Zero-profile columns are reset to the fixed output coordinate `a₀`. -/
theorem character_encoder_attains (A : Finset G) (a₀ : A) (b d r t : G → ℝ) (c : ℝ)
    (hb : ∀ z, 0 ≤ b z) (hs : ∑ z, b z = 1)
    (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i ≤ 1)
    (ht : ∀ i, t i = Real.sqrt (d i) * r i)
    (hclip : ∀ i, d i < 1 → r i = c)
    (hnorm : ∑ i, t i ^ 2 = 1)
    (htranslate : ∀ i, d i = ∑ a : A, b (i - a)) :
    ∃ Φ : QuantumChannel G A,
      (∀ X : Matrix G G ℂ, channelMatrix Φ X =
        (∑ z, translateKraus A b d z * X * (translateKraus A b d z)ᴴ) +
          trace ((1 - profileSupport d) * X) • Matrix.single a₀ a₀ (1 : ℂ)) ∧
      ∀ χ : AddChar G ℂ,
        (trace (characterEffect A χ *
          CStarMatrix.ofMatrix.symm (Φ.mapState (characterState t hnorm χ)).1)).re =
          (Fintype.card G : ℝ)⁻¹ * profileValue t d ^ 2 := by
  classical
  have hPH : (profileSupport d)ᴴ = profileSupport d := by
    rw [profileSupport, diagonal_conjTranspose]
    congr 1
    funext i
    by_cases hi : d i = 0 <;> simp [hi]
  have hPP : profileSupport d * profileSupport d = profileSupport d := by
    rw [profileSupport, diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : d i = 0 <;> simp [hi]
  obtain ⟨Φ, hΦ⟩ := complete_quantum_channel (translateKraus A b d) (profileSupport d)
    a₀ hPH hPP (translateKraus_gram A b d hb hd0 htranslate)
  change ∀ X, channelMatrix Φ X = _ at hΦ
  refine ⟨Φ, hΦ, fun χ => ?_⟩
  let ψ := characterVector t χ
  have hkill : (1 - profileSupport d) *ᵥ ψ = 0 := by
    ext i
    by_cases hi : d i = 0
    · have hψ : ψ i = 0 := by simp [ψ, characterVector, ht i, hi]
      simp [sub_mulVec, profileSupport, mulVec_diagonal, hi, hψ]
    · simp [sub_mulVec, profileSupport, mulVec_diagonal, hi]
  have hnorm' : ∑ i, d i * r i = profileValue t d := by
    apply Finset.sum_congr rfl
    intro i _
    rw [ht i, mul_right_comm, Real.mul_self_sqrt (hd0 i)]
  have hstate : CStarMatrix.ofMatrix.symm (Φ.mapState (characterState t hnorm χ)).1 =
      channelMatrix Φ (rankOneDensity ψ) := rfl
  have hK (z : G) : translateKraus A b d z * rankOneDensity ψ * (translateKraus A b d z)ᴴ =
      rankOneDensity (translateKraus A b d z *ᵥ ψ) := by
    rw [rankOneDensity, mul_vecMulVec, vecMulVec_mul, vecMul_conjTranspose, star_star]
    rfl
  rw [hstate, hΦ, trace_rankOne, hkill, dotProduct_zero, zero_smul, add_zero,
    Matrix.mul_sum, trace_sum, Complex.re_sum]
  calc
    _ = ∑ z, (Fintype.card G : ℝ)⁻¹ * b z * profileValue t d ^ 2 := by
      apply Finset.sum_congr rfl
      intro z _
      rw [hK z]
      change (trace (characterEffect A χ *
        rankOneDensity (translateKraus A b d z *ᵥ characterVector t χ))).re = _
      rw [trace_character_branch A b d r t ht hb htranslate]
      rcases (hb z).lt_or_eq with hz | hz
      · rw [window_sum A b d r c hb hs hd1 hclip htranslate z hz, hnorm']
      · simp [← hz]
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum, hs, mul_one]

end

end PhaseRecordDistillation
