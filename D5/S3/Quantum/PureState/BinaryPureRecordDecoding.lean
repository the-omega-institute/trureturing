/- GID: D5/S3/Quantum/PureState/BinaryPureRecordDecoding
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/BinaryPureRecordDecoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint POVM optimum for independent fair binary pure records on their product carrier. -/

import D5.S3.Quantum.PureState.JointRecordTransport
import Mathlib.Data.Fintype.EquivFin

/-! Application of the exact Walsh law to arbitrary normalized binary pure records. -/

namespace JointRecordDecoding

noncomputable section

open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Subentropy.GuessingProbability
open D5.S3.Quantum.PureState.PureStateHandshake

section CoordinateRecords

variable {k : ℕ} {A : Fin k → Type*} [∀ i, Fintype (A i)]

/-- The tensor product of the chosen local amplitudes in the original coordinate carriers. -/
def coordinateProductRecord (v : (i : Fin k) → Bool → A i → ℂ)
    (j : Word k) (x : (i : Fin k) → A i) : ℂ :=
  ∏ i, v i (j i) (x i)

theorem coordinateProductRecord_norm (v : (i : Fin k) → Bool → A i → ℂ)
    (hv : ∀ i b, star (v i b) ⬝ᵥ v i b = 1) (j : Word k) :
    star (coordinateProductRecord v j) ⬝ᵥ coordinateProductRecord v j = 1 := by
  simp only [dotProduct, Pi.star_apply, coordinateProductRecord, star_prod,
    ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i x => star (v i (j i) x) * v i (j i) x)]
  exact Finset.prod_eq_one fun i _ => hv i (j i)

/-- The actual joint pure states for independent binary inputs on the original product carrier. -/
def coordinateProductRecordState [∀ i, DecidableEq (A i)]
    (v : (i : Fin k) → Bool → A i → ℂ) (hv : ∀ i b, star (v i b) ⬝ᵥ v i b = 1)
    (j : Word k) : DensityState ((i : Fin k) → A i) :=
  pureState (coordinateProductRecord v j) (coordinateProductRecord_norm v hv j)

private def tensorMatrix (V : (i : Fin k) → Matrix (A i) Bool ℂ) :
    Matrix ((i : Fin k) → A i) (Word k) ℂ :=
  fun x b => ∏ i, V i (x i) (b i)

private theorem tensorMatrix_gram (V : (i : Fin k) → Matrix (A i) Bool ℂ)
    (d : Fin k → Bool → ℂ) (hV : ∀ i, (V i)ᴴ * V i = diagonal (d i)) :
    (tensorMatrix V)ᴴ * tensorMatrix V = diagonal (fun b => ∏ i, d i (b i)) := by
  ext b c
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, tensorMatrix, star_prod,
    ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i x => star (V i x (b i)) * V i x (c i))]
  change (∏ i, ((V i)ᴴ * V i) (b i) (c i)) = _
  simp_rw [hV]
  by_cases h : b = c
  · subst c
    simp
  · obtain ⟨i, hi⟩ : ∃ i, b i ≠ c i := by
      by_contra! hc
      exact h (funext hc)
    rw [Matrix.diagonal_apply_ne _ h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.diagonal_apply_ne _ hi)

end CoordinateRecords

private def bitVector (s : ℝ) (j x : Bool) : ℂ :=
  (bitWeight s x : ℂ) * bitPhase j x

/-- The minus coordinate is unoccupied exactly when the overlap has modulus one. -/
private def bitSupport (s : ℝ) (b : Bool) : ℂ :=
  if s = 1 ∧ b = true then 0 else 1

private theorem bitSupport_mul_bitVector (s : ℝ) (b x : Bool) :
    bitSupport s x * bitVector s b x = bitVector s b x := by
  by_cases h : s = 1
  · subst s
    cases x <;> norm_num [bitSupport, bitVector, bitWeight]
  · simp [bitSupport, h]

private theorem coordinateRecordVector_apply {k : ℕ} (s : Fin k → ℝ) (j x : Word k) :
    coordinateRecordVector s j x = ∏ i, bitVector (s i) (j i) (x i) := by
  simp only [coordinateRecordVector, phaseVector, coordinateWeight, walsh, bitVector,
    Complex.ofReal_prod, Finset.prod_mul_distrib]

private theorem tensorMatrix_mul_recordVector {k : ℕ} {A : Fin k → Type*}
    (V : (i : Fin k) → Matrix (A i) Bool ℂ)
    (v : (i : Fin k) → Bool → A i → ℂ) (s : Fin k → ℝ)
    (h : ∀ i b, V i *ᵥ bitVector (s i) b = v i b) (j : Word k) :
    tensorMatrix V *ᵥ coordinateRecordVector s j = coordinateProductRecord v j := by
  funext x
  change (∑ y, (∏ i, V i (x i) (y i)) * coordinateRecordVector s j y) = _
  simp only [coordinateRecordVector_apply, ← Finset.prod_mul_distrib]
  rw [sum_words (fun i y => V i (x i) y * bitVector (s i) (j i) y)]
  exact Finset.prod_congr rfl fun i _ => congrFun (h i (j i)) (x i)

section LocalRecords

variable {A : Type*} [Fintype A]

private theorem dot_smul_left (c : ℂ) (v w : A → ℂ) :
    star (c • v) ⬝ᵥ w = star c * (star v ⬝ᵥ w) := by
  rw [star_smul, smul_dotProduct, smul_eq_mul]

private theorem dot_smul_right (c : ℂ) (v w : A → ℂ) :
    star v ⬝ᵥ (c • w) = c * (star v ⬝ᵥ w) :=
  dotProduct_smul c _ _

private theorem real_overlap_pair (v w : A → ℂ) (s : ℝ)
    (hs : star v ⬝ᵥ w = (s : ℂ)) :
    star w ⬝ᵥ v = (s : ℂ) := by
  rw [star_dotProduct, hs]
  simp

private theorem pair_plus_self (v w : A → ℂ) (s : ℝ)
    (hv : star v ⬝ᵥ v = 1) (hw : star w ⬝ᵥ w = 1)
    (hs : star v ⬝ᵥ w = (s : ℂ)) :
    star (v + w) ⬝ᵥ (v + w) = 2 * (1 + (s : ℂ)) := by
  simp only [star_add, add_dotProduct, dotProduct_add, hv, hw, hs,
    real_overlap_pair v w s hs]
  ring

private theorem pair_minus_self (v w : A → ℂ) (s : ℝ)
    (hv : star v ⬝ᵥ v = 1) (hw : star w ⬝ᵥ w = 1)
    (hs : star v ⬝ᵥ w = (s : ℂ)) :
    star (v - w) ⬝ᵥ (v - w) = 2 * (1 - (s : ℂ)) := by
  simp only [star_sub, sub_dotProduct, dotProduct_sub, hv, hw, hs,
    real_overlap_pair v w s hs]
  ring

private theorem pair_plus_minus (v w : A → ℂ) (s : ℝ)
    (hv : star v ⬝ᵥ v = 1) (hw : star w ⬝ᵥ w = 1)
    (hs : star v ⬝ᵥ w = (s : ℂ)) :
    star (v + w) ⬝ᵥ (v - w) = 0 := by
  simp only [star_add, add_dotProduct, dotProduct_sub, hv, hw, hs,
    real_overlap_pair v w s hs]
  ring

private theorem exists_pair_isometry (v : Bool → A → ℂ)
    (hv : ∀ b, star (v b) ⬝ᵥ v b = 1) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hs : star (v false) ⬝ᵥ v true = (s : ℂ)) :
    ∃ V : Matrix A Bool ℂ, Vᴴ * V = 1 ∧ ∀ b, V *ᵥ bitVector s b = v b := by
  let a : ℂ := (bitWeight s false : ℝ)
  let b : ℂ := (bitWeight s true : ℝ)
  have ha0 : a ≠ 0 := by
    dsimp [a, bitWeight]
    exact_mod_cast (Real.sqrt_pos.2 (by linarith : 0 < (1 + s) / 2)).ne'
  have hb0 : b ≠ 0 := by
    dsimp [b, bitWeight]
    exact_mod_cast (Real.sqrt_pos.2 (by linarith : 0 < (1 - s) / 2)).ne'
  have ha2 : a ^ 2 = (1 + (s : ℂ)) / 2 := by
    dsimp [a, bitWeight]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith : 0 ≤ (1 + s) / 2)]
    push_cast
    rfl
  have hb2 : b ^ 2 = (1 - (s : ℂ)) / 2 := by
    dsimp [b, bitWeight]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith : 0 ≤ (1 - s) / 2)]
    push_cast
    rfl
  let plus : A → ℂ := (2 * a)⁻¹ • (v false + v true)
  let minus : A → ℂ := (2 * b)⁻¹ • (v false - v true)
  have htwo : (starRingEnd ℂ) 2 = 2 := map_natCast (starRingEnd ℂ) 2
  have hplus : star plus ⬝ᵥ plus = 1 := by
    dsimp only [plus]
    rw [dot_smul_left, dot_smul_right, pair_plus_self _ _ s (hv false) (hv true) hs]
    simp only [star_inv₀, star_mul, Complex.star_def, Complex.conj_ofReal, a]
    rw [htwo, mul_comm (↑(bitWeight s false) : ℂ) 2]
    change (2 * a)⁻¹ * ((2 * a)⁻¹ * (2 * (1 + (s : ℂ)))) = 1
    rw [show 2 * (1 + (s : ℂ)) = (2 * a) ^ 2 by rw [mul_pow, ha2]; ring]
    field_simp
  have hminus : star minus ⬝ᵥ minus = 1 := by
    dsimp only [minus]
    rw [dot_smul_left, dot_smul_right, pair_minus_self _ _ s (hv false) (hv true) hs]
    simp only [star_inv₀, star_mul, Complex.star_def, Complex.conj_ofReal, b]
    rw [htwo, mul_comm (↑(bitWeight s true) : ℂ) 2]
    change (2 * b)⁻¹ * ((2 * b)⁻¹ * (2 * (1 - (s : ℂ)))) = 1
    rw [show 2 * (1 - (s : ℂ)) = (2 * b) ^ 2 by rw [mul_pow, hb2]; ring]
    field_simp
  have hcross : star plus ⬝ᵥ minus = 0 := by
    dsimp only [plus, minus]
    rw [dot_smul_left, dot_smul_right, pair_plus_minus _ _ s (hv false) (hv true) hs]
    simp
  have hcross' : star minus ⬝ᵥ plus = 0 := by rw [star_dotProduct, hcross, star_zero]
  let V : Matrix A Bool ℂ := fun x i => if i then minus x else plus x
  refine ⟨V, ?_, ?_⟩
  · ext i j
    cases i <;> cases j
    · change star plus ⬝ᵥ plus = 1
      exact hplus
    · change star plus ⬝ᵥ minus = 0
      exact hcross
    · change star minus ⬝ᵥ plus = 0
      exact hcross'
    · change star minus ⬝ᵥ minus = 1
      exact hminus
  · intro j
    funext x
    change (∑ z, V x z * bitVector s j z) = _
    rw [sum_bool]
    have ha : (bitWeight s false : ℂ) = a := rfl
    have hb : (bitWeight s true : ℂ) = b := rfl
    cases j <;>
      simp only [V, bitVector, bitPhase, Bool.false_eq_true, ↓reduceIte,
        Bool.and_false, Bool.and_true, mul_one, mul_neg, plus, minus, Pi.smul_apply,
        Pi.add_apply, Pi.sub_apply, smul_eq_mul] <;>
      rw [ha, hb] <;> field_simp <;> ring

private theorem exists_pair_partialIsometry (v : Bool → A → ℂ)
    (hv : ∀ b, star (v b) ⬝ᵥ v b = 1) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hs : star (v false) ⬝ᵥ v true = (s : ℂ)) :
    ∃ V : Matrix A Bool ℂ,
      Vᴴ * V = diagonal (bitSupport s) ∧
      (∀ x b, V x b * bitSupport s b = V x b) ∧
      ∀ b, V *ᵥ bitVector s b = v b := by
  rcases lt_or_eq_of_le hs1 with hlt | rfl
  · obtain ⟨V, hgram, hmap⟩ := exists_pair_isometry v hv s hs0 hlt hs
    refine ⟨V, ?_, ?_, hmap⟩
    · have hd : bitSupport s = fun _ => 1 := funext fun b => by simp [bitSupport, hlt.ne]
      rw [hd, diagonal_one]
      exact hgram
    · intro x b
      simp [bitSupport, hlt.ne]
  · have he : v false = v true := by
      apply sub_eq_zero.mp
      apply dotProduct_star_self_eq_zero.mp
      rw [pair_minus_self _ _ 1 (hv false) (hv true) hs]
      norm_num
    let V : Matrix A Bool ℂ := fun x b => if b then 0 else v false x
    refine ⟨V, ?_, ?_, ?_⟩
    · ext b c
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
      cases b <;> cases c
      · simpa [V, bitSupport, dotProduct, Pi.star_apply] using hv false
      all_goals simp [V, bitSupport]
    · intro x b
      cases b <;> simp [V, bitSupport]
    · intro b
      funext x
      change (∑ y, V x y * bitVector 1 b y) = v b x
      rw [sum_bool]
      cases b <;> norm_num [V, bitVector, bitPhase, bitWeight, ← he]

private theorem unit_phase (c : ℂ) (hc : ‖c‖ = 1) : star c * c = 1 := by
  change (starRingEnd ℂ) c * c = 1
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hc]
  norm_num

private theorem pureState_smul_eq [DecidableEq A] (c : ℂ) (v : A → ℂ)
    (hc : ‖c‖ = 1) (hv : star v ⬝ᵥ v = 1) :
    pureState (c • v)
      (by rw [dot_smul_left, dot_smul_right, hv, mul_one, unit_phase c hc]) =
    pureState v hv := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  simp only [pureState_matrix]
  ext i j
  simp only [rankOneDensity, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply, star_mul]
  have hunit : c * star c = 1 := by rw [mul_comm, unit_phase c hc]
  linear_combination (v i * star (v j)) * hunit

/-- The modulus of the overlap of two unit amplitudes is in the domain of the finite law. -/
theorem unit_overlap_le (v w : A → ℂ) (hv : star v ⬝ᵥ v = 1) (hw : star w ⬝ᵥ w = 1) :
    ‖star v ⬝ᵥ w‖ ≤ 1 := by
  let a : EuclideanSpace ℂ A := WithLp.toLp 2 v
  let b : EuclideanSpace ℂ A := WithLp.toLp 2 w
  have norm_unit (u : A → ℂ) (hu : star u ⬝ᵥ u = 1) :
      ‖(WithLp.toLp 2 u : EuclideanSpace ℂ A)‖ = 1 := by
    have hsq := norm_sq_eq_re_inner (𝕜 := ℂ) (WithLp.toLp 2 u : EuclideanSpace ℂ A)
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hsq
    rw [dotProduct_comm] at hsq
    change _ = (star u ⬝ᵥ u).re at hsq
    rw [hu, Complex.one_re] at hsq
    nlinarith [norm_nonneg (WithLp.toLp 2 u : EuclideanSpace ℂ A)]
  have h := norm_inner_le_norm (𝕜 := ℂ) a b
  change ‖⟪a, b⟫_ℂ‖ ≤ ‖(WithLp.toLp 2 v : EuclideanSpace ℂ A)‖ *
    ‖(WithLp.toLp 2 w : EuclideanSpace ℂ A)‖ at h
  rw [EuclideanSpace.inner_eq_star_dotProduct, norm_unit v hv, norm_unit w hw, one_mul] at h
  simpa [a, b, dotProduct_comm] using h

private theorem exists_pair_phase (v : Bool → A → ℂ) :
    ∃ phase : Bool → ℂ, (∀ b, ‖phase b‖ = 1) ∧
      star (phase false • v false) ⬝ᵥ (phase true • v true) =
        (‖star (v false) ⬝ᵥ v true‖ : ℂ) := by
  let z := star (v false) ⬝ᵥ v true
  let c : ℂ := if z = 0 then 1 else (‖z‖ : ℂ) / z
  have hc : ‖c‖ = 1 := by
    dsimp [c]
    split_ifs with h
    · simp
    · simp [norm_ne_zero_iff.mpr h]
  have hcz : c * z = (‖z‖ : ℂ) := by
    dsimp [c]
    split_ifs with h
    · simp [h]
    · exact div_mul_cancel₀ _ h
  refine ⟨fun b => if b then c else 1, fun b => ?_, ?_⟩
  · cases b <;> simp [hc]
  · rw [dot_smul_left, dot_smul_right]
    simpa [z] using hcz

end LocalRecords

section ProductOptimum

variable {k : ℕ} {A : Fin k → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

private theorem productRecord_realOverlap_optimum
    (v : (i : Fin k) → Bool → A i → ℂ) (hv : ∀ i b, star (v i b) ⬝ᵥ v i b = 1)
    (s : Fin k → ℝ) (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∀ i, s i ≤ 1)
    (hs : ∀ i, star (v i false) ⬝ᵥ v i true = (s i : ℂ)) :
    pGuess (uniformPrior (Word k)) (coordinateProductRecordState v hv) =
      (∏ i, (1 + Real.sqrt (1 - (s i) ^ 2)) / 2) ∧
    IsGreatest (successProbabilitySet (uniformPrior (Word k)) (coordinateProductRecordState v hv))
      (pGuess (uniformPrior (Word k)) (coordinateProductRecordState v hv)) := by
  choose V hgram hcols hmap using
    fun i => exists_pair_partialIsometry (v i) (hv i) (s i) (hs0 i) (hs1 i) (hs i)
  let T := tensorMatrix V
  have hT : Tᴴ * T = diagonal (fun b => ∏ i, bitSupport (s i) (b i)) :=
    tensorMatrix_gram V (fun i => bitSupport (s i)) hgram
  have hpartial : T * (Tᴴ * T) = T := by
    ext x b
    rw [hT, Matrix.mul_diagonal]
    change (∏ i, V i (x i) (b i)) * (∏ i, bitSupport (s i) (b i)) = _
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => hcols i (x i) (b i)
  have hsupport (j : Word k) : (Tᴴ * T) *ᵥ coordinateRecordVector s j =
      coordinateRecordVector s j := by
    funext x
    rw [hT, Matrix.mulVec_diagonal, coordinateRecordVector_apply, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => bitSupport_mul_bitVector (s i) (j i) (x i)
  have hguess := pGuess_pure_partialIsometry (uniformPrior (Word k))
    (coordinateRecordVector s) (coordinateProductRecord v) (coordinateRecordVector_norm hs0 hs1)
    (coordinateProductRecord_norm v hv) T hpartial hsupport
    (tensorMatrix_mul_recordVector V v s hmap)
  change pGuess (uniformPrior (Word k)) (coordinateProductRecordState v hv) =
    pGuess (uniformPrior (Word k)) (coordinateRecordState s hs0 hs1) at hguess
  refine ⟨hguess.trans (pGuess_coordinateRecord s hs0 hs1), ?_⟩
  have hset := success_set_pure_partialIsometry (uniformPrior (Word k))
    (coordinateRecordVector s) (coordinateProductRecord v) (coordinateRecordVector_norm hs0 hs1)
    (coordinateProductRecord_norm v hv) T hpartial hsupport
    (tensorMatrix_mul_recordVector V v s hmap)
  change successProbabilitySet (uniformPrior (Word k)) (coordinateProductRecordState v hv) =
    successProbabilitySet (uniformPrior (Word k)) (coordinateRecordState s hs0 hs1) at hset
  have hmax := isGreatest_phase (walsh (k := k)) (coordinateWeight s) walsh_norm walsh_orthogonal
    (coordinateWeight_nonneg s) (coordinateWeight_sq_sum hs0 hs1)
  change IsGreatest (successProbabilitySet (uniformPrior (Word k))
    (coordinateRecordState s hs0 hs1)) _ at hmax
  rw [hguess, hset, pGuess, hmax.csSup_eq]
  exact hmax

private theorem exists_real_overlap_records
    (v : (i : Fin k) → Bool → A i → ℂ) (hv : ∀ i b, star (v i b) ⬝ᵥ v i b = 1) :
    ∃ (w : (i : Fin k) → Bool → A i → ℂ) (hw : ∀ i b, star (w i b) ⬝ᵥ w i b = 1),
      (∀ i, star (w i false) ⬝ᵥ w i true = (‖star (v i false) ⬝ᵥ v i true‖ : ℂ)) ∧
      coordinateProductRecordState w hw = coordinateProductRecordState v hv := by
  choose phase hphase hreal using fun i => exists_pair_phase (v i)
  let w : (i : Fin k) → Bool → A i → ℂ := fun i b => phase i b • v i b
  have hw (i : Fin k) (b : Bool) : star (w i b) ⬝ᵥ w i b = 1 := by
    dsimp only [w]
    rw [dot_smul_left, dot_smul_right, hv, mul_one, unit_phase _ (hphase i b)]
  have hstates (j : Word k) : coordinateProductRecordState w hw j =
      coordinateProductRecordState v hv j := by
    let d := ∏ i, phase i (j i)
    have hd : ‖d‖ = 1 := by simp [d, norm_prod, hphase]
    have hp : coordinateProductRecord w j = d • coordinateProductRecord v j := by
      funext x
      simp only [coordinateProductRecord, w, Pi.smul_apply, smul_eq_mul, d,
        Finset.prod_mul_distrib]
    unfold coordinateProductRecordState
    exact (show ∀ (u : ((i : Fin k) → A i) → ℂ) (hu : star u ⬝ᵥ u = 1),
        u = d • coordinateProductRecord v j →
        pureState u hu = pureState (coordinateProductRecord v j)
          (coordinateProductRecord_norm v hv j) from by
        intro u hu he
        subst u
        exact pureState_smul_eq d _ hd _) _ _ hp
  exact ⟨w, hw, hreal, funext hstates⟩

private theorem coordinateProductRecord_optimum
    (v : (i : Fin k) → Bool → A i → ℂ) (hv : ∀ i b, star (v i b) ⬝ᵥ v i b = 1) :
    pGuess (uniformPrior (Word k)) (coordinateProductRecordState v hv) =
      (∏ i, (1 + Real.sqrt (1 - ‖star (v i false) ⬝ᵥ v i true‖ ^ 2)) / 2) ∧
    IsGreatest (successProbabilitySet (uniformPrior (Word k)) (coordinateProductRecordState v hv))
      (pGuess (uniformPrior (Word k)) (coordinateProductRecordState v hv)) := by
  obtain ⟨w, hw, hreal, hstates⟩ := exists_real_overlap_records v hv
  rw [← hstates]
  exact productRecord_realOverlap_optimum w hw _ (fun _ => norm_nonneg _)
    (fun i => unit_overlap_le _ _ (hv i false) (hv i true)) hreal

/-- For strict coordinate overlaps, the canonical Walsh carrier embeds isometrically
into the original product carrier and carries the same conditional density matrices. -/
theorem exists_coordinateRecord_isometry
    (v : (i : Fin k) → Bool → A i → ℂ) (hv : ∀ i b, star (v i b) ⬝ᵥ v i b = 1)
    (hs : ∀ i, ‖star (v i false) ⬝ᵥ v i true‖ < 1) :
    ∃ T : Matrix ((i : Fin k) → A i) (Word k) ℂ, Tᴴ * T = 1 ∧
      ∀ j, CStarMatrix.ofMatrix.symm (coordinateProductRecordState v hv j).1 =
        T * CStarMatrix.ofMatrix.symm (coordinateRecordState
          (fun i => ‖star (v i false) ⬝ᵥ v i true‖)
          (fun _ => norm_nonneg _) (fun i => (hs i).le) j).1 * Tᴴ := by
  obtain ⟨w, hw, hreal, hstates⟩ := exists_real_overlap_records v hv
  let s : Fin k → ℝ := fun i => ‖star (v i false) ⬝ᵥ v i true‖
  choose V hgram hmap using
    fun i => exists_pair_isometry (w i) (hw i) (s i) (norm_nonneg _) (hs i) (hreal i)
  refine ⟨tensorMatrix V, ?_, ?_⟩
  · simpa using tensorMatrix_gram V (fun _ _ => 1) (fun i => by simpa using hgram i)
  · intro j
    rw [← hstates]
    change rankOneDensity (coordinateProductRecord w j) =
      tensorMatrix V * rankOneDensity (coordinateRecordVector s j) * (tensorMatrix V)ᴴ
    simp only [rankOneDensity, mul_vecMulVec, vecMulVec_mul, ← star_mulVec,
      tensorMatrix_mul_recordVector V w s hmap]

/-- Remove the zero Walsh coordinates of repeated pure pairs while keeping every label.
The remaining Walsh carrier embeds isometrically into the original tensor product. -/
theorem exists_activeRecord_isometry
    (v : (i : Fin k) → Bool → A i → ℂ) (hv : ∀ i b, star (v i b) ⬝ᵥ v i b = 1)
    (s : Fin k → ℝ) (hs : ∀ i, s i = ‖star (v i false) ⬝ᵥ v i true‖)
    (p : Fin k → Prop) [DecidablePred p] (hp : ∀ i, p i ↔ s i < 1) :
    let a := Fintype.card {i // p i}
    ∃ (reindex : {i // p i} ≃ Fin a)
      (T : Matrix ((i : Fin k) → A i) (Word a) ℂ), Tᴴ * T = 1 ∧
      ∀ j : Word k, CStarMatrix.ofMatrix.symm (coordinateProductRecordState v hv j).1 =
        T * rankOneDensity (coordinateRecordVector (fun i => s (reindex.symm i))
          (fun i => j (reindex.symm i))) * Tᴴ := by
  let e := Fintype.equivFin {i // p i}
  let r := fun i => s (e.symm i)
  have hs0 (i : Fin k) : 0 ≤ s i := (hs i).symm ▸ norm_nonneg _
  have hs1 (i : Fin k) : s i ≤ 1 :=
    (hs i).symm ▸ unit_overlap_le _ _ (hv i false) (hv i true)
  have hrepeated (i : Fin k) (hi : ¬ p i) : s i = 1 :=
    le_antisymm (hs1 i) (le_of_not_gt (fun h => hi ((hp i).mpr h)))
  obtain ⟨w, hw, hreal, hstates⟩ := exists_real_overlap_records v hv
  choose V hgram _ hmap using fun i => exists_pair_partialIsometry
    (w i) (hw i) (s i) (hs0 i) (hs1 i) (by rw [hreal, hs])
  let U := tensorMatrix V
  let extend : Word (Fintype.card {i // p i}) ↪ Word k :=
    ⟨fun a i => if hi : p i then a (e ⟨i, hi⟩) else false, by
      intro a b h
      funext i
      have hi := congrFun h (e.symm i).val
      simpa [(e.symm i).property] using hi⟩
  have hon (a : Word (Fintype.card {i // p i})) (i : Fin k) (hi : p i) :
      extend a i = a (e ⟨i, hi⟩) := dite_eq_left hi
  have hoff (a : Word (Fintype.card {i // p i})) (i : Fin k) (hi : ¬ p i) :
      extend a i = false := dite_eq_right hi
  let T := U.submatrix id extend
  refine ⟨e, T, ?_, ?_⟩
  · have hU := tensorMatrix_gram V (fun i => bitSupport (s i)) hgram
    change Uᴴ * U = _ at hU
    dsimp only [T]
    rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ id _ Function.bijective_id, hU]
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.diagonal_apply, Matrix.one_apply,
      extend.injective.eq_iff]
    split_ifs with hab
    · subst b
      apply Finset.prod_eq_one
      intro i _
      by_cases hi : p i
      · simp [bitSupport, ne_of_lt ((hp i).mp hi)]
      · simp [hoff _ _ hi, bitSupport]
    · rfl
  · intro j
    have hrestrict (a : Word (Fintype.card {i // p i})) :
        coordinateRecordVector s j (extend a) =
          coordinateRecordVector r (fun i => j (e.symm i)) a := by
      rw [coordinateRecordVector_apply, coordinateRecordVector_apply,
        ← Fintype.prod_subtype_mul_prod_subtype p (fun i => bitVector (s i) (j i) (extend a i))]
      have hones : (∏ i : {i // ¬ p i}, bitVector (s i) (j i) (extend a i)) = 1 := by
        apply Finset.prod_eq_one
        intro i _
        rw [hoff _ _ i.property, hrepeated _ i.property]
        cases j i <;> norm_num [bitVector, bitPhase, bitWeight]
      rw [hones, mul_one]
      apply Fintype.prod_equiv e
      intro i
      simp [hon _ _ i.property, r]
    have hzero (b : Word k) (hb : b ∉ (Finset.univ : Finset (Word _)).map extend) :
        coordinateRecordVector s j b = 0 := by
      have hbad : ∃ i, ¬ p i ∧ b i = true := by
        by_contra! h
        apply hb
        refine Finset.mem_map.mpr ⟨fun i => b (e.symm i), Finset.mem_univ _, ?_⟩
        funext i
        by_cases hi : p i
        · simp [hon _ _ hi]
        · rw [hoff _ _ hi]
          cases hbi : b i
          · rfl
          · exact (h i hi hbi).elim
      obtain ⟨i, hi, hbi⟩ := hbad
      rw [coordinateRecordVector_apply]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [hrepeated i hi, hbi]
      simp [bitVector, bitWeight]
    have hvec : T *ᵥ coordinateRecordVector r (fun i => j (e.symm i)) =
        coordinateProductRecord w j := by
      rw [← tensorMatrix_mul_recordVector V w s hmap]
      funext x
      change (∑ a, U x (extend a) * coordinateRecordVector r (fun i => j (e.symm i)) a) =
        ∑ b, U x b * coordinateRecordVector s j b
      simp_rw [← hrestrict]
      calc
        _ = ∑ b ∈ Finset.univ.map extend, U x b * coordinateRecordVector s j b :=
          (Finset.sum_map Finset.univ extend (fun b => U x b * coordinateRecordVector s j b)).symm
        _ = _ := Finset.sum_subset (Finset.subset_univ _)
          (fun b _ hb => by rw [hzero b hb, mul_zero])
    rw [← hstates]
    change rankOneDensity (coordinateProductRecord w j) =
      T * rankOneDensity (coordinateRecordVector r (fun i => j (e.symm i))) * Tᴴ
    simp only [rankOneDensity, mul_vecMulVec, vecMulVec_mul, ← star_mulVec, hvec]

/-- The exact success probability of an optimal joint POVM for a uniform binary word.
The normalized local pairs may have different carriers and complex overlaps of any modulus
in the closed unit interval. For zero coordinates the empty product is one. -/
theorem pGuess_coordinateProductRecord
    (v : (i : Fin k) → Bool → A i → ℂ) (hv : ∀ i b, star (v i b) ⬝ᵥ v i b = 1) :
    pGuess (uniformPrior (Word k)) (coordinateProductRecordState v hv) =
      ∏ i, (1 + Real.sqrt (1 - ‖star (v i false) ⬝ᵥ v i true‖ ^ 2)) / 2 :=
  (coordinateProductRecord_optimum v hv).1

end ProductOptimum

section EqualRecords

variable {A : Type*} [Fintype A]

/-- The whole record for equal local pairs. -/
def productRecord (v : Bool → A → ℂ) {k : ℕ} (j : Word k) (x : Fin k → A) : ℂ :=
  coordinateProductRecord (fun _ => v) j x

theorem productRecord_norm (v : Bool → A → ℂ) (hv : ∀ b, star (v b) ⬝ᵥ v b = 1)
    {k : ℕ} (j : Word k) :
    star (productRecord v j) ⬝ᵥ productRecord v j = 1 :=
  coordinateProductRecord_norm (fun _ => v) (fun _ => hv) j

variable [DecidableEq A]

/-- The joint states for repeated copies of the same local pair. -/
def productRecordState (v : Bool → A → ℂ) (hv : ∀ b, star (v b) ⬝ᵥ v b = 1)
    {k : ℕ} (j : Word k) : DensityState (Fin k → A) :=
  coordinateProductRecordState (fun _ => v) (fun _ => hv) j

/-- The finite law when the two unit amplitudes already have real nonnegative overlap. -/
theorem pGuess_productRecord_realOverlap (v : Bool → A → ℂ)
    (hv : ∀ b, star (v b) ⬝ᵥ v b = 1) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hs : star (v false) ⬝ᵥ v true = (s : ℂ)) (k : ℕ) :
    pGuess (uniformPrior (Word k)) (productRecordState v hv) =
      ((1 + Real.sqrt (1 - s ^ 2)) / 2) ^ k := by
  change pGuess (uniformPrior (Word k))
    (coordinateProductRecordState (fun _ => v) (fun _ => hv)) = _
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (productRecord_realOverlap_optimum (k := k) (fun _ => v) (fun _ => hv) (fun _ => s)
      (fun _ => hs0) (fun _ => hs1) (fun _ => hs)).1

/-- Exact success over all joint POVMs for repeated copies of two arbitrary unit amplitudes. -/
theorem pGuess_productRecord (v : Bool → A → ℂ)
    (hv : ∀ b, star (v b) ⬝ᵥ v b = 1) (k : ℕ) :
    pGuess (uniformPrior (Word k)) (productRecordState v hv) =
      ((1 + Real.sqrt (1 - ‖star (v false) ⬝ᵥ v true‖ ^ 2)) / 2) ^ k := by
  change pGuess (uniformPrior (Word k))
    (coordinateProductRecordState (fun _ => v) (fun _ => hv)) = _
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    pGuess_coordinateProductRecord (k := k) (fun _ => v) (fun _ => hv)

/-- Some joint POVM on the original product carrier attains the optimum, and every joint
POVM on that carrier has success at most the optimum. -/
theorem isGreatest_pGuess_productRecord (v : Bool → A → ℂ)
    (hv : ∀ b, star (v b) ⬝ᵥ v b = 1) (k : ℕ) :
    IsGreatest (successProbabilitySet (uniformPrior (Word k)) (productRecordState v hv))
      (pGuess (uniformPrior (Word k)) (productRecordState v hv)) :=
  (coordinateProductRecord_optimum (k := k) (fun _ => v) (fun _ => hv)).2

end EqualRecords

end

end JointRecordDecoding
