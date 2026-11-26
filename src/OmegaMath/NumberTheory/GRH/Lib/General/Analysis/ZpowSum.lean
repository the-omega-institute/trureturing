import OmegaMath.NumberTheory.GRH.Lib.General.LinearAlgebra.Base
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas (textbook or folklore) of algebraic number theory, commutative algebra and
analysis.

This file: General facts on differents, root discriminants; ramified ideals divide the different.
One-dimensional Sobolev trace inequality, iterated at a cube corner for families. -/

open Ideal Set ENNReal Fintype Function MeasureTheory Module NumberField MeasureTheory.Measure

open scoped _root_.Algebra Polynomial

variable (K) {L} [Field K] [Field L] [NumberField K] [NumberField L] [IsTotallyComplex K] {x : 𝓞 L}

lemma differentIdeal_eq_span_of_dvd K {A} [Field K] [NumberField K] [Algebra K L] [CommRing A]
  [IsDedekindDomain A]
  [Algebra A K] [IsFractionRing A K] [Algebra A (𝓞 L)] [IsTorsionFree A (𝓞 L)] [Module.Finite A (𝓞
  L)] [CharZero A] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A (𝓞 L) L] {x y : 𝓞 L} (hx :
  K[x.val] = ⊤) (f : A[X]) (hf : Polynomial.aeval x f = 0) (e : Polynomial.aeval x f.derivative =
  y) (h : span {y} ∣ differentIdeal A _) : differentIdeal A _ = span {y} ∧ A[x] = ⊤ := by
  obtain ⟨⟨⟩, C⟩ := minpoly.isIntegrallyClosed_dvd (.of_finite ..) hf,
    (conductor_mul_differentIdeal A K L x hx).dvd
  have t H := ((C.trans H).trans h).antisymm
  rw [h.antisymm] <;>
    simp_all [← conductor_eq_top_iff_adjoin_eq_top, differentIdeal_ne_bot, ← e, mul_mem_right]

/-- If x generates the different of the ring of integers of a number field L over ℤ, then x ≠ 0. -/
lemma ne_zero_of_differentIdeal_eq_span : differentIdeal ℤ _ = span {x} →
  x ≠ 0 := by aesop (add simp differentIdeal_ne_bot)

/-- The number of infinite places of the number field K. -/
noncomputable abbrev numInfPlaces := card (InfinitePlace K)

/-- The degree over ℚ of a totally complex number field is twice its number of infinite places. -/
lemma finrank_eq_two_mul_card_infinitePlace :
  finrank ℚ K = 2 * numInfPlaces K := by simp +arith [← InfinitePlace.sum_mult_eq]

omit [IsTotallyComplex K] in
lemma rootDiscr_pos : 0 < rootDiscr K := Real.rpow_pos_of_pos (by simp [discr_ne_zero]) _

lemma abs_discr_eq_rootDiscr_pow : (|discr K| : ℝ) = (rootDiscr K ^ numInfPlaces K) ^ 2 := by
  simp [← pow_mul', finrank_eq_two_mul_card_infinitePlace, rootDiscr,
    Real.rpow_inv_natCast_pow, -Nat.cast_mul]

/-- An ideal P of the integers of a number field L whose square contains a rational prime
divides the different of L over ℚ. -/
lemma dvd_differentIdeal_of_mem_sq {P : Ideal (𝓞 L)} {p} [Fact (Nat.Prime p)] (h : ↑p ∈ P ^ 2) :
  P ∣ differentIdeal
  ℤ _ := by simpa [NeZero.ne, h] using pow_sub_one_dvd_differentIdeal ℤ (p := span {↑p}) P 2

/-- One-dimensional Sobolev trace inequality: for g differentiable at every point of [0, ε], 0 <
ε ≤ 1, with values in a real inner product space, ‖g(0)‖² ≤ (2/ε) ∫₀^ε (‖g‖² + ‖g'‖²). -/
lemma sobolev_trace {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {g : ℝ → E} {b : ℝ → _} {ε}
    (hε : 0 < ε) (hε' : ε ≤ 1) (h : ∀ t ∈ Icc 0 ε, ∃ c, HasDerivAt g c t ∧ ‖c‖ ≤ b t) :
    ‖g 0‖ₑ ^ 2 ≤ ∫⁻ t in Icc 0 ε, .ofReal (2 / ε * (‖g t‖ ^ 2 + b t ^ 2)) := by
  choose! g' h k using h; let := HasDerivAt.continuousOn h
  grw [← setLIntegral_mono', ← addHaar_image_le_lintegral_abs_det_fderiv _ _ (h · · |>.norm_sq.mul
    ((hasDerivAt_id _).sub_const ε) |>.hasDerivWithinAt.mul_const ε⁻¹), ← intermediate_value_Icc
    hε.le (by fun_prop)] <;> simp [↓ofReal_le_ofReal_iff', ne_of_gt, abs_of_pos, field, *]
  grw [← k, abs_add_le, (abs_mul ..).le, mul_le_of_le_one_right, ← add_sq_le] <;>
    grind [abs_sq, abs_real_inner_le_norm]

/-- Let measurable f_i(x, ω), i words in L, have ‖∂_d f_i‖ ≤ Λ∑_l ‖f_{li}‖ on the cube [0, ε]^D,
0 < ε ≤ 1, for almost all ω. If ∬‖f_i‖² ≤ K on the cube for |i| ≤ |D|, then ∫‖f_∅(0, ω)‖² ≤
(2(1+(|L|Λ)²)/ε)^{|D|}K. -/
lemma sobolev_chain {Ω I L D} [MeasurableSpace Ω] {σ : Measure Ω} [SFinite σ] [Fintype L] [Fintype
    I] [Fintype D] (f : _ → (D → ℝ) → Ω → EuclideanSpace ℂ I) (hm : ∀ i, Measurable ↿(f i)) {ε Λ K}
    (hε : 0 < ε) (hε' : ε ≤ 1) (hd : ∀ᵐ ω ∂σ, ∀ i d x t, update x d t ∈ Icc 0 (fun _ ↦ ε) → ∃ c,
    HasDerivAt (update x d · |> f i <| ω) c t ∧ ‖c‖ ≤ ∑ l : L, Λ * ‖f (l :: i) (update x d t) ω‖) :
    (∀ i, i.length ≤ card D → ∫⁻ x in Icc 0 fun _ ↦ ε, ∫⁻ ω, ‖f i x ω‖ₑ ^ 2 ∂σ ≤ K) → ∫⁻ ω, ‖f [] 0
    ω‖ₑ ^ 2 ∂σ ≤ .ofReal ((2 / ε * (1 + (card L * Λ) ^ 2)) ^ card D) * K := by
  simp_rw [volume_pi, ← pi_univ_Icc, restrict_pi_pi, lintegral_eq_lmarginal_univ 0, card]
  refine' Finset.univ.induction (by simp) (fun d s e ih K h ↦ (ih (id ..) fun i _ ↦ _).trans_eq _) K
  grw [lmarginal, ← restrict_pi_pi, setLIntegral_mono' _ fun y _ ↦ (lintegral_mono_ae (hd.mono
    fun ω hd ↦ (sobolev_trace hε hε' (hd i d (updateFinset 0 _ y) · ∘ by
    simp_all [Pi.le_def, updateFinset_def]; grind)).trans_eq' (by congr; simp [e, updateFinset]))
    ).trans_eq (lintegral_lintegral_swap (by fun_prop)), restrict_pi_pi, sq_sum_le_card_mul_sum_sq]
  any_goals simp (disch := intros; with_unfolding_all first | positivity | fun_prop) [lmarginal,
    mul_pow, ↓lmarginal_insert' _ _ e, lintegral_finsetSum, ofReal_add, ofReal_sum_of_nonneg] at h ⊢
  grw [h, h] <;> grind; simp [*]; ring

/-- Weak Nullstellensatz: a proper ideal J of a finitely generated algebra A over an
algebraically closed field k lies in the kernel of some k-algebra homomorphism A → k. -/
lemma nullstellensatz_exists_le_ker {k A} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
    [f : Algebra.FiniteType k A] {J} (n : J ≠ ⊤)
    : ∃ o : A →ₐ[k] k, J ≤ RingHom.ker o := have ⟨m, _, j⟩ := J.exists_le_maximal n
  have := @finite_of_finite_type_of_isJacobsonRing k _ _ (Quotient.field m) _ _ _
  ⟨IsAlgClosed.lift.comp (Quotient.mkₐ k m), (by simp [Quotient.eq_zero_iff_mem.2, @j · ·])⟩

lemma zpow_sum_of_ne_zero {ι K} [Field K] {s : K} (hs : s ≠ 0) t (f : ι → ℤ) :
    s ^ ∑ i ∈ t, f i = t.prod (s ^ f ·) := t.induction (by simp) (by simp_all [zpow_add₀])
