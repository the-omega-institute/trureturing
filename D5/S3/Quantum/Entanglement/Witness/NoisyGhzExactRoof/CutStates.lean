/- GID: D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Actual noisy-GHZ CutStates in the original finite-ensemble semantics. -/


import D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.Foundations
import D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.TwoMeanBound
import D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.ObservableOptimum


open scoped BigOperators ComplexOrder MatrixOrder
open _root_.Matrix
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Quantum.Entanglement.OccupancyWordSectors (Word)
open D5.S3.Quantum.Information.MultiEntropyPositivityRefutation (IsUnitState)
open D5.S3.Quantum.Recovery.ProductPrefixRigidity (readout)
open D5.S3.Quantum.Entanglement.Witness.NoisyGhzWitnessBoundGap

namespace D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof

noncomputable section

lemma sum_on_embedding {ι κ α : Type*} [Fintype ι] [Fintype κ]
    [AddCommMonoid α] (e : ι ↪ κ) (f : κ → α)
    (hf : ∀ x, (¬ ∃ i, e i = x) → f x = 0) : ∑ x, f x = ∑ i, f (e i) := by
  classical
  have hs : (∑ x ∈ Finset.univ.image e, f x) = ∑ x, f x := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    apply hf x
    intro h
    exact hx (Finset.mem_image.mpr (by obtain ⟨i, hi⟩ := h; exact ⟨i, Finset.mem_univ _, hi⟩))
  rw [← hs]
  exact Finset.sum_image (fun i _ j _ h => e.injective h)

def pushVector {ι κ : Type*} [Fintype ι] (e : ι ↪ κ) (c : ι → ℂ) : κ → ℂ := by
  classical
  exact fun x => ∑ i, if e i = x then c i else 0

lemma pushVector_apply {ι κ : Type*} [Fintype ι] (e : ι ↪ κ) (c : ι → ℂ) (i : ι) :
    pushVector e c (e i) = c i := by
  classical
  simp [pushVector, e.injective.eq_iff]

lemma pushVector_off {ι κ : Type*} [Fintype ι] (e : ι ↪ κ) (c : ι → ℂ) (x : κ)
    (hx : ¬ ∃ i, e i = x) : pushVector e c x = 0 := by
  classical
  unfold pushVector
  apply Finset.sum_eq_zero
  intro i hi
  exact if_neg (not_exists.mp hx i)

private lemma pushVector_norm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ↪ κ) (c : ι → ℂ) :
    ∑ x, Complex.normSq (pushVector e c x) = ∑ i, Complex.normSq (c i) := by
  rw [sum_on_embedding e _ (by intro x hx; rw [pushVector_off e c x hx]; simp)]
  simp only [pushVector_apply]

private lemma pushVector_inner {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ↪ κ) (c v : ι → ℂ) :
    star (pushVector e c) ⬝ᵥ pushVector e v = star c ⬝ᵥ v := by
  unfold dotProduct
  simp only [Pi.star_apply]
  rw [sum_on_embedding e _ (by intro x hx; rw [pushVector_off e c x hx]; simp)]
  simp only [Pi.star_apply, pushVector_apply]

/-- The actual embedding of the d×d cut sector into computational words. -/
def cutEmbedding {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty) (hc : aᶜ.Nonempty) :
    (Fin d × Fin d) ↪ Word (Fin d) n := ⟨_, join_injective a ha hc⟩

/-- The source product vector u on A and conjugate(u) on the complementary cut. -/
def cutProduct {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty) (hc : aᶜ.Nonempty)
    (u : Fin d → ℂ) : Word (Fin d) n → ℂ :=
  pushVector (cutEmbedding a ha hc) (fun ij => u ij.1 * star (u ij.2))

private lemma cutProduct_unit {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty) (hc : aᶜ.Nonempty)
    (u : Fin d → ℂ) (hu : ∑ i, Complex.normSq (u i) = 1) : IsUnitState (cutProduct a ha hc u) := by
  classical
  unfold IsUnitState cutProduct
  rw [pushVector_norm]
  simp only [Fintype.sum_prod_type, Complex.normSq_mul, Complex.star_def, Complex.normSq_conj,
    ← Finset.mul_sum, hu, mul_one]

private lemma cutEmbedding_eq {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty) (hc : aᶜ.Nonempty)
    (i j : Fin d) (x : Word (Fin d) n) :
    cutEmbedding a ha hc (i,j) = x ↔
      (∀ k : a, x k = i) ∧ (∀ k : ↥aᶜ, x k = j) := by
  classical
  constructor
  · intro h
    constructor
    · intro k
      simpa [cutEmbedding, k.property] using (congrFun h k).symm
    · intro k
      simpa [cutEmbedding, Finset.mem_compl.mp k.property] using (congrFun h k).symm
  · rintro ⟨hA, hB⟩
    funext k
    by_cases hk : k ∈ a
    · simpa [cutEmbedding, hk] using (hA ⟨k,hk⟩).symm
    · simpa [cutEmbedding, hk] using (hB ⟨k,Finset.mem_compl.mpr hk⟩).symm

/-- The cut product is genuinely biseparable in the original factorization
predicate, not a fully-separable replacement. -/
theorem cutProduct_biseparable {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty) (hc : aᶜ.Nonempty)
    (u : Fin d → ℂ) (hu : ∑ i, Complex.normSq (u i) = 1) : IsBiseparable (cutProduct a ha hc u) := by
  classical
  refine ⟨cutProduct_unit a ha hc u hu, a, ha, hc,
    fun x => ∑ i, if ∀ k, x k = i then u i else 0,
    fun x => ∑ j, if ∀ k, x k = j then star (u j) else 0, ?_⟩
  intro x
  simp only [cutProduct, pushVector, Fintype.sum_prod_type]
  change (∑ i, ∑ j, if cutEmbedding a ha hc (i,j) = x then u i * star (u j) else 0) = _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [cutEmbedding_eq]
  by_cases hA : ∀ k : a, x k = i <;> by_cases hB : ∀ k : ↥aᶜ, x k = j <;>
    simp only [hA, hB, and_self, and_false, false_and, ite_true, ite_false, mul_zero, zero_mul, forall_const, true_and]
  all_goals simp

private lemma pairCharacter_apply {d : ℕ} (i j : Fin d) (θ : Fin d → ZMod 3) :
    phaseCharacter (pairCoefficient i j) θ = ZMod.stdAddChar (θ i - θ j) := by
  unfold phaseCharacter pairCoefficient
  congr 1
  simp [sub_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq]

/-- The finite source phase vectors, on all independent cubic phases. -/
def phaseVector {d : ℕ} (θ : Fin d → ZMod 3) : Fin d → ℂ :=
  fun j => (Real.sqrt d : ℂ)⁻¹ * ZMod.stdAddChar (θ j)

lemma phaseVector_unit {d : ℕ} (hd : 0 < d) (θ : Fin d → ZMod 3) :
    ∑ j, Complex.normSq (phaseVector θ j) = 1 := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp [phaseVector, Complex.normSq_mul, ZMod.stdAddChar_apply,
    Complex.normSq_ofReal, Real.sq_sqrt (Nat.cast_nonneg d), hdR]

lemma phaseVector_pair {d : ℕ} (hd : 0 < d) (θ : Fin d → ZMod 3) (i j : Fin d) :
    phaseVector θ i * star (phaseVector θ j) =
      (1 / (d : ℂ)) * phaseCharacter (pairCoefficient i j) θ := by
  rw [pairCharacter_apply, AddChar.map_sub_eq_div]
  have hs (a : ZMod 3) : star (ZMod.stdAddChar a) = (ZMod.stdAddChar a)⁻¹ := by
    simpa only [starRingEnd_apply, AddChar.inv_apply'] using
      (AddChar.starComp_apply (R := ZMod 3) (by rw [ZMod.ringChar_zmod_n]; norm_num)
        (φ := ZMod.stdAddChar) a)
  have hroot : (Real.sqrt d : ℂ)^2 = (d : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg d)
  have hroot0 : (Real.sqrt d : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < d by exact_mod_cast hd)).ne'
  unfold phaseVector
  rw [star_mul, hs]
  have hr : star ((Real.sqrt d : ℂ)⁻¹) = (Real.sqrt d : ℂ)⁻¹ := by simp
  rw [hr]
  calc
    _ = ((Real.sqrt d : ℂ)^2)⁻¹ *
        (ZMod.stdAddChar (θ i) / ZMod.stdAddChar (θ j)) := by
      rw [pow_two, mul_inv]
      ring
    _ = _ := by rw [hroot]; simp

/-- The source finite constituent in one cut sector. -/
def cutState {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty) (hc : aᶜ.Nonempty)
    (α β : ℝ) (u : Fin d → ℂ) : Word (Fin d) n → ℂ := by
  classical
  exact pushVector (cutEmbedding a ha hc)
    (fun ij => (if ij.1 = ij.2 then (β : ℂ) else 0) +
      ((α - β : ℝ) : ℂ) * u ij.1 * star (u ij.2))

private lemma cut_coefficient_norm {d : ℕ} (β τ : ℝ) (u : Fin d → ℂ)
    (hu : ∑ i, Complex.normSq (u i) = 1) :
    (∑ ij : Fin d × Fin d, Complex.normSq
      ((if ij.1 = ij.2 then (β : ℂ) else 0) + (τ : ℂ) * u ij.1 * star (u ij.2))) =
      (d : ℝ) * β^2 + 2 * β * τ + τ^2 := by
  classical
  have hd : (∑ ij : Fin d × Fin d, Complex.normSq
      (if ij.1 = ij.2 then (β : ℂ) else 0)) = (d : ℝ) * β^2 := by
    simp [Fintype.sum_prod_type, apply_ite Complex.normSq, Complex.normSq_ofReal, pow_two]
  have hr : (∑ ij : Fin d × Fin d, Complex.normSq
      ((τ : ℂ) * u ij.1 * star (u ij.2))) = τ^2 := by
    simp only [Fintype.sum_prod_type, Complex.normSq_mul, Complex.normSq_ofReal,
      Complex.star_def, Complex.normSq_conj, mul_assoc, ← Finset.mul_sum, hu, mul_one]
    ring
  have hcross (i j : Fin d) :
      ((if i = j then (β : ℂ) else 0) *
        star ((τ : ℂ) * u i * star (u j))).re =
          if i = j then β * τ * Complex.normSq (u i) else 0 := by
    by_cases hij : i = j
    · subst j
      have he : (τ : ℂ) * u i * star (u i) = ((τ * Complex.normSq (u i) : ℝ) : ℂ) := by
        rw [mul_assoc, Complex.star_def, Complex.mul_conj]
        push_cast
        rfl
      simp only [ite_true]
      rw [he]
      simp
      <;> ring
    · simp [hij]
  have hx : (∑ ij : Fin d × Fin d, 2 *
      ((if ij.1 = ij.2 then (β : ℂ) else 0) *
        star ((τ : ℂ) * u ij.1 * star (u ij.2))).re) = 2 * β * τ := by
    simp only [Fintype.sum_prod_type, hcross]
    simp [Finset.mul_sum, ← Finset.mul_sum, hu, mul_assoc]
  simp_rw [Complex.normSq_add, ← Complex.star_def]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hd, hr, hx]
  ring

/-- Normalization of each source cut constituent, independent of the cut
and of the chosen unit vector u. -/
theorem cutState_unit {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty) (hc : aᶜ.Nonempty)
    (α β : ℝ) (u : Fin d → ℂ) (hu : ∑ i, Complex.normSq (u i) = 1)
    (hαβ : α^2 + (d - 1 : ℝ) * β^2 = 1) : IsUnitState (cutState a ha hc α β u) := by
  unfold IsUnitState cutState
  rw [pushVector_norm, cut_coefficient_norm β (α - β) u hu]
  nlinarith

private lemma cutState_supported {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty) (hc : aᶜ.Nonempty)
    (α β : ℝ) (u : Fin d → ℂ) :
    supportProjector n d *ᵥ cutState a ha hc α β u = cutState a ha hc α β u := by
  classical
  ext x
  simp only [supportProjector, mulVec_diagonal]
  by_cases hx : (Finset.univ.image x).card ≤ 2
  · simp [hx]
  · have hz : cutState a ha hc α β u x = 0 := by
      apply pushVector_off
      rintro ⟨ij, hij⟩
      apply hx
      rw [← hij]
      exact join_support a ij.1 ij.2
    simp [hx, hz]

private lemma cutState_constant {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty) (hc : aᶜ.Nonempty)
    (α β : ℝ) (u : Fin d → ℂ) (j : Fin d) :
    cutState a ha hc α β u (fun _ => j) =
      (β : ℂ) + ((α - β : ℝ) : ℂ) * ((Complex.normSq (u j) : ℝ) : ℂ) := by
  have he : cutEmbedding a ha hc (j,j) = (fun _ => j) := by
    ext k
    simp [cutEmbedding, Finset.piecewise]
  rw [← he, cutState, pushVector_apply]
  simp only [ite_true, mul_assoc, Complex.star_def, Complex.mul_conj]

private lemma cutProduct_overlap {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty) (hc : aᶜ.Nonempty)
    (α β : ℝ) (u : Fin d → ℂ) (hu : ∑ i, Complex.normSq (u i) = 1) :
    star (cutProduct a ha hc u) ⬝ᵥ cutState a ha hc α β u = (α : ℂ) := by
  classical
  have hsum : (∑ i, (Complex.normSq (u i) : ℂ)) = 1 := by
    rw [← Complex.ofReal_sum, hu, Complex.ofReal_one]
  have hterm (i j : Fin d) :
      star (u i * star (u j)) *
        ((if i = j then (β : ℂ) else 0) + ((α - β : ℝ) : ℂ) * u i * star (u j)) =
      (if i = j then (β : ℂ) * Complex.normSq (u i) else 0) +
        ((α - β : ℝ) : ℂ) * Complex.normSq (u i) * Complex.normSq (u j) := by
    rw [star_mul, star_star, mul_add]
    congr 1
    · by_cases hij : i = j
      · subst j
        simp only [ite_true]
        rw [show u i * star (u i) = (Complex.normSq (u i) : ℂ) by
          rw [Complex.star_def, Complex.mul_conj]]
        ring
      · simp [hij]
    · have hi : star (u i) * u i = (Complex.normSq (u i) : ℂ) := by
        rw [mul_comm, Complex.star_def, Complex.mul_conj]
      have hj : u j * star (u j) = (Complex.normSq (u j) : ℂ) := by
        rw [Complex.star_def, Complex.mul_conj]
      calc
        _ = ((α - β : ℝ) : ℂ) * (star (u i) * u i) * (u j * star (u j)) := by ring
        _ = _ := by rw [hi, hj]
  unfold cutProduct cutState
  rw [pushVector_inner]
  simp only [dotProduct, Pi.star_apply, Fintype.sum_prod_type, hterm,
    Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ← Finset.mul_sum, hsum, mul_one]
  push_cast
  ring

private lemma cutState_means {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (a : Finset (Fin n)) (ha : a.Nonempty) (hc : aᶜ.Nonempty)
    (α β : ℝ) (u : Fin d → ℂ) (hu : ∑ i, Complex.normSq (u i) = 1)
    (hαβ : α^2 + (d - 1 : ℝ) * β^2 = 1) :
    readout (supportProjector n d) (cutState a ha hc α β u) = 1 ∧
      readout (rankOneDensity (ghz n d)) (cutState a ha hc α β u) =
        (α + (d - 1 : ℝ) * β)^2 / d := by
  have hunit := cutState_unit a ha hc α β u hu hαβ
  constructor
  · change (star _ ⬝ᵥ (supportProjector n d *ᵥ _)).re = 1
    rw [cutState_supported]
    have he := expectation_one (cutState a ha hc α β u)
    simp only [readout, one_mulVec] at he
    exact he.trans hunit
  · have hsum : (∑ i, (Complex.normSq (u i) : ℂ)) = 1 := by
      rw [← Complex.ofReal_sum, hu, Complex.ofReal_one]
    have h : (∑ j, cutState a ha hc α β u (fun _ => j)) =
        ((α + (d - 1 : ℝ) * β : ℝ) : ℂ) := by
      simp only [cutState_constant, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hsum, mul_one]
      push_cast
      ring
    apply (eq_div_iff (show (d : ℝ) ≠ 0 by exact_mod_cast hd.ne')).mpr
    rw [mul_comm, ghz_expectation hn hd, h, Complex.normSq_ofReal]
    ring

/-- Every unit-vector cut constituent has the genuine all-cut pure measure
specified by the source, including both endpoint values of F. -/
theorem cutState_attainment {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    (a : Finset (Fin n)) (ha : a.Nonempty) (hc : aᶜ.Nonempty)
    (u : Fin d → ℂ) (hu : ∑ i, Complex.normSq (u i) = 1)
    {F : ℝ} (hF : 1 / (d : ℝ) ≤ F) (hF1 : F ≤ 1) :
    IsUnitState (cutState a ha hc (optimalAlpha d F) (optimalBeta d F) u) ∧
      readout (supportProjector n d) (cutState a ha hc (optimalAlpha d F) (optimalBeta d F) u) = 1 ∧
      readout (rankOneDensity (ghz n d)) (cutState a ha hc (optimalAlpha d F) (optimalBeta d F) u) = F ∧
      geometricMeasurePure (cutState a ha hc (optimalAlpha d F) (optimalBeta d F) u) =
        twoMeanOptimum d F 1 := by
  classical
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hb, hba, hnorm, hmean, hvalue⟩ := optimal_amplitudes (by omega : 2 ≤ d) hF hF1
  let ψ := cutState a ha hc (optimalAlpha d F) (optimalBeta d F) u
  have hψ : IsUnitState ψ := cutState_unit a ha hc _ _ u hu hnorm
  obtain ⟨hy,hf⟩ := cutState_means (by omega : 0 < n) (by omega : 0 < d) a ha hc _ _ u hu hnorm
  rw [hmean] at hf
  have hβ : twoMeanOptimum d F 1 = 1 - (optimalAlpha d F)^2 := by
    unfold twoMeanOptimum
    split_ifs with h
    · have hF' : 1 ≤ (d : ℝ) * F := by
        simpa only [mul_comm] using (div_le_iff₀ (by positivity : (0 : ℝ) < d)).mp hF
      have hFeq : F = 1 / (d : ℝ) := by
        apply (eq_div_iff (by positivity : (d : ℝ) ≠ 0)).mpr
        nlinarith
      have hh : twoMeanValue d F 1 = 0 := by
        unfold twoMeanValue
        have he : (d - 1 : ℝ) * F * (1 - F) = ((d - 1 : ℝ) / d)^2 := by
          rw [hFeq]
          field_simp
          <;> ring
        rw [he, Real.sqrt_sq (div_nonneg (by linarith) (by positivity))]
        rw [hFeq]
        field_simp
        <;> ring
      linarith
    · exact hvalue
  have hl := pure_two_mean_lower hn hd ψ hψ
  change twoMeanOptimum d _ _ ≤ _ at hl
  rw [hf, hy] at hl
  have hupp : geometricMeasurePure ψ ≤ 1 - (optimalAlpha d F)^2 := by
    have hs := le_csSup (overlap_values_bdd ψ hψ)
      (show Complex.normSq (star (cutProduct a ha hc u) ⬝ᵥ ψ) ∈
        {t : ℝ | ∃ φ, IsBiseparable φ ∧ t = Complex.normSq (star φ ⬝ᵥ ψ)} from
        ⟨_, cutProduct_biseparable a ha hc u hu, rfl⟩)
    change Complex.normSq (star (cutProduct a ha hc u) ⬝ᵥ cutState a ha hc _ _ u) ≤ _ at hs
    rw [cutProduct_overlap a ha hc _ _ u hu, Complex.normSq_ofReal] at hs
    unfold geometricMeasurePure
    nlinarith
  exact ⟨hψ,hy,hf,le_antisymm (hupp.trans_eq hβ.symm) hl⟩

/-- The actual support-projector trace, with the full arbitrary-parameter
combinatorial rank. -/
theorem support_trace {n d : ℕ} (hn : 0 < n) :
    trace (supportProjector n d) = (supportRank n d : ℂ) := by
  classical
  have hcard := support_rank_card (d := d) hn
  have h : (∑ x : Word (Fin d) n,
      if (Finset.univ.image x).card ≤ 2 then (1 : ℂ) else 0) =
      (Fintype.card {x : Word (Fin d) n // (Finset.univ.image x).card ≤ 2} : ℂ) := by
    simp [Fintype.card_subtype, Finset.sum_boole]
  simpa only [supportProjector, trace_diagonal, hcard] using h


lemma basis_projector_sum {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (∑ x : ι, rankOneDensity (Pi.single x (1 : ℂ))) = (1 : Matrix ι ι ℂ) := by
  ext i j
  simp only [Matrix.sum_apply, rankOneDensity, vecMulVec_apply, Pi.star_apply]
  simp [Pi.single_apply, Matrix.one_apply]

end
end D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof
