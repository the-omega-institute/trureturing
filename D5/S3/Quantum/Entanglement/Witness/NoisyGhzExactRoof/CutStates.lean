/- GID: D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/CutStates
   generality: G
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

private lemma phaseCharacter_normSq {d : ℕ} (v θ : Fin d → ZMod 3) :
    Complex.normSq (phaseCharacter v θ) = 1 := by
  simp [phaseCharacter, ZMod.stdAddChar_apply]

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

/-- Nonempty cuts excluding the first party; their complements are the
anchored representatives of nontrivial unordered bipartitions. -/
def SourceCut (n : ℕ) (hn : 0 < n) :=
  {s : Finset (Fin n) // s ∈ ((Finset.univ.erase ⟨0,hn⟩).powerset.erase ∅)}

lemma sourceCut_nonempty {n : ℕ} (hn : 0 < n) (s : SourceCut n hn) : s.1.Nonempty := by
  have h : s.1 ≠ ∅ := (Finset.mem_erase.mp s.2).1
  exact Finset.nonempty_iff_ne_empty.mpr h

private lemma sourceCut_first {n : ℕ} (hn : 0 < n) (s : SourceCut n hn) :
    (⟨0,hn⟩ : Fin n) ∉ s.1 := by
  have hsub := Finset.mem_powerset.mp (Finset.mem_erase.mp s.2).2
  intro h
  exact (Finset.mem_erase.mp (hsub h)).1 rfl

lemma sourceCut_complement {n : ℕ} (hn : 0 < n) (s : SourceCut n hn) : s.1ᶜ.Nonempty :=
  ⟨⟨0,hn⟩, Finset.mem_compl.mpr (sourceCut_first hn s)⟩

instance sourceCutFintype (n : ℕ) (hn : 0 < n) : Fintype (SourceCut n hn) := by
  classical
  unfold SourceCut
  infer_instance

/-- Exactly one anchored representative for each nontrivial unordered cut. -/
theorem sourceCut_card {n : ℕ} (hn : 0 < n) : Fintype.card (SourceCut n hn) = cutCount n := by
  classical
  change Fintype.card ↥((Finset.univ.erase (⟨0,hn⟩ : Fin n)).powerset.erase ∅) = _
  rw [Fintype.card_coe, Finset.card_erase_of_mem]
  · simp [cutCount, Finset.card_powerset]
  · simp

/-- Distinct ordered local symbols for a nonconstant cut word. -/
def OffPair (d : ℕ) := {ij : Fin d × Fin d // ij.1 ≠ ij.2}

instance offPairFintype (d : ℕ) : Fintype (OffPair d) := by
  classical
  unfold OffPair
  infer_instance

private lemma offPair_card (d : ℕ) : Fintype.card (OffPair d) = d * (d - 1) := by
  classical
  let e : OffPair d ≃ (i : Fin d) × {j : Fin d // i ≠ j} :=
    { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun x => ⟨(x.1,x.2.1), x.2.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  have h (i : Fin d) : Fintype.card {j : Fin d // i ≠ j} = d - 1 := by
    rw [Fintype.card_subtype_compl (fun j : Fin d => i = j)]
    simp
  simp [h]

/-- The word corresponding to one anchored cut and one distinct symbol pair. -/
def sourceCutWord {n d : ℕ} (hn : 0 < n) (s : SourceCut n hn) (ij : OffPair d) : Word (Fin d) n :=
  s.1.piecewise (fun _ => ij.1.2) (fun _ => ij.1.1)

private lemma sourceCutWord_first {n d : ℕ} (hn : 0 < n) (s : SourceCut n hn) (ij : OffPair d) :
    sourceCutWord hn s ij ⟨0,hn⟩ = ij.1.1 := by
  classical
  simp [sourceCutWord, sourceCut_first hn s]

private lemma sourceCutWord_nonconstant {n d : ℕ} (hn : 0 < n) (s : SourceCut n hn) (ij : OffPair d) :
    ¬ ∃ j : Fin d, ∀ i, sourceCutWord hn s ij i = j := by
  classical
  rintro ⟨j,hj⟩
  have hfirst := hj ⟨0,hn⟩
  rw [sourceCutWord_first] at hfirst
  obtain ⟨k,hk⟩ := sourceCut_nonempty hn s
  have hsecond := hj k
  simp only [sourceCutWord, Finset.piecewise, hk, ite_true] at hsecond
  exact ij.2 (hfirst.trans hsecond.symm)

private lemma sourceCutWord_supported {n d : ℕ} (hn : 0 < n) (s : SourceCut n hn) (ij : OffPair d) :
    (Finset.univ.image (sourceCutWord hn s ij)).card ≤ 2 :=
  join_support s.1 ij.1.2 ij.1.1

private lemma sourceCutWord_mem {n d : ℕ} (hn : 0 < n) (s : SourceCut n hn) (ij : OffPair d)
    (k : Fin n) : k ∈ s.1 ↔ sourceCutWord hn s ij k ≠ sourceCutWord hn s ij ⟨0,hn⟩ := by
  classical
  rw [sourceCutWord_first]
  by_cases hk : k ∈ s.1 <;> simp [sourceCutWord, hk, ij.2, Ne.symm ij.2]

/-- Constant words and uniquely anchored nonconstant two-symbol cut words. -/
def SupportIndex (n d : ℕ) (hn : 0 < n) := Fin d ⊕ (SourceCut n hn × OffPair d)

instance supportIndexFintype (n d : ℕ) (hn : 0 < n) : Fintype (SupportIndex n d hn) := by
  unfold SupportIndex
  infer_instance

def supportIndexWord {n d : ℕ} (hn : 0 < n) : SupportIndex n d hn → Word (Fin d) n
  | .inl j => fun _ => j
  | .inr x => sourceCutWord hn x.1 x.2

lemma supportIndexWord_injective {n d : ℕ} (hn : 0 < n) :
    Function.Injective (supportIndexWord (d := d) hn) := by
  classical
  intro x y h
  cases x with
  | inl i =>
    cases y with
    | inl j => exact congrArg Sum.inl (constant_word_injective hn h)
    | inr y =>
      exact (sourceCutWord_nonconstant hn y.1 y.2 ⟨i, fun k => (congrFun h k).symm⟩).elim
  | inr x =>
    cases y with
    | inl j =>
      exact (sourceCutWord_nonconstant hn x.1 x.2 ⟨j, fun k => congrFun h k⟩).elim
    | inr y =>
      have hs : x.1 = y.1 := by
        apply Subtype.ext
        ext k
        rw [sourceCutWord_mem hn x.1 x.2 k, sourceCutWord_mem hn y.1 y.2 k]
        change sourceCutWord hn x.1 x.2 k ≠ sourceCutWord hn x.1 x.2 ⟨0,hn⟩ ↔
          sourceCutWord hn y.1 y.2 k ≠ sourceCutWord hn y.1 y.2 ⟨0,hn⟩
        exact iff_of_eq (congrArg (fun z => z k ≠ z ⟨0,hn⟩) h)
      have hij : x.2 = y.2 := by
        apply Subtype.ext
        apply Prod.ext
        · simpa only [supportIndexWord, sourceCutWord_first] using congrFun h ⟨0,hn⟩
        · obtain ⟨k,hk⟩ := sourceCut_nonempty hn x.1
          have hky : k ∈ y.1.1 := hs ▸ hk
          simpa [supportIndexWord, sourceCutWord, hk, hky] using congrFun h k
      exact congrArg Sum.inr (Prod.ext hs hij)

lemma supportIndexWord_supported {n d : ℕ} (hn : 0 < n) (z : SupportIndex n d hn) :
    (Finset.univ.image (supportIndexWord hn z)).card ≤ 2 := by
  classical
  cases z with
  | inl j =>
    haveI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
    simp [supportIndexWord, Finset.image_const]
  | inr x => exact sourceCutWord_supported hn x.1 x.2

lemma supportIndexWord_surjective {n d : ℕ} (hn : 0 < n) (x : Word (Fin d) n)
    (hx : (Finset.univ.image x).card ≤ 2) : ∃ z : SupportIndex n d hn, supportIndexWord hn z = x := by
  classical
  by_cases hc : ∃ j : Fin d, ∀ k, x k = j
  · obtain ⟨j,hj⟩ := hc
    exact ⟨.inl j, (funext hj).symm⟩
  · let i := x ⟨0,hn⟩
    obtain ⟨k,hki⟩ : ∃ k, x k ≠ i := by
      by_contra h
      apply hc
      refine ⟨i, ?_⟩
      intro k
      exact not_ne_iff.mp (not_exists.mp h k)
    let j := x k
    have hij : i ≠ j := Ne.symm hki
    have hsub : ({i,j} : Finset (Fin d)) ⊆ Finset.univ.image x := by
      intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · exact Finset.mem_image.mpr ⟨⟨0,hn⟩, Finset.mem_univ _, rfl⟩
      · exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
    have himage : Finset.univ.image x = {i,j} :=
      (Finset.eq_of_subset_of_card_le hsub (by simpa [hij] using hx)).symm
    let s : Finset (Fin n) := Finset.univ.filter (fun k => x k ≠ i)
    have hs0 : s ≠ ∅ := by
      exact Finset.nonempty_iff_ne_empty.mp ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hki⟩⟩
    have hss : s ⊆ Finset.univ.erase ⟨0,hn⟩ := by
      intro l hl
      obtain ⟨_,hl⟩ := Finset.mem_filter.mp hl
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_univ _⟩
      intro h
      exact hl (congrArg x h)
    let c : SourceCut n hn := ⟨s, Finset.mem_erase.mpr ⟨hs0,Finset.mem_powerset.mpr hss⟩⟩
    refine ⟨.inr (c,⟨(i,j),hij⟩), ?_⟩
    funext l
    have hl : x l ∈ ({i,j} : Finset (Fin d)) := by
      rw [← himage]
      exact Finset.mem_image.mpr ⟨l,Finset.mem_univ _,rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with hl | hl <;> simp [supportIndexWord, sourceCutWord, Finset.piecewise, c, s, hl, hij, Ne.symm hij]

/-- Exact disjoint enumeration of the computational support of P. -/
def supportIndexEquiv {n d : ℕ} (hn : 0 < n) :
    SupportIndex n d hn ≃ {x : Word (Fin d) n // (Finset.univ.image x).card ≤ 2} :=
  Equiv.ofBijective (fun z => ⟨supportIndexWord hn z, supportIndexWord_supported hn z⟩)
    ⟨fun _ _ h => supportIndexWord_injective hn (congrArg Subtype.val h), by
      rintro ⟨x,hx⟩
      obtain ⟨z,hz⟩ := supportIndexWord_surjective hn x hx
      exact ⟨z,Subtype.ext hz⟩⟩

/-- The support rank is the source formula d+K d(d-1), in every dimension. -/
theorem support_rank_card {n d : ℕ} (hn : 0 < n) :
    Fintype.card {x : Word (Fin d) n // (Finset.univ.image x).card ≤ 2} = supportRank n d := by
  rw [← Fintype.card_congr (supportIndexEquiv (d := d) hn)]
  simp [SupportIndex, Fintype.card_sum, Fintype.card_prod, sourceCut_card hn,
    offPair_card, supportRank]
  ring

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

/-- Strict rank inequalities use the actual missing computational Q-vector. -/
theorem support_rank_bounds {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    d < supportRank n d ∧ supportRank n d < wordCount n d := by
  have hp : 1 < 2 ^ (n - 1) := by
    have he : n - 1 ≠ 0 := by omega
    exact Nat.one_lt_pow he (by norm_num)
  have hk : 0 < cutCount n := by unfold cutCount; omega
  constructor
  · unfold supportRank
    have hh : 0 < cutCount n * d * (d - 1) := Nat.mul_pos (Nat.mul_pos hk (by omega)) (by omega)
    omega
  · have h := Fintype.card_lt_of_injective_of_notMem
      (fun x : {x : Word (Fin d) n // (Finset.univ.image x).card ≤ 2} => x.1)
      Subtype.val_injective (b := qWord (n := n) hd) (by
        rintro ⟨x,hx⟩
        exact (qWord_outside hn hd) (hx ▸ x.2))
    rw [support_rank_card (by omega)] at h
    simpa [wordCount, Word] using h

lemma basis_projector_sum {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (∑ x : ι, rankOneDensity (Pi.single x (1 : ℂ))) = (1 : Matrix ι ι ℂ) := by
  ext i j
  simp only [Matrix.sum_apply, rankOneDensity, vecMulVec_apply, Pi.star_apply]
  simp [Pi.single_apply, Matrix.one_apply]

end
end D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof
