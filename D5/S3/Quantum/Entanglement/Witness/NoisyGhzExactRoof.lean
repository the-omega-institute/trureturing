/- GID: D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Independent-coordinate phase character cancellation for the noisy-GHZ finite witness. -/

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Tactic
import D5.S3.Quantum.Entanglement.Witness.NoisyGhzWitnessBoundGap

/-! This module records the finite phase identity needed by the full matrix
    ensemble. The character is indexed by the whole phase vector
    `(Fin d → ZMod 3)`, so equal scalar differences are never used to identify
    distinct ordered pairs. -/

open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof

noncomputable section

/-! The phase character associated with a coefficient vector. -/

def phaseCharacter {d : ℕ} (v θ : Fin d → ZMod 3) : ℂ :=
  ZMod.stdAddChar (∑ j, v j * θ j)

private lemma phaseCharacter_prod {d : ℕ} (v θ : Fin d → ZMod 3) :
    phaseCharacter v θ = ∏ j, ZMod.stdAddChar (v j * θ j) := by
  unfold phaseCharacter
  exact congrArg Additive.toMul
      (map_sum ZMod.stdAddChar.toAddMonoidHom (fun j : Fin d => v j * θ j) Finset.univ) |>.trans
    (toMul_sum _ _)

/-- Averaging an arbitrary coefficient character over all independent phases.

The zero coefficient vector is the only surviving mode.  This is the
coordinate-wise orthogonality statement used for the phase part of the full
finite noisy-GHZ matrix ensemble.
-/
theorem phaseCharacter_sum {d : ℕ} (v : Fin d → ZMod 3) :
    (∑ θ : Fin d → ZMod 3, phaseCharacter v θ) =
      if v = 0 then (3 ^ d : ℕ) else 0 := by
  classical
  simp_rw [phaseCharacter_prod]
  rw [← Fintype.prod_sum (fun j (a : ZMod 3) => ZMod.stdAddChar (v j * a))]
  have hs (j : Fin d) :
      (∑ a : ZMod 3, ZMod.stdAddChar (v j * a)) =
        if v j = 0 then (3 : ℂ) else 0 := by
    simpa [ZMod.card, mul_comm] using
      (AddChar.sum_mulShift (ψ := ZMod.stdAddChar) (v j)
        (ZMod.isPrimitive_stdAddChar 3))
  simp_rw [hs]
  by_cases hv : v = 0
  · simp [hv]
  · rw [if_neg hv]
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra h
      apply hv
      funext j
      exact not_ne_iff.mp (not_exists.mp h j)
    have hzero : (∏ x : Fin d, if v x = 0 then (3 : ℂ) else 0) = 0 := by
      refine Finset.prod_eq_zero (s := (Finset.univ : Finset (Fin d)))
        (f := fun x => if v x = 0 then (3 : ℂ) else 0) (Finset.mem_univ j) ?_
      simp [hj]
    simpa only [Nat.cast_zero] using hzero

/-- The coefficient vector for the ordered pair `(i,j)`. -/
def pairCoefficient {d : ℕ} (i j : Fin d) : Fin d → ZMod 3 :=
  fun k => (if k = i then 1 else 0) - (if k = j then 1 else 0)

/-! Source parameter functions used by the exact two-mean and noisy-state
    formulas.  They are kept as natural/real functions so their domains are
    visible in the checked declarations. -/

def wordCount (n d : ℕ) : ℕ := d ^ n

def cutCount (n : ℕ) : ℕ := 2 ^ (n - 1) - 1

def supportRank (n d : ℕ) : ℕ := d + cutCount n * d * (d - 1)

def witnessSlope (n d : ℕ) : ℝ :=
  (d - 1 : ℝ) / d + ((supportRank n d : ℝ) / d - 1) / wordCount n d

def witnessZeroProbability (n d : ℕ) : ℝ :=
  ((d - 1 : ℝ) / d) / witnessSlope n d

def twoMeanValue (d : ℕ) (f y : ℝ) : ℝ :=
  (y + (d - 2 : ℝ) * f - 2 * Real.sqrt ((d - 1 : ℝ) * f * (y - f))) / d

theorem qutrit_source_arithmetic :
    wordCount 3 3 = 27 ∧ cutCount 3 = 3 ∧ supportRank 3 3 = 21 ∧
      witnessSlope 3 3 = 8 / 9 ∧ witnessZeroProbability 3 3 = 3 / 4 := by
  norm_num [wordCount, cutCount, supportRank, witnessSlope, witnessZeroProbability]

theorem qutrit_two_mean_value :
    twoMeanValue 3 (23 / 36) (11 / 12) = (14 - Real.sqrt 115) / 27 := by
  unfold twoMeanValue
  have hs : Real.sqrt ((2 : ℝ) * (23 / 36) * (11 / 12 - 23 / 36)) =
      Real.sqrt 115 / 18 := by
    have h : (2 : ℝ) * (23 / 36) * (11 / 12 - 23 / 36) = 115 / 324 := by norm_num
    rw [h, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 115)]
    norm_num
  have hs' : Real.sqrt (((3 : ℝ) - 1) * (23 / 36) * (11 / 12 - 23 / 36)) =
      Real.sqrt 115 / 18 := by
    convert hs using 1 <;> norm_num
  norm_num [hs']
  ring

theorem pairCoefficient_eq_zero_iff {d : ℕ} (i j : Fin d) :
    pairCoefficient i j = 0 ↔ i = j := by
  constructor
  · intro h
    by_contra hij
    have hi : pairCoefficient i j i = (1 : ZMod 3) := by
      simp [pairCoefficient, hij]
    have hz : pairCoefficient i j i = 0 := by simpa [h] using congrFun h i
    rw [hi] at hz
    norm_num at hz
  · intro h
    rcases h with rfl
    funext k
    simp [pairCoefficient]

theorem pair_phase_sum {d : ℕ} (i j : Fin d) :
    (∑ θ : Fin d → ZMod 3, phaseCharacter (pairCoefficient i j) θ) =
      if i = j then (3 ^ d : ℕ) else 0 := by
  rw [phaseCharacter_sum]
  simp [pairCoefficient_eq_zero_iff]

private lemma nonzero_pairCoefficient_injective {d : ℕ} (i j k l : Fin d)
    (hij : i ≠ j) (h : pairCoefficient i j = pairCoefficient k l) :
    i = k ∧ j = l := by
  have hi : i = k := by
    by_contra hik
    have hh : (1 : ZMod 3) = -(if i = l then 1 else 0) := by
      simpa only [pairCoefficient, ite_true, if_neg hij, if_neg hik,
        sub_zero, zero_sub] using congrFun h i
    by_cases hil : i = l
    · have hh' : (1 : ZMod 3) = -1 := by simpa [hil] using hh
      exact (by decide : (1 : ZMod 3) ≠ -1) hh'
    · norm_num [hil] at hh
  subst k
  refine ⟨rfl, ?_⟩
  by_contra hjl
  have hh := congrFun h j
  simp [pairCoefficient, Ne.symm hij, hjl] at hh

theorem pairCoefficient_eq_iff {d : ℕ} (i j k l : Fin d) :
    pairCoefficient i j = pairCoefficient k l ↔
      (i = j ∧ k = l) ∨ (i = k ∧ j = l) := by
  constructor
  · intro h
    by_cases hij : i = j
    · left
      refine ⟨hij, ?_⟩
      apply (pairCoefficient_eq_zero_iff k l).mp
      rw [← h, (pairCoefficient_eq_zero_iff i j).mpr hij]
    · exact Or.inr (nonzero_pairCoefficient_injective i j k l hij h)
  · rintro (⟨hij, hkl⟩ | ⟨hik, hjl⟩)
    · rw [(pairCoefficient_eq_zero_iff i j).mpr hij,
        (pairCoefficient_eq_zero_iff k l).mpr hkl]
    · rw [hik, hjl]

private lemma phaseCharacter_mul_star {d : ℕ} (v w θ : Fin d → ZMod 3) :
    phaseCharacter v θ * star (phaseCharacter w θ) = phaseCharacter (v - w) θ := by
  have hs (a : ZMod 3) :
      star (ZMod.stdAddChar a) = (ZMod.stdAddChar a)⁻¹ := by
    simpa only [starRingEnd_apply, AddChar.inv_apply'] using
      (AddChar.starComp_apply (R := ZMod 3) (by rw [ZMod.ringChar_zmod_n]; norm_num)
        (φ := ZMod.stdAddChar) a)
  unfold phaseCharacter
  rw [hs, ← div_eq_mul_inv, ← AddChar.map_sub_eq_div]
  congr 1
  simp [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- The complete Gram matrix of ordered-pair characters. All constant pairs
share the zero mode; every off-diagonal ordered pair has its own character
on the independent phase group, in every dimension. -/
theorem pair_cross_phase_sum {d : ℕ} (i j k l : Fin d) :
    (∑ θ : Fin d → ZMod 3,
      phaseCharacter (pairCoefficient i j) θ *
        star (phaseCharacter (pairCoefficient k l) θ)) =
      if (i = j ∧ k = l) ∨ (i = k ∧ j = l) then (3 ^ d : ℕ) else 0 := by
  simp_rw [phaseCharacter_mul_star]
  rw [phaseCharacter_sum]
  simp only [sub_eq_zero, pairCoefficient_eq_iff]

open _root_.Matrix
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Quantum.Entanglement.OccupancyWordSectors (Word)
open D5.S3.Quantum.Information.MultiEntropyPositivityRefutation (IsUnitState)
open D5.S3.Quantum.Recovery.ProductPrefixRigidity (readout)
open NoisyGhzWitnessBoundGap

private lemma constant_word_injective {n d : ℕ} (hn : 0 < n) :
    Function.Injective (fun j : Fin d => (fun _ : Fin n => j)) := by
  intro i j h
  exact congrFun h ⟨0, hn⟩

private lemma sum_supported_constants {n d : ℕ} {α : Type*} [AddCommMonoid α]
    (hn : 0 < n) (f : Word (Fin d) n → α)
    (hf : ∀ x, (¬ ∃ j : Fin d, ∀ i, x i = j) → f x = 0) :
    ∑ x, f x = ∑ j : Fin d, f (fun _ => j) := by
  classical
  let s := Finset.univ.image (fun j : Fin d => (fun _ : Fin n => j))
  have hs : ∑ x ∈ s, f x = ∑ x, f x := by
    apply Finset.sum_subset (Finset.subset_univ s)
    intro x _ hx
    apply hf x
    rintro ⟨j, hj⟩
    apply hx
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, (funext hj).symm⟩
  rw [← hs]
  exact Finset.sum_image (fun i _ j _ h => constant_word_injective hn h)

/-- The actual equal-superposition vector is normalized in every nonempty
party and local-dimension domain. -/
theorem ghz_unit {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    IsUnitState (ghz n d) := by
  classical
  unfold IsUnitState
  rw [sum_supported_constants hn _ (by
    intro x hx
    simp [ghz, hx])]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hg (j : Fin d) : ghz n d (fun _ => j) = (Real.sqrt d : ℂ)⁻¹ := by
    exact if_pos ⟨j, fun _ => rfl⟩
  simp [hg, Complex.normSq_inv, Complex.normSq_ofReal,
    Real.sq_sqrt (Nat.cast_nonneg d), hdR]

/-- For local dimension two every computational word is supported. This is
the operator boundary identifying the witness with the fidelity witness. -/
theorem qubit_support (n : ℕ) :
    supportProjector n 2 = (1 : Matrix (Word (Fin 2) n) (Word (Fin 2) n) ℂ) := by
  classical
  have h (x : Word (Fin 2) n) : (Finset.univ.image x).card ≤ 2 := by
    exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin 2)
  simp [supportProjector, h, diagonal_one]

theorem qubit_witness (n : ℕ) :
    witnessOp n 2 = (1 / 2 : ℝ) •
      (1 : Matrix (Word (Fin 2) n) (Word (Fin 2) n) ℂ) -
        rankOneDensity (ghz n 2) := by
  simp [witnessOp, qubit_support]

private lemma cs {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    Complex.normSq (star u ⬝ᵥ v) ≤
      (∑ i, Complex.normSq (u i)) * ∑ i, Complex.normSq (v i) := by
  classical
  simpa only [Complex.normSq_eq_norm_sq] using
    D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays.cs_sq u v

private lemma expectation_rank_one {ι : Type*} [Fintype ι] (φ ψ : ι → ℂ) :
    readout (rankOneDensity φ) ψ = Complex.normSq (star φ ⬝ᵥ ψ) := by
  have h := D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.quadratic_projector ψ φ
  rw [star_dotProduct ψ φ, Complex.star_def, Complex.normSq_conj] at h
  exact congrArg Complex.re h

private lemma support_expectation {n d : ℕ} (ψ : Word (Fin d) n → ℂ) :
    readout (supportProjector n d) ψ =
      ∑ x ∈ Finset.univ.filter (fun x : Word (Fin d) n => (Finset.univ.image x).card ≤ 2),
        Complex.normSq (ψ x) := by
  classical
  rw [readout, supportProjector]
  have hdiag :
      (fun x : Word (Fin d) n =>
        if (Finset.univ.image x).card ≤ 2 then (1 : ℂ) else 0) =
        (fun x : Word (Fin d) n =>
          ((if (Finset.univ.image x).card ≤ 2 then (1 : ℝ) else 0) : ℂ)) := by
    funext x
    split_ifs <;> rfl
  rw [hdiag]
  have hquad :=
    D5.S3.Quantum.Divergence.CanonicalChannelDPI.diagonal_quadratic_form
      (d := fun x : Word (Fin d) n =>
        if (Finset.univ.image x).card ≤ 2 then (1 : ℝ) else 0) ψ
  convert hquad using 1
  · congr 2
    funext x
    simp only [mulVec_diagonal]
    split_ifs <;> rfl
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp [Complex.normSq_eq_norm_sq]

private lemma ghz_expectation {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (ψ : Word (Fin d) n → ℂ) :
    (d : ℝ) * readout (rankOneDensity (ghz n d)) ψ =
      Complex.normSq (∑ i : Fin d, ψ (fun _ => i)) := by
  classical
  have he : star (ghz n d) ⬝ᵥ ψ =
      (Real.sqrt d : ℂ)⁻¹ * ∑ i : Fin d, ψ (fun _ => i) := by
    unfold dotProduct
    rw [sum_supported_constants hn _ (by
      intro x hx
      simp [ghz, hx])]
    have hg (j : Fin d) : ghz n d (fun _ => j) = (Real.sqrt d : ℂ)⁻¹ := by
      exact if_pos ⟨j, fun _ => rfl⟩
    simp [hg, Finset.mul_sum]
  rw [expectation_rank_one, he, Complex.normSq_mul]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp [Complex.normSq_inv, Complex.normSq_ofReal,
    Real.sq_sqrt (Nat.cast_nonneg d), hdR, ← mul_assoc]

private lemma join_support {n d : ℕ} (a : Finset (Fin n)) (i j : Fin d) :
    (Finset.univ.image (a.piecewise (fun _ => i) (fun _ => j))).card ≤ 2 := by
  classical
  have h : Finset.univ.image (a.piecewise (fun _ => i) (fun _ => j)) ⊆ {i, j} := by
    intro x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
    by_cases hk : k ∈ a <;> simp [Finset.piecewise, hk]
  exact (Finset.card_le_card h).trans Finset.card_le_two

private lemma join_injective {n d : ℕ} (a : Finset (Fin n))
    (ha : a.Nonempty) (hc : aᶜ.Nonempty) :
    Function.Injective (fun ij : Fin d × Fin d =>
      a.piecewise (fun _ => ij.1) (fun _ => ij.2)) := by
  classical
  obtain ⟨k, hk⟩ := ha
  obtain ⟨l, hl⟩ := hc
  intro x y h
  apply Prod.ext
  · simpa [hk] using congrFun h k
  · simpa [Finset.mem_compl.mp hl] using congrFun h l

/-- The all-cut biseparable overlap inequality in the actual word space.
No assumption on normalized factors, chosen Schmidt bases, or a scalar roof
is introduced: the factors are exactly those in `IsBiseparable`. -/
theorem biseparable_overlap {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (φ : Word (Fin d) n → ℂ) (hφ : IsBiseparable φ) :
    (d : ℝ) * readout (rankOneDensity (ghz n d)) φ ≤
      readout (supportProjector n d) φ := by
  classical
  obtain ⟨_, a, ha, hc, u, v, h⟩ := hφ
  have hj (i j : Fin d) :
      φ (a.piecewise (fun _ => i) (fun _ => j)) =
        u (fun _ => i) * v (fun _ => j) := by
    rw [h]
    congr 1
    · congr 1; funext k; simp [k.property]
    · congr 1; funext k; simp [Finset.mem_compl.mp k.property]
  have hd' (i : Fin d) : φ (fun _ => i) = u (fun _ => i) * v (fun _ => i) := h _
  rw [ghz_expectation hn hd, support_expectation]
  calc
    Complex.normSq (∑ i : Fin d, φ (fun _ => i)) ≤
        (∑ i : Fin d, Complex.normSq (u (fun _ => i))) *
          ∑ j : Fin d, Complex.normSq (v (fun _ => j)) := by
      simpa [dotProduct, Complex.star_def, hd'] using
        cs (star (fun i : Fin d => u (fun _ => i))) (fun j : Fin d => v (fun _ => j))
    _ = ∑ ij : Fin d × Fin d, Complex.normSq
        (φ (a.piecewise (fun _ => ij.1) (fun _ => ij.2))) := by
      simp only [Fintype.sum_prod_type, hj, Complex.normSq_mul,
        Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ ≤ _ := by
      have hs : (∑ ij : Fin d × Fin d, Complex.normSq
          (φ (a.piecewise (fun _ => ij.1) (fun _ => ij.2)))) =
          ∑ x ∈ Finset.univ.image (fun ij : Fin d × Fin d =>
            a.piecewise (fun _ => ij.1) (fun _ => ij.2)), Complex.normSq (φ x) :=
        (Finset.sum_image (f := fun x : Word (Fin d) n => Complex.normSq (φ x))
          (s := Finset.univ) (g := fun ij : Fin d × Fin d =>
            a.piecewise (fun _ => ij.1) (fun _ => ij.2))
          (fun x _ y _ hxy => join_injective a ha hc hxy)).symm
      rw [hs]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        obtain ⟨ij, _, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, join_support a ij.1 ij.2⟩
      · intro x _ _; exact Complex.normSq_nonneg _

private lemma basis_unit {n d : ℕ} (x : Word (Fin d) n) :
    IsUnitState (Pi.single x 1) := by
  classical
  simp [IsUnitState, Pi.single_apply]

/-- Every computational vector factors across a nonempty proper cut. -/
theorem computational_biseparable {n d : ℕ} (hn : 2 ≤ n) (w : Word (Fin d) n) :
    IsBiseparable (Pi.single w (1 : ℂ)) := by
  classical
  let a : Finset (Fin n) := {⟨0, by omega⟩}
  have ha : a.Nonempty := by simp [a]
  have hc : aᶜ.Nonempty := by
    refine ⟨⟨1, by omega⟩, ?_⟩
    simp [a]
  refine ⟨basis_unit _, a, ha, hc,
    fun u => if ∀ i, u i = w i then 1 else 0,
    fun v => if ∀ i, v i = w i then 1 else 0, ?_⟩
  intro x
  have he : x = w ↔
      (∀ i : a, x i = w i) ∧ (∀ i : ↥aᶜ, x i = w i) := by
    rw [← Set.eqOn_univ x w, ← Set.union_compl_self (↑a : Set (Fin n)), Set.eqOn_union]
    simp only [Set.EqOn, Finset.mem_coe, Subtype.forall,
      Finset.mem_compl, Set.mem_compl_iff]
  simp only [Pi.single_apply]
  change (if x = w then (1 : ℂ) else 0) =
    (if ∀ i : a, x i = w i then 1 else 0) *
      (if ∀ i : ↥aᶜ, x i = w i then 1 else 0)
  simp only [he]
  split_ifs <;> simp_all

private lemma overlap_values_nonempty {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    (ψ : Word (Fin d) n → ℂ) :
    {t : ℝ | ∃ φ, IsBiseparable φ ∧ t = Complex.normSq (star φ ⬝ᵥ ψ)}.Nonempty := by
  exact ⟨_, Pi.single (fun _ => (⟨0, hd⟩ : Fin d)) 1,
    computational_biseparable hn _, rfl⟩

private lemma overlap_values_bdd {n d : ℕ} (ψ : Word (Fin d) n → ℂ)
    (hψ : IsUnitState ψ) :
    BddAbove {t : ℝ | ∃ φ, IsBiseparable φ ∧ t = Complex.normSq (star φ ⬝ᵥ ψ)} := by
  refine ⟨1, ?_⟩
  rintro t ⟨φ, hφ, rfl⟩
  have h := cs φ ψ
  rw [hφ.1, hψ, mul_one] at h
  exact h

/-- Both bounds use a nonempty, bounded actual biseparable-overlap set. -/
theorem pure_measure_bounds {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    (ψ : Word (Fin d) n → ℂ) (hψ : IsUnitState ψ) :
    0 ≤ geometricMeasurePure ψ ∧ geometricMeasurePure ψ ≤ 1 := by
  have hs := overlap_values_nonempty hn hd ψ
  have hb := overlap_values_bdd ψ hψ
  have hu : sSup {t : ℝ | ∃ φ, IsBiseparable φ ∧
      t = Complex.normSq (star φ ⬝ᵥ ψ)} ≤ 1 := by
    apply csSup_le hs
    rintro t ⟨φ, hφ, rfl⟩
    have h := cs φ ψ
    rw [hφ.1, hψ, mul_one] at h
    exact h
  obtain ⟨t, ht⟩ := hs
  have hl := le_csSup hb ht
  obtain ⟨φ, hφ, rfl⟩ := ht
  have hz := Complex.normSq_nonneg (star φ ⬝ᵥ ψ)
  unfold geometricMeasurePure
  constructor <;> linarith

private def ensembleValues {n d : ℕ}
    (ρ : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ) : Set ℝ :=
  {t | ∃ (k : ℕ) (p : Fin k → ℝ) (ψ : Fin k → Word (Fin d) n → ℂ),
    (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧ (∀ i, IsUnitState (ψ i)) ∧
    ρ = ∑ i, p i • rankOneDensity (ψ i) ∧ t = ∑ i, p i * geometricMeasurePure (ψ i)}

private lemma ensemble_values_nonempty {n d : ℕ}
    (ρ : D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Word (Fin d) n)) :
    (ensembleValues (CStarMatrix.ofMatrix.symm ρ.1)).Nonempty := by
  classical
  obtain ⟨k, p, ψ, hp, hs, hu, he⟩ :=
    D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.density_ensemble ρ
  refine ⟨_, k, p, ψ, hp, hs, ?_, ?_, rfl⟩
  · intro i
    exact (D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.unit_norm_iff _).mp (hu i)
  · change CStarMatrix.ofMatrix.symm ρ.1 =
      ∑ i, (algebraMap ℝ ℂ) (p i) • rankOneDensity (ψ i) at he
    simpa only [algebraMap_smul] using he

private lemma ensemble_values_bdd {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    (ρ : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ) :
    BddBelow (ensembleValues ρ) := by
  refine ⟨0, ?_⟩
  rintro t ⟨k, p, ψ, hp, hs, hu, he, rfl⟩
  exact Finset.sum_nonneg (fun i _ =>
    mul_nonneg (hp i) (pure_measure_bounds hn hd (ψ i) (hu i)).1)

/-- The actual finite convex-roof set of every density state is nonempty and
bounded below; in particular the roof is nonnegative without an empty-infimum
convention. -/
theorem density_measure_nonneg {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    (ρ : D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Word (Fin d) n)) :
    0 ≤ geometricMeasure (CStarMatrix.ofMatrix.symm ρ.1) := by
  apply le_csInf (ensemble_values_nonempty ρ)
  rintro t ⟨k, p, ψ, hp, hs, hu, he, rfl⟩
  exact Finset.sum_nonneg (fun i _ =>
    mul_nonneg (hp i) (pure_measure_bounds hn hd (ψ i) (hu i)).1)

/-- The complementary measured projector, on the original computational space. -/
def complementProjector (n d : ℕ) :
    Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ := 1 - supportProjector n d

private lemma ghz_supported {n d : ℕ} (hn : 0 < n) (x : Word (Fin d) n) :
    (if (Finset.univ.image x).card ≤ 2 then (1 : ℂ) else 0) * ghz n d x = ghz n d x := by
  classical
  by_cases h : ∃ j : Fin d, ∀ i, x i = j
  · obtain ⟨j, hj⟩ := h
    have he : x = fun _ => j := funext hj
    subst x
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    simp [Finset.image_const]
  · simp [ghz, h]

private lemma projector_data {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    supportProjector n d * supportProjector n d = supportProjector n d ∧
    supportProjector n d * rankOneDensity (ghz n d) = rankOneDensity (ghz n d) ∧
    rankOneDensity (ghz n d) * supportProjector n d = rankOneDensity (ghz n d) ∧
    rankOneDensity (ghz n d) * rankOneDensity (ghz n d) = rankOneDensity (ghz n d) := by
  classical
  have hu : star (ghz n d) ⬝ᵥ ghz n d = 1 :=
    (D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.unit_norm_iff _).mpr
      (ghz_unit hn hd)
  refine ⟨?_, ?_, ?_,
    (D5.S3.Quantum.PureState.PureStateHandshake.pure_state_handshake (ghz n d) hu 1).1⟩
  · simp only [supportProjector, diagonal_mul_diagonal]
    congr 1
    funext x
    split_ifs <;> norm_num
  · ext x y
    simp only [supportProjector, diagonal_mul, rankOneDensity, vecMulVec_apply, Pi.star_apply]
    rw [← mul_assoc, ghz_supported hn]
  · ext x y
    simp only [supportProjector, mul_diagonal, rankOneDensity, vecMulVec_apply, Pi.star_apply]
    by_cases h : (Finset.univ.image y).card ≤ 2
    · simp [h]
    · have hz : ghz n d y = 0 := by simpa [h] using (ghz_supported hn y).symm
      simp [h, hz]

private lemma orthogonal_positive {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    (supportProjector n d - rankOneDensity (ghz n d)).PosSemidef ∧
      (complementProjector n d).PosSemidef := by
  classical
  obtain ⟨hpp, hpg, hgp, hgg⟩ := projector_data hn hd
  have hp : (supportProjector n d).IsHermitian := by
    apply isHermitian_diagonal_of_self_adjoint
    funext x
    simp only [Pi.star_apply]
    split_ifs <;> simp
  have hg : (rankOneDensity (ghz n d)).IsHermitian :=
    (posSemidef_vecMulVec_self_star (ghz n d)).isHermitian
  have hP : IsStarProjection (supportProjector n d) := ⟨hpp, hp.isSelfAdjoint⟩
  have hG : IsStarProjection (rankOneDensity (ghz n d)) := ⟨hgg, hg.isSelfAdjoint⟩
  exact ⟨(hG.sub_of_mul_eq_left hP hgp).nonneg.posSemidef,
    hP.one_sub_nonneg.posSemidef⟩

/-- Finite positive metrics, including the affine certificate family. -/
def metric (n d : ℕ) (a b : ℝ) :
    Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ :=
  a • rankOneDensity (ghz n d) +
    b • (supportProjector n d - rankOneDensity (ghz n d)) + complementProjector n d

private def metricInverse (n d : ℕ) (a b : ℝ) :
    Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ :=
  a⁻¹ • rankOneDensity (ghz n d) +
    b⁻¹ • (supportProjector n d - rankOneDensity (ghz n d)) + complementProjector n d

private lemma metric_positive {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hab : a ≤ b) :
    (metric n d a b).PosDef := by
  have he : metric n d a b =
      a • (1 : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ) +
      (b - a) • (supportProjector n d - rankOneDensity (ghz n d)) +
      (1 - a) • complementProjector n d := by
    dsimp [metric, complementProjector]
    module
  rw [he]
  exact ((Matrix.PosDef.one.smul ha).add_posSemidef
    ((orthogonal_positive hn hd).1.smul (sub_nonneg.mpr hab))).add_posSemidef
      ((orthogonal_positive hn hd).2.smul (sub_nonneg.mpr ha1))

private lemma metric_inverse {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    metric n d a b * metricInverse n d a b = 1 := by
  classical
  obtain ⟨hpp, hpg, hgp, hgg⟩ := projector_data hn hd
  simp only [metric, metricInverse, complementProjector,
    add_mul, mul_add, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, one_mul, mul_one, hpp, hpg, hgp, hgg]
  match_scalars <;> field_simp <;> ring

private lemma metric_weighted_cs {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hab : a ≤ b)
    (φ ψ : Word (Fin d) n → ℂ) :
    Complex.normSq (star φ ⬝ᵥ ψ) ≤
      readout (metricInverse n d a b) φ * readout (metric n d a b) ψ := by
  classical
  have hb : 0 < b := ha.trans_le hab
  have hi : (metricInverse n d a b).PosSemidef := by
    exact (((posSemidef_vecMulVec_self_star (ghz n d)).smul
      (inv_nonneg.mpr ha.le)).add
      ((orthogonal_positive hn hd).1.smul (inv_nonneg.mpr hb.le))).add
        (orthogonal_positive hn hd).2
  have hm : metric n d a b *ᵥ (metricInverse n d a b *ᵥ φ) = φ := by
    rw [mulVec_mulVec, metric_inverse hn hd ha.ne' hb.ne', one_mulVec]
  have hr : star (metricInverse n d a b *ᵥ φ) ⬝ᵥ φ =
      star φ ⬝ᵥ metricInverse n d a b *ᵥ φ := by
    rw [star_mulVec, hi.isHermitian.eq, ← dotProduct_mulVec]
  have hc := D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.psd_cauchy_schwarz
    (metric n d a b) (metric_positive hn hd ha ha1 hab).posSemidef
      ψ (metricInverse n d a b *ᵥ φ)
  rw [hm, hr] at hc
  rw [← Complex.normSq_eq_norm_sq,
    D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.normSq_overlap_comm ψ φ] at hc
  simpa only [readout, mul_comm] using hc

private lemma expectation_add {n d : ℕ}
    (a c : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ)
    (ψ : Word (Fin d) n → ℂ) : readout (a + c) ψ = readout a ψ + readout c ψ := by
  exact RHLinalg.hermForm_add a c ψ

private lemma expectation_sub {n d : ℕ}
    (a c : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ)
    (ψ : Word (Fin d) n → ℂ) : readout (a - c) ψ = readout a ψ - readout c ψ := by
  exact RHLinalg.hermForm_sub a c ψ

private lemma expectation_smul {n d : ℕ} (r : ℝ)
    (a : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ)
    (ψ : Word (Fin d) n → ℂ) : readout (r • a) ψ = r * readout a ψ := by
  change (star ψ ⬝ᵥ ((r • a) *ᵥ ψ)).re = r * (star ψ ⬝ᵥ (a *ᵥ ψ)).re
  rw [← Complex.coe_smul r a]
  exact D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.quadratic_smul ψ r a

private lemma expectation_one {n d : ℕ} (ψ : Word (Fin d) n → ℂ) :
    readout 1 ψ = ∑ x, Complex.normSq (ψ x) := by
  simpa only [RHLinalg.hermForm, readout, RCLike.re_to_complex,
    Complex.normSq_eq_norm_sq] using RHLinalg.hermForm_one ψ

private lemma metric_inverse_bound {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (he : a⁻¹ + (d - 1 : ℝ) * b⁻¹ = d)
    (φ : Word (Fin d) n → ℂ) (hφ : IsBiseparable φ) :
    readout (metricInverse n d a b) φ ≤ 1 := by
  have hu : readout 1 φ = 1 := by rw [expectation_one]; exact hφ.1
  have h := biseparable_overlap hn hd φ hφ
  have hc : 0 ≤ a⁻¹ - b⁻¹ := sub_nonneg.mpr (inv_anti₀ ha hab)
  have hm := mul_nonneg hc (sub_nonneg.mpr h)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  simp only [metricInverse, complementProjector, expectation_add,
    expectation_sub, expectation_smul, hu]
  have he' := congrArg (fun z : ℝ => z * readout (supportProjector n d) φ) he
  nlinarith

private lemma pure_metric_lower {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hab : a ≤ b)
    (he : a⁻¹ + (d - 1 : ℝ) * b⁻¹ = d)
    (ψ : Word (Fin d) n → ℂ) (hψ : IsUnitState ψ) :
    (1 - b) * readout (supportProjector n d) ψ +
      (b - a) * readout (rankOneDensity (ghz n d)) ψ ≤ geometricMeasurePure ψ := by
  have hn' : 0 < n := by omega
  have hpos : 0 ≤ readout (metric n d a b) ψ :=
    RHLinalg.hermForm_nonneg_of_posSemidef
      (metric_positive hn' hd ha ha1 hab).posSemidef ψ
  have hs : sSup {t : ℝ | ∃ φ, IsBiseparable φ ∧
      t = Complex.normSq (star φ ⬝ᵥ ψ)} ≤ readout (metric n d a b) ψ := by
    apply csSup_le (overlap_values_nonempty hn hd ψ)
    rintro t ⟨φ, hφ, rfl⟩
    exact (metric_weighted_cs hn' hd ha ha1 hab φ ψ).trans
      (mul_le_of_le_one_left hpos (metric_inverse_bound hn' hd ha hab he φ hφ))
  have hu : readout 1 ψ = 1 := by rw [expectation_one]; exact hψ
  simp only [metric, complementProjector, expectation_add,
    expectation_sub, expectation_smul, hu] at hs
  unfold geometricMeasurePure
  linarith

/-- An observable mean in the original complex matrix representation. -/
def observableMean {n d : ℕ}
    (ρ A : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ) : ℝ :=
  (trace (ρ * A)).re

private lemma trace_average {n d k : ℕ} (p : Fin k → ℝ)
    (ψ : Fin k → Word (Fin d) n → ℂ)
    (A : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ) :
    observableMean (∑ i, p i • rankOneDensity (ψ i)) A =
      ∑ i, p i * readout A (ψ i) := by
  classical
  unfold observableMean
  rw [trace_mul_comm]
  have ht := congrArg Complex.re
    (D5.S3.Zeros.CriticalPoints.RankOneTraceBound.trace_rank_one_sum
      (fun i => WithLp.toLp 2 (ψ i)) p (fun _ => 1) A)
  simpa only [mul_one, rankOneDensity, Complex.coe_smul,
    EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply,
    WithLp.ofLp_toLp, Complex.re_sum, Complex.re_ofReal_mul, readout,
    dotProduct_comm] using ht

/-- The full finite-metric supporting family applies to every actual density
state and the original finite-ensemble roof. Its proof uses nonempty roof and
overlap sets, and the all-cut biseparable inequality. -/
theorem metric_roof_bound {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hab : a ≤ b)
    (he : a⁻¹ + (d - 1 : ℝ) * b⁻¹ = d)
    (ρ : D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Word (Fin d) n)) :
    (1 - b) * observableMean (CStarMatrix.ofMatrix.symm ρ.1) (supportProjector n d) +
      (b - a) * observableMean (CStarMatrix.ofMatrix.symm ρ.1)
        (rankOneDensity (ghz n d)) ≤ geometricMeasure (CStarMatrix.ofMatrix.symm ρ.1) := by
  classical
  apply le_csInf (ensemble_values_nonempty ρ)
  rintro t ⟨k, p, ψ, hp, hs, hu, heρ, rfl⟩
  rw [heρ, trace_average, trace_average]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (pure_metric_lower hn hd ha ha1 hab he (ψ i) (hu i)) (hp i))
  convert h using 1
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private def metricA (d : ℕ) (t : ℝ) : ℝ := (t + d - 1) / (d * t)
private def metricB (d : ℕ) (t : ℝ) : ℝ := (t + d - 1) / d

private lemma metric_parameters {d : ℕ} (hd : 2 ≤ d) {t : ℝ} (ht : 1 ≤ t) :
    0 < metricA d t ∧ metricA d t ≤ 1 ∧ metricA d t ≤ metricB d t ∧
      (metricA d t)⁻¹ + (d - 1 : ℝ) * (metricB d t)⁻¹ = d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have ht0 : 0 < t := by linarith
  have hsum : 0 < t + d - 1 := by linarith
  have hdt : 0 < (d : ℝ) * t := mul_pos hd0 ht0
  refine ⟨div_pos hsum hdt, (div_le_one hdt).mpr ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.mpr hd0.le) (sub_nonneg.mpr ht)]
  · unfold metricA metricB
    rw [div_le_div_iff₀ hdt hd0]
    nlinarith [mul_nonneg (mul_nonneg hsum.le hd0.le) (sub_nonneg.mpr ht)]
  · unfold metricA metricB
    rw [inv_div, inv_div]
    field_simp
    <;> ring

/-- All finite supporting lines, parametrized without singular coefficients.
The endpoint where the two means coincide is obtained by their supremum. -/
theorem supporting_line {n d : ℕ} (hn : 2 ≤ n) (hd : 2 ≤ d)
    {t : ℝ} (ht : 1 ≤ t)
    (ρ : D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Word (Fin d) n)) :
    (observableMean (CStarMatrix.ofMatrix.symm ρ.1) (supportProjector n d) +
      (d - 2 : ℝ) * observableMean (CStarMatrix.ofMatrix.symm ρ.1)
        (rankOneDensity (ghz n d)) -
      t * (observableMean (CStarMatrix.ofMatrix.symm ρ.1) (supportProjector n d) -
        observableMean (CStarMatrix.ofMatrix.symm ρ.1) (rankOneDensity (ghz n d))) -
      (d - 1 : ℝ) * observableMean (CStarMatrix.ofMatrix.symm ρ.1)
        (rankOneDensity (ghz n d)) / t) / d ≤
      geometricMeasure (CStarMatrix.ofMatrix.symm ρ.1) := by
  obtain ⟨ha, ha1, hab, he⟩ := metric_parameters hd ht
  have h := metric_roof_bound hn (by omega) ha ha1 hab he ρ
  convert h using 1
  unfold metricA metricB
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht)
  field_simp
  <;> ring

private lemma mean_add {n d : ℕ}
    (ρ A B : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ) :
    observableMean ρ (A + B) = observableMean ρ A + observableMean ρ B := by
  simp [observableMean, mul_add, trace_add]

private lemma mean_sub {n d : ℕ}
    (ρ A B : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ) :
    observableMean ρ (A - B) = observableMean ρ A - observableMean ρ B := by
  simp [observableMean, mul_sub, trace_sub]

private lemma mean_smul {n d : ℕ} (r : ℝ)
    (ρ A : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ) :
    observableMean ρ (r • A) = r * observableMean ρ A := by
  simp [observableMean, Matrix.mul_smul, trace_smul, Complex.real_smul]

private lemma mean_one {n d : ℕ}
    (ρ : D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Word (Fin d) n)) :
    observableMean (CStarMatrix.ofMatrix.symm ρ.1) 1 = 1 := by
  have h : trace (CStarMatrix.ofMatrix.symm ρ.1) = 1 := ρ.2.2
  simpa [observableMean] using congrArg Complex.re h

/-- The universal analytic affine certificate, for every density operator,
in the original witness and complementary-projector readouts. -/
theorem affine_certificate {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    (ρ : D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Word (Fin d) n)) :
    -(d - 1 : ℝ) / (d * (d - 2)) *
        observableMean (CStarMatrix.ofMatrix.symm ρ.1) (witnessOp n d) +
      1 / ((d : ℝ)^2 * (d - 2)) *
        observableMean (CStarMatrix.ofMatrix.symm ρ.1) (complementProjector n d) -
      1 / ((d : ℝ)^2 * (d - 2)) ≤
        geometricMeasure (CStarMatrix.ofMatrix.symm ρ.1) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd2 : (d - 2 : ℝ) ≠ 0 := by linarith
  have hd1 : (d - 1 : ℝ) ≠ 0 := by linarith
  have ht : (1 : ℝ) ≤ (d - 1 : ℝ) / (d - 2) := by
    apply (le_div_iff₀ (by linarith)).mpr
    linarith
  have h := supporting_line (by omega : 2 ≤ n) (by omega : 2 ≤ d) ht ρ
  convert h using 1
  simp only [witnessOp, complementProjector, mean_sub, mean_smul, mean_one]
  field_simp [hd0, hd1, hd2]
  <;> ring

/-- The complete two-observable value, with its zero region retained. The
older `twoMeanValue` denotes only the radical branch. -/
def twoMeanOptimum (d : ℕ) (f y : ℝ) : ℝ :=
  if (d : ℝ) * f ≤ y then 0 else twoMeanValue d f y

private lemma supporting_envelope {d : ℕ} (hd : 2 ≤ d) {f y E : ℝ}
    (hf : 0 ≤ f) (hfy : f ≤ y) (hE : 0 ≤ E)
    (hline : ∀ t : ℝ, 1 ≤ t →
      (y + (d - 2 : ℝ) * f - t * (y - f) - (d - 1 : ℝ) * f / t) / d ≤ E) :
    twoMeanOptimum d f y ≤ E := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hdne : (d : ℝ) ≠ 0 := hdpos.ne'
  unfold twoMeanOptimum
  split_ifs with hlow
  · exact hE
  by_cases heq : f = y
  · subst y
    have hB : twoMeanValue d f f = (d - 1 : ℝ) * f / d := by
      simp only [twoMeanValue, sub_self, mul_zero, Real.sqrt_zero, sub_zero]
      ring
    rw [hB]
    let c : ℝ := (d - 1 : ℝ) * f / d
    change c ≤ E
    by_contra h
    have hδ : 0 < c - E := sub_pos.mpr (lt_of_not_ge h)
    have hc : 0 ≤ c := div_nonneg (mul_nonneg (by linarith) hf) hdpos.le
    let t : ℝ := 1 + c / (c - E)
    have ht : 1 ≤ t := by dsimp [t]; exact le_add_of_nonneg_right (div_nonneg hc hδ.le)
    have htpos : 0 < t := zero_lt_one.trans_le ht
    have hdt : (c - E) * t = (c - E) + c := by
      dsimp [t]
      field_simp
      <;> ring
    have hct : c / t < c - E := (div_lt_iff₀ htpos).mpr (by rw [hdt]; linarith)
    have hb := hline t ht
    have hform :
        (f + (d - 2 : ℝ) * f - t * (f - f) - (d - 1 : ℝ) * f / t) / d = c - c / t := by
      dsimp [c]
      field_simp
      <;> ring
    rw [hform] at hb
    linarith
  · have hlt : f < y := lt_of_le_of_ne hfy heq
    have hfpos : 0 < f := by nlinarith
    let X := Real.sqrt ((d - 1 : ℝ) * f)
    let Y := Real.sqrt (y - f)
    have hX : 0 < X := Real.sqrt_pos.mpr (mul_pos (by linarith) hfpos)
    have hY : 0 < Y := Real.sqrt_pos.mpr (sub_pos.mpr hlt)
    have hXs : X ^ 2 = (d - 1 : ℝ) * f := Real.sq_sqrt (mul_nonneg (by linarith) hf)
    have hYs : Y ^ 2 = y - f := Real.sq_sqrt (sub_nonneg.mpr hfy)
    have hXY : Y ≤ X := by nlinarith
    let t := X / Y
    have ht : 1 ≤ t := (le_div_iff₀ hY).mpr (by simpa using hXY)
    have hfirst : t * (y - f) = X * Y := by
      rw [← hYs]
      dsimp [t]
      field_simp
      <;> ring
    have hsecond : (d - 1 : ℝ) * f / t = X * Y := by
      rw [← hXs]
      dsimp [t]
      field_simp
      <;> ring
    have hroot : Real.sqrt ((d - 1 : ℝ) * f * (y - f)) = X * Y :=
      Real.sqrt_mul (mul_nonneg (by linarith) hf) _
    have hb := hline t ht
    rw [hfirst, hsecond] at hb
    unfold twoMeanValue
    rw [hroot]
    convert hb using 1 <;> ring

private lemma mean_positive {n d : ℕ}
    (ρ : D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Word (Fin d) n))
    (A : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ) (hA : A.PosSemidef) :
    0 ≤ observableMean (CStarMatrix.ofMatrix.symm ρ.1) A := by
  classical
  obtain ⟨_, k, p, ψ, hp, hs, hu, he, hv⟩ := ensemble_values_nonempty ρ
  rw [he, trace_average]
  exact Finset.sum_nonneg (fun i _ =>
    mul_nonneg (hp i) (RHLinalg.hermForm_nonneg_of_posSemidef hA (ψ i)))

/-- The measured means of every density state lie in the required triangle. -/
theorem means_triangle {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (ρ : D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Word (Fin d) n)) :
    0 ≤ observableMean (CStarMatrix.ofMatrix.symm ρ.1) (rankOneDensity (ghz n d)) ∧
    observableMean (CStarMatrix.ofMatrix.symm ρ.1) (rankOneDensity (ghz n d)) ≤
      observableMean (CStarMatrix.ofMatrix.symm ρ.1) (supportProjector n d) ∧
    observableMean (CStarMatrix.ofMatrix.symm ρ.1) (supportProjector n d) ≤ 1 := by
  have hf := mean_positive ρ _ (posSemidef_vecMulVec_self_star (ghz n d))
  have hfy := mean_positive ρ _ (orthogonal_positive hn hd).1
  have hy := mean_positive ρ _ (orthogonal_positive hn hd).2
  simp only [complementProjector, mean_sub, mean_one] at hfy hy
  exact ⟨hf, by linarith, by linarith⟩

/-- The universal two-mean lower bound in actual density and finite-ensemble
semantics, including both coincident means and the complete zero region. -/
theorem two_mean_lower {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    (ρ : D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Word (Fin d) n)) :
    twoMeanOptimum d
      (observableMean (CStarMatrix.ofMatrix.symm ρ.1) (rankOneDensity (ghz n d)))
      (observableMean (CStarMatrix.ofMatrix.symm ρ.1) (supportProjector n d)) ≤
      geometricMeasure (CStarMatrix.ofMatrix.symm ρ.1) := by
  obtain ⟨hf, hfy, _⟩ := means_triangle (by omega : 0 < n) (by omega : 0 < d) ρ
  exact supporting_envelope (by omega) hf hfy (density_measure_nonneg (by omega) (by omega) ρ)
    (fun t ht => supporting_line (by omega) (by omega) ht ρ)

private lemma pure_means_triangle {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (ψ : Word (Fin d) n → ℂ) (hψ : IsUnitState ψ) :
    0 ≤ readout (rankOneDensity (ghz n d)) ψ ∧
    readout (rankOneDensity (ghz n d)) ψ ≤ readout (supportProjector n d) ψ ∧
    readout (supportProjector n d) ψ ≤ 1 := by
  have hf := RHLinalg.hermForm_nonneg_of_posSemidef
    (posSemidef_vecMulVec_self_star (ghz n d)) ψ
  have hfy := RHLinalg.hermForm_nonneg_of_posSemidef (orthogonal_positive hn hd).1 ψ
  have hy := RHLinalg.hermForm_nonneg_of_posSemidef (orthogonal_positive hn hd).2 ψ
  change 0 ≤ readout (rankOneDensity (ghz n d)) ψ at hf
  change 0 ≤ readout (supportProjector n d - rankOneDensity (ghz n d)) ψ at hfy
  change 0 ≤ readout (complementProjector n d) ψ at hy
  have hu : readout 1 ψ = 1 := by rw [expectation_one]; exact hψ
  simp only [complementProjector, expectation_sub, hu] at hfy hy
  exact ⟨hf, by linarith, by linarith⟩

private lemma pure_supporting_line {n d : ℕ} (hn : 2 ≤ n) (hd : 2 ≤ d)
    {t : ℝ} (ht : 1 ≤ t) (ψ : Word (Fin d) n → ℂ) (hψ : IsUnitState ψ) :
    (readout (supportProjector n d) ψ + (d - 2 : ℝ) *
        readout (rankOneDensity (ghz n d)) ψ -
      t * (readout (supportProjector n d) ψ - readout (rankOneDensity (ghz n d)) ψ) -
      (d - 1 : ℝ) * readout (rankOneDensity (ghz n d)) ψ / t) / d ≤
      geometricMeasurePure ψ := by
  obtain ⟨ha, ha1, hab, he⟩ := metric_parameters hd ht
  have h := pure_metric_lower hn (by omega) ha ha1 hab he ψ hψ
  convert h using 1
  unfold metricA metricB
  field_simp
  <;> ring

/-- The same two-mean bound holds for every normalized pure vector and its
actual supremum over all biseparable cuts. -/
theorem pure_two_mean_lower {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    (ψ : Word (Fin d) n → ℂ) (hψ : IsUnitState ψ) :
    twoMeanOptimum d (readout (rankOneDensity (ghz n d)) ψ)
      (readout (supportProjector n d) ψ) ≤ geometricMeasurePure ψ := by
  obtain ⟨hf, hfy, _⟩ := pure_means_triangle (by omega : 0 < n) (by omega : 0 < d) ψ hψ
  exact supporting_envelope (by omega) hf hfy (pure_measure_bounds (by omega) (by omega) ψ hψ).1
    (fun t ht => pure_supporting_line (by omega) (by omega) ht ψ hψ)

private lemma biseparable_measure_zero {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    (φ : Word (Fin d) n → ℂ) (hφ : IsBiseparable φ) : geometricMeasurePure φ = 0 := by
  have hu : star φ ⬝ᵥ φ = 1 :=
    (D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.unit_norm_iff φ).mpr hφ.1
  have hself : (1 : ℝ) ∈ {t : ℝ | ∃ ψ, IsBiseparable ψ ∧
      t = Complex.normSq (star ψ ⬝ᵥ φ)} := by
    refine ⟨φ, hφ, ?_⟩
    simp [hu]
  have hl := le_csSup (overlap_values_bdd φ hφ.1) hself
  have hz := (pure_measure_bounds hn hd φ hφ.1).1
  unfold geometricMeasurePure at *
  linarith

/-- A finite normalized family is an actual competitor in the original roof,
with any finite index type, by explicit reindexing to `Fin`. -/
theorem finite_ensemble_upper {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    {ι : Type*} [Fintype ι] (p : ι → ℝ) (ψ : ι → Word (Fin d) n → ℂ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (hu : ∀ i, IsUnitState (ψ i)) :
    geometricMeasure (∑ i, p i • rankOneDensity (ψ i)) ≤
      ∑ i, p i * geometricMeasurePure (ψ i) := by
  classical
  let e := (Fintype.equivFin ι).symm
  apply csInf_le (ensemble_values_bdd hn hd _)
  refine ⟨Fintype.card ι, p ∘ e, ψ ∘ e, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => hp (e i)
  · simpa only [Function.comp_apply, Equiv.sum_comp] using hs
  · exact fun i => hu (e i)
  · exact (Equiv.sum_comp e (fun i => p i • rankOneDensity (ψ i))).symm
  · exact (Equiv.sum_comp e (fun i => p i * geometricMeasurePure (ψ i))).symm

private lemma trace_rank_one {n d : ℕ} (ψ : Word (Fin d) n → ℂ) :
    trace (rankOneDensity ψ) = ((∑ x, Complex.normSq (ψ x) : ℝ) : ℂ) := by
  simpa only [rankOneDensity, trace_vecMulVec, dotProduct_comm, Complex.normSq_eq_norm_sq] using
    D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays.dot_star_self ψ

/-- The density operator represented by a concrete normalized finite ensemble. -/
def ensembleDensity {n d : ℕ} {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (ψ : ι → Word (Fin d) n → ℂ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (hu : ∀ i, IsUnitState (ψ i)) :
    D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Word (Fin d) n) := by
  classical
  refine ⟨CStarMatrix.ofMatrix (∑ i, p i • rankOneDensity (ψ i)), ?_, ?_⟩
  · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    exact Finset.sum_nonneg (fun i _ =>
      ((posSemidef_vecMulVec_self_star (ψ i)).smul (hp i)).nonneg)
  · change trace (∑ i, p i • rankOneDensity (ψ i)) = 1
    have hu' : ∀ i, ∑ x, Complex.normSq (ψ i x) = 1 := hu
    simp only [trace_sum, trace_smul, trace_rank_one, hu', Complex.real_smul,
      mul_one, ← Complex.ofReal_sum, hs, Complex.ofReal_one]

/-- A concrete biseparable finite ensemble has zero actual convex roof. -/
theorem biseparable_ensemble_zero {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    {ι : Type*} [Fintype ι] (p : ι → ℝ) (φ : ι → Word (Fin d) n → ℂ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (hφ : ∀ i, IsBiseparable (φ i)) :
    geometricMeasure (∑ i, p i • rankOneDensity (φ i)) = 0 := by
  have hl := density_measure_nonneg hn hd (ensembleDensity p φ hp hs (fun i => (hφ i).1))
  have hh := finite_ensemble_upper hn hd p φ hp hs (fun i => (hφ i).1)
  simp only [biseparable_measure_zero hn hd _ (hφ _), mul_zero, Finset.sum_const_zero] at hh
  exact le_antisymm hh hl

/-- A vector supported on constant computational words, with specified amplitudes. -/
def constantVector {n d : ℕ} (hn : 0 < n) (c : Fin d → ℂ) : Word (Fin d) n → ℂ := by
  classical
  exact fun x => if ∀ i, x i = x ⟨0, hn⟩ then c (x ⟨0, hn⟩) else 0

private lemma constantVector_apply {n d : ℕ} (hn : 0 < n) (c : Fin d → ℂ)
    (j : Fin d) : constantVector hn c (fun _ => j) = c j := by
  simp [constantVector]

private lemma constantVector_off {n d : ℕ} (hn : 0 < n) (c : Fin d → ℂ)
    (x : Word (Fin d) n) (hx : ¬ ∃ j : Fin d, ∀ i, x i = j) : constantVector hn c x = 0 := by
  have h : ¬ ∀ i, x i = x ⟨0, hn⟩ := by
    intro h; exact hx ⟨_, h⟩
  simp [constantVector, h]

private lemma constantVector_norm {n d : ℕ} (hn : 0 < n) (c : Fin d → ℂ) :
    ∑ x, Complex.normSq (constantVector hn c x) = ∑ j, Complex.normSq (c j) := by
  rw [sum_supported_constants hn _ (by
    intro x hx; rw [constantVector_off hn c x hx]; exact Complex.normSq_zero)]
  simp only [constantVector_apply]

private lemma constantVector_support {n d : ℕ} (hn : 0 < n) (c : Fin d → ℂ) :
    readout (supportProjector n d) (constantVector hn c) = ∑ j, Complex.normSq (c j) := by
  rw [support_expectation, Finset.sum_filter]
  rw [sum_supported_constants hn _ (by
    intro x hx; rw [constantVector_off hn c x hx]; simp)]
  apply Finset.sum_congr rfl
  intro j hj
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  simp [constantVector_apply, Finset.image_const]

private lemma basis_overlap {n d : ℕ} (x : Word (Fin d) n) (ψ : Word (Fin d) n → ℂ) :
    Complex.normSq (star (Pi.single x (1 : ℂ)) ⬝ᵥ ψ) = Complex.normSq (ψ x) := by
  classical
  simp [dotProduct, Pi.single_apply, Pi.star_apply]

private lemma constantVector_ghz {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (c : Fin d → ℂ) :
    readout (rankOneDensity (ghz n d)) (constantVector hn c) =
      Complex.normSq (∑ j, c j) / d := by
  have h := ghz_expectation hn hd (constantVector hn c)
  simp only [constantVector_apply] at h
  exact (eq_div_iff (by exact_mod_cast hd.ne')).mpr (by linarith)

/-- The distinguished source vector has one amplitude `α` and `d-1` amplitudes `β`. -/
def chiVector {n d : ℕ} (hn : 0 < n) (j : Fin d) (α β : ℝ) : Word (Fin d) n → ℂ :=
  constantVector hn (fun i => if i = j then (α : ℂ) else (β : ℂ))

private lemma chi_norm {n d : ℕ} (hn : 0 < n) (j : Fin d) (α β : ℝ) :
    ∑ x, Complex.normSq (chiVector hn j α β x) = α^2 + (d - 1 : ℝ) * β^2 := by
  classical
  rw [chiVector, constantVector_norm]
  simp only [apply_ite Complex.normSq, Complex.normSq_ofReal, ← pow_two]
  calc
    (∑ i : Fin d, if i = j then α^2 else β^2) =
        ∑ i : Fin d, (β^2 + if i = j then α^2 - β^2 else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> ring
    _ = α^2 + (d - 1 : ℝ) * β^2 := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring

/-- Source amplitudes, expressed with a single nonnegative cross radical. -/
def optimalAlpha (d : ℕ) (F : ℝ) : ℝ :=
  (Real.sqrt F + Real.sqrt ((d - 1 : ℝ) * (1 - F))) / Real.sqrt d

def optimalBeta (d : ℕ) (F : ℝ) : ℝ :=
  (Real.sqrt F - Real.sqrt ((d - 1 : ℝ) * (1 - F)) / (d - 1 : ℝ)) / Real.sqrt d

private lemma optimal_amplitudes {d : ℕ} (hd : 2 ≤ d) {F : ℝ}
    (hF : 1 / (d : ℝ) ≤ F) (hF1 : F ≤ 1) :
    0 ≤ optimalBeta d F ∧ optimalBeta d F ≤ optimalAlpha d F ∧
      (optimalAlpha d F)^2 + (d - 1 : ℝ) * (optimalBeta d F)^2 = 1 ∧
      (optimalAlpha d F + (d - 1 : ℝ) * optimalBeta d F)^2 / d = F ∧
      twoMeanValue d F 1 = 1 - (optimalAlpha d F)^2 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hd1 : 0 < (d - 1 : ℝ) := by linarith
  have hf0 : 0 ≤ F := (one_div_nonneg.mpr hdpos.le).trans hF
  have hcross : 0 ≤ (d - 1 : ℝ) * (1 - F) := mul_nonneg hd1.le (sub_nonneg.mpr hF1)
  have hS := Real.sq_sqrt hf0
  have hC := Real.sq_sqrt hcross
  have hD := Real.sq_sqrt hdpos.le
  have hDpos := Real.sqrt_pos.mpr hdpos
  have hbeta : Real.sqrt ((d - 1 : ℝ) * (1 - F)) / (d - 1 : ℝ) ≤ Real.sqrt F := by
    apply (div_le_iff₀ hd1).mpr
    have hm : 1 ≤ (d : ℝ) * F := by simpa only [mul_comm] using (div_le_iff₀ hdpos).mp hF
    have hs0 := Real.sqrt_nonneg F
    have hc0 := Real.sqrt_nonneg ((d - 1 : ℝ) * (1 - F))
    have hsquare : (Real.sqrt F * (d - 1 : ℝ))^2 -
        (Real.sqrt ((d - 1 : ℝ) * (1 - F)))^2 = (d - 1 : ℝ) * ((d : ℝ) * F - 1) := by
      rw [mul_pow, hS, hC]
      ring
    apply (sq_le_sq₀ hc0 (mul_nonneg hs0 hd1.le)).mp
    apply sub_nonneg.mp
    rw [hsquare]
    exact mul_nonneg hd1.le (sub_nonneg.mpr hm)
  refine ⟨div_nonneg (sub_nonneg.mpr hbeta) hDpos.le, ?_, ?_, ?_, ?_⟩
  · unfold optimalBeta optimalAlpha
    apply div_le_div_of_nonneg_right _ hDpos.le
    have hc := Real.sqrt_nonneg ((d - 1 : ℝ) * (1 - F))
    have hq := div_nonneg hc hd1.le
    linarith
  · unfold optimalAlpha optimalBeta
    field_simp [hdpos.ne', hd1.ne', hDpos.ne']
    linear_combination (d : ℝ) * (d - 1) * hS + (d : ℝ) * hC - (d - 1 : ℝ) * hD
  · unfold optimalAlpha optimalBeta
    field_simp [hdpos.ne', hd1.ne', hDpos.ne']
    linear_combination (d : ℝ)^2 * hS - (d : ℝ) * F * hD
  · unfold twoMeanValue optimalAlpha
    have hmul : Real.sqrt ((d - 1 : ℝ) * F * (1 - F)) =
        Real.sqrt F * Real.sqrt ((d - 1 : ℝ) * (1 - F)) := by
      rw [← Real.sqrt_mul hf0]
      congr 1
      ring
    rw [hmul]
    field_simp [hdpos.ne', hd1.ne', hDpos.ne']
    <;> nlinarith

/-- The original single-witness conjugate with an arbitrary feasible mean. -/
def epsilonWitness (n d : ℕ) (w : ℝ) : ℝ :=
  sSup {t : ℝ | ∃ r : ℝ, t = r * w - hatE n d r}

private lemma epsilonO_bridge (n d : ℕ) (p : ℝ) :
    epsilonO n d p = epsilonWitness n d (witnessValue n d p) := rfl

private lemma witness_pure_bounds {n d : ℕ} (hn : 0 < n) (hd : 1 ≤ d)
    (ψ : Word (Fin d) n → ℂ) (hψ : IsUnitState ψ) :
    -(1 : ℝ) ≤ readout (witnessOp n d) ψ ∧ readout (witnessOp n d) ψ ≤ 1 := by
  obtain ⟨hf, hfy, hy⟩ := pure_means_triangle hn (by omega) ψ hψ
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : 0 ≤ 1 / (d : ℝ) := one_div_nonneg.mpr (by linarith)
  have hden1 : 1 / (d : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr hdR
  simp only [witnessOp, expectation_sub, expectation_smul]
  have hprod := mul_le_mul_of_nonneg_left hy hden
  have hy0 : 0 ≤ readout (supportProjector n d) ψ := hf.trans hfy
  have hz := mul_nonneg hden hy0
  constructor <;> nlinarith

private lemma hat_values_nonempty {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d) (r : ℝ) :
    {t : ℝ | ∃ ψ φ, IsUnitState ψ ∧ IsBiseparable φ ∧
      t = readout (r • witnessOp n d + rankOneDensity φ) ψ - 1}.Nonempty := by
  let φ : Word (Fin d) n → ℂ := Pi.single (fun _ => (⟨0, hd⟩ : Fin d)) (1 : ℂ)
  exact ⟨_, φ, φ, basis_unit _, computational_biseparable hn _, rfl⟩

private lemma hat_values_bdd {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d) (r : ℝ) :
    BddAbove {t : ℝ | ∃ ψ φ, IsUnitState ψ ∧ IsBiseparable φ ∧
      t = readout (r • witnessOp n d + rankOneDensity φ) ψ - 1} := by
  refine ⟨|r|, ?_⟩
  rintro t ⟨ψ, φ, hψ, hφ, rfl⟩
  obtain ⟨hw0, hw1⟩ := witness_pure_bounds (by omega : 0 < n) (by omega : 1 ≤ d) ψ hψ
  have habs : |readout (witnessOp n d) ψ| ≤ 1 := abs_le.mpr ⟨hw0, hw1⟩
  have hmul : r * readout (witnessOp n d) ψ ≤ |r| := by
    calc
      _ ≤ |r * readout (witnessOp n d) ψ| := le_abs_self _
      _ = |r| * |readout (witnessOp n d) ψ| := abs_mul _ _
      _ ≤ |r| := by nlinarith [mul_le_mul_of_nonneg_left habs (abs_nonneg r)]
  have hov := cs φ ψ
  rw [hφ.1, hψ, mul_one] at hov
  simp only [expectation_add, expectation_smul, expectation_rank_one]
  linarith

private lemma pure_conjugate_bound {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    (r : ℝ) (ψ : Word (Fin d) n → ℂ) (hψ : IsUnitState ψ) :
    r * readout (witnessOp n d) ψ - hatE n d r ≤ geometricMeasurePure ψ := by
  have hs : sSup {t : ℝ | ∃ φ, IsBiseparable φ ∧
      t = Complex.normSq (star φ ⬝ᵥ ψ)} ≤ 1 + hatE n d r - r * readout (witnessOp n d) ψ := by
    apply csSup_le (overlap_values_nonempty hn hd ψ)
    rintro t ⟨φ, hφ, rfl⟩
    have h := le_csSup (hat_values_bdd hn hd r)
      (show readout (r • witnessOp n d + rankOneDensity φ) ψ - 1 ∈
        {t : ℝ | ∃ ψ φ, IsUnitState ψ ∧ IsBiseparable φ ∧
          t = readout (r • witnessOp n d + rankOneDensity φ) ψ - 1} from
        ⟨ψ, φ, hψ, hφ, rfl⟩)
    change _ ≤ hatE n d r at h
    simp only [expectation_add, expectation_smul, expectation_rank_one] at h
    linarith
  unfold geometricMeasurePure
  linarith

private lemma hat_zero {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d) : hatE n d 0 = 0 := by
  apply le_antisymm
  · apply csSup_le (hat_values_nonempty hn hd 0)
    rintro t ⟨ψ, φ, hψ, hφ, rfl⟩
    have hov := cs φ ψ
    rw [hφ.1, hψ, mul_one] at hov
    simp only [zero_smul, zero_add, expectation_rank_one]
    linarith
  · let φ : Word (Fin d) n → ℂ := Pi.single (fun _ => (⟨0, hd⟩ : Fin d)) (1 : ℂ)
    have hφ := computational_biseparable hn (fun _ => (⟨0, hd⟩ : Fin d))
    have hu : star φ ⬝ᵥ φ = 1 :=
      (D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.unit_norm_iff φ).mpr hφ.1
    apply le_csSup (hat_values_bdd hn hd 0)
    refine ⟨φ, φ, hφ.1, hφ, ?_⟩
    simp [zero_smul, expectation_rank_one, hu]

private lemma conjugate_ensemble_bound {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    {ι : Type*} [Fintype ι] (p : ι → ℝ) (ψ : ι → Word (Fin d) n → ℂ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (hu : ∀ i, IsUnitState (ψ i)) (r : ℝ) :
    r * (∑ i, p i * readout (witnessOp n d) (ψ i)) - hatE n d r ≤
      ∑ i, p i * geometricMeasurePure (ψ i) := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (pure_conjugate_bound hn hd r (ψ i) (hu i)) (hp i))
  convert h using 1
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hs]
  simp only [one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

private lemma sum_distinguished {d : ℕ} {R : Type*} [CommRing R]
    (j : Fin d) (a b : R) : (∑ i : Fin d, if i = j then a else b) = a + (d - 1 : R) * b := by
  classical
  calc
    _ = ∑ i : Fin d, (b + if i = j then a - b else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring

/-- The canonical source pure vector really has the stated norm, two means,
and all-cut entanglement, including F=1/d and F=1. -/
theorem chi_attainment {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    (j : Fin d) {F : ℝ} (hF : 1 / (d : ℝ) ≤ F) (hF1 : F ≤ 1) :
    IsUnitState (chiVector (by omega : 0 < n) j (optimalAlpha d F) (optimalBeta d F)) ∧
      readout (supportProjector n d)
        (chiVector (by omega : 0 < n) j (optimalAlpha d F) (optimalBeta d F)) = 1 ∧
      readout (rankOneDensity (ghz n d))
        (chiVector (by omega : 0 < n) j (optimalAlpha d F) (optimalBeta d F)) = F ∧
      geometricMeasurePure (chiVector (by omega : 0 < n) j (optimalAlpha d F) (optimalBeta d F)) =
        twoMeanOptimum d F 1 := by
  classical
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hb, hba, hnorm, hmean, hvalue⟩ := optimal_amplitudes (by omega : 2 ≤ d) hF hF1
  let ψ := chiVector (by omega : 0 < n) j (optimalAlpha d F) (optimalBeta d F)
  have hψ : IsUnitState ψ := by
    change ∑ x, Complex.normSq (chiVector _ _ _ _ x) = 1
    rw [chi_norm, hnorm]
  have hy : readout (supportProjector n d) ψ = 1 := by
    change readout (supportProjector n d) (constantVector _ _) = 1
    rw [constantVector_support]
    have hnorm' := chi_norm (by omega : 0 < n) j (optimalAlpha d F) (optimalBeta d F)
    rw [chiVector, constantVector_norm] at hnorm'
    exact hnorm'.trans hnorm
  have hf : readout (rankOneDensity (ghz n d)) ψ = F := by
    change readout (rankOneDensity (ghz n d)) (constantVector _ _) = F
    rw [constantVector_ghz (by omega) (by omega), sum_distinguished]
    have he : (optimalAlpha d F : ℂ) + (d - 1 : ℂ) * optimalBeta d F =
        ((optimalAlpha d F + (d - 1 : ℝ) * optimalBeta d F : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.normSq_ofReal]
    simpa only [pow_two] using hmean
  have hl := pure_two_mean_lower hn hd ψ hψ
  rw [hf, hy] at hl
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
        rw [he, Real.sqrt_sq (div_nonneg (by linarith) (by linarith))]
        rw [hFeq]
        field_simp
        <;> ring
      linarith
    · exact hvalue
  have hupper : geometricMeasurePure ψ ≤ 1 - (optimalAlpha d F)^2 := by
    have hs := le_csSup (overlap_values_bdd ψ hψ)
      (show Complex.normSq (star (Pi.single (fun _ => j) (1 : ℂ)) ⬝ᵥ ψ) ∈
        {t : ℝ | ∃ φ, IsBiseparable φ ∧ t = Complex.normSq (star φ ⬝ᵥ ψ)} from
        ⟨_, computational_biseparable (by omega) _, rfl⟩)
    rw [basis_overlap] at hs
    have hc : ψ (fun _ => j) = (optimalAlpha d F : ℂ) := by
      simp [ψ, chiVector, constantVector_apply]
    rw [hc, Complex.normSq_ofReal] at hs
    unfold geometricMeasurePure
    nlinarith
  exact ⟨hψ, hy, hf, le_antisymm (hupper.trans_eq hβ.symm) hl⟩

private lemma basis_readout {n d : ℕ} (x : Word (Fin d) n)
    (A : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ) :
    readout A (Pi.single x 1) = (A x x).re := by
  classical
  simp [readout, dotProduct, mulVec, Pi.single_apply, Pi.star_apply]

private lemma basis_support_mean {n d : ℕ} (x : Word (Fin d) n) :
    readout (supportProjector n d) (Pi.single x 1) =
      if (Finset.univ.image x).card ≤ 2 then 1 else 0 := by
  classical
  rw [basis_readout]
  by_cases h : (Finset.univ.image x).card ≤ 2 <;> simp [supportProjector, h]

private lemma basis_ghz_mean {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (x : Word (Fin d) n) :
    readout (rankOneDensity (ghz n d)) (Pi.single x 1) =
      if ∃ j : Fin d, ∀ i, x i = j then 1 / (d : ℝ) else 0 := by
  classical
  rw [expectation_rank_one,
    D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.normSq_overlap_comm,
    basis_overlap]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  split_ifs with h
  · simp [ghz, h, Complex.normSq_ofReal, Real.sq_sqrt (Nat.cast_nonneg d), hdR]
  · simp [ghz, h]

/-- The source computational Q-vector |0,1,2,0,...>. -/
def qWord {n d : ℕ} (hd : 3 ≤ d) : Word (Fin d) n :=
  fun k => if k.val = 1 then ⟨1, by omega⟩ else if k.val = 2 then ⟨2, by omega⟩ else ⟨0, by omega⟩

/-- A nonconstant two-symbol computational product word. -/
def twoSymbolWord {n d : ℕ} (hd : 2 ≤ d) : Word (Fin d) n :=
  fun k => if k.val = 0 then ⟨0, by omega⟩ else ⟨1, by omega⟩

private lemma qWord_outside {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    ¬ (Finset.univ.image (qWord (n := n) hd)).card ≤ 2 := by
  classical
  let s : Finset (Fin d) := {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩}
  have hs : s.card = 3 := by simp [s, Fin.ext_iff]
  have hsub : s ⊆ Finset.univ.image (qWord (n := n) hd) := by
    intro x hx
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, by simp [qWord]⟩
    · exact Finset.mem_image.mpr ⟨⟨1, by omega⟩, Finset.mem_univ _, by simp [qWord]⟩
    · exact Finset.mem_image.mpr ⟨⟨2, by omega⟩, Finset.mem_univ _, by simp [qWord]⟩
  have h := Finset.card_le_card hsub
  omega

private lemma qWord_nonconstant {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    ¬ ∃ j : Fin d, ∀ i, qWord (n := n) hd i = j := by
  rintro ⟨j, hj⟩
  have h := (hj ⟨0, by omega⟩).trans (hj ⟨1, by omega⟩).symm
  have hh := congrArg Fin.val h
  norm_num [qWord] at hh

private lemma twoSymbolWord_data {n d : ℕ} (hn : 2 ≤ n) (hd : 2 ≤ d) :
    (Finset.univ.image (twoSymbolWord (n := n) hd)).card ≤ 2 ∧
      ¬ ∃ j : Fin d, ∀ i, twoSymbolWord (n := n) hd i = j := by
  classical
  constructor
  · have hsub : Finset.univ.image (twoSymbolWord (n := n) hd) ⊆
        {⟨0, by omega⟩, ⟨1, by omega⟩} := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      simp only [twoSymbolWord]
      split_ifs <;> simp
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · rintro ⟨j, hj⟩
    have h := (hj ⟨0, by omega⟩).trans (hj ⟨1, by omega⟩).symm
    have hh := congrArg Fin.val h
    norm_num [twoSymbolWord] at hh

private lemma twoMean_scaling {d : ℕ} {f y : ℝ} (hy : 0 < y) :
    twoMeanOptimum d f y = y * twoMeanOptimum d (f / y) 1 := by
  have he : (d : ℝ) * (f / y) ≤ 1 ↔ (d : ℝ) * f ≤ y := by
    rw [← mul_div_assoc, div_le_one hy]
  unfold twoMeanOptimum
  simp only [he]
  by_cases h : (d : ℝ) * f ≤ y
  · simp [h]
  · simp only [h, ite_false]
    unfold twoMeanValue
    have hrad : (d - 1 : ℝ) * f * (y - f) =
        y^2 * ((d - 1 : ℝ) * (f / y) * (1 - f / y)) := by
      field_simp
      <;> ring
    rw [hrad, Real.sqrt_mul (sq_nonneg y), Real.sqrt_sq hy.le]
    field_simp
    <;> ring

/-- The means W,Q and the means G,P determine one another on every density state. -/
theorem observable_correspondence {n d : ℕ}
    (ρ : D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Word (Fin d) n)) :
    observableMean (CStarMatrix.ofMatrix.symm ρ.1) (supportProjector n d) =
      1 - observableMean (CStarMatrix.ofMatrix.symm ρ.1) (complementProjector n d) ∧
    observableMean (CStarMatrix.ofMatrix.symm ρ.1) (rankOneDensity (ghz n d)) =
      (1 - observableMean (CStarMatrix.ofMatrix.symm ρ.1) (complementProjector n d)) / d -
        observableMean (CStarMatrix.ofMatrix.symm ρ.1) (witnessOp n d) := by
  simp only [complementProjector, witnessOp, mean_sub, mean_smul, mean_one]
  constructor <;> ring

/-- The three weights of a concrete optimizer for every feasible pair of means. -/
def twoMeanWeights (d : ℕ) (f y : ℝ) : Fin 3 → ℝ := by
  classical
  exact if (d : ℝ) * f ≤ y then ![(d : ℝ) * f, y - (d : ℝ) * f, 1 - y] else ![y, 1 - y, 0]

/-- The actual computational or constant-sector vectors in the optimizer. -/
def twoMeanStates {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) (f y : ℝ) :
    Fin 3 → Word (Fin d) n → ℂ := by
  classical
  exact if (d : ℝ) * f ≤ y then
    ![Pi.single (fun _ => (⟨0, by omega⟩ : Fin d)) 1,
      Pi.single (twoSymbolWord (show 2 ≤ d by omega)) 1, Pi.single (qWord hd) 1]
  else ![chiVector (show 0 < n by omega) ⟨0, by omega⟩ (optimalAlpha d (f / y)) (optimalBeta d (f / y)),
    Pi.single (qWord hd) 1, Pi.single (qWord hd) 1]

private lemma two_mean_ensemble_data {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {f y : ℝ} (hf : 0 ≤ f) (hfy : f ≤ y) (hy : y ≤ 1) :
    (∀ i, 0 ≤ twoMeanWeights d f y i) ∧ (∑ i, twoMeanWeights d f y i) = 1 ∧
      (∀ i, IsUnitState (twoMeanStates hn hd f y i)) ∧
      (∑ i, twoMeanWeights d f y i * readout (rankOneDensity (ghz n d))
        (twoMeanStates hn hd f y i)) = f ∧
      (∑ i, twoMeanWeights d f y i * readout (supportProjector n d)
        (twoMeanStates hn hd f y i)) = y ∧
      (∑ i, twoMeanWeights d f y i * geometricMeasurePure (twoMeanStates hn hd f y i)) =
        twoMeanOptimum d f y := by
  classical
  have hn0 : 0 < n := by omega
  have hd0 : 0 < d := by omega
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  let j : Fin d := ⟨0, by omega⟩
  have hcG : readout (rankOneDensity (ghz n d)) (Pi.single (fun _ => j) 1) = 1 / d := by
    rw [basis_ghz_mean hn0 hd0]
    simp only [exists_const, forall_const, dite_true, ite_true]
    simp
  have hcP : readout (supportProjector n d) (Pi.single (fun _ => j) 1) = 1 := by
    rw [basis_support_mean]
    haveI : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
    simp [Finset.image_const]
  obtain ⟨h2P, h2c⟩ := twoSymbolWord_data (by omega : 2 ≤ n) (by omega : 2 ≤ d)
  have h2G : readout (rankOneDensity (ghz n d))
      (Pi.single (twoSymbolWord (n := n) (show 2 ≤ d by omega)) 1) = 0 := by
    rw [basis_ghz_mean hn0 hd0]
    simp [h2c]
  have h2P' : readout (supportProjector n d)
      (Pi.single (twoSymbolWord (n := n) (show 2 ≤ d by omega)) 1) = 1 := by
    rw [basis_support_mean]; simp [h2P]
  have hqG : readout (rankOneDensity (ghz n d)) (Pi.single (qWord (n := n) hd) 1) = 0 := by
    rw [basis_ghz_mean hn0 hd0]; simp [qWord_nonconstant hn hd]
  have hqP : readout (supportProjector n d) (Pi.single (qWord (n := n) hd) 1) = 0 := by
    rw [basis_support_mean]; simp [qWord_outside hn hd]
  have hzero (w : Word (Fin d) n) : geometricMeasurePure (Pi.single w 1) = 0 :=
    biseparable_measure_zero (by omega) hd0 _ (computational_biseparable (by omega) w)
  by_cases hlow : (d : ℝ) * f ≤ y
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simp only [twoMeanWeights, hlow, ite_true, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_fin_one] <;> nlinarith
    · simp [twoMeanWeights, hlow, Fin.sum_univ_succ]; ring
    · intro i; fin_cases i <;> simp only [twoMeanStates, hlow, ite_true, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_fin_one] <;> apply basis_unit
    · simp only [twoMeanWeights, twoMeanStates, hlow, ite_true, Fin.sum_univ_succ,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Fin.sum_univ_zero,
        add_zero, hcG, h2G, hqG, mul_zero]
      field_simp
    · simp [twoMeanWeights, twoMeanStates, hlow, Fin.sum_univ_succ, hcP, h2P', hqP]
    · simp [twoMeanWeights, twoMeanStates, hlow, Fin.sum_univ_succ, hzero, twoMeanOptimum]
  · have hy0 : 0 < y := by nlinarith
    have hF0 : 1 / (d : ℝ) ≤ f / y := by
      apply (div_le_div_iff₀ (by linarith) hy0).mpr
      nlinarith
    have hF1 : f / y ≤ 1 := (div_le_one hy0).mpr hfy
    obtain ⟨hunit, hP, hG, hE⟩ := chi_attainment hn hd j hF0 hF1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simp [twoMeanWeights, hlow] <;> linarith
    · simp [twoMeanWeights, hlow, Fin.sum_univ_succ]
    · intro i; fin_cases i
      · simpa only [twoMeanStates, hlow, ite_false, Matrix.cons_val_zero] using hunit
      · simp only [twoMeanStates, hlow, ite_false, Matrix.cons_val_one]; apply basis_unit
      · simp only [twoMeanStates, hlow, ite_false, Matrix.cons_val_fin_one]; apply basis_unit
    · simp only [twoMeanWeights, twoMeanStates, hlow, ite_false, Fin.sum_univ_succ,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Fin.sum_univ_zero,
        add_zero, hG, hqG, mul_zero, zero_mul]
      field_simp
    · simp [twoMeanWeights, twoMeanStates, hlow, Fin.sum_univ_succ, hP, hqP]
    · simp only [twoMeanWeights, twoMeanStates, hlow, ite_false, Fin.sum_univ_succ,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Fin.sum_univ_zero,
        add_zero, hE, hzero, mul_zero, zero_mul]
      exact (twoMean_scaling hy0).symm

/-- Every feasible pair of means is realized by an actual density operator
and the explicit finite normalized ensemble above, with roof equal to the
universal lower bound. This is an attained all-state minimum. -/
theorem two_mean_attainment {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {f y : ℝ} (hf : 0 ≤ f) (hfy : f ≤ y) (hy : y ≤ 1) :
    ∃ σ : D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Word (Fin d) n),
      CStarMatrix.ofMatrix.symm σ.1 = ∑ i, twoMeanWeights d f y i •
        rankOneDensity (twoMeanStates hn hd f y i) ∧
      observableMean (CStarMatrix.ofMatrix.symm σ.1) (rankOneDensity (ghz n d)) = f ∧
      observableMean (CStarMatrix.ofMatrix.symm σ.1) (supportProjector n d) = y ∧
      geometricMeasure (CStarMatrix.ofMatrix.symm σ.1) = twoMeanOptimum d f y ∧
      (∀ i, 0 ≤ twoMeanWeights d f y i) ∧ (∑ i, twoMeanWeights d f y i) = 1 ∧
      (∀ i, IsUnitState (twoMeanStates hn hd f y i)) ∧
      (∑ i, twoMeanWeights d f y i * geometricMeasurePure (twoMeanStates hn hd f y i)) =
        twoMeanOptimum d f y := by
  obtain ⟨hp, hs, hu, hG, hP, hE⟩ := two_mean_ensemble_data hn hd hf hfy hy
  let σ := ensembleDensity (twoMeanWeights d f y) (twoMeanStates hn hd f y) hp hs hu
  have he : CStarMatrix.ofMatrix.symm σ.1 = ∑ i, twoMeanWeights d f y i •
      rankOneDensity (twoMeanStates hn hd f y i) := rfl
  have hfσ : observableMean (CStarMatrix.ofMatrix.symm σ.1) (rankOneDensity (ghz n d)) = f := by
    rw [he, trace_average]; exact hG
  have hyσ : observableMean (CStarMatrix.ofMatrix.symm σ.1) (supportProjector n d) = y := by
    rw [he, trace_average]; exact hP
  refine ⟨σ, he, hfσ, hyσ, ?_, hp, hs, hu, hE⟩
  apply le_antisymm
  · rw [he]
    exact (finite_ensemble_upper (by omega) (by omega) _ _ hp hs hu).trans_eq hE
  · have h := two_mean_lower hn hd σ
    rwa [hfσ, hyσ] at h

end
end D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof
