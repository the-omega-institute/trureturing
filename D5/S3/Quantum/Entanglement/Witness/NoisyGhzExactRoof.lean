/- GID: D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Attained actual noisy-GHZ finite roofs, two-mean optima and strict witness gaps. -/

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Tactic
import D5.S3.Quantum.Entanglement.Witness.NoisyGhzWitnessBoundGap

/-! The complete noisy-GHZ result uses the original complex matrices,
    arbitrary-cut biseparable pure states and actual finite-ensemble roof.
    Universal density bounds and attained two-mean optima are joined to full
    finite matrix reconstructions in both noise regimes. The original hatE
    conjugate supplies the single-witness optimum and its strict gaps.

    Scientific source: Haobo Ma, then Wenlin Zhang; CC BY 4.0. The scalar and
    multiple-observable antecedents of Xu et al. are retained. No priority
    claim is made. The released phase wording is resolved by characters on
    independent (Fin d → ZMod 3) coordinates, with no scalar-difference
    shortcut. The literal all-real-slope antecedent formula is not used.
    The d=2 operator identity is preserved separately from the d≥3 roof. -/

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
    exact if_pos ⟨j, fun _ => rfl⟩
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
  dsimp [j] at hcG hcP
  by_cases hlow : (d : ℝ) * f ≤ y
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num [twoMeanWeights, hlow] <;> nlinarith
    · simp [twoMeanWeights, hlow, Fin.sum_univ_succ] <;> ring
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
    dsimp [j] at hunit hP hG hE
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simp [twoMeanWeights, hlow] <;> linarith
    · simp [twoMeanWeights, hlow, Fin.sum_univ_succ]
    · intro i; fin_cases i
      · simpa [twoMeanStates, hlow] using hunit
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

private lemma metric_intercept_nonpos {d : ℕ} (hd : 2 ≤ d) {t : ℝ} (ht : 1 ≤ t) :
    1 - metricB d t + (metricB d t - metricA d t) / d ≤ 0 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have ht0 : 0 < t := by linarith
  have he : 1 - metricB d t + (metricB d t - metricA d t) / d =
      -((d - 1 : ℝ) * (t - 1)^2) / ((d : ℝ)^2 * t) := by
    unfold metricA metricB
    field_simp
    <;> ring
  rw [he]
  apply div_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos.mpr (mul_nonneg (by linarith) (sq_nonneg _))
  · positivity

private lemma hat_supporting {n d : ℕ} (hn : 2 ≤ n) (hd : 2 ≤ d)
    {t : ℝ} (ht : 1 ≤ t) :
    hatE n d (metricA d t - metricB d t) ≤
      -(1 - metricB d t + (metricB d t - metricA d t) / d) := by
  obtain ⟨ha, ha1, hab, he⟩ := metric_parameters hd ht
  apply csSup_le (hat_values_nonempty hn (by omega) _)
  rintro v ⟨ψ, φ, hψ, hφ, rfl⟩
  have hm := pure_metric_lower hn (by omega) ha ha1 hab he ψ hψ
  obtain ⟨_, _, hy⟩ := pure_means_triangle (by omega : 0 < n) (by omega : 0 < d) ψ hψ
  have hc := metric_intercept_nonpos hd ht
  have hcy := mul_le_mul_of_nonpos_left hy hc
  have hov := le_csSup (overlap_values_bdd ψ hψ)
    (show Complex.normSq (star φ ⬝ᵥ ψ) ∈ {v : ℝ | ∃ φ, IsBiseparable φ ∧
      v = Complex.normSq (star φ ⬝ᵥ ψ)} from ⟨φ, hφ, rfl⟩)
  have hov' : Complex.normSq (star φ ⬝ᵥ ψ) ≤ 1 - geometricMeasurePure ψ := by
    unfold geometricMeasurePure
    linarith only [hov]
  simp only [expectation_add, expectation_smul, expectation_rank_one,
    witnessOp, expectation_sub]
  rw [expectation_rank_one] at hm
  have hh :
      (metricA d t - metricB d t) *
          (1 / (d : ℝ) * readout (supportProjector n d) ψ -
            Complex.normSq (star (ghz n d) ⬝ᵥ ψ)) +
        (1 - metricB d t + (metricB d t - metricA d t) / d) ≤ geometricMeasurePure ψ := by
    calc
      _ ≤ (metricA d t - metricB d t) *
          (1 / (d : ℝ) * readout (supportProjector n d) ψ -
            Complex.normSq (star (ghz n d) ⬝ᵥ ψ)) +
        (1 - metricB d t + (metricB d t - metricA d t) / d) *
          readout (supportProjector n d) ψ :=
        by linarith only [hcy]
      _ = (1 - metricB d t) * readout (supportProjector n d) ψ +
          (metricB d t - metricA d t) * Complex.normSq (star (ghz n d) ⬝ᵥ ψ) := by ring
      _ ≤ _ := hm
  linarith only [hh, hov']

/-- The complete optimum for the original two-vector single-witness
conjugate on the entire feasible interval. No all-real-slope supplier formula
is assumed, and all limiting endpoints follow from finite supporting lines. -/
theorem witness_optimum {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) {w : ℝ}
    (hw0 : -(d - 1 : ℝ) / d ≤ w) (hw1 : w ≤ 1 / (d : ℝ)) :
    epsilonWitness n d w = twoMeanOptimum d (1 / (d : ℝ) - w) 1 := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  let F : ℝ := 1 / (d : ℝ) - w
  have hf : 0 ≤ F := sub_nonneg.mpr hw1
  have hf1 : F ≤ 1 := by
    have he : -(d - 1 : ℝ) / d = 1 / (d : ℝ) - 1 := by field_simp <;> ring
    rw [he] at hw0
    dsimp [F]; linarith
  obtain ⟨hp, hs, hu, hG, hP, hE⟩ := two_mean_ensemble_data hn hd hf hf1 (le_refl 1)
  let p := twoMeanWeights d F 1
  let ψ := twoMeanStates hn hd F 1
  have hw : (∑ i, p i * readout (witnessOp n d) (ψ i)) = w := by
    simp only [witnessOp, expectation_sub, expectation_smul]
    have hterm (i : Fin 3) : p i * ((1 / (d : ℝ)) * readout (supportProjector n d) (ψ i) -
        readout (rankOneDensity (ghz n d)) (ψ i)) =
        (1 / (d : ℝ)) * (p i * readout (supportProjector n d) (ψ i)) -
          p i * readout (rankOneDensity (ghz n d)) (ψ i) := by ring
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hP, hG]
    dsimp [F]
    ring
  have hb : BddAbove {v : ℝ | ∃ r : ℝ, v = r * w - hatE n d r} := by
    refine ⟨twoMeanOptimum d F 1, ?_⟩
    rintro v ⟨r, rfl⟩
    have h := conjugate_ensemble_bound (by omega : 2 ≤ n) (by omega : 0 < d) p ψ hp hs hu r
    rw [hw] at h
    exact h.trans_eq hE
  have hs0 : {v : ℝ | ∃ r : ℝ, v = r * w - hatE n d r}.Nonempty := ⟨_, 0, rfl⟩
  have hnonneg : 0 ≤ epsilonWitness n d w := by
    apply le_csSup hb
    refine ⟨0, ?_⟩
    rw [zero_mul, hat_zero (by omega : 2 ≤ n) (by omega : 0 < d), sub_self]
  apply le_antisymm
  · apply csSup_le hs0
    rintro v ⟨r, rfl⟩
    have h := conjugate_ensemble_bound (by omega : 2 ≤ n) (by omega : 0 < d) p ψ hp hs hu r
    rw [hw] at h
    exact h.trans_eq hE
  · apply supporting_envelope (by omega : 2 ≤ d) hf hf1 hnonneg
    intro t ht
    have hhat := hat_supporting (by omega : 2 ≤ n) (by omega : 2 ≤ d) ht
    have hslope := le_csSup hb
      (show (metricA d t - metricB d t) * w - hatE n d (metricA d t - metricB d t) ∈
        {v : ℝ | ∃ r : ℝ, v = r * w - hatE n d r} from ⟨_, rfl⟩)
    change _ ≤ epsilonWitness n d w at hslope
    have he :
        (1 + (d - 2 : ℝ) * F - t * (1 - F) - (d - 1 : ℝ) * F / t) / d =
        (metricA d t - metricB d t) * w +
          (1 - metricB d t + (metricB d t - metricA d t) / d) := by
      dsimp [F, metricA, metricB]
      field_simp
      <;> ring
    rw [he]
    linarith

private lemma sum_on_embedding {ι κ α : Type*} [Fintype ι] [Fintype κ]
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

private def pushVector {ι κ : Type*} [Fintype ι] (e : ι ↪ κ) (c : ι → ℂ) : κ → ℂ := by
  classical
  exact fun x => ∑ i, if e i = x then c i else 0

private lemma pushVector_apply {ι κ : Type*} [Fintype ι] (e : ι ↪ κ) (c : ι → ℂ) (i : ι) :
    pushVector e c (e i) = c i := by
  classical
  simp [pushVector, e.injective.eq_iff]

private lemma pushVector_off {ι κ : Type*} [Fintype ι] (e : ι ↪ κ) (c : ι → ℂ) (x : κ)
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

private lemma phaseVector_unit {d : ℕ} (hd : 0 < d) (θ : Fin d → ZMod 3) :
    ∑ j, Complex.normSq (phaseVector θ j) = 1 := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp [phaseVector, Complex.normSq_mul, ZMod.stdAddChar_apply,
    Complex.normSq_ofReal, Real.sq_sqrt (Nat.cast_nonneg d), hdR]

private lemma phaseVector_pair {d : ℕ} (hd : 0 < d) (θ : Fin d → ZMod 3) (i j : Fin d) :
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

private lemma sourceCut_nonempty {n : ℕ} (hn : 0 < n) (s : SourceCut n hn) : s.1.Nonempty := by
  have h : s.1 ≠ ∅ := (Finset.mem_erase.mp s.2).1
  exact Finset.nonempty_iff_ne_empty.mpr h

private lemma sourceCut_first {n : ℕ} (hn : 0 < n) (s : SourceCut n hn) :
    (⟨0,hn⟩ : Fin n) ∉ s.1 := by
  have hsub := Finset.mem_powerset.mp (Finset.mem_erase.mp s.2).2
  intro h
  exact (Finset.mem_erase.mp (hsub h)).1 rfl

private lemma sourceCut_complement {n : ℕ} (hn : 0 < n) (s : SourceCut n hn) : s.1ᶜ.Nonempty :=
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

private def supportIndexWord {n d : ℕ} (hn : 0 < n) : SupportIndex n d hn → Word (Fin d) n
  | .inl j => fun _ => j
  | .inr x => sourceCutWord hn x.1 x.2

private lemma supportIndexWord_injective {n d : ℕ} (hn : 0 < n) :
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

private lemma supportIndexWord_supported {n d : ℕ} (hn : 0 < n) (z : SupportIndex n d hn) :
    (Finset.univ.image (supportIndexWord hn z)).card ≤ 2 := by
  classical
  cases z with
  | inl j =>
    haveI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
    simp [supportIndexWord, Finset.image_const]
  | inr x => exact sourceCutWord_supported hn x.1 x.2

private lemma supportIndexWord_surjective {n d : ℕ} (hn : 0 < n) (x : Word (Fin d) n)
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

private lemma basis_projector_sum {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (∑ x : ι, rankOneDensity (Pi.single x (1 : ℂ))) = (1 : Matrix ι ι ℂ) := by
  ext i j
  simp only [Matrix.sum_apply, rankOneDensity, vecMulVec_apply, Pi.star_apply]
  simp [Pi.single_apply, Matrix.one_apply]

/-- An explicit finite computational-basis/GHZ ensemble for the noisy state.
This also proves density and roof nonvacuity before any optimizing ensemble
is used. -/
def noisyWeights (n d : ℕ) (p : ℝ) : Unit ⊕ Word (Fin d) n → ℝ
  | .inl _ => 1 - p
  | .inr _ => p / (wordCount n d : ℝ)

def noisyStates (n d : ℕ) : Unit ⊕ Word (Fin d) n → Word (Fin d) n → ℂ
  | .inl _ => ghz n d
  | .inr x => Pi.single x 1

private lemma noisy_ensemble_data {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (∀ i, 0 ≤ noisyWeights n d p i) ∧
      (∑ i, noisyWeights n d p i) = 1 ∧
      (∀ i, IsUnitState (noisyStates n d i)) ∧
      noisyGhz n d p = ∑ i, noisyWeights n d p i • rankOneDensity (noisyStates n d i) := by
  classical
  have hM : (0 : ℝ) < wordCount n d := by
    unfold wordCount
    exact_mod_cast (pow_pos hd n)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    cases i <;> simp only [noisyWeights]
    · exact sub_nonneg.mpr hp1
    · exact div_nonneg hp hM.le
  · simp only [Fintype.sum_sum_type, noisyWeights, Finset.sum_const, Finset.card_univ,
      Fintype.card_unit, Fintype.card_fun, Fintype.card_fin, one_nsmul, nsmul_eq_mul]
    simp only [Nat.cast_one, one_mul]
    change 1 - p + (wordCount n d : ℝ) * (p / wordCount n d) = 1
    field_simp
    <;> ring
  · intro i
    cases i with
    | inl _ => exact ghz_unit hn hd
    | inr x => exact basis_unit x
  · simp only [Fintype.sum_sum_type, noisyWeights, noisyStates, Fintype.sum_unique,
      ← Finset.smul_sum, basis_projector_sum]
    unfold noisyGhz wordCount
    push_cast
    exact add_comm _ _

def noisyDensity {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Word (Fin d) n) :=
  ensembleDensity (noisyWeights n d p) (noisyStates n d)
    (noisy_ensemble_data hn hd hp hp1).1
    (noisy_ensemble_data hn hd hp hp1).2.1
    (noisy_ensemble_data hn hd hp hp1).2.2.1

private lemma noisyDensity_matrix {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    CStarMatrix.ofMatrix.symm (noisyDensity hn hd p hp hp1).1 = noisyGhz n d p := by
  exact (noisy_ensemble_data hn hd hp hp1).2.2.2.symm

private def pushMatrix {ι κ : Type*} (e : ι ↪ κ) (m : Matrix ι ι ℂ) : Matrix κ κ ℂ := by
  classical
  exact fun x y => if hx : ∃ i, e i = x then
    if hy : ∃ j, e j = y then m hx.choose hy.choose else 0 else 0

private lemma pushMatrix_apply {ι κ : Type*} (e : ι ↪ κ) (m : Matrix ι ι ℂ) (i j : ι) :
    pushMatrix e m (e i) (e j) = m i j := by
  classical
  have hi : ∃ k, e k = e i := ⟨i,rfl⟩
  have hj : ∃ k, e k = e j := ⟨j,rfl⟩
  have hi' : hi.choose = i := e.injective hi.choose_spec
  have hj' : hj.choose = j := e.injective hj.choose_spec
  simp only [pushMatrix, dif_pos hi, dif_pos hj, hi', hj']

private lemma pushMatrix_off_left {ι κ : Type*} (e : ι ↪ κ) (m : Matrix ι ι ℂ) (x y : κ)
    (hx : ¬ ∃ i, e i = x) : pushMatrix e m x y = 0 := by
  classical
  simp [pushMatrix,hx]

private lemma pushMatrix_off_right {ι κ : Type*} (e : ι ↪ κ) (m : Matrix ι ι ℂ) (x y : κ)
    (hy : ¬ ∃ j, e j = y) : pushMatrix e m x y = 0 := by
  classical
  simp [pushMatrix,hy]

private lemma pushMatrix_add {ι κ : Type*} (e : ι ↪ κ) (a b : Matrix ι ι ℂ) :
    pushMatrix e (a+b) = pushMatrix e a + pushMatrix e b := by
  classical
  ext x y
  simp only [pushMatrix, Matrix.add_apply]
  split_ifs <;> simp_all [pushMatrix]

private lemma pushMatrix_smul {ι κ : Type*} (e : ι ↪ κ) (r : ℝ) (m : Matrix ι ι ℂ) :
    pushMatrix e (r • m) = r • pushMatrix e m := by
  classical
  ext x y
  simp only [pushMatrix, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  split_ifs <;> simp_all [pushMatrix]

private lemma pushMatrix_sum {ι κ σ : Type*} [Fintype σ] (e : ι ↪ κ)
    (m : σ → Matrix ι ι ℂ) : pushMatrix e (∑ t, m t) = ∑ t, pushMatrix e (m t) := by
  classical
  ext x y
  by_cases hx : ∃ i, e i = x
  · obtain ⟨i,rfl⟩ := hx
    by_cases hy : ∃ j, e j = y
    · obtain ⟨j,rfl⟩ := hy
      simp only [Matrix.sum_apply, pushMatrix_apply]
    · simp only [Matrix.sum_apply, pushMatrix_off_right e _ _ _ hy, Finset.sum_const_zero]
  · simp only [Matrix.sum_apply, pushMatrix_off_left e _ _ _ hx, Finset.sum_const_zero]

private lemma pushMatrix_projector {ι κ : Type*} [Fintype ι] (e : ι ↪ κ) (c : ι → ℂ) :
    pushMatrix e (rankOneDensity c) = rankOneDensity (pushVector e c) := by
  classical
  ext x y
  by_cases hx : ∃ i, e i = x
  · obtain ⟨i,rfl⟩ := hx
    by_cases hy : ∃ j, e j = y
    · obtain ⟨j,rfl⟩ := hy
      simp only [pushMatrix_apply, rankOneDensity, vecMulVec_apply, Pi.star_apply, pushVector_apply]
    · rw [pushMatrix_off_right e _ _ _ hy]
      simp [rankOneDensity, vecMulVec_apply, Pi.star_apply, pushVector_off e c y hy]
  · rw [pushMatrix_off_left e _ _ _ hx]
    simp [rankOneDensity, vecMulVec_apply, Pi.star_apply, pushVector_off e c x hx]

private def phaseCutCoefficient {d : ℕ} (α β : ℝ) (θ : Fin d → ZMod 3) (ij : Fin d × Fin d) : ℂ :=
  if ij.1 = ij.2 then ((β + (α - β) / d : ℝ) : ℂ)
  else (((α - β) / d : ℝ) : ℂ) * phaseCharacter (pairCoefficient ij.1 ij.2) θ

private lemma phaseCutCoefficient_eq {d : ℕ} (hd : 0 < d) (α β : ℝ)
    (θ : Fin d → ZMod 3) (ij : Fin d × Fin d) :
    phaseCutCoefficient α β θ ij =
      (if ij.1 = ij.2 then (β : ℂ) else 0) +
        ((α - β : ℝ) : ℂ) * phaseVector θ ij.1 * star (phaseVector θ ij.2) := by
  rw [mul_assoc,phaseVector_pair hd]
  by_cases hij : ij.1 = ij.2
  · have hz : pairCoefficient ij.1 ij.2 = 0 := (pairCoefficient_eq_zero_iff _ _).mpr hij
    simp [phaseCutCoefficient,hij,pairCoefficient,phaseCharacter]
    push_cast
    ring
  · simp only [phaseCutCoefficient,hij,ite_false,zero_add]
    push_cast
    ring

private lemma phase_coefficient_gram {d : ℕ} (α β : ℝ) (ij kl : Fin d × Fin d) :
    (∑ θ : Fin d → ZMod 3, phaseCutCoefficient α β θ ij *
      star (phaseCutCoefficient α β θ kl)) =
      if ij.1 = ij.2 ∧ kl.1 = kl.2 then
        ((3 ^ d : ℕ) : ℂ) * (((β + (α - β) / d)^2 : ℝ) : ℂ)
      else if ij = kl then ((3 ^ d : ℕ) : ℂ) * ((((α - β) / d)^2 : ℝ) : ℂ) else 0 := by
  classical
  let γ : ℂ := ((β + (α - β) / d : ℝ) : ℂ)
  let δ : ℂ := (((α - β) / d : ℝ) : ℂ)
  have hγ : star γ = γ := by simp [γ]
  have hδ : star δ = δ := by simp [δ]
  have hstar (r : ℝ) (z : ℂ) : star ((r : ℂ) * z) = (r : ℂ) * star z := by
    simp only [star_mul]
    simp
    <;> ring
  by_cases hij : ij.1 = ij.2
  · by_cases hkl : kl.1 = kl.2
    · simp [phaseCutCoefficient,hij,hkl,pow_two]
    · have hne : ij ≠ kl := by intro h; exact hkl (h ▸ hij)
      simp only [phaseCutCoefficient,hij,hkl,ite_true,ite_false,true_and,and_false,
        if_neg hne,hstar]
      change (∑ θ, γ * (δ * star (phaseCharacter (pairCoefficient kl.1 kl.2) θ))) = 0
      simp only [← mul_assoc, ← Finset.mul_sum, ← star_sum, pair_phase_sum, if_neg hkl,
        Nat.cast_zero, star_zero, mul_zero]
  · by_cases hkl : kl.1 = kl.2
    · have hne : ij ≠ kl := by intro h; exact hij (h.symm ▸ hkl)
      simp only [phaseCutCoefficient,hij,hkl,ite_true,ite_false,false_and,
        if_neg hne]
      change (∑ θ, δ * phaseCharacter (pairCoefficient ij.1 ij.2) θ * star γ) = 0
      rw [hγ, ← Finset.sum_mul, ← Finset.mul_sum, pair_phase_sum, if_neg hij]
      simp
    · have he : ((ij.1 = kl.1 ∧ ij.2 = kl.2) ↔ ij = kl) := Prod.ext_iff.symm
      simp only [phaseCutCoefficient,hij,hkl,ite_false,false_and,hstar]
      change (∑ θ, (δ * phaseCharacter (pairCoefficient ij.1 ij.2) θ) *
        (δ * star (phaseCharacter (pairCoefficient kl.1 kl.2) θ))) = _
      have hterm (θ : Fin d → ZMod 3) :
          (δ * phaseCharacter (pairCoefficient ij.1 ij.2) θ) *
            (δ * star (phaseCharacter (pairCoefficient kl.1 kl.2) θ)) =
          δ^2 * (phaseCharacter (pairCoefficient ij.1 ij.2) θ *
            star (phaseCharacter (pairCoefficient kl.1 kl.2) θ)) := by ring
      simp only [hterm, ← Finset.mul_sum, pair_cross_phase_sum, hij, false_and, false_or, he]
      by_cases h : ij = kl <;> simp [h,δ,pow_two,mul_comm]

private lemma basis_coefficient_gram {d : ℕ} (α β : ℝ) (i k : Fin d) :
    (∑ j : Fin d, (if i = j then (α : ℂ) else β) *
      star (if k = j then (α : ℂ) else β)) =
      (((d : ℝ) * β^2 + 2 * β * (α - β) +
        (if i = k then (α - β)^2 else 0) : ℝ) : ℂ) := by
  classical
  have he (i j : Fin d) : (if i = j then (α : ℂ) else β) =
      (β : ℂ) + (if i = j then ((α - β : ℝ) : ℂ) else 0) := by
    by_cases h : i = j <;> simp [h] <;> push_cast <;> ring
  have ht (j : Fin d) :
      (if i = j then (α : ℂ) else β) * star (if k = j then (α : ℂ) else β) =
      (β^2 : ℝ) + (if i = j then ((β * (α - β) : ℝ) : ℂ) else 0) +
        (if k = j then ((β * (α - β) : ℝ) : ℂ) else 0) +
        (if i = j ∧ k = j then (((α - β)^2 : ℝ) : ℂ) else 0) := by
    by_cases hi : i = j <;> by_cases hk : k = j <;> simp [hi,hk] <;> push_cast <;> ring
  simp only [ht, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hlast : (∑ j : Fin d, if i = j ∧ k = j then (((α - β)^2 : ℝ) : ℂ) else 0) =
      if i = k then (((α - β)^2 : ℝ) : ℂ) else 0 := by
    by_cases hik : i = k
    · subst k
      simp
    · rw [if_neg hik]
      apply Finset.sum_eq_zero
      intro j hj
      have hh : ¬ (i = j ∧ k = j) := by rintro ⟨rfl,rfl⟩; exact hik rfl
      simp [hh,hik]
  rw [hlast]
  split_ifs <;> push_cast <;> ring

/-- The piecewise optimum is exactly the source's truncated radical on the
entire closed triangle, including the zero and fidelity boundaries. -/
theorem twoMeanOptimum_max {d : ℕ} (hd : 2 ≤ d) {f y : ℝ}
    (hf : 0 ≤ f) (hfy : f ≤ y) :
    twoMeanOptimum d f y =
      (max (Real.sqrt ((d - 1 : ℝ) * f) - Real.sqrt (y - f)) 0)^2 / d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hA : 0 ≤ (d - 1 : ℝ) * f := mul_nonneg (by linarith) hf
  have hB : 0 ≤ y - f := sub_nonneg.mpr hfy
  by_cases h : (d : ℝ) * f ≤ y
  · have hr : Real.sqrt ((d - 1 : ℝ) * f) ≤ Real.sqrt (y - f) :=
      Real.sqrt_le_sqrt (by nlinarith)
    simp [twoMeanOptimum,h,max_eq_right (sub_nonpos.mpr hr)]
  · have hr : Real.sqrt (y - f) ≤ Real.sqrt ((d - 1 : ℝ) * f) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rw [twoMeanOptimum,if_neg h,max_eq_left (sub_nonneg.mpr hr)]
    unfold twoMeanValue
    rw [Real.sqrt_mul hA]
    have hS := Real.sq_sqrt hA
    have hT := Real.sq_sqrt hB
    congr 1
    nlinarith

private lemma twoMeanOptimum_nonneg {d : ℕ} (hd : 2 ≤ d) {f y : ℝ}
    (hf : 0 ≤ f) (hfy : f ≤ y) : 0 ≤ twoMeanOptimum d f y := by
  rw [twoMeanOptimum_max hd hf hfy]
  positivity

/-- The diagonal projector onto the constant computational words. -/
def constantProjector (n d : ℕ) : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ := by
  classical
  exact diagonal (fun x => if ∃ j : Fin d, ∀ k, x k = j then 1 else 0)

/-- The off-constant sector belonging to one actual bipartition. -/
def cutOffProjector {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty) (hc : aᶜ.Nonempty) :
    Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ := by
  classical
  exact pushMatrix (cutEmbedding a ha hc) (diagonal (fun ij => if ij.1 ≠ ij.2 then 1 else 0))

private lemma cutEmbedding_diagonal {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty)
    (hc : aᶜ.Nonempty) (j : Fin d) : cutEmbedding a ha hc (j,j) = (fun _ => j) := by
  funext k
  simp [cutEmbedding,Finset.piecewise]

private lemma cutEmbedding_isConstant {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty)
    (hc : aᶜ.Nonempty) (ij : Fin d × Fin d) :
    (∃ j : Fin d, ∀ k, cutEmbedding a ha hc ij k = j) ↔ ij.1 = ij.2 := by
  constructor
  · rintro ⟨j,hj⟩
    obtain ⟨k,hk⟩ := ha
    obtain ⟨l,hl⟩ := hc
    have h1 := hj k
    have h2 := hj l
    simp [cutEmbedding,hk] at h1
    simp [cutEmbedding,Finset.mem_compl.mp hl] at h2
    exact h1.trans h2.symm
  · intro h
    refine ⟨ij.1,?_⟩
    intro k
    simp [cutEmbedding,Finset.piecewise,h]

private lemma ghz_cutEmbedding {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty)
    (hc : aᶜ.Nonempty) (ij : Fin d × Fin d) :
    ghz n d (cutEmbedding a ha hc ij) =
      if ij.1 = ij.2 then (Real.sqrt d : ℂ)⁻¹ else 0 := by
  simp only [ghz,cutEmbedding_isConstant]

private lemma ghz_off_cutEmbedding {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty)
    (hc : aᶜ.Nonempty) (x : Word (Fin d) n) (hx : ¬ ∃ ij, cutEmbedding a ha hc ij = x) :
    ghz n d x = 0 := by
  have h : ¬ ∃ j : Fin d, ∀ k, x k = j := by
    rintro ⟨j,hj⟩
    exact hx ⟨(j,j),(cutEmbedding_diagonal a ha hc j).trans (funext hj).symm⟩
  simp [ghz,h]

private lemma cut_coherent_matrix {n d : ℕ} (hd : 0 < d)
    (a : Finset (Fin n)) (ha : a.Nonempty) (hc : aᶜ.Nonempty) :
    pushMatrix (cutEmbedding a ha hc)
      (Matrix.of fun ij kl => if ij.1 = ij.2 ∧ kl.1 = kl.2 then 1 else 0) =
      (d : ℝ) • rankOneDensity (ghz n d) := by
  classical
  have hroot : (Real.sqrt d : ℂ)^2 = (d : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg d)
  have hroot0 : (Real.sqrt d : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < d by exact_mod_cast hd)).ne'
  have hscalar : (d : ℂ) * (Real.sqrt d : ℂ)⁻¹ * (Real.sqrt d : ℂ)⁻¹ = 1 := by
    rw [← hroot]
    field_simp
  ext x y
  by_cases hx : ∃ ij, cutEmbedding a ha hc ij = x
  · obtain ⟨ij,rfl⟩ := hx
    by_cases hy : ∃ kl, cutEmbedding a ha hc kl = y
    · obtain ⟨kl,rfl⟩ := hy
      rw [pushMatrix_apply]
      simp only [Matrix.smul_apply,rankOneDensity,vecMulVec_apply,Pi.star_apply,ghz_cutEmbedding,
        Complex.real_smul,Matrix.of_apply]
      by_cases hij : ij.1 = ij.2 <;> by_cases hkl : kl.1 = kl.2 <;>
        simp [hij,hkl,← mul_assoc,hscalar]
    · rw [pushMatrix_off_right _ _ _ _ hy]
      simp [rankOneDensity,vecMulVec_apply,Pi.star_apply,ghz_off_cutEmbedding a ha hc y hy]
  · rw [pushMatrix_off_left _ _ _ _ hx]
    simp [rankOneDensity,vecMulVec_apply,Pi.star_apply,ghz_off_cutEmbedding a ha hc x hx]

private lemma phase_raw_matrix {n d : ℕ} (hd : 0 < d)
    (a : Finset (Fin n)) (ha : a.Nonempty) (hc : aᶜ.Nonempty) (α β : ℝ) :
    (∑ θ : Fin d → ZMod 3, rankOneDensity (cutState a ha hc α β (phaseVector θ))) =
      ((3 ^ d : ℕ) * (β + (α - β) / d)^2 * d : ℝ) • rankOneDensity (ghz n d) +
        ((3 ^ d : ℕ) * ((α - β) / d)^2 : ℝ) • cutOffProjector a ha hc := by
  classical
  have he (θ : Fin d → ZMod 3) :
      cutState a ha hc α β (phaseVector θ) =
        pushVector (cutEmbedding a ha hc) (phaseCutCoefficient α β θ) := by
    unfold cutState
    congr 1
    funext ij
    exact (phaseCutCoefficient_eq hd α β θ ij).symm
  simp_rw [he, ← pushMatrix_projector]
  rw [← pushMatrix_sum]
  have hm : (∑ θ : Fin d → ZMod 3, rankOneDensity (phaseCutCoefficient α β θ)) =
      ((3 ^ d : ℕ) * (β + (α - β) / d)^2 : ℝ) •
        (Matrix.of fun ij kl => if ij.1 = ij.2 ∧ kl.1 = kl.2 then (1 : ℂ) else 0) +
      ((3 ^ d : ℕ) * ((α - β) / d)^2 : ℝ) •
        diagonal (fun ij : Fin d × Fin d => if ij.1 ≠ ij.2 then (1 : ℂ) else 0) := by
    ext ij kl
    simp only [Matrix.sum_apply,rankOneDensity,vecMulVec_apply,Pi.star_apply,phase_coefficient_gram,
      Matrix.add_apply,Matrix.smul_apply,Complex.real_smul,diagonal_apply,Matrix.of_apply]
    by_cases hij : ij.1 = ij.2 <;> by_cases hkl : kl.1 = kl.2 <;>
      by_cases heq : ij = kl <;> simp_all <;> push_cast <;> ring
  rw [hm,pushMatrix_add,pushMatrix_smul,pushMatrix_smul,cut_coherent_matrix hd a ha hc]
  rw [smul_smul]
  rfl

private lemma ghz_constant_matrix {n d : ℕ} (hd : 0 < d) (i j : Fin d) :
    rankOneDensity (ghz n d) (fun _ => i) (fun _ => j) = (1 / (d : ℂ)) := by
  have hroot : (Real.sqrt d : ℂ)^2 = (d : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg d)
  have hinv : (Real.sqrt d : ℂ)⁻¹ * (Real.sqrt d : ℂ)⁻¹ = (d : ℂ)⁻¹ := by
    rw [← mul_inv,← pow_two,hroot]
  have hi : ∃ a : Fin d, ∀ _k : Fin n, i = a := ⟨i,fun _ => rfl⟩
  have hj : ∃ a : Fin d, ∀ _k : Fin n, j = a := ⟨j,fun _ => rfl⟩
  simpa [rankOneDensity,vecMulVec_apply,Pi.star_apply,ghz,hi,hj] using hinv

private lemma constantProjector_constant {n d : ℕ} (hn : 0 < n) (i j : Fin d) :
    constantProjector n d (fun _ => i) (fun _ => j) = if i = j then 1 else 0 := by
  classical
  have he : ((fun _ : Fin n => i) = fun _ : Fin n => j) ↔ i = j :=
    ⟨fun h => constant_word_injective hn h,fun h => h ▸ rfl⟩
  have hi : ∃ a : Fin d, ∀ _k : Fin n, i = a := ⟨i,fun _ => rfl⟩
  simp [constantProjector,diagonal_apply,he,hi]

private lemma constantProjector_off {n d : ℕ} (x y : Word (Fin d) n)
    (hx : ¬ ∃ j : Fin d, ∀ k, x k = j) : constantProjector n d x y = 0 := by
  classical
  simp [constantProjector,diagonal_apply,hx]

private lemma basis_raw_matrix {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (α β : ℝ) :
    (∑ j : Fin d, rankOneDensity (chiVector hn j α β)) =
      ((d : ℝ)*((d : ℝ)*β^2+2*β*(α-β))) • rankOneDensity (ghz n d) +
        (α-β)^2 • constantProjector n d := by
  classical
  have hgoff (x : Word (Fin d) n) (hx : ¬ ∃ j : Fin d, ∀ k, x k = j) : ghz n d x = 0 := by
    simp [ghz,hx]
  have hcoff (j : Fin d) (x : Word (Fin d) n) (hx : ¬ ∃ j : Fin d, ∀ k, x k = j) :
      chiVector hn j α β x = 0 := constantVector_off hn _ _ hx
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  ext x y
  by_cases hx : ∃ i : Fin d, ∀ k, x k = i
  · obtain ⟨i,hi⟩ := hx
    have hxi := funext hi
    subst x
    by_cases hy : ∃ k : Fin d, ∀ l, y l = k
    · obtain ⟨k,hk⟩ := hy
      have hyk := funext hk
      subst y
      simp only [Matrix.sum_apply,chiVector,constantVector_apply,rankOneDensity,vecMulVec_apply,
        Pi.star_apply]
      rw [basis_coefficient_gram]
      change _ = (((d : ℝ)*((d : ℝ)*β^2+2*β*(α-β))) • rankOneDensity (ghz n d))
        (fun _ => i) (fun _ => k) + ((α-β)^2 • constantProjector n d) (fun _ => i) (fun _ => k)
      rw [Matrix.smul_apply,Matrix.smul_apply,ghz_constant_matrix hd,constantProjector_constant hn]
      split_ifs <;> simp only [Complex.real_smul,mul_one,mul_zero,add_zero] <;>
        push_cast <;> field_simp <;> ring
    · have hne : (fun _ : Fin n => i) ≠ y := by
        intro h
        exact hy ⟨i,fun k => (congrFun h k).symm⟩
      simp [Matrix.sum_apply,rankOneDensity,vecMulVec_apply,Pi.star_apply,hcoff _ y hy,
        hgoff y hy,constantProjector,diagonal_apply,hne]
  · simp [Matrix.sum_apply,rankOneDensity,vecMulVec_apply,Pi.star_apply,hcoff _ x hx,
      hgoff x hx,constantProjector_off x y hx]

private lemma pushVector_single {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (e : ι ↪ κ) (i : ι) : pushVector e (Pi.single i (1 : ℂ)) = Pi.single (e i) 1 := by
  ext x
  by_cases hx : ∃ j, e j = x
  · obtain ⟨j,rfl⟩ := hx
    rw [pushVector_apply]
    simp [Pi.single_apply,e.injective.eq_iff]
  · rw [pushVector_off e _ x hx]
    have hi : e i ≠ x := fun h => hx ⟨i,h⟩
    simp [Pi.single_apply,hi,Ne.symm hi]

private lemma diagonal_projector_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → Prop)
    [DecidablePred p] :
    diagonal (fun i => if p i then (1 : ℂ) else 0) =
      ∑ i : ι, if p i then rankOneDensity (Pi.single i (1 : ℂ)) else 0 := by
  rw [← Matrix.sum_single_eq_diagonal]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hp : p c
  · simp only [hp,ite_true]
    ext i j
    by_cases hi : i = c <;> by_cases hj : j = c <;>
      simp [Matrix.single,rankOneDensity,vecMulVec_apply,Pi.star_apply,
        Pi.single_apply,hi,hj,eq_comm] <;> aesop
  · simp [hp]

private lemma pushMatrix_diagonal_projector {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq κ] (e : ι ↪ κ) (p : ι → Prop) [DecidablePred p] :
    pushMatrix e (diagonal (fun i => if p i then (1 : ℂ) else 0)) =
      ∑ i : ι, if p i then rankOneDensity (Pi.single (e i) (1 : ℂ)) else 0 := by
  rw [diagonal_projector_sum,pushMatrix_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : p i
  · simp only [h,ite_true,pushMatrix_projector,pushVector_single]
  · simp only [h,ite_false]
    ext x y
    simp [pushMatrix]

private lemma cutOffProjector_basis {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty)
    (hc : aᶜ.Nonempty) :
    cutOffProjector a ha hc =
      ∑ ij : OffPair d, rankOneDensity (Pi.single (cutEmbedding a ha hc ij.1) (1 : ℂ)) := by
  classical
  rw [cutOffProjector,pushMatrix_diagonal_projector]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

private lemma constantProjector_basis {n d : ℕ} (hn : 0 < n) :
    constantProjector n d = ∑ j : Fin d, rankOneDensity (Pi.single (fun _ : Fin n => j) (1 : ℂ)) := by
  classical
  have he : (∑ x : Word (Fin d) n,
      if ∃ j : Fin d, ∀ k, x k = j then rankOneDensity (Pi.single x (1 : ℂ)) else 0) =
      ∑ j : Fin d, rankOneDensity (Pi.single (fun _ : Fin n => j) (1 : ℂ)) := by
    rw [sum_supported_constants hn _ (by intro x hx; simp [hx])]
    apply Finset.sum_congr rfl
    intro j hj
    rw [if_pos ⟨j,fun _ => rfl⟩]
  simpa only [constantProjector,diagonal_projector_sum] using he

private lemma sourceSector_eq {n d : ℕ} (hn : 0 < n) (s : SourceCut n hn) (ij : OffPair d) :
    cutEmbedding s.1ᶜ (sourceCut_complement hn s)
      (by simpa only [compl_compl] using sourceCut_nonempty hn s) ij.1 =
      sourceCutWord hn s ij := by
  classical
  funext k
  by_cases hk : k ∈ s.1 <;> simp [cutEmbedding,sourceCutWord,Finset.piecewise,hk]

/-- The source's full disjoint projector decomposition, as actual complex
matrices rather than a scalar rank count. -/
theorem support_projector_decomposition {n d : ℕ} (hn : 0 < n) :
    supportProjector n d = constantProjector n d +
      ∑ s : SourceCut n hn, cutOffProjector s.1ᶜ (sourceCut_complement hn s)
        (by simpa only [compl_compl] using sourceCut_nonempty hn s) := by
  classical
  have hfull : supportProjector n d =
      ∑ z : SupportIndex n d hn, rankOneDensity (Pi.single (supportIndexWord hn z) (1 : ℂ)) := by
    rw [supportProjector,diagonal_projector_sum]
    rw [sum_on_embedding ⟨supportIndexWord hn,supportIndexWord_injective hn⟩ _ (by
      intro x hx
      have hnot : ¬ (Finset.univ.image x).card ≤ 2 := by
        intro hs
        exact hx (supportIndexWord_surjective hn x hs)
      simp [hnot])]
    apply Finset.sum_congr rfl
    intro z hz
    simp [supportIndexWord_supported hn z]
  rw [hfull]
  change (∑ z : Fin d ⊕ (SourceCut n hn × OffPair d), _) = _
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type,constantProjector_basis hn]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  rw [cutOffProjector_basis]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [sourceSector_eq]
  rfl

private lemma optimal_matrix_parameters {d : ℕ} (hd : 2 ≤ d) {F : ℝ}
    (hF : 1/(d : ℝ) ≤ F) (hF1 : F ≤ 1) :
    (optimalAlpha d F-optimalBeta d F)^2/d = (1-F)/(d-1 : ℝ) ∧
      (d : ℝ)*(optimalBeta d F+(optimalAlpha d F-optimalBeta d F)/d)^2 = F ∧
      (d : ℝ)*(optimalBeta d F)^2+2*optimalBeta d F*(optimalAlpha d F-optimalBeta d F) =
        F-(1-F)/(d-1 : ℝ) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d-1 : ℝ) ≠ 0 := by linarith
  obtain ⟨_,_,hnorm,hmean,_⟩ := optimal_amplitudes hd hF hF1
  have hm : (optimalAlpha d F+(d-1 : ℝ)*optimalBeta d F)^2 = F*d :=
    (div_eq_iff hd0).mp hmean
  have ht : (d-1 : ℝ)*(optimalAlpha d F-optimalBeta d F)^2 = (d : ℝ)*(1-F) := by
    linear_combination (d : ℝ)*hnorm-hm
  have ht' : (optimalAlpha d F-optimalBeta d F)^2/d = (1-F)/(d-1 : ℝ) := by
    field_simp
    linear_combination ht
  have hg : (d : ℝ)*(optimalBeta d F+(optimalAlpha d F-optimalBeta d F)/d)^2 = F := by
    field_simp
    linear_combination hm
  refine ⟨ht',hg,?_⟩
  calc
    _ = (d : ℝ)*(optimalBeta d F+(optimalAlpha d F-optimalBeta d F)/d)^2-
        (optimalAlpha d F-optimalBeta d F)^2/d := by field_simp <;> ring
    _ = _ := by rw [hg,ht']

/-- The actual finite d-component basis average from the source. -/
def basisAverage {n d : ℕ} (hn : 0 < n) (F : ℝ) : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ :=
  (1/(d : ℝ)) • ∑ j : Fin d, rankOneDensity (chiVector hn j (optimalAlpha d F) (optimalBeta d F))

/-- The actual finite 3^d-component independent-phase average from one cut. -/
def phaseAverage {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty) (hc : aᶜ.Nonempty)
    (F : ℝ) : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ :=
  (1/((3^d : ℕ) : ℝ)) • ∑ θ : Fin d → ZMod 3,
    rankOneDensity (cutState a ha hc (optimalAlpha d F) (optimalBeta d F) (phaseVector θ))

/-- The full actual basis-average matrix J_F. -/
theorem basis_average_matrix {n d : ℕ} (hn : 0 < n) (hd : 3 ≤ d)
    {F : ℝ} (hF : 1/(d : ℝ) ≤ F) (hF1 : F ≤ 1) :
    basisAverage hn F = F • rankOneDensity (ghz n d) +
      ((1-F)/(d-1 : ℝ)) • (constantProjector n d-rankOneDensity (ghz n d)) := by
  obtain ⟨ht,hg,hb⟩ := optimal_matrix_parameters (by omega : 2 ≤ d) hF hF1
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  rw [basisAverage,basis_raw_matrix hn (by omega : 0 < d),smul_add,smul_smul,smul_smul]
  have h1 : (1/(d : ℝ))*((d : ℝ)*((d : ℝ)*(optimalBeta d F)^2+
      2*optimalBeta d F*(optimalAlpha d F-optimalBeta d F))) = F-(1-F)/(d-1 : ℝ) := by
    calc
      _ = (d : ℝ)*(optimalBeta d F)^2+2*optimalBeta d F*(optimalAlpha d F-optimalBeta d F) := by
        field_simp
      _ = _ := hb
  have h2 : (1/(d : ℝ))*(optimalAlpha d F-optimalBeta d F)^2 = (1-F)/(d-1 : ℝ) := by
    simpa [div_eq_mul_inv,mul_comm] using ht
  rw [h1,h2,sub_smul,smul_sub]
  abel

/-- The full actual phase-average matrix H_{A,F}. Every off-diagonal entry
is controlled by the independent-coordinate Gram identity in arbitrary d. -/
theorem phase_average_matrix {n d : ℕ} (hd : 3 ≤ d)
    (a : Finset (Fin n)) (ha : a.Nonempty) (hc : aᶜ.Nonempty)
    {F : ℝ} (hF : 1/(d : ℝ) ≤ F) (hF1 : F ≤ 1) :
    phaseAverage a ha hc F = F • rankOneDensity (ghz n d) +
      ((1-F)/((d : ℝ)*(d-1 : ℝ))) • cutOffProjector a ha hc := by
  obtain ⟨ht,hg,_⟩ := optimal_matrix_parameters (by omega : 2 ≤ d) hF hF1
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hN : ((3^d : ℕ) : ℝ) ≠ 0 := by positivity
  rw [phaseAverage,phase_raw_matrix (by omega : 0 < d) a ha hc,smul_add,smul_smul,smul_smul]
  have h1 : (1/((3^d : ℕ) : ℝ))*(((3^d : ℕ) : ℝ)*
      (optimalBeta d F+(optimalAlpha d F-optimalBeta d F)/d)^2*d) = F := by
    calc
      _ = (d : ℝ)*(optimalBeta d F+(optimalAlpha d F-optimalBeta d F)/d)^2 := by
        field_simp
        <;> ring
      _ = _ := hg
  have h2 : (1/((3^d : ℕ) : ℝ))*(((3^d : ℕ) : ℝ)*
      ((optimalAlpha d F-optimalBeta d F)/d)^2) = (1-F)/((d : ℝ)*(d-1 : ℝ)) := by
    calc
      _ = ((optimalAlpha d F-optimalBeta d F)^2/d)/d := by field_simp <;> ring
      _ = _ := by rw [ht]; field_simp <;> ring
  rw [h1,h2]


private lemma at_least_three_pos {k : ℕ} (h : 3 ≤ k) : 0 < k := by omega

def noisyF (n d : ℕ) (p : ℝ) : ℝ := 1-p+p/(wordCount n d : ℝ)
def noisyY (n d : ℕ) (p : ℝ) : ℝ := 1-p+p*(supportRank n d : ℝ)/(wordCount n d : ℝ)

/-- Exact real trace readouts of the actual noisy matrix. -/
theorem noisy_means {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (p : ℝ) :
    observableMean (noisyGhz n d p) (rankOneDensity (ghz n d)) = noisyF n d p ∧
      observableMean (noisyGhz n d p) (supportProjector n d) = noisyY n d p := by
  obtain ⟨_,_,hgp,hgg⟩ := projector_data hn hd
  have ht : trace (rankOneDensity (ghz n d)) = 1 := by
    rw [trace_rank_one,ghz_unit hn hd]
    rfl
  constructor
  · simp only [observableMean,noisyGhz,add_mul,Matrix.smul_mul,one_mul,trace_add,
      trace_smul,hgg,ht,Complex.real_smul,Complex.add_re,Complex.ofReal_re,mul_one]
    simp [noisyF,wordCount]
    ring
  · simp only [observableMean,noisyGhz,add_mul,Matrix.smul_mul,one_mul,trace_add,
      trace_smul,hgp,ht,support_trace hn,Complex.real_smul,Complex.add_re,
      Complex.ofReal_re,mul_one]
    simp [noisyY,wordCount, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    ring

/-- The source witness value is the exact affine trace of the noisy state. -/
theorem witness_value_affine {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (p : ℝ) :
    witnessValue n d p = -(d-1 : ℝ)/d+witnessSlope n d*p := by
  have hM : (0 : ℝ) < wordCount n d := by unfold wordCount; exact_mod_cast pow_pos hd n
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  change observableMean (noisyGhz n d p) (witnessOp n d) = _
  rw [witnessOp,mean_sub,mean_smul,(noisy_means hn hd p).1,(noisy_means hn hd p).2]
  unfold noisyF noisyY witnessSlope
  field_simp
  <;> ring

private lemma noisy_parameter_data {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    0 < (wordCount n d : ℝ) ∧ (d : ℝ) < supportRank n d ∧
      (supportRank n d : ℝ) < wordCount n d ∧ 0 < witnessSlope n d ∧
      0 < witnessZeroProbability n d ∧ witnessZeroProbability n d < 1 := by
  obtain ⟨hR,hRM⟩ := support_rank_bounds hn hd
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hR' : (d : ℝ) < supportRank n d := by exact_mod_cast hR
  have hRM' : (supportRank n d : ℝ) < wordCount n d := by exact_mod_cast hRM
  have hM : (0 : ℝ) < wordCount n d := by linarith
  have ha : 0 < (d-1 : ℝ)/d := div_pos (by linarith) (by linarith)
  have hk : (d-1 : ℝ)/d < witnessSlope n d := by
    unfold witnessSlope
    have hq : 0 < (supportRank n d : ℝ)/d-1 := by
      apply sub_pos.mpr
      exact (lt_div_iff₀ (by linarith : (0 : ℝ) < d)).mpr (by simpa)
    exact lt_add_of_pos_right _ (div_pos hq hM)
  have hk0 : 0 < witnessSlope n d := ha.trans hk
  refine ⟨hM,hR',hRM',hk0,?_,?_⟩
  · exact div_pos ha hk0
  · exact (div_lt_one hk0).mpr hk

private lemma noisy_triangle {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ noisyF n d p ∧ noisyF n d p ≤ noisyY n d p ∧
      0 < noisyY n d p ∧ noisyY n d p ≤ 1 := by
  obtain ⟨hM,hR,hRM,_,_,_⟩ := noisy_parameter_data hn hd
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hratio : 0 < (supportRank n d : ℝ)/wordCount n d := div_pos (by linarith) hM
  have hratio1 : (supportRank n d : ℝ)/wordCount n d < 1 := (div_lt_one hM).mpr hRM
  have hF := add_nonneg (sub_nonneg.mpr hp1) (div_nonneg hp hM.le)
  have hfy : noisyY n d p-noisyF n d p = p*((supportRank n d : ℝ)-1)/wordCount n d := by
    unfold noisyF noisyY
    field_simp
    <;> ring
  have hy : noisyY n d p = (supportRank n d : ℝ)/wordCount n d+
      (1-p)*(1-(supportRank n d : ℝ)/wordCount n d) := by
    unfold noisyY
    ring
  refine ⟨hF,?_,?_,?_⟩
  · apply sub_nonneg.mp
    rw [hfy]
    exact div_nonneg (mul_nonneg hp (by linarith)) hM.le
  · rw [hy]
    exact add_pos_of_pos_of_nonneg hratio (mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hratio1.le))
  · unfold noisyY
    have hq := mul_nonneg hp (sub_nonneg.mpr hratio1.le)
    have he : p*(1-(supportRank n d : ℝ)/wordCount n d) =
        p-p*(supportRank n d : ℝ)/wordCount n d := by ring
    rw [he] at hq
    linarith

private lemma noisy_witness_means {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (p : ℝ) :
    witnessValue n d p = noisyY n d p/d-noisyF n d p := by
  change observableMean (noisyGhz n d p) (witnessOp n d) = _
  rw [witnessOp,mean_sub,mean_smul,(noisy_means hn hd p).1,(noisy_means hn hd p).2]
  ring

/-- Exact original epsilonO on every physical noise probability, obtained
from the actual hatE conjugate and the actual matrix trace. -/
theorem noisy_witness_optimum {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    epsilonO n d p = twoMeanOptimum d (noisyF n d p+(1-noisyY n d p)/d) 1 := by
  obtain ⟨hf,hfy,hy0,hy1⟩ := noisy_triangle hn hd hp hp1
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hdf := mul_le_mul_of_nonneg_left hfy hdpos.le
  have hdf0 := mul_nonneg hdpos.le hf
  have hwm := noisy_witness_means (at_least_three_pos hn) (by omega : 0 < d) p
  have hw0 : -(d-1 : ℝ)/d ≤ witnessValue n d p := by
    rw [hwm]
    apply (div_le_iff₀ hdpos).mpr
    have hy := mul_nonneg (sub_nonneg.mpr hy1) (show (0 : ℝ) ≤ d-1 by linarith)
    field_simp
    nlinarith
  have hw1 : witnessValue n d p ≤ 1/(d : ℝ) := by
    rw [hwm]
    apply (le_div_iff₀ hdpos).mpr
    field_simp
    nlinarith
  rw [epsilonO_bridge,witness_optimum hn hd hw0 hw1,hwm]
  congr 1
  ring

private lemma low_noise_ratio {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hp : 0 ≤ p) (hpW : p ≤ witnessZeroProbability n d) :
    0 < noisyY n d p ∧ 1/(d : ℝ) ≤ noisyF n d p/noisyY n d p ∧
      noisyF n d p/noisyY n d p ≤ 1 := by
  obtain ⟨hM,hR,hRM,hk,hpW0,hpW1⟩ := noisy_parameter_data hn hd
  have hp1 : p ≤ 1 := hpW.trans hpW1.le
  obtain ⟨hf,hfy,hy0,hy1⟩ := noisy_triangle hn hd hp hp1
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hw : witnessValue n d p ≤ 0 := by
    rw [witness_value_affine (by omega) (by omega)]
    have h := (le_div_iff₀ hk).mp hpW
    change p*witnessSlope n d ≤ (d-1 : ℝ)/d at h
    rw [neg_div]
    nlinarith
  rw [noisy_witness_means (by omega) (by omega)] at hw
  refine ⟨hy0,?_,(div_le_one hy0).mpr hfy⟩
  apply (div_le_div_iff₀ hdpos hy0).mpr
  have h := (div_le_iff₀ hdpos).mp (show noisyY n d p/d ≤ noisyF n d p by linarith)
  simpa only [one_mul,mul_comm] using h

private lemma twoMeanOptimum_pos {d : ℕ} (hd : 2 ≤ d) {f y : ℝ}
    (hf : 0 ≤ f) (hfy : f ≤ y) (h : y < (d : ℝ) * f) :
    0 < twoMeanOptimum d f y := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hB : 0 ≤ y - f := sub_nonneg.mpr hfy
  have hA : 0 ≤ (d - 1 : ℝ) * f := mul_nonneg (by linarith) hf
  have hr : Real.sqrt (y - f) < Real.sqrt ((d - 1 : ℝ) * f) :=
    Real.sqrt_lt_sqrt hB (by nlinarith)
  rw [twoMeanOptimum_max hd hf hfy,max_eq_left (sub_nonneg.mpr hr.le)]
  exact div_pos (sq_pos_of_pos (sub_pos.mpr hr)) (by linarith)

/-- A nonzero Q-readout gives a strict advantage over the entire original
single-witness optimum whenever the witness is negative. This comparison
uses the exact radicals, with no endpoint slope assigned a singular value. -/
theorem two_mean_strict_witness_gap {d : ℕ} (hd : 3 ≤ d) {f y : ℝ}
    (hf : 0 ≤ f) (hfy : f ≤ y) (hy : y < 1) (hneg : y < (d : ℝ) * f) :
    twoMeanOptimum d (f + (1-y) / d) 1 < twoMeanOptimum d f y := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  let q : ℝ := 1-y
  let c : ℝ := (d-1 : ℝ) * q / d
  let F : ℝ := f+q/d
  have hq : 0 < q := sub_pos.mpr hy
  have hc : 0 < c := div_pos (mul_pos (by linarith) hq) hdpos
  have hF0 : 0 ≤ F := add_nonneg hf (div_nonneg hq.le hdpos.le)
  have hF1 : F ≤ 1 := by
    have hq' : q / (d : ℝ) ≤ q := div_le_self hq.le (by linarith)
    dsimp [F]
    dsimp [q] at hq'
    linarith
  have hFdef : (d : ℝ)*F = (d : ℝ)*f+q := by
    dsimp [F]
    field_simp
    <;> ring
  have hFneg : 1 < (d : ℝ) * F := by
    rw [hFdef]
    dsimp [q]
    linarith
  have hA : 0 ≤ (d-1 : ℝ)*f*(y-f) := mul_nonneg (mul_nonneg (by linarith) hf) (sub_nonneg.mpr hfy)
  have hA' : 0 ≤ (d-1 : ℝ)*F*(1-F) := mul_nonneg (mul_nonneg (by linarith) hF0) (sub_nonneg.mpr hF1)
  have hpos := twoMeanOptimum_pos (by omega : 2 ≤ d) hf hfy hneg
  rw [twoMeanOptimum,if_neg (not_le.mpr hneg),twoMeanValue] at hpos
  have hL : 0 < y+(d-2 : ℝ)*f-2*Real.sqrt ((d-1 : ℝ)*f*(y-f)) :=
    (div_pos_iff_of_pos_right hdpos).mp hpos
  have hident : (d-1 : ℝ)*F*(1-F) = (d-1 : ℝ)*f*(y-f)+c^2+c*(y+(d-2 : ℝ)*f) := by
    dsimp [F,c,q]
    field_simp
    <;> ring
  have hsq : (Real.sqrt ((d-1 : ℝ)*f*(y-f))+c)^2 <
      (Real.sqrt ((d-1 : ℝ)*F*(1-F)))^2 := by
    rw [Real.sq_sqrt hA']
    have hs := Real.sq_sqrt hA
    have hprod := mul_pos hc hL
    nlinarith [hident]
  have hr := (sq_lt_sq₀ (add_nonneg (Real.sqrt_nonneg _) hc.le) (Real.sqrt_nonneg _)).mp hsq
  change twoMeanOptimum d F 1 < twoMeanOptimum d f y
  rw [twoMeanOptimum,if_neg (not_le.mpr hFneg),twoMeanOptimum,if_neg (not_le.mpr hneg)]
  unfold twoMeanValue
  apply (div_lt_div_iff_of_pos_right hdpos).mpr
  have hconst : y+(d-2 : ℝ)*f-(1+(d-2 : ℝ)*F) = -2*c := by
    dsimp [F,c,q]
    field_simp
    <;> ring
  linarith

/-- The finite source combination of its basis and anchored-cut phase averages. -/
def sourceAverage {n d : ℕ} (hn : 0 < n) (F : ℝ) :
    Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ :=
  ((d-1 : ℝ)/(supportRank n d-1 : ℝ)) • basisAverage hn F +
    ((d : ℝ)*(d-1 : ℝ)/(supportRank n d-1 : ℝ)) •
      ∑ s : SourceCut n hn, phaseAverage s.1ᶜ (sourceCut_complement hn s)
        (by simpa only [compl_compl] using sourceCut_nonempty hn s) F

/-- Full source matrix identity for S_F, using the actual disjoint support
and finite averages, in arbitrary allowed n,d. -/
theorem source_average_matrix {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {F : ℝ} (hF : 1/(d : ℝ) ≤ F) (hF1 : F ≤ 1) :
    sourceAverage (at_least_three_pos hn) F = F • rankOneDensity (ghz n d) +
      ((1-F)/(supportRank n d-1 : ℝ)) • (supportProjector n d-rankOneDensity (ghz n d)) := by
  classical
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hR : (supportRank n d : ℝ) = (d : ℝ)+(cutCount n : ℝ)*d*(d-1 : ℝ) := by
    simp [supportRank,Nat.cast_sub (by omega : 1 ≤ d)]
  have hR0 : (supportRank n d-1 : ℝ) ≠ 0 := by
    have h := (support_rank_bounds hn hd).1
    have h' : (d : ℝ) < supportRank n d := by exact_mod_cast h
    linarith
  have hT := support_projector_decomposition (d := d) (at_least_three_pos hn)
  have hT' : (∑ s : SourceCut n (at_least_three_pos hn),
      cutOffProjector s.1ᶜ (sourceCut_complement (by omega) s)
        (by simpa only [compl_compl] using sourceCut_nonempty (by omega) s)) =
      supportProjector n d-constantProjector n d := by rw [hT]; abel
  rw [sourceAverage,basis_average_matrix (by omega) hd hF hF1]
  simp_rw [phase_average_matrix hd _ _ _ hF hF1]
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,sourceCut_card,
    ← Nat.cast_smul_eq_nsmul ℝ,← Finset.smul_sum,hT']
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast (show (d : ℝ) ≠ 0 by linarith)
  have hdC1 : (d : ℂ)-1 ≠ 0 := by exact_mod_cast (show (d : ℝ)-1 ≠ 0 by linarith)
  have hRC0 : (supportRank n d : ℂ)-1 ≠ 0 := by exact_mod_cast hR0
  have hRC : (supportRank n d : ℂ) = (d : ℂ)+(cutCount n : ℂ)*d*(d-1 : ℂ) := by
    exact_mod_cast hR
  ext x y
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,Complex.real_smul]
  push_cast
  field_simp [hdC,hdC1,hRC0]
  rw [hRC]
  ring

/-- The actual computational Q sector, not an assumed cardinality. -/
def QIndex (n d : ℕ) := {x : Word (Fin d) n // ¬ (Finset.univ.image x).card ≤ 2}

instance qIndexFintype (n d : ℕ) : Fintype (QIndex n d) := by
  classical
  unfold QIndex
  infer_instance

/-- The source's d basis, K*3^d phase, and M-R Q components. -/
abbrev LowNoiseIndex (n d : ℕ) (hn : 0 < n) :=
  Fin d ⊕ ((SourceCut n hn × (Fin d → ZMod 3)) ⊕ QIndex n d)

instance lowNoiseIndexFintype (n d : ℕ) (hn : 0 < n) : Fintype (LowNoiseIndex n d hn) := by
  unfold LowNoiseIndex
  infer_instance

def lowNoiseWeights {n d : ℕ} (hn : 0 < n) (p : ℝ) : LowNoiseIndex n d hn → ℝ
  | .inl _ => noisyY n d p*(d-1 : ℝ)/((supportRank n d-1 : ℝ)*d)
  | .inr (.inl _) => noisyY n d p*(d : ℝ)*(d-1 : ℝ)/((supportRank n d-1 : ℝ)*(3^d : ℕ))
  | .inr (.inr _) => p/(wordCount n d : ℝ)

def lowNoiseStates {n d : ℕ} (hn : 0 < n) (p : ℝ) :
    LowNoiseIndex n d hn → Word (Fin d) n → ℂ
  | .inl j => chiVector hn j
      (optimalAlpha d (noisyF n d p/noisyY n d p)) (optimalBeta d (noisyF n d p/noisyY n d p))
  | .inr (.inl (s,θ)) => cutState s.1ᶜ (sourceCut_complement hn s)
      (by simpa only [compl_compl] using sourceCut_nonempty hn s)
      (optimalAlpha d (noisyF n d p/noisyY n d p)) (optimalBeta d (noisyF n d p/noisyY n d p))
      (phaseVector θ)
  | .inr (.inr x) => Pi.single x.1 1

private lemma qIndex_card {n d : ℕ} (hn : 0 < n) :
    Fintype.card (QIndex n d) = wordCount n d-supportRank n d := by
  classical
  unfold QIndex
  rw [Fintype.card_subtype_compl,support_rank_card hn]
  simp [wordCount,Word]

private lemma complementProjector_basis {n d : ℕ} :
    complementProjector n d = ∑ x : QIndex n d, rankOneDensity (Pi.single x.1 (1 : ℂ)) := by
  classical
  have he : complementProjector n d =
      diagonal (fun x : Word (Fin d) n => if ¬ (Finset.univ.image x).card ≤ 2 then (1 : ℂ) else 0) := by
    ext x y
    by_cases h : (Finset.univ.image x).card ≤ 2
    · simp [complementProjector,supportProjector,diagonal_apply,Matrix.one_apply,h]
    · have h' : 2 < (Finset.univ.image x).card := Nat.lt_of_not_ge h
      simp [complementProjector,supportProjector,diagonal_apply,Matrix.one_apply,h,h']
  rw [he,diagonal_projector_sum,← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

private lemma twoMeanOptimum_scaling {d : ℕ} {f y : ℝ} (hy : 0 < y) :
    y*twoMeanOptimum d (f/y) 1 = twoMeanOptimum d f y :=
  (twoMean_scaling hy).symm

private lemma low_noise_weight_sums {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hp : 0 ≤ p) (hpW : p ≤ witnessZeroProbability n d) :
    ((∑ j : Fin d, lowNoiseWeights (d := d) (at_least_three_pos hn) p (.inl j))+
      (∑ z : SourceCut n (at_least_three_pos hn) × (Fin d → ZMod 3),
        lowNoiseWeights (d := d) (at_least_three_pos hn) p (.inr (.inl z)))) = noisyY n d p ∧
      (∑ x : QIndex n d, lowNoiseWeights (d := d) (at_least_three_pos hn) p (.inr (.inr x))) = 1-noisyY n d p := by
  classical
  obtain ⟨hM,hR,hRM,hk,hpW0,hpW1⟩ := noisy_parameter_data hn hd
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hR0 : (supportRank n d-1 : ℝ) ≠ 0 := by linarith
  have hN : ((3^d : ℕ) : ℝ) ≠ 0 := by positivity
  have hRank : (supportRank n d : ℝ) = (d : ℝ)+(cutCount n : ℝ)*d*(d-1 : ℝ) := by
    simp [supportRank,Nat.cast_sub (by omega : 1 ≤ d)]
  constructor
  · simp only [lowNoiseWeights,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      Fintype.card_prod,Fintype.card_fun,ZMod.card,sourceCut_card,nsmul_eq_mul]
    push_cast
    field_simp [hd0,hR0,hN]
    rw [hRank]
    ring
  · have hRMnat : supportRank n d ≤ wordCount n d := (support_rank_bounds hn hd).2.le
    simp only [lowNoiseWeights,Finset.sum_const,Finset.card_univ,qIndex_card (at_least_three_pos hn),nsmul_eq_mul]
    push_cast [Nat.cast_sub hRMnat]
    unfold noisyY
    field_simp
    <;> ring

private lemma low_noise_weights_normalized {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hp : 0 ≤ p) (hpW : p ≤ witnessZeroProbability n d) :
    (∀ i, 0 ≤ lowNoiseWeights (d := d) (at_least_three_pos hn) p i) ∧
      (∑ i, lowNoiseWeights (d := d) (at_least_three_pos hn) p i) = 1 := by
  classical
  obtain ⟨hM,hR,hRM,hk,hpW0,hpW1⟩ := noisy_parameter_data hn hd
  obtain ⟨hy,hF,hF1⟩ := low_noise_ratio hn hd hp hpW
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hRpos : 0 < (supportRank n d-1 : ℝ) := by linarith
  constructor
  · intro i
    cases i with
    | inl j => exact div_nonneg (mul_nonneg hy.le (by linarith)) (mul_pos hRpos hdpos).le
    | inr z =>
      cases z with
      | inl z =>
        exact div_nonneg (mul_nonneg (mul_nonneg hy.le hdpos.le) (by linarith))
          (mul_pos hRpos (by positivity)).le
      | inr z => exact div_nonneg hp hM.le
  · obtain ⟨hs,hq⟩ := low_noise_weight_sums hn hd hp hpW
    change (∑ i : Fin d ⊕ ((SourceCut n (at_least_three_pos hn) × (Fin d → ZMod 3)) ⊕ QIndex n d), _) = 1
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    linarith

private lemma low_noise_states_unit {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hp : 0 ≤ p) (hpW : p ≤ witnessZeroProbability n d) :
    ∀ i, IsUnitState (lowNoiseStates (d := d) (at_least_three_pos hn) p i) := by
  obtain ⟨hy,hF,hF1⟩ := low_noise_ratio hn hd hp hpW
  intro i
  cases i with
  | inl j => exact (chi_attainment hn hd j hF hF1).1
  | inr z =>
    cases z with
    | inl z => exact (cutState_attainment hn hd _ _ _ (phaseVector z.2)
        (phaseVector_unit (by omega : 0 < d) z.2) hF hF1).1
    | inr x => exact basis_unit x.1

private lemma low_noise_matrix {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) (p : ℝ) :
    (∑ i, lowNoiseWeights (d := d) (at_least_three_pos hn) p i •
      rankOneDensity (lowNoiseStates (d := d) (at_least_three_pos hn) p i)) =
      noisyY n d p • sourceAverage (at_least_three_pos hn) (noisyF n d p/noisyY n d p) +
        (p/(wordCount n d : ℝ)) • complementProjector n d := by
  classical
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hR : (d : ℝ) < supportRank n d := by exact_mod_cast (support_rank_bounds hn hd).1
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hR0 : (supportRank n d-1 : ℝ) ≠ 0 := by linarith
  have hN : ((3^d : ℕ) : ℝ) ≠ 0 := by positivity
  change (∑ i : Fin d ⊕ ((SourceCut n (at_least_three_pos hn) × (Fin d → ZMod 3)) ⊕ QIndex n d), _) = _
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,lowNoiseWeights,lowNoiseStates]
  simp_rw [← Finset.smul_sum]
  rw [← complementProjector_basis]
  unfold sourceAverage basisAverage phaseAverage
  simp_rw [← Finset.smul_sum]
  simp only [smul_add,smul_smul]
  have ha : noisyY n d p*(d-1 : ℝ)/((supportRank n d-1 : ℝ)*d) =
      noisyY n d p*((d-1 : ℝ)/(supportRank n d-1 : ℝ))*(1/d) := by field_simp <;> ring
  have hb : noisyY n d p*(d : ℝ)*(d-1 : ℝ)/((supportRank n d-1 : ℝ)*(3^d : ℕ)) =
      noisyY n d p*((d : ℝ)*(d-1 : ℝ)/(supportRank n d-1 : ℝ))*(1/((3^d : ℕ) : ℝ)) := by
    field_simp
    <;> ring
  rw [ha,hb]
  module

/-- The complete original noisy matrix is reconstructed by the displayed
finite source ensemble, for the full closed low-noise interval. -/
theorem low_noise_reconstruction {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hp : 0 ≤ p) (hpW : p ≤ witnessZeroProbability n d) :
    noisyGhz n d p = ∑ i, lowNoiseWeights (d := d) (at_least_three_pos hn) p i •
      rankOneDensity (lowNoiseStates (d := d) (at_least_three_pos hn) p i) := by
  obtain ⟨hy,hF,hF1⟩ := low_noise_ratio hn hd hp hpW
  obtain ⟨hM,hR,_,_,_,_⟩ := noisy_parameter_data hn hd
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hR0 : (supportRank n d-1 : ℝ) ≠ 0 := by linarith
  have hyF : noisyY n d p*(noisyF n d p/noisyY n d p) = noisyF n d p := mul_div_cancel₀ _ hy.ne'
  have hc : noisyY n d p*((1-noisyF n d p/noisyY n d p)/(supportRank n d-1 : ℝ)) =
      p/(wordCount n d : ℝ) := by
    calc
      _ = (noisyY n d p-noisyY n d p*(noisyF n d p/noisyY n d p))/(supportRank n d-1 : ℝ) := by ring
      _ = (noisyY n d p-noisyF n d p)/(supportRank n d-1 : ℝ) := by rw [hyF]
      _ = _ := by unfold noisyY noisyF; field_simp <;> ring
  rw [low_noise_matrix hn hd,source_average_matrix hn hd hF hF1,
    smul_add,smul_smul,smul_smul,hyF,hc]
  unfold noisyGhz complementProjector noisyF wordCount
  ext x y
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,Complex.real_smul]
  push_cast
  ring

private lemma low_noise_average {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hp : 0 ≤ p) (hpW : p ≤ witnessZeroProbability n d) :
    (∑ i, lowNoiseWeights (d := d) (at_least_three_pos hn) p i *
      geometricMeasurePure (lowNoiseStates (d := d) (at_least_three_pos hn) p i)) =
      twoMeanOptimum d (noisyF n d p) (noisyY n d p) := by
  classical
  obtain ⟨hy,hF,hF1⟩ := low_noise_ratio hn hd hp hpW
  let e := twoMeanOptimum d (noisyF n d p/noisyY n d p) 1
  have hEb (j : Fin d) : geometricMeasurePure
      (lowNoiseStates (d := d) (at_least_three_pos hn) p (.inl j)) = e :=
    (chi_attainment hn hd j hF hF1).2.2.2
  have hEp (z : SourceCut n (at_least_three_pos hn) × (Fin d → ZMod 3)) :
      geometricMeasurePure (lowNoiseStates (d := d) (at_least_three_pos hn) p (.inr (.inl z))) = e :=
    (cutState_attainment hn hd _ _ _ (phaseVector z.2)
      (phaseVector_unit (by omega : 0 < d) z.2) hF hF1).2.2.2
  have hEq (x : QIndex n d) : geometricMeasurePure
      (lowNoiseStates (d := d) (at_least_three_pos hn) p (.inr (.inr x))) = 0 :=
    biseparable_measure_zero (by omega : 2 ≤ n) (by omega : 0 < d) _
      (computational_biseparable (by omega) x.1)
  have hs := (low_noise_weight_sums hn hd hp hpW).1
  calc
    _ = ((∑ j : Fin d, lowNoiseWeights (d := d) (at_least_three_pos hn) p (.inl j))+
        (∑ z : SourceCut n (at_least_three_pos hn) × (Fin d → ZMod 3),
          lowNoiseWeights (d := d) (at_least_three_pos hn) p (.inr (.inl z))))*e := by
      simp only [Fintype.sum_sum_type]
      simp_rw [hEb,hEp,hEq]
      simp only [mul_zero,Finset.sum_const_zero,add_zero]
      rw [← Finset.sum_mul,← Finset.sum_mul]
      ring
    _ = noisyY n d p*e := by rw [hs]
    _ = _ := twoMeanOptimum_scaling hy

/-- All finite weights, amplitudes, full matrix reconstruction and mean
entanglement of the low-noise ensemble, with its attained actual roof. -/
theorem low_noise_attainment {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hp : 0 ≤ p) (hpW : p ≤ witnessZeroProbability n d) :
    (∀ i, 0 ≤ lowNoiseWeights (d := d) (at_least_three_pos hn) p i) ∧
      (∑ i, lowNoiseWeights (d := d) (at_least_three_pos hn) p i) = 1 ∧
      (∀ i, IsUnitState (lowNoiseStates (d := d) (at_least_three_pos hn) p i)) ∧
      noisyGhz n d p = ∑ i, lowNoiseWeights (d := d) (at_least_three_pos hn) p i •
        rankOneDensity (lowNoiseStates (d := d) (at_least_three_pos hn) p i) ∧
      (∑ i, lowNoiseWeights (d := d) (at_least_three_pos hn) p i *
        geometricMeasurePure (lowNoiseStates (d := d) (at_least_three_pos hn) p i)) =
        twoMeanOptimum d (noisyF n d p) (noisyY n d p) ∧
      geometricMeasure (noisyGhz n d p) = twoMeanOptimum d (noisyF n d p) (noisyY n d p) := by
  obtain ⟨hweights,hsum⟩ := low_noise_weights_normalized hn hd hp hpW
  have hunit := low_noise_states_unit hn hd hp hpW
  have hmatrix := low_noise_reconstruction hn hd hp hpW
  have havg := low_noise_average hn hd hp hpW
  refine ⟨hweights,hsum,hunit,hmatrix,havg,?_⟩
  apply le_antisymm
  · rw [hmatrix]
    exact (finite_ensemble_upper (by omega) (by omega) _ _ hweights hsum hunit).trans_eq havg
  · have hp1 := hpW.trans (noisy_parameter_data hn hd).2.2.2.2.2.le
    have h := two_mean_lower hn hd (noisyDensity (by omega) (by omega) p hp hp1)
    rw [noisyDensity_matrix,(noisy_means (by omega) (by omega) p).1,
      (noisy_means (by omega) (by omega) p).2] at h
    exact h

private lemma optimal_threshold_amplitudes {d : ℕ} (hd : 3 ≤ d) :
    optimalAlpha d (1/(d : ℝ)) = 1 ∧ optimalBeta d (1/(d : ℝ)) = 0 := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hd0 : (d : ℝ) ≠ 0 := hdpos.ne'
  have hF1 : 1/(d : ℝ) ≤ 1 := (div_le_one hdpos).mpr (by linarith)
  obtain ⟨hb,hba,hnorm,hmean,_⟩ := optimal_amplitudes (by omega : 2 ≤ d) (le_refl (1/(d : ℝ))) hF1
  have ha := hb.trans hba
  have hm : (optimalAlpha d (1/(d : ℝ))+(d-1 : ℝ)*optimalBeta d (1/(d : ℝ)))^2 = 1 := by
    have h := congrArg (fun x : ℝ => x*(d : ℝ)) hmean
    simpa [hd0] using h
  have he : (d-1 : ℝ)*(d-2 : ℝ)*(optimalBeta d (1/(d : ℝ)))^2+
      2*(d-1 : ℝ)*optimalAlpha d (1/(d : ℝ))*optimalBeta d (1/(d : ℝ)) = 0 := by
    linear_combination hm-hnorm
  have hcross : 0 ≤ 2*(d-1 : ℝ)*optimalAlpha d (1/(d : ℝ))*optimalBeta d (1/(d : ℝ)) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) ha) hb
  have hcoeff : 0 < (d-1 : ℝ)*(d-2 : ℝ) := mul_pos (by linarith) (by linarith)
  have hsq : (optimalBeta d (1/(d : ℝ)))^2 ≤ 0 := by
    nlinarith [sq_nonneg (optimalBeta d (1/(d : ℝ)))]
  have hβ : optimalBeta d (1/(d : ℝ)) = 0 := by nlinarith [sq_nonneg (optimalBeta d (1/(d : ℝ)))]
  refine ⟨?_,hβ⟩
  rw [hβ] at hnorm
  nlinarith

private lemma cutState_one_zero {n d : ℕ} (a : Finset (Fin n)) (ha : a.Nonempty)
    (hc : aᶜ.Nonempty) (u : Fin d → ℂ) : cutState a ha hc 1 0 u = cutProduct a ha hc u := by
  unfold cutState cutProduct
  congr 1
  funext ij
  simp

private lemma chi_one_zero {n d : ℕ} (hn : 0 < n) (j : Fin d) :
    chiVector hn j 1 0 = Pi.single (fun _ : Fin n => j) (1 : ℂ) := by
  classical
  ext x
  by_cases hx : ∃ i : Fin d, ∀ k, x k = i
  · obtain ⟨i,hi⟩ := hx
    have he := funext hi
    subst x
    have hconst : ((fun _ : Fin n => i) = fun _ : Fin n => j) ↔ i = j :=
      ⟨fun h => constant_word_injective hn h,fun h => h ▸ rfl⟩
    simp [chiVector,constantVector_apply,Pi.single_apply,hconst,eq_comm]
  · have hne : (fun _ : Fin n => j) ≠ x := by
      intro h
      exact hx ⟨j,fun k => (congrFun h k).symm⟩
    rw [chiVector,constantVector_off hn _ _ hx]
    simp [Pi.single_apply,hne,Ne.symm hne]

private lemma noisy_threshold_ratio {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    noisyF n d (witnessZeroProbability n d)/noisyY n d (witnessZeroProbability n d) = 1/(d : ℝ) := by
  obtain ⟨hM,hR,hRM,hk,hpW0,hpW1⟩ := noisy_parameter_data hn hd
  obtain ⟨_,_,hy,_⟩ := noisy_triangle hn hd hpW0.le hpW1.le
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hw : witnessValue n d (witnessZeroProbability n d) = 0 := by
    rw [witness_value_affine (by omega) (by omega),witnessZeroProbability]
    field_simp
    <;> ring
  rw [noisy_witness_means (by omega) (by omega)] at hw
  have h := (div_eq_iff hd0).mp (show noisyY n d (witnessZeroProbability n d)/d =
    noisyF n d (witnessZeroProbability n d) by linarith)
  apply (div_eq_div_iff hy.ne' hd0).mpr
  nlinarith

/-- Every finite constituent at the threshold is genuinely biseparable
across its displayed cut; this does not infer factorization from a zero roof. -/
theorem threshold_constituents_biseparable {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    ∀ i, IsBiseparable (lowNoiseStates (d := d) (at_least_three_pos hn) (witnessZeroProbability n d) i) := by
  obtain ⟨hα,hβ⟩ := optimal_threshold_amplitudes hd
  intro i
  cases i with
  | inl j =>
    simp only [lowNoiseStates,noisy_threshold_ratio hn hd,hα,hβ,chi_one_zero]
    exact computational_biseparable (by omega) _
  | inr z =>
    cases z with
    | inl z =>
      simp only [lowNoiseStates,noisy_threshold_ratio hn hd,hα,hβ,cutState_one_zero]
      exact cutProduct_biseparable _ _ _ _ (phaseVector_unit (by omega) z.2)
    | inr x => exact computational_biseparable (by omega) x.1


def highNoiseLambda (n d : ℕ) (p : ℝ) : ℝ :=
  (1-p)/(1-witnessZeroProbability n d)

abbrev HighNoiseIndex (n d : ℕ) (hn : 0 < n) := LowNoiseIndex n d hn ⊕ Word (Fin d) n

instance highNoiseIndexFintype (n d : ℕ) (hn : 0 < n) : Fintype (HighNoiseIndex n d hn) := by
  unfold HighNoiseIndex
  infer_instance

def highNoiseWeights {n d : ℕ} (hn : 0 < n) (p : ℝ) : HighNoiseIndex n d hn → ℝ
  | .inl i => highNoiseLambda n d p*lowNoiseWeights (d := d) hn (witnessZeroProbability n d) i
  | .inr _ => (1-highNoiseLambda n d p)/(wordCount n d : ℝ)

def highNoiseStates {n d : ℕ} (hn : 0 < n) : HighNoiseIndex n d hn → Word (Fin d) n → ℂ
  | .inl i => lowNoiseStates (d := d) hn (witnessZeroProbability n d) i
  | .inr x => Pi.single x 1

private lemma high_noise_lambda_bounds {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hpW : witnessZeroProbability n d ≤ p) (hp1 : p ≤ 1) :
    0 ≤ highNoiseLambda n d p ∧ highNoiseLambda n d p ≤ 1 := by
  have hW := (noisy_parameter_data hn hd).2.2.2.2.2
  have hden : 0 < 1-witnessZeroProbability n d := sub_pos.mpr hW
  exact ⟨div_nonneg (sub_nonneg.mpr hp1) hden.le,
    (div_le_one hden).mpr (by linarith)⟩

private lemma high_noise_weights_normalized {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hpW : witnessZeroProbability n d ≤ p) (hp1 : p ≤ 1) :
    (∀ i, 0 ≤ highNoiseWeights (d := d) (at_least_three_pos hn) p i) ∧
      (∑ i, highNoiseWeights (d := d) (at_least_three_pos hn) p i) = 1 := by
  classical
  obtain ⟨hM,_,_,_,hW0,_⟩ := noisy_parameter_data hn hd
  obtain ⟨hl,hl1⟩ := high_noise_lambda_bounds hn hd hpW hp1
  obtain ⟨hw,hs⟩ := low_noise_weights_normalized hn hd hW0.le (le_refl _)
  constructor
  · intro i
    cases i with
    | inl i => exact mul_nonneg hl (hw i)
    | inr x => exact div_nonneg (sub_nonneg.mpr hl1) hM.le
  · change (∑ i : LowNoiseIndex n d (at_least_three_pos hn) ⊕ Word (Fin d) n, _) = 1
    simp only [Fintype.sum_sum_type,highNoiseWeights,← Finset.mul_sum,hs,mul_one,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    have hcard : (Fintype.card (Word (Fin d) n) : ℝ) = wordCount n d := by simp [Word,wordCount]
    rw [hcard,mul_div_cancel₀ _ hM.ne']
    ring

private lemma high_noise_states_biseparable {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    ∀ i, IsBiseparable (highNoiseStates (d := d) (at_least_three_pos hn) i) := by
  intro i
  cases i with
  | inl i => exact threshold_constituents_biseparable hn hd i
  | inr x => exact computational_biseparable (by omega) x

/-- Exact actual high-noise reconstruction from the threshold cut products
and the finite computational ensemble for I/M. -/
theorem high_noise_reconstruction {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hpW : witnessZeroProbability n d ≤ p) (hp1 : p ≤ 1) :
    noisyGhz n d p = ∑ i, highNoiseWeights (d := d) (at_least_three_pos hn) p i •
      rankOneDensity (highNoiseStates (d := d) (at_least_three_pos hn) i) := by
  classical
  obtain ⟨hM,_,_,_,hW0,hW1⟩ := noisy_parameter_data hn hd
  have hl : highNoiseLambda n d p*(1-witnessZeroProbability n d) = 1-p := by
    unfold highNoiseLambda
    exact div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hW1))
  change noisyGhz n d p = ∑ i : LowNoiseIndex n d (at_least_three_pos hn) ⊕ Word (Fin d) n, _
  rw [Fintype.sum_sum_type]
  simp only [highNoiseWeights,highNoiseStates,mul_smul,← Finset.smul_sum]
  rw [← low_noise_reconstruction hn hd hW0.le (le_refl _),basis_projector_sum]
  unfold noisyGhz wordCount
  simp only [Nat.cast_pow]
  rw [smul_add,smul_smul,smul_smul,hl]
  have he : highNoiseLambda n d p*(witnessZeroProbability n d/(d^n : ℝ))+
      (1-highNoiseLambda n d p)/(d^n : ℝ) = p/(d^n : ℝ) := by
    have hM0 : (d^n : ℝ) ≠ 0 := by positivity
    field_simp
    nlinarith [hl]
  rw [add_assoc,add_comm ((1-p) • rankOneDensity (ghz n d)),← add_assoc,← add_smul,he]

/-- The high-noise interval has an explicit normalized finite biseparable
ensemble and hence zero actual convex roof, including p=1. -/
theorem high_noise_attainment {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hpW : witnessZeroProbability n d ≤ p) (hp1 : p ≤ 1) :
    (∀ i, 0 ≤ highNoiseWeights (d := d) (at_least_three_pos hn) p i) ∧
      (∑ i, highNoiseWeights (d := d) (at_least_three_pos hn) p i) = 1 ∧
      (∀ i, IsBiseparable (highNoiseStates (d := d) (at_least_three_pos hn) i)) ∧
      noisyGhz n d p = ∑ i, highNoiseWeights (d := d) (at_least_three_pos hn) p i •
        rankOneDensity (highNoiseStates (d := d) (at_least_three_pos hn) i) ∧
      geometricMeasure (noisyGhz n d p) = 0 := by
  obtain ⟨hw,hs⟩ := high_noise_weights_normalized hn hd hpW hp1
  have hb := high_noise_states_biseparable hn hd
  have hm := high_noise_reconstruction hn hd hpW hp1
  refine ⟨hw,hs,hb,hm,?_⟩
  rw [hm]
  exact biseparable_ensemble_zero (by omega) (by omega) _ _ hw hs hb

private lemma noisy_optimum_zero {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hpW : witnessZeroProbability n d ≤ p) :
    twoMeanOptimum d (noisyF n d p) (noisyY n d p) = 0 := by
  obtain ⟨_,_,_,hk,_,_⟩ := noisy_parameter_data hn hd
  have hw : 0 ≤ witnessValue n d p := by
    rw [witness_value_affine (by omega) (by omega)]
    have h := (div_le_iff₀ hk).mp hpW
    change (d-1 : ℝ)/d ≤ p*witnessSlope n d at h
    rw [neg_div]
    nlinarith
  rw [noisy_witness_means (by omega) (by omega)] at hw
  have hdpos : (0 : ℝ) < d := by positivity
  have h : (d : ℝ)*noisyF n d p ≤ noisyY n d p := by
    have h' := (le_div_iff₀ hdpos).mp (show noisyF n d p ≤ noisyY n d p/d by linarith)
    linarith
  simp [twoMeanOptimum,h]

/-- The complete all-parameter noisy-GHZ convex roof in the original finite
matrix-ensemble semantics, obtained by the two explicit finite regimes. -/
theorem noisy_exact_roof {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    geometricMeasure (noisyGhz n d p) = twoMeanOptimum d (noisyF n d p) (noisyY n d p) ∧
      geometricMeasure (noisyGhz n d p) =
        (max (Real.sqrt ((d-1 : ℝ)*(1-p+p/(wordCount n d : ℝ)))-
          Real.sqrt (p*(supportRank n d-1 : ℝ)/(wordCount n d : ℝ))) 0)^2/d := by
  have he : geometricMeasure (noisyGhz n d p) = twoMeanOptimum d (noisyF n d p) (noisyY n d p) := by
    by_cases h : p ≤ witnessZeroProbability n d
    · exact (low_noise_attainment hn hd hp h).2.2.2.2.2
    · rw [(high_noise_attainment hn hd (le_of_not_ge h) hp1).2.2.2.2,noisy_optimum_zero hn hd (le_of_not_ge h)]
  refine ⟨he,?_⟩
  obtain ⟨hf,hfy,_,_⟩ := noisy_triangle hn hd hp hp1
  rw [he,twoMeanOptimum_max (by omega : 2 ≤ d) hf hfy]
  congr 4
  unfold noisyY noisyF
  ring

def starDenominator (d : ℕ) : ℝ := (d : ℝ)^2-3*d+3
def starProbability (n d : ℕ) : ℝ := (d-2 : ℝ)^2/(starDenominator d*witnessSlope n d)
def starWitness (d : ℕ) : ℝ := -(2*d-3 : ℝ)/((d : ℝ)*starDenominator d)
def starValue (d : ℕ) : ℝ := 1/((d-1 : ℝ)^3+1)

private lemma star_value_formula (d : ℕ) : starValue d = 1/((d : ℝ)*starDenominator d) := by
  unfold starValue starDenominator
  congr 1
  ring

private lemma star_denominator_pos {d : ℕ} (hd : 3 ≤ d) : 0 < starDenominator d := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h : starDenominator d = (d-1 : ℝ)*(d-2 : ℝ)+1 := by unfold starDenominator; ring
  rw [h]
  exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) (by linarith)) (by norm_num)

/-- Exact source noise threshold, including strict physical probability bounds. -/
theorem witness_threshold_formula {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    witnessZeroProbability n d = (wordCount n d : ℝ)*(d-1 : ℝ)/
      ((wordCount n d : ℝ)*(d-1 : ℝ)+supportRank n d-d) ∧
      0 < witnessZeroProbability n d ∧ witnessZeroProbability n d < 1 := by
  obtain ⟨hM,hR,hRM,hk,hpW0,hpW1⟩ := noisy_parameter_data hn hd
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hden : 0 < (wordCount n d : ℝ)*(d-1 : ℝ)+supportRank n d-d := by
    have hpos := mul_pos hM (show 0 < (d-1 : ℝ) by linarith)
    linarith
  refine ⟨?_,hpW0,hpW1⟩
  unfold witnessZeroProbability witnessSlope
  field_simp
  <;> ring

private lemma star_probability_bounds {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    0 < starProbability n d ∧ starProbability n d < witnessZeroProbability n d := by
  obtain ⟨hM,hR,hRM,hk,hpW0,hpW1⟩ := noisy_parameter_data hn hd
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hT := star_denominator_pos hd
  have hpoly : (d : ℝ)*(d-2 : ℝ)^2 < (d-1 : ℝ)*starDenominator d := by
    unfold starDenominator
    nlinarith
  refine ⟨div_pos (sq_pos_of_pos (by linarith)) (mul_pos hT hk),?_⟩
  unfold starProbability witnessZeroProbability
  have he : ((d-1 : ℝ)/d)/witnessSlope n d = (d-1 : ℝ)/(d*witnessSlope n d) := by field_simp
  rw [he]
  apply (div_lt_div_iff₀ (mul_pos hT hk) (mul_pos hdpos hk)).mpr
  have h := mul_lt_mul_of_pos_right hpoly hk
  nlinarith

private lemma star_witness_value {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    witnessValue n d (starProbability n d) = starWitness d := by
  obtain ⟨hM,hR,hRM,hk,_,_⟩ := noisy_parameter_data hn hd
  have hT := star_denominator_pos hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  rw [witness_value_affine (by omega) (by omega)]
  unfold starProbability starWitness
  field_simp [hT.ne',hk.ne',hdpos.ne']
  unfold starDenominator
  ring

private lemma star_optimum_value {d : ℕ} (hd : 3 ≤ d) :
    twoMeanOptimum d ((d-1 : ℝ)/starDenominator d) 1 = starValue d := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hT := star_denominator_pos hd
  have hhigh : 1 < (d : ℝ)*((d-1 : ℝ)/starDenominator d) := by
    rw [← mul_div_assoc]
    apply (lt_div_iff₀ hT).mpr
    unfold starDenominator
    nlinarith
  have hrad : (d-1 : ℝ)*((d-1 : ℝ)/starDenominator d)*(1-(d-1 : ℝ)/starDenominator d) =
      ((d-1 : ℝ)*(d-2 : ℝ)/starDenominator d)^2 := by
    unfold starDenominator
    field_simp
    <;> ring
  have hrad0 : 0 ≤ (d-1 : ℝ)*(d-2 : ℝ)/starDenominator d :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) hT.le
  rw [twoMeanOptimum,if_neg (not_le.mpr hhigh),twoMeanValue,hrad,Real.sqrt_sq hrad0]
  rw [star_value_formula]
  field_simp [hT.ne',show (d : ℝ) ≠ 0 by linarith]
  unfold starDenominator
  ring

/-- The original single-witness conjugate has the exact source value at
the strict interior probability p_star. -/
theorem star_single_witness {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    0 < starProbability n d ∧ starProbability n d < witnessZeroProbability n d ∧
      witnessZeroProbability n d < 1 ∧
      witnessValue n d (starProbability n d) = starWitness d ∧
      epsilonO n d (starProbability n d) = starValue d := by
  obtain ⟨hp,hpW⟩ := star_probability_bounds hn hd
  have hpW1 := (noisy_parameter_data hn hd).2.2.2.2.2
  refine ⟨hp,hpW,hpW1,star_witness_value hn hd,?_⟩
  have hε := noisy_witness_optimum hn hd hp.le (hpW.trans hpW1).le
  have hw := noisy_witness_means (by omega : 0 < n) (by omega : 0 < d) (starProbability n d)
  have harg : noisyF n d (starProbability n d)+(1-noisyY n d (starProbability n d))/d =
      (d-1 : ℝ)/starDenominator d := by
    rw [star_witness_value hn hd] at hw
    have he : 1/(d : ℝ)-starWitness d = (d-1 : ℝ)/starDenominator d := by
      have hT := star_denominator_pos hd
      unfold starWitness
      field_simp [hT.ne',show (d : ℝ) ≠ 0 by positivity]
      unfold starDenominator
      ring
    calc
      _ = 1/(d : ℝ)-(noisyY n d (starProbability n d)/d-noisyF n d (starProbability n d)) := by ring
      _ = 1/(d : ℝ)-starWitness d := by rw [← hw]
      _ = _ := he
  rw [harg] at hε
  exact hε.trans (star_optimum_value hd)

/-- Strict failure of the complete original single-witness optimum throughout
the open negative-witness noisy interval. -/
theorem noisy_strict_gap {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {p : ℝ} (hp : 0 < p) (hpW : p < witnessZeroProbability n d) :
    epsilonO n d p < twoMeanOptimum d (noisyF n d p) (noisyY n d p) ∧
      twoMeanOptimum d (noisyF n d p) (noisyY n d p) = geometricMeasure (noisyGhz n d p) := by
  obtain ⟨hM,_,hRM,hk,_,hW1⟩ := noisy_parameter_data hn hd
  have hp1 := (hpW.trans hW1).le
  obtain ⟨hf,hfy,hy0,hy1⟩ := noisy_triangle hn hd hp.le hp1
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hy : noisyY n d p < 1 := by
    have hr := (div_lt_one hM).mpr hRM
    have hprod := mul_pos hp (sub_pos.mpr hr)
    have he : 1-noisyY n d p = p*(1-(supportRank n d : ℝ)/wordCount n d) := by
      unfold noisyY
      ring
    rw [← he] at hprod
    linarith
  have hw : witnessValue n d p < 0 := by
    rw [witness_value_affine (by omega) (by omega)]
    have h := (lt_div_iff₀ hk).mp hpW
    change p*witnessSlope n d < (d-1 : ℝ)/d at h
    rw [neg_div]
    nlinarith
  rw [noisy_witness_means (by omega) (by omega)] at hw
  have hneg : noisyY n d p < (d : ℝ)*noisyF n d p := by
    have h := (div_lt_iff₀ hdpos).mp (show noisyY n d p/d < noisyF n d p by linarith)
    linarith
  rw [noisy_witness_optimum hn hd hp.le hp1]
  exact ⟨two_mean_strict_witness_gap hd hf hfy hy hneg,(noisy_exact_roof hn hd hp.le hp1).1.symm⟩

/-- The common zero region and the noiseless endpoint retain equality;
the strict gap excludes both endpoints of its stated interval. -/
theorem noisy_gap_endpoints {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    epsilonO n d 0 = geometricMeasure (noisyGhz n d 0) ∧
      ∀ p : ℝ, witnessZeroProbability n d ≤ p → p ≤ 1 →
        epsilonO n d p = 0 ∧ geometricMeasure (noisyGhz n d p) = 0 := by
  constructor
  · rw [noisy_witness_optimum hn hd (le_refl 0) (by norm_num),
      (noisy_exact_roof hn hd (le_refl 0) (by norm_num)).1]
    simp [noisyF,noisyY]
  · intro p hpW hp1
    have hp := (noisy_parameter_data hn hd).2.2.2.2.1.le.trans hpW
    have hz := noisy_optimum_zero hn hd hpW
    have hDF : (d : ℝ)*noisyF n d p ≤ noisyY n d p := by
      by_contra h
      obtain ⟨hf,hfy,_,_⟩ := noisy_triangle hn hd hp hp1
      have hpos := twoMeanOptimum_pos (by omega : 2 ≤ d) hf hfy (lt_of_not_ge h)
      linarith
    have hdpos : (0 : ℝ) < d := by positivity
    have he : (d : ℝ)*(noisyF n d p+(1-noisyY n d p)/d) ≤ 1 := by
      field_simp
      nlinarith
    rw [noisy_witness_optimum hn hd hp hp1]
    exact ⟨by simp [twoMeanOptimum,he],(high_noise_attainment hn hd hpW hp1).2.2.2.2⟩

/-- At p_star the universal affine certificate itself strictly exceeds the
entire original witness optimum by the source's positive Q correction. -/
theorem star_certificate_gap {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    starValue d < starValue d+1/((d : ℝ)^2*(d-2 : ℝ))*starProbability n d*
        (1-(supportRank n d : ℝ)/wordCount n d) ∧
      starValue d+1/((d : ℝ)^2*(d-2 : ℝ))*starProbability n d*
        (1-(supportRank n d : ℝ)/wordCount n d) ≤
        geometricMeasure (noisyGhz n d (starProbability n d)) := by
  obtain ⟨hM,_,hRM,_,_,hW1⟩ := noisy_parameter_data hn hd
  obtain ⟨hp,hpW⟩ := star_probability_bounds hn hd
  have hp1 := (hpW.trans hW1).le
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hT := star_denominator_pos hd
  have hh : 0 < 1/((d : ℝ)^2*(d-2 : ℝ)) :=
    div_pos (by norm_num) (mul_pos (sq_pos_of_pos (by linarith)) (by linarith))
  have hq : 0 < 1-(supportRank n d : ℝ)/wordCount n d := sub_pos.mpr ((div_lt_one hM).mpr hRM)
  refine ⟨lt_add_of_pos_right _ (mul_pos (mul_pos hh hp) hq),?_⟩
  have hc := affine_certificate hn hd (noisyDensity (by omega) (by omega) (starProbability n d) hp.le hp1)
  rw [noisyDensity_matrix] at hc
  have hQ : observableMean (noisyGhz n d (starProbability n d)) (complementProjector n d) =
      starProbability n d*(1-(supportRank n d : ℝ)/wordCount n d) := by
    rw [complementProjector,mean_sub,← noisyDensity_matrix (by omega) (by omega) _ hp.le hp1,
      mean_one,noisyDensity_matrix,(noisy_means (by omega) (by omega) _).2]
    unfold noisyY
    ring
  change -(d-1 : ℝ)/(d*(d-2 : ℝ))*witnessValue n d (starProbability n d)+
    1/((d : ℝ)^2*(d-2 : ℝ))*observableMean (noisyGhz n d (starProbability n d)) (complementProjector n d)-
    1/((d : ℝ)^2*(d-2 : ℝ)) ≤ _ at hc
  rw [star_witness_value hn hd,hQ] at hc
  have he : -(d-1 : ℝ)/(d*(d-2 : ℝ))*starWitness d-1/((d : ℝ)^2*(d-2 : ℝ)) = starValue d := by
    rw [star_value_formula]
    unfold starWitness
    field_simp [hT.ne',show (d : ℝ) ≠ 0 by linarith,show (d : ℝ)-2 ≠ 0 by linarith]
    unfold starDenominator
    ring
  linarith

private lemma qutrit_noisy_means :
    noisyF 3 3 (3/8) = 23/36 ∧ noisyY 3 3 (3/8) = 11/12 ∧
      noisyF 3 3 (3/8)/noisyY 3 3 (3/8) = 23/33 := by
  norm_num [noisyF,noisyY,wordCount,supportRank,cutCount]

private lemma qutrit_radical_strict : (13 : ℝ)/108 < (14-Real.sqrt 115)/27 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 115)
  have hp := Real.sqrt_nonneg (115 : ℝ)
  have h : Real.sqrt (115 : ℝ) < 43/4 := by nlinarith
  linarith

/-- Exact qutrit roof and the 90 actual source components. Amplitudes are
the universal lowNoiseStates specialized at F=23/33; the full matrix identity
is specialized from the arbitrary-dimensional reconstruction, not inferred
from its two means. -/
theorem qutrit_exact_ensemble :
    Fintype.card (SourceCut 3 (by norm_num) × (Fin 3 → ZMod 3)) = 81 ∧
      Fintype.card (QIndex 3 3) = 6 ∧
      Fintype.card (LowNoiseIndex 3 3 (by norm_num)) = 90 ∧
      (∀ j : Fin 3, lowNoiseWeights (n := 3) (d := 3) (by norm_num) (3/8) (.inl j) = 11/360) ∧
      (∀ z : SourceCut 3 (by norm_num) × (Fin 3 → ZMod 3),
        lowNoiseWeights (n := 3) (d := 3) (by norm_num) (3/8) (.inr (.inl z)) = 11/1080) ∧
      (∀ x : QIndex 3 3,
        lowNoiseWeights (n := 3) (d := 3) (by norm_num) (3/8) (.inr (.inr x)) = 1/72) ∧
      (∀ i, 0 ≤ lowNoiseWeights (n := 3) (d := 3) (by norm_num) (3/8) i) ∧
      (∑ i, lowNoiseWeights (n := 3) (d := 3) (by norm_num) (3/8) i) = 1 ∧
      (∀ i, IsUnitState (lowNoiseStates (n := 3) (d := 3) (by norm_num) (3/8) i)) ∧
      ((1/72 : ℝ) • (1 : Matrix (Word (Fin 3) 3) (Word (Fin 3) 3) ℂ)+
        (5/8 : ℝ) • rankOneDensity (ghz 3 3)) =
        ∑ i, lowNoiseWeights (n := 3) (d := 3) (by norm_num) (3/8) i •
          rankOneDensity (lowNoiseStates (n := 3) (d := 3) (by norm_num) (3/8) i) ∧
      (∑ i, lowNoiseWeights (n := 3) (d := 3) (by norm_num) (3/8) i *
        geometricMeasurePure (lowNoiseStates (n := 3) (d := 3) (by norm_num) (3/8) i)) =
          (14-Real.sqrt 115)/27 ∧
      geometricMeasure ((1/72 : ℝ) • (1 : Matrix (Word (Fin 3) 3) (Word (Fin 3) 3) ℂ)+
        (5/8 : ℝ) • rankOneDensity (ghz 3 3)) = (14-Real.sqrt 115)/27 ∧
      (13 : ℝ)/108 < (14-Real.sqrt 115)/27 ∧
      (1 : ℝ)/9 < 13/108 ∧ epsilonO 3 3 (3/8) = 1/9 := by
  have hpW : (3 : ℝ)/8 ≤ witnessZeroProbability 3 3 := by
    rw [qutrit_source_arithmetic.2.2.2.2]
    norm_num
  obtain ⟨hw,hs,hu,hm,ha,he⟩ := low_noise_attainment (n := 3) (d := 3) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ 3/8) hpW
  have hm' : noisyGhz 3 3 (3/8) =
      (1/72 : ℝ) • (1 : Matrix (Word (Fin 3) 3) (Word (Fin 3) 3) ℂ)+
        (5/8 : ℝ) • rankOneDensity (ghz 3 3) := by norm_num [noisyGhz]
  have hv : twoMeanOptimum 3 (noisyF 3 3 (3/8)) (noisyY 3 3 (3/8)) =
      (14-Real.sqrt 115)/27 := by
    rw [qutrit_noisy_means.1,qutrit_noisy_means.2.1]
    rw [twoMeanOptimum,if_neg (by norm_num)]
    exact qutrit_two_mean_value
  have hc : Fintype.card (LowNoiseIndex 3 3 (by norm_num)) = 90 := by
    simp [LowNoiseIndex,Fintype.card_sum,Fintype.card_prod,Fintype.card_fun,
      sourceCut_card,qIndex_card,wordCount,supportRank,cutCount]
  refine ⟨by simp [Fintype.card_prod,Fintype.card_fun,sourceCut_card,cutCount],
    by simp [qIndex_card (by norm_num : 0 < 3),wordCount,supportRank,cutCount],hc,?_,?_,?_,hw,hs,hu,hm' ▸ hm,ha.trans hv,?_,qutrit_radical_strict,by norm_num,?_⟩
  · intro j
    norm_num [lowNoiseWeights,noisyY,wordCount,supportRank,cutCount]
  · intro z
    norm_num [lowNoiseWeights,noisyY,wordCount,supportRank,cutCount]
  · intro x
    norm_num [lowNoiseWeights,wordCount]
  · rw [← hm']
    exact he.trans hv
  · have h := (star_single_witness (n := 3) (d := 3) (by norm_num) (by norm_num)).2.2.2.2
    norm_num [starProbability,starDenominator,witnessSlope,supportRank,wordCount,cutCount,starValue] at h
    exact h

/-- The two-symbol support rank also has the manuscript's binomial form. -/
theorem support_rank_binomial {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    supportRank n d = d+Nat.choose d 2*(2^n-2) := by
  have hchoose : d*(d-1) = Nat.choose d 2*2 := by
    simpa only [Nat.sub_add_cancel hd,Nat.choose_one_right] using
      Nat.add_one_mul_choose_eq (d-1) 1
  have hpow : 2^n = 2^(n-1)*2 := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [pow_succ]
  have hpos : 1 ≤ 2^(n-1) := Nat.one_le_pow _ _ (by norm_num)
  have hsub : 2^n-2 = 2*(2^(n-1)-1) := by omega
  unfold supportRank cutCount
  calc
    _ = d+(2^(n-1)-1)*(d*(d-1)) := by ring
    _ = d+(2^(n-1)-1)*(Nat.choose d 2*2) := by rw [hchoose]
    _ = d+Nat.choose d 2*(2*(2^(n-1)-1)) := by ring
    _ = _ := by rw [← hsub]

private lemma chi_at_one {n d : ℕ} (hn : 0 < n) (j : Fin d) :
    chiVector hn j (optimalAlpha d 1) (optimalBeta d 1) = ghz n d := by
  classical
  have ha : optimalAlpha d 1 = 1/Real.sqrt d := by simp [optimalAlpha]
  have hb : optimalBeta d 1 = 1/Real.sqrt d := by simp [optimalBeta]
  rw [ha,hb]
  ext x
  by_cases hx : ∃ i : Fin d, ∀ k, x k = i
  · obtain ⟨i,hi⟩ := hx
    have he := funext hi
    subst x
    have hc : ∃ k : Fin d, ∀ l : Fin n, (fun _ : Fin n => i) l = k := ⟨i,fun _ => rfl⟩
    simp [chiVector,constantVector_apply,ghz,one_div,hc]
  · rw [chiVector,constantVector_off hn _ _ hx]
    simp [ghz,hx]

/-- The actual GHZ vector attains the left spectral endpoint, with its
pure all-cut measure and the original witness conjugate value. -/
theorem ghz_left_endpoint {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    geometricMeasurePure (ghz n d) = (d-1 : ℝ)/d ∧
      readout (witnessOp n d) (ghz n d) = -(d-1 : ℝ)/d ∧
      epsilonWitness n d (-(d-1 : ℝ)/d) = (d-1 : ℝ)/d := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hF : 1/(d : ℝ) ≤ 1 := (div_le_one hdpos).mpr (by linarith)
  have h := chi_attainment hn hd (⟨0,by omega⟩ : Fin d) hF (le_refl 1)
  rw [chi_at_one] at h
  have hv : twoMeanOptimum d 1 1 = (d-1 : ℝ)/d := by
    rw [twoMeanOptimum,if_neg (by linarith),twoMeanValue]
    simp
    ring
  refine ⟨h.2.2.2.trans hv,?_,?_⟩
  · rw [witnessOp,expectation_sub,expectation_smul,h.2.1,h.2.2.1]
    field_simp
    <;> ring
  · have hw : -(d-1 : ℝ)/d ≤ 1/(d : ℝ) := by
      rw [neg_div]
      have hnonneg : 0 ≤ (d-1 : ℝ)/d := div_nonneg (by linarith) hdpos.le
      exact (neg_nonpos.mpr hnonneg).trans (div_nonneg (by norm_num) hdpos.le)
    rw [witness_optimum hn hd (le_refl _) hw]
    have he : 1/(d : ℝ)-(-(d-1 : ℝ)/d) = 1 := by field_simp <;> ring
    rw [he,hv]

end
end D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof
