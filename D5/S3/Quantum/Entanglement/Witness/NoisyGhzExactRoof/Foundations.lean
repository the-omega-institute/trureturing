/- GID: D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/Foundations
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/Foundations
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Actual noisy-GHZ Foundations in the original finite-ensemble semantics. -/


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
open _root_.Matrix
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Quantum.Entanglement.OccupancyWordSectors (Word)
open D5.S3.Quantum.Information.MultiEntropyPositivityRefutation (IsUnitState)
open D5.S3.Quantum.Recovery.ProductPrefixRigidity (readout)
open D5.S3.Quantum.Entanglement.Witness.NoisyGhzWitnessBoundGap

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

lemma constant_word_injective {n d : ℕ} (hn : 0 < n) :
    Function.Injective (fun j : Fin d => (fun _ : Fin n => j)) := by
  intro i j h
  exact congrFun h ⟨0, hn⟩

lemma sum_supported_constants {n d : ℕ} {α : Type*} [AddCommMonoid α]
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

lemma cs {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    Complex.normSq (star u ⬝ᵥ v) ≤
      (∑ i, Complex.normSq (u i)) * ∑ i, Complex.normSq (v i) := by
  classical
  simpa only [Complex.normSq_eq_norm_sq] using
    D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays.cs_sq u v

lemma expectation_rank_one {ι : Type*} [Fintype ι] (φ ψ : ι → ℂ) :
    readout (rankOneDensity φ) ψ = Complex.normSq (star φ ⬝ᵥ ψ) := by
  have h := D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.quadratic_projector ψ φ
  rw [star_dotProduct ψ φ, Complex.star_def, Complex.normSq_conj] at h
  exact congrArg Complex.re h

lemma support_expectation {n d : ℕ} (ψ : Word (Fin d) n → ℂ) :
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

lemma ghz_expectation {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
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

lemma join_support {n d : ℕ} (a : Finset (Fin n)) (i j : Fin d) :
    (Finset.univ.image (a.piecewise (fun _ => i) (fun _ => j))).card ≤ 2 := by
  classical
  have h : Finset.univ.image (a.piecewise (fun _ => i) (fun _ => j)) ⊆ {i, j} := by
    intro x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
    by_cases hk : k ∈ a <;> simp [Finset.piecewise, hk]
  exact (Finset.card_le_card h).trans Finset.card_le_two

lemma join_injective {n d : ℕ} (a : Finset (Fin n))
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

lemma basis_unit {n d : ℕ} (x : Word (Fin d) n) :
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

lemma overlap_values_nonempty {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    (ψ : Word (Fin d) n → ℂ) :
    {t : ℝ | ∃ φ, IsBiseparable φ ∧ t = Complex.normSq (star φ ⬝ᵥ ψ)}.Nonempty := by
  exact ⟨_, Pi.single (fun _ => (⟨0, hd⟩ : Fin d)) 1,
    computational_biseparable hn _, rfl⟩

lemma overlap_values_bdd {n d : ℕ} (ψ : Word (Fin d) n → ℂ)
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

lemma ensemble_values_nonempty {n d : ℕ}
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

lemma ensemble_values_bdd {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
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

lemma projector_data {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
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

lemma orthogonal_positive {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
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

end
end D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof
