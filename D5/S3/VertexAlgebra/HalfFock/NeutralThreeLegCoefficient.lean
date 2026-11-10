/- GID: D5/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/NeutralThreeLegCoefficient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual full neutral-field raw three-leg Gaussian coefficient identity. -/

import D5.S3.VertexAlgebra.HalfFock.NeutralThreeLegModeExpansion
import D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectionGaussian
import D5.S3.VertexAlgebra.TwistedGround.NativeGaussianMoment

/-!
The source side is the actual `correctedField` and its literal finite Corr;
normal coefficients remain pointwise finite sums in the actual tensor module.
Output projection proves a common finite frequency restriction. The actual
full corrected coefficients are finite scalar Laurent entries times the
identity on arbitrary ground tensors. The raw mixed kernel blocks act in
literal normal order. Actual SO/SI coefficient lowering and the native IO
base identify the full block Gaussian coefficient, with source and input
factorials and ordinary output coefficient. No analytic evaluation of an
unrestricted Hahn series is introduced.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct


namespace D5.S3.VertexAlgebra.HalfFock.NeutralThreeLegCoefficient

open MvPolynomial
open LatticeGeneratingFieldLocality
open LatticeHalfFockFockNormalField
open LatticeHalfFock
open LatticeHalfFockFiniteCorrection
open LatticeHalfFockCorrectedField
open LatticeHalfFockCorrectedConformal
open LatticeHalfFockChargedTensorCoefficients
open HalfFockSpectralFiberSource
open D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectionGaussian
open D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate

open LatticeHalfFockCurrentCorrection

/-- Linear normal readout of the literal finite raw-mode action. Its mode box
is the already proved input/output frequency box, independent of exponent. -/
def nativeNormalReadout (D : LatticeData) (T : ℂˣ)
    (input output : Index D →₀ ℕ) : Oscillator D →ₗ[ℂ] ℂ :=
  (basisMonomials (Index D) ℂ).constr ℂ (fun mon =>
    ∑ m ∈ nativeModeBox D (nativeNeutralModeProjection D output input) (occurrences D mon),
      (nativeRawNormalTerm D T (occurrences D mon) m (monomial input 1)).coeff output)

private theorem nativeNormalReadout_monomial (D : LatticeData) (T : ℂˣ)
    (input output mon : Index D →₀ ℕ) :
    nativeNormalReadout D T input output (monomial mon 1) =
      ∑ m ∈ nativeModeBox D (nativeNeutralModeProjection D output input) (occurrences D mon),
        (nativeRawNormalTerm D T (occurrences D mon) m (monomial input 1)).coeff output :=
  (basisMonomials (Index D) ℂ).constr_basis ℂ _ mon

private theorem nativeNormalReadout_expansion (D : LatticeData) (T : ℂˣ)
    (input output : Index D →₀ ℕ) (p : Oscillator D) :
    nativeNormalReadout D T input output p =
      ∑ mon ∈ p.support, p.coeff mon *
        nativeNormalReadout D T input output (monomial mon 1) := by
  conv_lhs => rw [p.as_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro mon hm
  rw [show (monomial mon (p.coeff mon) : Oscillator D) =
    p.coeff mon • monomial mon 1 by simp [smul_monomial], map_smul, smul_eq_mul]

private theorem nativeNeutralLaurentEntry_readout (D : LatticeData) (T : ℂˣ)
    (d input output : Index D →₀ ℕ) :
    nativeNeutralLaurentEntry D T d input output =
      nativeNormalReadout D T input output (correctionAt D T (monomial d 1)) := by
  rw [nativeNeutralLaurentEntry_raw_normal_expansion, correctionAt_shift_sum]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro s hs
  rw [nativeNormalReadout_expansion]
  simp only [Finset.mul_sum, nativeNormalReadout_monomial]
  apply Finset.sum_congr rfl
  intro mon hm
  apply Finset.sum_congr rfl
  intro m hmem
  ring

/-- Source insertion in the actual full Laurent entry. The paired branch
uses the literal SS kernel with multiplicity d(b), including diagonal pairs;
the unpaired branch retains the actual normal readout. This is a recurrence
for the native field, not a Gaussian identity assumed as input. -/
private theorem nativeNeutralLaurentEntry_source_insertion
    (D : LatticeData) (T : ℂˣ) (d input output : Index D →₀ ℕ) (a : Index D) :
    nativeNeutralLaurentEntry D T (d + Finsupp.single a 1) input output =
      nativeNormalReadout D T input output
        (X a * correctionAt D T (monomial d 1)) +
      ∑ b ∈ d.support, (d b : ℂ) * nativeSourceSourceKernel D T a b *
        nativeNeutralLaurentEntry D T (d - Finsupp.single b 1) input output := by
  rw [nativeNeutralLaurentEntry_readout,
    show (monomial (d + Finsupp.single a 1) 1 : Oscillator D) =
      monomial d 1 * X a by simp [X], correctionAt_X_mul, map_add, map_sum,
    vars_monomial (one_ne_zero : (1 : ℂ) ≠ 0)]
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  have hderiv : pderiv b (monomial d (1 : ℂ)) =
      (d b : ℂ) • monomial (d - Finsupp.single b 1) 1 := by
    simp [pderiv_monomial, smul_monomial]
  rw [hderiv, map_smul, map_smul, map_smul,
    ← nativeNeutralLaurentEntry_readout]
  simp only [smul_eq_mul]
  ring

/-- The SS insertion recurrence for the actual corrected-field coefficient at
its forced exponent. The entire ground module is carried by identity. The
remaining unpaired normal readout has not been replaced by a Gaussian premise. -/
theorem nativeNeutralCoefficient_source_insertion
    (D : LatticeData) (hu : IsUnit D.G.det) (T : ℂˣ)
    (d input output : Index D →₀ ℕ) (a : Index D) (g : ActualGround D hu) :
    let E : ℤ := (LatticeHalfFockGradedTrace.oddWeight D output : ℤ) -
      (LatticeHalfFockGradedTrace.oddWeight D input : ℤ) -
      2 * nativeSourceEnergy D (d + Finsupp.single a 1)
    (T : ℂ) ^ E • nativeOutputProjection D hu output
        (nativeNeutralCoefficient D hu (d + Finsupp.single a 1) E
          (monomial input 1 ⊗ₜ[ℂ] g)) =
      nativeNormalReadout D T input output
        (X a * correctionAt D T (monomial d 1)) • g +
      ∑ b ∈ d.support, ((d b : ℂ) * nativeSourceSourceKernel D T a b) •
        (nativeNeutralLaurentEntry D T (d - Finsupp.single b 1) input output • g) := by
  dsimp only
  rw [← nativeNeutralLaurentEntry_at_energy D hu T (d + Finsupp.single a 1) input output g,
    nativeNeutralLaurentEntry_source_insertion, add_smul, Finset.sum_smul]
  simp only [mul_smul]

private def normalWord (D : LatticeData) (T : ℂˣ) (B : Finset ℤ)
    (w : List (Index D)) : Module.End ℂ (Oscillator D) :=
  ∑ m ∈ nativeModeBox D B w, nativeRawNormalTerm D T w m

private def creationSum (D : LatticeData) (T : ℂˣ) (B : Finset ℤ)
    (a : Index D) : Module.End ℂ (Oscillator D) :=
  ∑ m ∈ B, if m < 0 then rawModeOperator D T a m else 0

private def annihilationSum (D : LatticeData) (T : ℂˣ) (B : Finset ℤ)
    (a : Index D) : Module.End ℂ (Oscillator D) :=
  ∑ m ∈ B, if m < 0 then 0 else rawModeOperator D T a m

private theorem normalWord_cons (D : LatticeData) (T : ℂˣ) (B : Finset ℤ)
    (a : Index D) (w : List (Index D)) :
    normalWord D T B (a :: w) =
      creationSum D T B a * normalWord D T B w +
        normalWord D T B w * annihilationSum D T B a := by
  classical
  calc
    normalWord D T B (a :: w) = ∑ m ∈ B,
        if m < 0 then rawModeOperator D T a m * normalWord D T B w
        else normalWord D T B w * rawModeOperator D T a m := by
      change (∑ m ∈ B.product (nativeModeBox D B w),
        if m.1 < 0 then rawModeOperator D T a m.1 * nativeRawNormalTerm D T w m.2
        else nativeRawNormalTerm D T w m.2 * rawModeOperator D T a m.1) = _
      trans ∑ m ∈ B, ∑ n ∈ nativeModeBox D B w,
        if m < 0 then rawModeOperator D T a m * nativeRawNormalTerm D T w n
        else nativeRawNormalTerm D T w n * rawModeOperator D T a m
      · exact Finset.sum_product B (nativeModeBox D B w) _
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hn : m < 0 <;> simp [hn, normalWord, Finset.mul_sum, Finset.sum_mul]
    _ = _ := by
      simp only [creationSum, annihilationSum, Finset.sum_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hn : m < 0 <;> simp [hn]

private theorem rawModeOperator_same_sign (D : LatticeData) (T : ℂˣ)
    (a b : Index D) (m n : ℤ)
    (hs : (m < 0 ∧ n < 0) ∨ (0 ≤ m ∧ 0 ≤ n)) :
    rawModeOperator D T a m * rawModeOperator D T b n =
      rawModeOperator D T b n * rawModeOperator D T a m := by
  have hmn : m + n + 1 ≠ 0 := by rcases hs with hs | hs <;> omega
  apply LinearMap.ext
  intro p
  simp only [Module.End.mul_apply, rawModeOperator_eq, LinearMap.smul_apply,
    map_smul, smul_smul]
  have hc := sub_eq_zero.mp (by simpa only [if_neg hmn] using
    (current_heisenberg_apply D a.1 b.1 m n p))
  rw [hc]
  module

private theorem creationSum_commute (D : LatticeData) (T : ℂˣ)
    (B : Finset ℤ) (a b : Index D) :
    creationSum D T B a * creationSum D T B b =
      creationSum D T B b * creationSum D T B a := by
  classical
  simp only [creationSum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hm' : m < 0 <;> by_cases hn' : n < 0
  · simpa only [if_pos hm', if_pos hn'] using
      rawModeOperator_same_sign D T a b n m (Or.inl ⟨hn', hm'⟩)
  all_goals simp [hm', hn']

private theorem annihilationSum_commute (D : LatticeData) (T : ℂˣ)
    (B : Finset ℤ) (a b : Index D) :
    annihilationSum D T B a * annihilationSum D T B b =
      annihilationSum D T B b * annihilationSum D T B a := by
  classical
  simp only [annihilationSum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hm' : m < 0 <;> by_cases hn' : n < 0
  all_goals try simp [hm', hn']
  exact rawModeOperator_same_sign D T a b n m (Or.inr ⟨by omega, by omega⟩)

private theorem normalWord_perm (D : LatticeData) (T : ℂˣ) (B : Finset ℤ)
    {u v : List (Index D)} (h : u.Perm v) :
    normalWord D T B u = normalWord D T B v := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [normalWord_cons, ih]
  | swap a b w =>
    simp only [normalWord_cons]
    have hc : creationSum D T B a * (creationSum D T B b * normalWord D T B w) =
        creationSum D T B b * (creationSum D T B a * normalWord D T B w) := by
      rw [← mul_assoc, creationSum_commute D T B a b, mul_assoc]
    noncomm_ring [hc, annihilationSum_commute D T B a b]
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem nativeModeBox_mono (D : LatticeData) (B C : Finset ℤ)
    (h : B ⊆ C) (w : List (Index D)) :
    nativeModeBox D B w ⊆ nativeModeBox D C w := by
  induction w with
  | nil => exact le_refl _
  | cons a w ih => exact Finset.product_subset_product h ih

private theorem rawNormal_projected_support (D : LatticeData) (T : ℂˣ)
    (w : List (Index D)) (input output : Index D →₀ ℕ) (m : ModeTuple D w)
    (hn : (nativeRawNormalTerm D T w m (monomial input 1)).coeff output ≠ 0) :
    allModes D (fun n => n ∈ nativeNeutralModeProjection D output input) w m := by
  rw [nativeRawNormalTerm_eq, coeff_smul, smul_eq_mul] at hn
  exact normalPolynomial_projected_support D w input output m (mul_ne_zero_iff.mp hn).2

private theorem normalWord_box_independent (D : LatticeData) (T : ℂˣ)
    (B : Finset ℤ) (input output : Index D →₀ ℕ)
    (hB : nativeNeutralModeProjection D output input ⊆ B) (w : List (Index D)) :
    (normalWord D T B w (monomial input 1)).coeff output =
      (normalWord D T (nativeNeutralModeProjection D output input) w
        (monomial input 1)).coeff output := by
  classical
  simp only [normalWord, LinearMap.sum_apply, coeff_sum]
  symm
  apply Finset.sum_subset (nativeModeBox_mono D _ _ hB w)
  intro m hm hout
  by_contra hn
  exact hout ((nativeModeBox_mem D _ w m).mpr
    (rawNormal_projected_support D T w input output m hn))

private def normalReadoutBox (D : LatticeData) (T : ℂˣ) (B : Finset ℤ)
    (input output : Index D →₀ ℕ) : Oscillator D →ₗ[ℂ] ℂ :=
  (basisMonomials (Index D) ℂ).constr ℂ (fun mon =>
    (normalWord D T B (occurrences D mon) (monomial input 1)).coeff output)

private theorem normalReadoutBox_monomial (D : LatticeData) (T : ℂˣ)
    (B : Finset ℤ) (input output mon : Index D →₀ ℕ) :
    normalReadoutBox D T B input output (monomial mon 1) =
      (normalWord D T B (occurrences D mon) (monomial input 1)).coeff output :=
  (basisMonomials (Index D) ℂ).constr_basis ℂ _ mon

private theorem normalReadoutBox_independent (D : LatticeData) (T : ℂˣ)
    (B : Finset ℤ) (input output : Index D →₀ ℕ)
    (hB : nativeNeutralModeProjection D output input ⊆ B) :
    normalReadoutBox D T B input output = nativeNormalReadout D T input output := by
  classical
  apply (basisMonomials (Index D) ℂ).ext
  intro mon
  change normalReadoutBox D T B input output (monomial mon 1) =
    nativeNormalReadout D T input output (monomial mon 1)
  rw [normalReadoutBox_monomial, normalWord_box_independent D T B input output hB,
    nativeNormalReadout_monomial]
  simp [normalWord, LinearMap.sum_apply, coeff_sum]

private theorem normalReadoutBox_X_monomial (D : LatticeData) (T : ℂˣ)
    (B : Finset ℤ) (input output mon : Index D →₀ ℕ) (a : Index D) :
    normalReadoutBox D T B input output (X a * monomial mon 1) =
      ((creationSum D T B a * normalWord D T B (occurrences D mon) +
          normalWord D T B (occurrences D mon) * annihilationSum D T B a)
        (monomial input 1)).coeff output := by
  have enumeration : (a :: occurrences D mon).Perm
      (occurrences D (Finsupp.single a 1 + mon)) := by
    apply Multiset.coe_eq_coe.mp
    simp [occurrences, Finsupp.toMultiset_add, Finsupp.toMultiset_single,
      ← Multiset.cons_coe, Multiset.coe_toList, add_comm]
  rw [show (X a * monomial mon (1 : ℂ) : Oscillator D) =
      monomial (Finsupp.single a 1 + mon) 1 by simp [X],
    normalReadoutBox_monomial, ← normalWord_perm D T B enumeration, normalWord_cons]

/-- The actual neutral zero-source field propagates every input monomial
unchanged, with the identity on the entire ground module. -/
theorem nativeNeutralLaurentEntry_zero (D : LatticeData) (T : ℂˣ)
    (input output : Index D →₀ ℕ) :
    nativeNeutralLaurentEntry D T 0 input output = if input = output then 1 else 0 := by
  rw [nativeNeutralLaurentEntry_readout]
  have hz : correctionAt D T (monomial 0 1) = (monomial 0 1 : Oscillator D) := by
    change correctionEvaluation D T (correctionLift D 0 (C 1)) = C 1
    rw [correctionLift_C]
    simp [correctionEvaluation, algebraMap_eq]
  rw [hz, nativeNormalReadout_monomial]
  have he : occurrences D (0 : Index D →₀ ℕ) = [] := by
    simp only [occurrences, Finsupp.toMultiset_zero, Multiset.toList_zero]
  rw [he]
  simp [nativeModeBox, nativeRawNormalTerm, coeff_monomial, eq_comm]

private theorem creationSum_coefficient (D : LatticeData) (T : ℂˣ)
    (B : Finset ℤ) (a : Index D) (output : Index D →₀ ℕ) (p : Oscillator D)
    (hB : output.support.image (fun j => -(j.2 : ℤ) - 1) ⊆ B) :
    (creationSum D T B a p).coeff output =
      ∑ j ∈ output.support, nativeSourceOutputKernel D T a j *
        p.coeff (output - Finsupp.single j 1) := by
  classical
  have term (m : ℤ) :
      ((if m < 0 then rawModeOperator D T a m else 0) p).coeff output =
        if m < 0 then
          nativeSourceOutputKernel D T a (a.1, (-m - 1).toNat) *
            (if (a.1, (-m - 1).toNat) ∈ output.support then
              p.coeff (output - Finsupp.single (a.1, (-m - 1).toNat) 1) else 0)
        else 0 := by
    by_cases hn : m < 0
    · simp only [if_pos hn, rawModeOperator, LinearMap.smul_apply,
        LinearMap.mulLeft_apply, coeff_smul, smul_eq_mul, coeff_X_mul']
    · simp only [if_neg hn, LinearMap.zero_apply, AddMonoidAlgebra.coeff_zero,
        Finsupp.zero_apply]
  simp only [creationSum, LinearMap.sum_apply, coeff_sum]
  simp_rw [term]
  refine Finset.sum_bij_ne_zero (fun m _ _ => (a.1, (-m - 1).toNat)) ?_ ?_ ?_ ?_
  · intro m hm hn
    by_cases h : m < 0
    · by_contra ho
      simp only [if_pos h, if_neg ho, mul_zero, ne_eq, not_true_eq_false] at hn
    · simp only [if_neg h, ne_eq, not_true_eq_false] at hn
  · intro m hm hmn n hn hnn he
    have hm' : m < 0 := by by_contra hh; simp [hh] at hmn
    have hn' : n < 0 := by by_contra hh; simp [hh] at hnn
    have he' := congrArg Prod.snd he
    have h₁ := Int.toNat_of_nonneg (by omega : 0 ≤ -m - 1)
    have h₂ := Int.toNat_of_nonneg (by omega : 0 ≤ -n - 1)
    omega
  · intro j hj hn
    have hc : a.1 = j.1 := by
      by_contra hh
      simp [nativeSourceOutputKernel, hh] at hn
    refine ⟨-(j.2 : ℤ) - 1, hB (Finset.mem_image.mpr ⟨j, hj, rfl⟩), ?_, ?_⟩
    · have he : (a.1, (-(-(j.2 : ℤ) - 1) - 1).toNat) = j := by
        apply Prod.ext
        · exact hc
        · simp
      simpa only [if_pos (show -(j.2 : ℤ) - 1 < 0 by omega), he,
        if_pos hj] using hn
    · apply Prod.ext
      · exact hc
      · simp
  · intro m hm hn
    have hm' : m < 0 := by by_contra hh; simp [hh] at hn
    have hj : (a.1, (-m - 1).toNat) ∈ output.support := by
      by_contra hh
      simp only [if_pos hm', if_neg hh, mul_zero, ne_eq, not_true_eq_false] at hn
    rw [if_pos hm', if_pos hj]

private theorem annihilationSum_coefficient (D : LatticeData) (T : ℂˣ)
    (B : Finset ℤ) (a : Index D) (input output : Index D →₀ ℕ)
    (N : Module.End ℂ (Oscillator D))
    (hB : input.support.image (fun j => (j.2 : ℤ)) ⊆ B) :
    (N (annihilationSum D T B a (monomial input 1))).coeff output =
      ∑ j ∈ input.support, (input j : ℂ) * nativeSourceInputKernel D T a j *
        (N (monomial (input - Finsupp.single j 1) 1)).coeff output := by
  classical
  have term (m : ℤ) :
      (N ((if m < 0 then 0 else rawModeOperator D T a m)
        (monomial input 1))).coeff output =
      ∑ c : Fin D.rank, if m < 0 then 0 else
        (input (c, m.toNat) : ℂ) * nativeSourceInputKernel D T a (c, m.toNat) *
          (N (monomial (input - Finsupp.single (c, m.toNat) 1) 1)).coeff output := by
    by_cases hm : m < 0
    · simp [hm]
    · have hderiv (c : Fin D.rank) :
          pderiv (c, m.toNat) (monomial input (1 : ℂ)) =
            (input (c, m.toNat) : ℂ) • monomial (input - Finsupp.single (c, m.toNat) 1) 1 := by
        simp [pderiv_monomial, smul_monomial]
      simp only [hm, if_false, rawModeOperator, LinearMap.sum_apply,
        LinearMap.smul_apply, Derivation.coeFn_coe, hderiv, map_sum, map_smul,
        coeff_sum, coeff_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro c hc
      ring
  simp only [annihilationSum, LinearMap.sum_apply, map_sum, coeff_sum]
  simp_rw [term]
  rw [← Finset.sum_product' B (Finset.univ : Finset (Fin D.rank))]
  refine Finset.sum_bij_ne_zero (fun mc _ _ => (mc.2, mc.1.toNat)) ?_ ?_ ?_ ?_
  · intro mc hmc hn
    have hm : ¬ mc.1 < 0 := by intro hh; simp [hh] at hn
    apply Finsupp.mem_support_iff.mpr
    intro hz
    simp [hz, hm] at hn
  · intro mc hmc hn nd hnd hnd' he
    have hm : ¬ mc.1 < 0 := by intro hh; simp [hh] at hn
    have hn' : ¬ nd.1 < 0 := by intro hh; simp [hh] at hnd'
    have hc := congrArg Prod.fst he
    have hk := congrArg Prod.snd he
    have h₁ := Int.toNat_of_nonneg (by omega : 0 ≤ mc.1)
    have h₂ := Int.toNat_of_nonneg (by omega : 0 ≤ nd.1)
    exact Prod.ext (by omega) hc
  · intro j hj hn
    refine ⟨((j.2 : ℤ), j.1), Finset.mem_product.mpr
      ⟨hB (Finset.mem_image.mpr ⟨j, hj, rfl⟩), Finset.mem_univ _⟩, ?_, ?_⟩
    · simpa using hn
    · simp
  · intro mc hmc hn
    have hm : ¬ mc.1 < 0 := by intro hh; simp [hh] at hn
    simp [hm]

private theorem nativeNeutralModeProjection_mono (D : LatticeData)
    (input output input' output' : Index D →₀ ℕ)
    (hi : input' ≤ input) (ho : output' ≤ output) :
    nativeNeutralModeProjection D output' input' ⊆
      nativeNeutralModeProjection D output input := by
  exact Finset.union_subset_union
    (Finset.image_subset_image (Finsupp.support_mono ho))
    (Finset.image_subset_image (Finsupp.support_mono hi))

private theorem nativeNormalReadout_X_mul (D : LatticeData) (T : ℂˣ)
    (input output : Index D →₀ ℕ) (a : Index D) (p : Oscillator D) :
    nativeNormalReadout D T input output (X a * p) =
      ∑ j ∈ output.support, nativeSourceOutputKernel D T a j *
        nativeNormalReadout D T input (output - Finsupp.single j 1) p +
      ∑ j ∈ input.support, (input j : ℂ) * nativeSourceInputKernel D T a j *
        nativeNormalReadout D T (input - Finsupp.single j 1) output p := by
  classical
  let B := nativeNeutralModeProjection D output input
  have hC : output.support.image (fun j => -(j.2 : ℤ) - 1) ⊆ B :=
    Finset.subset_union_left
  have hA : input.support.image (fun j => (j.2 : ℤ)) ⊆ B :=
    Finset.subset_union_right
  have hbox : normalReadoutBox D T B input output = nativeNormalReadout D T input output :=
    normalReadoutBox_independent D T B input output (le_refl _)
  have base (mon : Index D →₀ ℕ) :
      nativeNormalReadout D T input output (X a * monomial mon 1) =
        ∑ j ∈ output.support, nativeSourceOutputKernel D T a j *
          nativeNormalReadout D T input (output - Finsupp.single j 1) (monomial mon 1) +
        ∑ j ∈ input.support, (input j : ℂ) * nativeSourceInputKernel D T a j *
          nativeNormalReadout D T (input - Finsupp.single j 1) output (monomial mon 1) := by
    rw [← hbox, normalReadoutBox_X_monomial]
    simp only [LinearMap.add_apply, Module.End.mul_apply,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    rw [creationSum_coefficient D T B a output _ hC,
      annihilationSum_coefficient D T B a input output _ hA]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      rw [← normalReadoutBox_monomial,
        normalReadoutBox_independent D T B input (output - Finsupp.single j 1)
          (nativeNeutralModeProjection_mono D input output input _ le_rfl tsub_le_self)]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [← normalReadoutBox_monomial,
        normalReadoutBox_independent D T B (input - Finsupp.single j 1) output
          (nativeNeutralModeProjection_mono D input output _ output tsub_le_self le_rfl)]
  let rhs : Oscillator D →ₗ[ℂ] ℂ :=
    (∑ j ∈ output.support, nativeSourceOutputKernel D T a j •
      nativeNormalReadout D T input (output - Finsupp.single j 1)) +
    ∑ j ∈ input.support, ((input j : ℂ) * nativeSourceInputKernel D T a j) •
      nativeNormalReadout D T (input - Finsupp.single j 1) output
  have maps : (nativeNormalReadout D T input output).comp
      (LinearMap.mulLeft ℂ (X a)) = rhs := by
    apply (basisMonomials (Index D) ℂ).ext
    intro mon
    simpa [rhs, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using base mon
  simpa [rhs, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using
    LinearMap.congr_fun maps p

/-- The unpaired source insertion is the actual SO/SI coefficient lowering:
creation has no output multiplicity and annihilation has the input multiplicity. -/
theorem nativeNeutralLaurentEntry_unpaired (D : LatticeData) (T : ℂˣ)
    (d input output : Index D →₀ ℕ) (a : Index D) :
    nativeNormalReadout D T input output (X a * correctionAt D T (monomial d 1)) =
      ∑ j ∈ output.support, nativeSourceOutputKernel D T a j *
        nativeNeutralLaurentEntry D T d input (output - Finsupp.single j 1) +
      ∑ j ∈ input.support, (input j : ℂ) * nativeSourceInputKernel D T a j *
        nativeNeutralLaurentEntry D T d (input - Finsupp.single j 1) output := by
  simp only [nativeNormalReadout_X_mul, nativeNeutralLaurentEntry_readout]

/-- Complete source insertion for the actual full corrected-field entry,
including SS, SO and SI and the native IO base. -/
theorem nativeNeutralLaurentEntry_recurrence (D : LatticeData) (T : ℂˣ)
    (d input output : Index D →₀ ℕ) (a : Index D) :
    nativeNeutralLaurentEntry D T (d + Finsupp.single a 1) input output =
      (∑ j ∈ output.support, nativeSourceOutputKernel D T a j *
        nativeNeutralLaurentEntry D T d input (output - Finsupp.single j 1) +
      ∑ j ∈ input.support, (input j : ℂ) * nativeSourceInputKernel D T a j *
        nativeNeutralLaurentEntry D T d (input - Finsupp.single j 1) output) +
      ∑ b ∈ d.support, (d b : ℂ) * nativeSourceSourceKernel D T a b *
        nativeNeutralLaurentEntry D T (d - Finsupp.single b 1) input output := by
  rw [nativeNeutralLaurentEntry_source_insertion, nativeNeutralLaurentEntry_unpaired]


open D5.S3.VertexAlgebra.TwistedGround.NativeGaussianMoment
  (nativeMoment nativeMoment_step weight_sub_single sub_single_degree)

/-- Finite raw SS/SI/SO/IO block matrix. The three summands of the index type
are source, input and output labels, respectively. -/
def nativeThreeLegMatrix {I : Type*} (D : LatticeData) (T : ℂˣ)
    (label : I ↪ Index D) : Matrix (I ⊕ (I ⊕ I)) (I ⊕ (I ⊕ I)) ℂ := by
  classical
  exact fun
    | .inl a, .inl b => nativeSourceSourceKernel D T (label a) (label b)
    | .inl a, .inr (.inl b) => nativeSourceInputKernel D T (label a) (label b)
    | .inl a, .inr (.inr b) => nativeSourceOutputKernel D T (label a) (label b)
    | .inr (.inl a), .inl b => nativeSourceInputKernel D T (label b) (label a)
    | .inr (.inr a), .inl b => nativeSourceOutputKernel D T (label b) (label a)
    | .inr (.inl a), .inr (.inr b) => if a = b then 1 else 0
    | .inr (.inr a), .inr (.inl b) => if b = a then 1 else 0
    | _, _ => 0

/-- The finite three-leg monomial occupation retains every repeated position. -/
def nativeThreeLegOccupation {I : Type*} (d input output : I →₀ ℕ) :
    (I ⊕ (I ⊕ I)) →₀ ℕ := d.sumElim (input.sumElim output)


/-- Literal raw coherent exponent: SS/2 + SO + SI + IO. -/
def nativeThreeLegRawPolynomial {I : Type*} [Fintype I]
    (D : LatticeData) (T : ℂˣ) (label : I ↪ Index D) :
    MvPolynomial (I ⊕ (I ⊕ I)) ℂ :=
  (1 / 2 : ℂ) • (∑ a, ∑ b, nativeSourceSourceKernel D T (label a) (label b) •
    (X (.inl a) * X (.inl b))) +
  (∑ a, ∑ b, nativeSourceOutputKernel D T (label a) (label b) •
    (X (.inl a) * X (.inr (.inr b)))) +
  (∑ a, ∑ b, nativeSourceInputKernel D T (label a) (label b) •
    (X (.inl a) * X (.inr (.inl b)))) +
  ∑ b, X (.inr (.inl b)) * X (.inr (.inr b))

private theorem nativeThreeLeg_quadratic {I : Type*} [Fintype I] [DecidableEq I]
    (D : LatticeData) (T : ℂˣ) (label : I ↪ Index D) :
    quadratic (nativeThreeLegMatrix D T label) = nativeThreeLegRawPolynomial D T label := by
  classical
  have hi : (∑ a : I, ∑ b : I, nativeSourceInputKernel D T (label b) (label a) •
      (X (.inr (.inl a)) * X (.inl b) : MvPolynomial (I ⊕ (I ⊕ I)) ℂ)) =
      ∑ a : I, ∑ b : I, nativeSourceInputKernel D T (label a) (label b) •
        (X (.inl a) * X (.inr (.inl b))) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [mul_comm]
  have ho : (∑ a : I, ∑ b : I, nativeSourceOutputKernel D T (label b) (label a) •
      (X (.inr (.inr a)) * X (.inl b) : MvPolynomial (I ⊕ (I ⊕ I)) ℂ)) =
      ∑ a : I, ∑ b : I, nativeSourceOutputKernel D T (label a) (label b) •
        (X (.inl a) * X (.inr (.inr b))) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [mul_comm]
  simp only [quadratic, Fintype.sum_sum_type, nativeThreeLegMatrix,
    Finset.sum_add_distrib, zero_smul, Finset.sum_const_zero, zero_add, add_zero,
    ite_smul, one_smul, zero_smul]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hi, ho]
  simp only [show ∀ a : I, (X (.inr (.inr a)) * X (.inr (.inl a)) :
      MvPolynomial (I ⊕ (I ⊕ I)) ℂ) = X (.inr (.inl a)) * X (.inr (.inr a))
    from fun _ => mul_comm _ _]
  unfold nativeThreeLegRawPolynomial
  module

/-- Ordinary coefficient of the finite raw coherent exponential. Homogeneity
makes its coefficient a single finite power divided by its exponential factorial. -/
def nativeThreeLegExponentialCoefficient {I : Type*} [Fintype I]
    (D : LatticeData) (T : ℂˣ) (label : I ↪ Index D) (d h l : I →₀ ℕ) : ℂ :=
  let o := nativeThreeLegOccupation d h l
  (((o.degree / 2).factorial : ℂ)⁻¹ •
    nativeThreeLegRawPolynomial D T label ^ (o.degree / 2)).coeff o

private theorem nativeThreeLegExponentialCoefficient_eq {I : Type*}
    [Fintype I] [DecidableEq I] (D : LatticeData) (T : ℂˣ)
    (label : I ↪ Index D) (d h l : I →₀ ℕ) :
    nativeThreeLegExponentialCoefficient D T label d h l =
      gaussianCoefficient (nativeThreeLegMatrix D T label) (nativeThreeLegOccupation d h l) := by
  simp only [nativeThreeLegExponentialCoefficient, gaussianCoefficient, gaussianPiece,
    nativeThreeLeg_quadratic]

private theorem nativeSourceSourceKernel_symm (D : LatticeData) (T : ℂˣ)
    (a b : Index D) :
    nativeSourceSourceKernel D T a b = nativeSourceSourceKernel D T b a := by
  have he (u v : Index D) : nativeSourceSourceKernel D T u v =
      covariance D ((T : ℂ) ^ (-2 : ℤ)) u v := by
    simp only [nativeSourceSourceKernel, covariance, sourceWeight]
    congr 1
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  rw [he, he, covariance_symm]

private theorem nativeThreeLegMatrix_symm {I : Type*} (D : LatticeData) (T : ℂˣ)
    (label : I ↪ Index D) :
    ∀ i j, nativeThreeLegMatrix D T label i j = nativeThreeLegMatrix D T label j i := by
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · exact nativeSourceSourceKernel_symm D T (label i) (label j)
  · rcases j with j | j <;> rfl
  · rcases i with i | i <;> rfl
  · rcases i with i | i <;> rcases j with j | j <;> rfl

private theorem threeOccupation_add_source {I : Type*}
    (d h l : I →₀ ℕ) (a : I) :
    nativeThreeLegOccupation (d + Finsupp.single a 1) h l =
      nativeThreeLegOccupation d h l + Finsupp.single (.inl a) 1 := by
  classical
  ext i
  rcases i with i | i
  · simp [nativeThreeLegOccupation, Finsupp.single_apply]
  · rcases i with i | i <;> simp [nativeThreeLegOccupation, Finsupp.single_apply]

private theorem threeOccupation_add_input {I : Type*}
    (d h l : I →₀ ℕ) (a : I) :
    nativeThreeLegOccupation d (h + Finsupp.single a 1) l =
      nativeThreeLegOccupation d h l + Finsupp.single (.inr (.inl a)) 1 := by
  classical
  ext i
  rcases i with i | i
  · simp [nativeThreeLegOccupation, Finsupp.single_apply]
  · rcases i with i | i <;> simp [nativeThreeLegOccupation, Finsupp.single_apply]

private theorem threeOccupation_add_output {I : Type*}
    (d h l : I →₀ ℕ) (a : I) :
    nativeThreeLegOccupation d h (l + Finsupp.single a 1) =
      nativeThreeLegOccupation d h l + Finsupp.single (.inr (.inr a)) 1 := by
  classical
  ext i
  rcases i with i | i
  · simp [nativeThreeLegOccupation, Finsupp.single_apply]
  · rcases i with i | i <;> simp [nativeThreeLegOccupation, Finsupp.single_apply]

private theorem threeOccupation_sub_source {I : Type*}
    (d h l : I →₀ ℕ) (a : I) :
    nativeThreeLegOccupation d h l - Finsupp.single (.inl a) 1 =
      nativeThreeLegOccupation (d - Finsupp.single a 1) h l := by
  classical
  ext i
  rcases i with i | i
  · simp [nativeThreeLegOccupation, Finsupp.single_apply, Finsupp.tsub_apply]
  · rcases i with i | i <;>
      simp [nativeThreeLegOccupation, Finsupp.single_apply, Finsupp.tsub_apply]

private theorem threeOccupation_sub_input {I : Type*}
    (d h l : I →₀ ℕ) (a : I) :
    nativeThreeLegOccupation d h l - Finsupp.single (.inr (.inl a)) 1 =
      nativeThreeLegOccupation d (h - Finsupp.single a 1) l := by
  classical
  ext i
  rcases i with i | i
  · simp [nativeThreeLegOccupation, Finsupp.single_apply, Finsupp.tsub_apply]
  · rcases i with i | i <;>
      simp [nativeThreeLegOccupation, Finsupp.single_apply, Finsupp.tsub_apply]

private theorem threeOccupation_sub_output {I : Type*}
    (d h l : I →₀ ℕ) (a : I) :
    nativeThreeLegOccupation d h l - Finsupp.single (.inr (.inr a)) 1 =
      nativeThreeLegOccupation d h (l - Finsupp.single a 1) := by
  classical
  ext i
  rcases i with i | i
  · simp [nativeThreeLegOccupation, Finsupp.single_apply, Finsupp.tsub_apply]
  · rcases i with i | i <;>
      simp [nativeThreeLegOccupation, Finsupp.single_apply, Finsupp.tsub_apply]

private theorem threeOccupation_weight {I : Type*} (d h l : I →₀ ℕ) :
    FactorialFockMetric.weight (nativeThreeLegOccupation d h l) =
      FactorialFockMetric.weight d * FactorialFockMetric.weight h *
        FactorialFockMetric.weight l := by
  simp only [nativeThreeLegOccupation, FactorialFockMetric.weight,
    Finsupp.prod_sumElim, Function.comp_def]
  ring

private theorem threeMoment_source_step {I : Type*} [Fintype I] [DecidableEq I]
    (D : LatticeData) (T : ℂˣ) (label : I ↪ Index D) (d h l : I →₀ ℕ) (a : I) :
    nativeMoment (nativeThreeLegMatrix D T label)
        (nativeThreeLegOccupation (d + Finsupp.single a 1) h l) =
      (∑ b ∈ d.support, (d b : ℂ) * nativeSourceSourceKernel D T (label a) (label b) *
        nativeMoment (nativeThreeLegMatrix D T label)
          (nativeThreeLegOccupation (d - Finsupp.single b 1) h l)) +
      (∑ b ∈ h.support, (h b : ℂ) * nativeSourceInputKernel D T (label a) (label b) *
        nativeMoment (nativeThreeLegMatrix D T label)
          (nativeThreeLegOccupation d (h - Finsupp.single b 1) l)) +
      ∑ b ∈ l.support, (l b : ℂ) * nativeSourceOutputKernel D T (label a) (label b) *
        nativeMoment (nativeThreeLegMatrix D T label)
          (nativeThreeLegOccupation d h (l - Finsupp.single b 1)) := by
  classical
  rw [threeOccupation_add_source, nativeMoment_step _ (nativeThreeLegMatrix_symm D T label)]
  simp only [Fintype.sum_sum_type, nativeThreeLegMatrix,
    show ∀ x, nativeThreeLegOccupation d h l (.inl x) = d x from fun _ => rfl,
    show ∀ x, nativeThreeLegOccupation d h l (.inr (.inl x)) = h x from fun _ => rfl,
    show ∀ x, nativeThreeLegOccupation d h l (.inr (.inr x)) = l x from fun _ => rfl,
    threeOccupation_sub_source, threeOccupation_sub_input, threeOccupation_sub_output]
  have restrict (q : I →₀ ℕ) (f : I → ℂ) :
      (∑ b, (q b : ℂ) * f b) = ∑ b ∈ q.support, (q b : ℂ) * f b := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro b hb hout
    simp only [Finsupp.notMem_support_iff.mp hout, Nat.cast_zero, zero_mul]
  simp only [mul_assoc]
  rw [restrict d, restrict h, restrict l, add_assoc]

private theorem threeMoment_input_step {I : Type*} [Fintype I] [DecidableEq I]
    (D : LatticeData) (T : ℂˣ) (label : I ↪ Index D) (h l : I →₀ ℕ) (a : I) :
    nativeMoment (nativeThreeLegMatrix D T label)
        (nativeThreeLegOccupation 0 (h + Finsupp.single a 1) l) =
      (l a : ℂ) * nativeMoment (nativeThreeLegMatrix D T label)
        (nativeThreeLegOccupation 0 h (l - Finsupp.single a 1)) := by
  classical
  rw [threeOccupation_add_input, nativeMoment_step _ (nativeThreeLegMatrix_symm D T label)]
  simp only [Fintype.sum_sum_type, nativeThreeLegMatrix,
    show ∀ x, nativeThreeLegOccupation (0 : I →₀ ℕ) h l (.inl x) = 0 from fun _ => rfl,
    show ∀ x, nativeThreeLegOccupation (0 : I →₀ ℕ) h l (.inr (.inl x)) = h x from fun _ => rfl,
    show ∀ x, nativeThreeLegOccupation (0 : I →₀ ℕ) h l (.inr (.inr x)) = l x from fun _ => rfl,
    Nat.cast_zero, zero_mul, mul_zero, Finset.sum_const_zero, zero_add,
    threeOccupation_sub_output]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    simp [Ne.symm hba]
  · simp

private theorem threeMoment_output_only {I : Type*} [Fintype I] [DecidableEq I]
    (D : LatticeData) (T : ℂˣ) (label : I ↪ Index D) (l : I →₀ ℕ) :
    nativeMoment (nativeThreeLegMatrix D T label) (nativeThreeLegOccupation 0 0 l) =
      if l = 0 then 1 else 0 := by
  classical
  by_cases hl : l = 0
  · subst l
    simp [nativeThreeLegOccupation, nativeMoment, FactorialFockMetric.weight,
      gaussianCoefficient_zero]
  · obtain ⟨a, ha⟩ : ∃ a, l a ≠ 0 := by
      by_contra hh
      push_neg at hh
      exact hl (Finsupp.ext hh)
    conv_lhs => rw [← Finsupp.sub_add_single_one_cancel ha]
    rw [threeOccupation_add_output,
      nativeMoment_step _ (nativeThreeLegMatrix_symm D T label)]
    simp [nativeThreeLegOccupation, nativeThreeLegMatrix, Fintype.sum_sum_type, hl]

private theorem threeMoment_IO {I : Type*} [Fintype I] [DecidableEq I]
    (D : LatticeData) (T : ℂˣ) (label : I ↪ Index D) (h l : I →₀ ℕ) :
    nativeMoment (nativeThreeLegMatrix D T label) (nativeThreeLegOccupation 0 h l) =
      (FactorialFockMetric.weight l : ℂ) * (if h = l then 1 else 0) := by
  classical
  suffices hh : ∀ n (h : I →₀ ℕ), h.degree = n → ∀ l,
      nativeMoment (nativeThreeLegMatrix D T label) (nativeThreeLegOccupation 0 h l) =
        (FactorialFockMetric.weight l : ℂ) * (if h = l then 1 else 0) from hh _ h rfl l
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro h hn l
    by_cases hz : h = 0
    · subst h
      rw [threeMoment_output_only]
      by_cases hl : l = 0
      · subst l
        simp [FactorialFockMetric.weight]
      · simp only [if_neg hl, if_neg (Ne.symm hl), mul_zero]
    · obtain ⟨a, ha⟩ : ∃ a, h a ≠ 0 := by
        by_contra hh
        push_neg at hh
        exact hz (Finsupp.ext hh)
      have hdeg := sub_single_degree h a ha
      have hr := Finsupp.sub_add_single_one_cancel ha
      conv_lhs => rw [← hr]
      rw [threeMoment_input_step, ih (h - Finsupp.single a 1).degree (by omega) _ rfl]
      by_cases hl : l a = 0
      · have hne : h ≠ l := by intro he; simpa [he, hl] using ha
        simp [hl, hne]
      · have hweight : (FactorialFockMetric.weight l : ℂ) =
            (l a : ℂ) * (FactorialFockMetric.weight (l - Finsupp.single a 1) : ℂ) := by
          exact_mod_cast weight_sub_single l a hl
        have he : h = l ↔ h - Finsupp.single a 1 = l - Finsupp.single a 1 := by
          constructor
          · intro hh; rw [hh]
          · intro hh
            rw [← hr, hh, Finsupp.sub_add_single_one_cancel hl]
        simp only [← he, hweight]
        ring

private def finiteEntry {I : Type*} (D : LatticeData) (T : ℂˣ)
    (label : I ↪ Index D) (d h l : I →₀ ℕ) : ℂ :=
  nativeNeutralLaurentEntry D T (d.embDomain label) (h.embDomain label) (l.embDomain label)

private theorem finiteEntry_step {I : Type*} (D : LatticeData) (T : ℂˣ)
    (label : I ↪ Index D) (d h l : I →₀ ℕ) (a : I) :
    finiteEntry D T label (d + Finsupp.single a 1) h l =
      (∑ j ∈ l.support, nativeSourceOutputKernel D T (label a) (label j) *
        finiteEntry D T label d h (l - Finsupp.single j 1) +
      ∑ j ∈ h.support, (h j : ℂ) * nativeSourceInputKernel D T (label a) (label j) *
        finiteEntry D T label d (h - Finsupp.single j 1) l) +
      ∑ j ∈ d.support, (d j : ℂ) * nativeSourceSourceKernel D T (label a) (label j) *
        finiteEntry D T label (d - Finsupp.single j 1) h l := by
  classical
  simp only [finiteEntry, Finsupp.embDomain_add, Finsupp.embDomain_single]
  rw [nativeNeutralLaurentEntry_recurrence]
  simp only [Finsupp.support_embDomain, Finset.sum_map,
    Finsupp.embDomain_apply_self, ← Finsupp.embDomain_single label,
    ← Finsupp.embDomain_tsub]

private theorem threeMoment_eq_actual {I : Type*} [Fintype I] [DecidableEq I]
    (D : LatticeData) (T : ℂˣ) (label : I ↪ Index D) (d h l : I →₀ ℕ) :
    nativeMoment (nativeThreeLegMatrix D T label) (nativeThreeLegOccupation d h l) =
      (FactorialFockMetric.weight l : ℂ) * finiteEntry D T label d h l := by
  classical
  suffices hh : ∀ n (d : I →₀ ℕ), d.degree = n → ∀ h l,
      nativeMoment (nativeThreeLegMatrix D T label) (nativeThreeLegOccupation d h l) =
        (FactorialFockMetric.weight l : ℂ) * finiteEntry D T label d h l from hh _ d rfl h l
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro d hn h l
    by_cases hz : d = 0
    · subst d
      rw [threeMoment_IO]
      simp [finiteEntry, nativeNeutralLaurentEntry_zero]
    · obtain ⟨a, ha⟩ : ∃ a, d a ≠ 0 := by
        by_contra hh
        push_neg at hh
        exact hz (Finsupp.ext hh)
      let r := d - Finsupp.single a 1
      have hr : r + Finsupp.single a 1 = d := Finsupp.sub_add_single_one_cancel ha
      have hdeg : r.degree < n := by have := sub_single_degree d a ha; dsimp [r]; omega
      conv_lhs => rw [← hr]
      conv_rhs => rw [← hr]
      rw [threeMoment_source_step, finiteEntry_step]
      have ihR := ih r.degree hdeg r rfl
      simp_rw [ihR]
      have ihS (b : I) (hb : b ∈ r.support) :
          nativeMoment (nativeThreeLegMatrix D T label)
              (nativeThreeLegOccupation (r - Finsupp.single b 1) h l) =
            (FactorialFockMetric.weight l : ℂ) *
              finiteEntry D T label (r - Finsupp.single b 1) h l := by
        have hd := sub_single_degree r b (Finsupp.mem_support_iff.mp hb)
        exact ih _ (by omega) _ rfl h l
      rw [mul_add, mul_add]
      simp only [Finset.mul_sum]
      have hs : (∑ b ∈ r.support, (r b : ℂ) * nativeSourceSourceKernel D T (label a) (label b) *
          nativeMoment (nativeThreeLegMatrix D T label)
            (nativeThreeLegOccupation (r - Finsupp.single b 1) h l)) =
          ∑ b ∈ r.support, (FactorialFockMetric.weight l : ℂ) *
            ((r b : ℂ) * nativeSourceSourceKernel D T (label a) (label b) *
              finiteEntry D T label (r - Finsupp.single b 1) h l) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [ihS b hb]
        ring
      rw [hs]
      have ho : (∑ b ∈ l.support, (l b : ℂ) * nativeSourceOutputKernel D T (label a) (label b) *
          ((FactorialFockMetric.weight (l - Finsupp.single b 1) : ℂ) *
            finiteEntry D T label r h (l - Finsupp.single b 1))) =
          ∑ b ∈ l.support, (FactorialFockMetric.weight l : ℂ) *
            (nativeSourceOutputKernel D T (label a) (label b) *
              finiteEntry D T label r h (l - Finsupp.single b 1)) := by
        apply Finset.sum_congr rfl
        intro b hb
        have hw : (FactorialFockMetric.weight l : ℂ) =
            (l b : ℂ) * (FactorialFockMetric.weight (l - Finsupp.single b 1) : ℂ) := by
          exact_mod_cast weight_sub_single l b (Finsupp.mem_support_iff.mp hb)
        rw [hw]
        ring
      rw [ho]
      have hi : (∑ b ∈ h.support, (h b : ℂ) * nativeSourceInputKernel D T (label a) (label b) *
          ((FactorialFockMetric.weight l : ℂ) * finiteEntry D T label r (h - Finsupp.single b 1) l)) =
          ∑ b ∈ h.support, (FactorialFockMetric.weight l : ℂ) *
            ((h b : ℂ) * nativeSourceInputKernel D T (label a) (label b) *
              finiteEntry D T label r (h - Finsupp.single b 1) l) := by
        apply Finset.sum_congr rfl
        intro b hb
        ring
      rw [hi]
      ring

private theorem actual_eq_threeGaussian {I : Type*} [Fintype I] [DecidableEq I]
    (D : LatticeData) (T : ℂˣ) (label : I ↪ Index D) (d h l : I →₀ ℕ) :
    finiteEntry D T label d h l =
      (FactorialFockMetric.weight d : ℂ) * (FactorialFockMetric.weight h : ℂ) *
        gaussianCoefficient (nativeThreeLegMatrix D T label) (nativeThreeLegOccupation d h l) := by
  have he := threeMoment_eq_actual D T label d h l
  rw [nativeMoment, threeOccupation_weight] at he
  push_cast at he
  have hl : (FactorialFockMetric.weight l : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (FactorialFockMetric.weight_pos l))
  apply mul_left_cancel₀ hl
  linear_combination -he

/-- Restriction to a finite label set, with no change of colour or factorials. -/
def nativeRestrictedOccupation (D : LatticeData) (K : Finset (Index D))
    (d : Index D →₀ ℕ) : K →₀ ℕ :=
  d.comapDomain (Function.Embedding.subtype (fun a => a ∈ K)) Subtype.val_injective.injOn

/-- Ordinary exponential coefficient of the literal finite raw three-leg kernel. -/
def nativeFiniteRawGaussianCoefficient (D : LatticeData) (T : ℂˣ)
    (K : Finset (Index D)) (d h l : Index D →₀ ℕ) : ℂ :=
  nativeThreeLegExponentialCoefficient D T (Function.Embedding.subtype (fun a => a ∈ K))
    (nativeRestrictedOccupation D K d) (nativeRestrictedOccupation D K h)
    (nativeRestrictedOccupation D K l)

private theorem nativeNeutralLaurentEntry_gaussian
    (D : LatticeData) (T : ℂˣ) (d h l : Index D →₀ ℕ) (K : Finset (Index D))
    (hd : d.support ⊆ K) (hh : h.support ⊆ K) (hl : l.support ⊆ K) :
    nativeNeutralLaurentEntry D T d h l =
      (FactorialFockMetric.weight d : ℂ) * (FactorialFockMetric.weight h : ℂ) *
        nativeFiniteRawGaussianCoefficient D T K d h l := by
  classical
  let label : K ↪ Index D := Function.Embedding.subtype (fun a => a ∈ K)
  have reconstruct (q : Index D →₀ ℕ) (hq : q.support ⊆ K) :
      (nativeRestrictedOccupation D K q).embDomain label = q := by
    apply Finsupp.embDomain_comapDomain
    intro a ha
    exact ⟨⟨a, hq ha⟩, rfl⟩
  have weight_restrict (q : Index D →₀ ℕ) (hq : q.support ⊆ K) :
      FactorialFockMetric.weight (nativeRestrictedOccupation D K q) =
        FactorialFockMetric.weight q := by
    calc
      _ = FactorialFockMetric.weight
          ((nativeRestrictedOccupation D K q).embDomain label) := by
            simp only [FactorialFockMetric.weight, Finsupp.prod_embDomain]
      _ = _ := congrArg FactorialFockMetric.weight (reconstruct q hq)
  have he := actual_eq_threeGaussian D T label (nativeRestrictedOccupation D K d)
    (nativeRestrictedOccupation D K h) (nativeRestrictedOccupation D K l)
  rw [← nativeThreeLegExponentialCoefficient_eq] at he
  simpa only [finiteEntry, reconstruct d hd, reconstruct h hh, reconstruct l hl,
    weight_restrict d hd, weight_restrict h hh, nativeFiniteRawGaussianCoefficient] using he

/-- The actual full neutral corrected field equals the finite raw coherent
Gaussian coefficient on every ground vector. Any finite label set containing
the occupied labels is valid; finite-support independence is proved, not assumed.
Only source and input factorials divide this ordinary output coefficient. -/
theorem nativeNeutralCoefficient_full_raw_gaussian
    (D : LatticeData) (hu : IsUnit D.G.det) (T : ℂˣ)
    (d h l : Index D →₀ ℕ) (K : Finset (Index D))
    (hd : d.support ⊆ K) (hh : h.support ⊆ K) (hl : l.support ⊆ K)
    (g : ActualGround D hu) :
    let E : ℤ := (LatticeHalfFockGradedTrace.oddWeight D l : ℤ) -
      (LatticeHalfFockGradedTrace.oddWeight D h : ℤ) - 2 * nativeSourceEnergy D d
    (((FactorialFockMetric.weight d : ℂ) * (FactorialFockMetric.weight h : ℂ))⁻¹) •
      ((T : ℂ) ^ E • nativeOutputProjection D hu l
        (nativeNeutralCoefficient D hu d E (monomial h 1 ⊗ₜ[ℂ] g))) =
      nativeFiniteRawGaussianCoefficient D T K d h l • g := by
  dsimp only
  rw [← nativeNeutralLaurentEntry_at_energy,
    nativeNeutralLaurentEntry_gaussian D T d h l K hd hh hl, smul_smul]
  have hd0 : (FactorialFockMetric.weight d : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (FactorialFockMetric.weight_pos d))
  have hh0 : (FactorialFockMetric.weight h : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (FactorialFockMetric.weight_pos h))
  congr 1
  field_simp

#print axioms nativeNeutralCoefficient_full_raw_gaussian
#print axioms nativeNeutralLaurentEntry_zero
#print axioms nativeNeutralLaurentEntry_unpaired
#print axioms nativeNeutralLaurentEntry_recurrence

#print axioms nativeNeutralCoefficient_source_insertion
#print axioms nativeNeutralCoefficient_source
#print axioms nativeNeutralCoefficient_shift_expansion
#print axioms nativeNeutralCoefficient_native_expansion
#print axioms nativeNeutralCoefficient_projected_support
#print axioms nativeNeutralCoefficient_frequency_projected_mode_sum
#print axioms nativeNeutralCoefficient_eq_laurent_coefficients
#print axioms nativeNeutralLaurentEntry_at_energy
#print axioms nativeNeutralLaurentEntry_raw_normal_expansion

end D5.S3.VertexAlgebra.HalfFock.NeutralThreeLegCoefficient
