/- GID: D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherds
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fractional Borcherds identity for native actual current generators. -/

import D5.S3.VertexAlgebra.LatticeHalfFockFiniteCurrentCorrection
import D5.S3.VertexAlgebra.LatticeHalfFockPositiveCurrentResidue
import D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling
import D5.S3.VertexAlgebra.LatticeAllStateLocality

/-! Fractional current coefficients on separate source and target carriers. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockFiniteCorrection
open LatticeHalfFockCorrectedField LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeAllStateField LatticeHalfFockChargedCoefficients MvPolynomial
open scoped BigOperators
noncomputable section

local macro "halfChoose" : term =>
  pure (Lean.mkIdent ((Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.halfBinomial_choose))
local macro "positivePascal" : term =>
  pure (Lean.mkIdent ((Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeHalfFockPositiveCurrentResidue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField.positive_pascal_difference))

private theorem finite_convolution
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (a c : ℂ) (K : ℕ) (v : ℕ → V) (hv : ∀ n, K ≤ n → v n = 0) :
    (∑ j ∈ Finset.range K, Ring.choose a j •
      (∑ k ∈ Finset.range K, Ring.choose c k • v (j + k))) =
    ∑ n ∈ Finset.range K, Ring.choose (a + c) n • v n := by
  classical
  simp_rw [Finset.smul_sum, smul_smul]
  calc
    _ = ∑ j ∈ Finset.range K, ∑ k ∈ Finset.range (K - j),
        (Ring.choose a j * Ring.choose c k) • v (j + k) := by
      apply Finset.sum_congr rfl
      intro j hj
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.sub_le K j))
      intro k hk outside
      rw [hv (j + k) (by simp only [Finset.mem_range] at outside; omega), smul_zero]
    _ = ∑ n ∈ Finset.range K, ∑ j ∈ Finset.range (n + 1),
        (Ring.choose a j * Ring.choose c (n - j)) • v n := by
      rw [← Finset.sum_range_diag_flip]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.add_sub_of_le (by simpa using Finset.mem_range.mp hj)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [← Finset.sum_smul, Ring.add_choose_eq n (Commute.all _ _),
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

private theorem original_source_current_residue_tail
    (D : LatticeData) (hu : IsUnit D.G.det) (index : Index D) (b : Carrier D)
    (gamma k : ℤ) (x : ActualTensor D hu) (j : ℕ)
    (hj : vectorFrequencyBound D b + 1 + sourceWeight D index ≤ j) :
    currentResidue D hu index.1 (correctedField D hu b) gamma
      (-(sourceWeight D index : ℤ) + (j : ℤ)) (k - (j : ℤ)) x = 0 := by
  have hm : sourceWeight D index ≤ j := by omega
  have mode : -(sourceWeight D index : ℤ) + (j : ℤ) = ((j - sourceWeight D index : ℕ) : ℤ) := by
    rw [Int.natCast_sub hm]
    ring
  rw [mode]
  exact correctedField_positive_current_residue_tail D hu index.1 b gamma
    (k - (j : ℤ)) (j - sourceWeight D index) x (by omega)

/- proof_shape: original_source_current_residue_cutoff: bind-only
   consumer: negative_inverse.
   The unweighted whole-residue tail discharges every added index, including
   the boundary j=N+m; no claim is made about the two ordered halves. -/
private theorem original_source_current_residue_cutoff
    (D : LatticeData) (hu : IsUnit D.G.det) (index : Index D) (b : Carrier D)
    (gamma k : ℤ) (x : ActualTensor D hu) (K : ℕ)
    (cutoff : vectorFrequencyBound D b + 1 + sourceWeight D index ≤ K) :
    (∑ j ∈ Finset.range (vectorFrequencyBound D b + 1 + sourceWeight D index),
      halfBinomial j • currentResidue D hu index.1 (correctedField D hu b) gamma
        (-(sourceWeight D index : ℤ) + (j : ℤ)) (k - (j : ℤ)) x) =
    ∑ j ∈ Finset.range K,
      halfBinomial j • currentResidue D hu index.1 (correctedField D hu b) gamma
        (-(sourceWeight D index : ℤ) + (j : ℤ)) (k - (j : ℤ)) x := by
  apply Finset.sum_subset (Finset.range_mono cutoff)
  intro j _ outside
  have high : vectorFrequencyBound D b + 1 + sourceWeight D index ≤ j := by
    simpa only [Finset.mem_range, not_lt] using outside
  rw [original_source_current_residue_tail D hu index b gamma k x j high, smul_zero]

private theorem negative_inverse
    (D : LatticeData) (hu : IsUnit D.G.det) (index : Index D) (b : Carrier D)
    (gamma k : ℤ) (x : ActualTensor D hu) (K : ℕ)
    (cutoff : vectorFrequencyBound D b + 1 + sourceWeight D index ≤ K) :
    let m : ℕ := sourceWeight D index
    (correctedField D hu (neutralMode D index.1 (-(m : ℤ)) b)).coeff
        (-2 * k - gamma - 3) x =
      ∑ j ∈ Finset.range K, halfBinomial j •
        currentResidue D hu index.1 (correctedField D hu b) gamma
          (-(m : ℤ) + (j : ℤ)) (k - (j : ℤ)) x := by
  classical
  dsimp only
  let m := sourceWeight D index
  let N := vectorFrequencyBound D b + 1
  have row (s : ℕ) :
      currentResidue D hu index.1 (correctedField D hu b) gamma
        (-(m : ℤ) + ((m + s : ℕ) : ℤ)) (k - ((m + s : ℕ) : ℤ)) x =
      ∑ n ∈ Finset.range N, if s ≤ n then
        Ring.choose (1 / 2 : ℂ) (n - s) •
          (correctedField D hu (neutralMode D index.1 (n : ℤ) b)).coeff
            (-2 * (k - (m : ℤ) - (n : ℤ)) - gamma - 3) x else 0 := by
    rw [Nat.cast_add, show -(m : ℤ) + ((m : ℤ) + s) = (s : ℤ) by ring,
      correctedField_positive_current_residue]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs
    · congr 3
      ring
    · rfl
  have base := correctedField_negative_current_insertion_finite_triangle
    D hu index b gamma k x N (le_refl N)
  dsimp only at base
  have glued :
      (correctedField D hu (neutralMode D index.1 (-(m : ℤ)) b)).coeff
          (-2 * k - gamma - 3) x =
        ∑ j ∈ Finset.range (N + m), halfBinomial j •
          currentResidue D hu index.1 (correctedField D hu b) gamma
            (-(m : ℤ) + (j : ℤ)) (k - (j : ℤ)) x := by
    rw [Nat.add_comm N m, Finset.sum_range_add]
    simp_rw [row]
    exact base
  exact glued.trans (original_source_current_residue_cutoff D hu index b gamma k x K cutoff)


private theorem positive_forward
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank) (b : Carrier D)
    (delta t : ℤ) (r K : ℕ) (x : ActualTensor D hu)
    (hK : vectorFrequencyBound D b + 1 ≤ r + K) :
    currentResidue D hu i (correctedField D hu b) delta r t x =
      ∑ j ∈ Finset.range K, Ring.choose (1 / 2 : ℂ) j •
        (correctedField D hu (neutralMode D i ((r : ℤ) + j) b)).coeff
          (-2 * (t - j) - delta - 3) x := by
  classical
  rw [correctedField_positive_current_residue]
  let f (n : ℕ) : ActualTensor D hu := if r ≤ n then
    Ring.choose (1 / 2 : ℂ) (n - r) •
      (correctedField D hu (neutralMode D i (n : ℤ) b)).coeff
        (-2 * (t + r - n) - delta - 3) x else 0
  have extend : (∑ n ∈ Finset.range (vectorFrequencyBound D b + 1), f n) =
      ∑ n ∈ Finset.range (r + K), f n := by
    apply Finset.sum_subset (Finset.range_mono hK)
    intro n hn outside
    have zero := neutralMode_vanish D i b (n : ℤ) (by
      simp only [Finset.mem_range] at outside; omega)
    simp [f, zero]
  change (∑ n ∈ Finset.range (vectorFrequencyBound D b + 1), f n) = _
  rw [extend, Finset.sum_range_add]
  have prefix_sum : (∑ n ∈ Finset.range r, f n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [f, ite_eq_right (by have := Finset.mem_range.mp hn; omega : ¬ r ≤ n)]
  rw [prefix_sum, zero_add]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [f, Nat.le_add_right, ite_true, Nat.add_sub_cancel_left, Nat.cast_add]
  congr 3
  ring

private theorem source_tail
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank) (b : Carrier D)
    (delta r t : ℤ) (x : ActualTensor D hu) (K : ℕ)
    (hK : (vectorFrequencyBound D b + 1 : ℤ) ≤ r + K) :
    ∀ j : ℕ, K ≤ j →
      (correctedField D hu (neutralMode D i (r + j) b)).coeff
        (-2 * (t - j) - delta - 3) x = 0 := by
  intro j hj
  rw [neutralMode_vanish D i b (r + j) (by omega), map_zero]
  simp

private theorem residue_tail
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank) (b : Carrier D)
    (delta r t : ℤ) (x : ActualTensor D hu) (K : ℕ)
    (hK : (vectorFrequencyBound D b + 1 : ℤ) ≤ r + K) :
    ∀ j : ℕ, K ≤ j →
      currentResidue D hu i (correctedField D hu b) delta (r + j) (t - j) x = 0 := by
  intro j hj
  have nonnegative : 0 ≤ r + j := by omega
  obtain ⟨s, hs⟩ := Int.eq_ofNat_of_zero_le nonnegative
  rw [hs]
  exact correctedField_positive_current_residue_tail D hu i b delta (t - j) s x (by omega)

private theorem finite_zero_transform
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (K : ℕ) (hK : 0 < K) (v : ℕ → V) :
    (∑ j ∈ Finset.range K, Ring.choose (0 : ℂ) j • v j) = v 0 := by
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hne
    rw [Ring.choose_zero_pos ℂ (Nat.pos_of_ne_zero hne), zero_smul]
  · simp only [Finset.mem_range, hK, not_true_eq_false, IsEmpty.forall_iff]


set_option maxHeartbeats 4000000 in
-- Finite dependent sums retain both orderings and the original source cutoff.
private theorem inverse_all
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank) (b : Carrier D)
    (delta r t : ℤ) (x : ActualTensor D hu) (K : ℕ)
    (hK : (vectorFrequencyBound D b + 1 : ℤ) ≤ r + K) :
    (correctedField D hu (neutralMode D i r b)).coeff (-2 * t - delta - 3) x =
      ∑ j ∈ Finset.range K, Ring.choose (-1 / 2 : ℂ) j •
        currentResidue D hu i (correctedField D hu b) delta (r + j) (t - j) x := by
  classical
  by_cases hzero : K = 0
  · subst K
    have z := neutralMode_vanish D i b r (by omega)
    simp [z]
  have Kpos : 0 < K := by omega
  by_cases hr : 0 ≤ r
  · obtain ⟨s, rfl⟩ := Int.eq_ofNat_of_zero_le hr
    let v (j : ℕ) := (correctedField D hu (neutralMode D i ((s : ℤ) + j) b)).coeff
      (-2 * (t - j) - delta - 3) x
    have hv := source_tail D hu i b delta s t x K hK
    have row (j : ℕ) :
        currentResidue D hu i (correctedField D hu b) delta
          ((s : ℤ) + j) (t - j) x =
        ∑ k ∈ Finset.range K, Ring.choose (1 / 2 : ℂ) k • v (j + k) := by
      have h := positive_forward D hu i b delta (t - j) (s + j) K x (by omega)
      simp only [Nat.cast_add] at h
      rw [h]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [v, Nat.cast_add, ← add_assoc, sub_sub]
    have convolution := finite_convolution (-1 / 2 : ℂ) (1 / 2 : ℂ) K v hv
    rw [show (-1 / 2 : ℂ) + 1 / 2 = 0 by ring,
      finite_zero_transform K Kpos v] at convolution
    simpa only [row, v, Nat.cast_zero, add_zero, sub_zero] using convolution.symm
  · let m := (-r).toNat
    have hm : 0 < m := by dsimp [m]; omega
    let index : Index D := (i, m - 1)
    have weight : sourceWeight D index = m := by simp [index, sourceWeight]; omega
    have mode : -(sourceWeight D index : ℤ) = r := by rw [weight]; dsimp [m]; omega
    have law := negative_inverse D hu index b delta t x K (by rw [weight]; dsimp [m]; omega)
    dsimp only at law
    rw [mode] at law
    simpa only [halfChoose, index] using law

set_option maxHeartbeats 4000000 in
-- Finite dependent sums retain both orderings and the original source cutoff.
private theorem forward_seed
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank) (b : Carrier D)
    (delta r t : ℤ) (x : ActualTensor D hu) (K : ℕ)
    (hK : (vectorFrequencyBound D b + 1 : ℤ) ≤ r + K) :
    currentResidue D hu i (correctedField D hu b) delta r t x =
      ∑ j ∈ Finset.range K, Ring.choose (1 / 2 : ℂ) j •
        (correctedField D hu (neutralMode D i (r + j) b)).coeff
          (-2 * (t - j) - delta - 3) x := by
  classical
  by_cases hzero : K = 0
  · subst K
    have high : (vectorFrequencyBound D b + 1 : ℤ) ≤ r := by omega
    obtain ⟨s, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ r by omega)
    simpa using correctedField_positive_current_residue_tail D hu i b delta t s x (by omega)
  let v (j : ℕ) := currentResidue D hu i (correctedField D hu b) delta (r + j) (t - j) x
  have hv := residue_tail D hu i b delta r t x K hK
  have row (j : ℕ) :
      (correctedField D hu (neutralMode D i (r + j) b)).coeff
        (-2 * (t - j) - delta - 3) x =
      ∑ k ∈ Finset.range K, Ring.choose (-1 / 2 : ℂ) k • v (j + k) := by
    rw [inverse_all D hu i b delta (r + j) (t - j) x K (by omega)]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [v, Nat.cast_add, ← add_assoc, sub_sub]
  have convolution := finite_convolution (1 / 2 : ℂ) (-1 / 2 : ℂ) K v hv
  rw [show (1 / 2 : ℂ) + -1 / 2 = 0 by ring,
    finite_zero_transform K (by omega) v] at convolution
  simpa only [row, v, Nat.cast_zero, add_zero, sub_zero] using convolution.symm

/- Native source and target identifications are consumed by the independent
   source and second-order support proofs below. -/
local macro "polyOne" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeHalfFockCurrentWard 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField.polynomialField_one))
private theorem vacuum_field (D : LatticeData) (hu : IsUnit D.G.det) :
    correctedField D hu (vacuum D) = chargedField D hu 0 := by
  have corr := Corr_monomial_enumeration D (0 : Charge D) 0 [] (by
    simp [LatticeAllStateField.occurrences])
  have one : Corr D (0 : Charge D) 1 = Finsupp.single 0 1 := by
    rw [show (monomial (0 : Index D →₀ ℕ) 1 : Oscillator D) = 1 by simp] at corr
    rw [corr]
    simp only [correctionWord, map_one]
    apply Finsupp.ext
    intro n
    change Polynomial.coeff (1 : Polynomial (Oscillator D)) n = (Finsupp.single 0 1) n
    simp [Polynomial.coeff_one, Finsupp.single_apply, eq_comm]
  simp only [vacuum, correctedField, Finsupp.lsum_single, correctedPolynomial,
    LinearMap.comp_apply, one, correctedSum, Finsupp.lsum_single]
  rw [polyOne]
  apply HVertexOperator.coeff_inj
  funext e
  rw [shiftField_coeff]
  simp
private theorem charged_zero_coeff (D : LatticeData) (hu : IsUnit D.G.det)
    (e : ℤ) (x : ActualTensor D hu) :
    (chargedField D hu 0).coeff e x = if e = 0 then x else 0 := by
  classical
  have series : halfCreationSeries D 0 = 0 := by
    ext n
    simp [halfCreationSeries]
  have exponential : halfCreationExponential D 0 = 1 := by
    simp [halfCreationExponential, series, PowerSeries.subst_zero_eq_C_constantCoeff]
  have creation (n : ℤ) : halfCreationCoeff D 0 n = if n = 0 then 1 else 0 := by
    simp only [halfCreationCoeff, exponential]
    split_ifs <;> simp_all [show ∀ n : ℤ, 0 ≤ n → (n.toNat = 0 ↔ n = 0) by omega]
  have translation (poly : Oscillator D) : halfTranslatedPolynomial D 0 poly = Polynomial.C poly := by
    induction poly using MvPolynomial.induction_on with
    | C c => simp [halfTranslatedPolynomial]
    | add a b ha hb =>
      simp only [halfTranslatedPolynomial] at ha hb ⊢
      rw [map_add, ha, hb, map_add]
    | mul_X poly index h =>
      simp only [halfTranslatedPolynomial] at h ⊢
      rw [map_mul, h, map_mul]
      congr 1
      simp [halfTranslationVariable, bilinear]
  have ground : groundAction D hu 0 = LinearMap.id := by
    change groundRepresentation D hu (QuotientGroup.mk (1 : LatticeTwistedGroundRealization.SignQuotient.Extension D)) = _
    simp only [QuotientGroup.mk_one, map_one]
    rfl
  have oscillator (poly : Oscillator D) : oscillatorCoefficient D 0 e poly =
      if e = 0 then poly else 0 := by
    change (∑ᶠ n : ℕ, oscillatorTerm D 0 e poly n) = _
    have term (n : ℕ) : oscillatorTerm D 0 e poly n =
        if n = 0 then (if e = 0 then poly else 0) else 0 := by
      simp only [oscillatorTerm, translation, Polynomial.coeff_C]
      by_cases hn : n = 0
      · subst n; simp [chargeNorm, bilinear, creation]
      · simp [hn]
    simp_rw [term]
    rw [finsum_eq_single _ 0]
    · simp
    · intro n hn; simp [hn]
  simp only [chargedField, HVertexOperator.coeff_of_coeff]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul poly v =>
    simp only [chargedCoefficient, LinearMap.smul_apply, TensorProduct.map_tmul,
      chargeScalar, chargeNorm, bilinear, Pi.zero_apply, Int.cast_zero, zero_mul,
      Finset.sum_const_zero, neg_zero, zpow_zero, one_smul, ground, LinearMap.id_apply, oscillator]
    split_ifs <;> simp
  | add x y hx hy => simp only [map_add, hx, hy]; split_ifs <;> simp
private theorem vacuum_coeff (D : LatticeData) (hu : IsUnit D.G.det)
    (e : ℤ) (x : ActualTensor D hu) :
    (correctedField D hu (vacuum D)).coeff e x = if e = 0 then x else 0 := by
  rw [vacuum_field, charged_zero_coeff]
local macro "sourceVacuum" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeAllStateField 0) ++
    `D5.S3.VertexAlgebra.LatticeAllStateField.neutral_creativity))

private theorem current_coeff (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (k : ℤ) (x : ActualTensor D hu) :
    (correctedField D hu (neutralMode D i (-1) (vacuum D))).coeff (-2*k-3) x =
      LatticeHalfFock.tensorCurrent D (ActualGround D hu) i k x := by
  classical
  have positive (n : ℕ) : neutralMode D i (n : ℤ) (vacuum D) = 0 :=
    sourceVacuum D i n (Int.natCast_nonneg n)
  have insertion := correctedField_negative_current_insertion D hu (i,0) (vacuum D)
  simp only [sourceWeight, Nat.zero_add, Nat.cast_one, positive, map_zero,
    shiftField, LinearMap.zero_apply, map_zero, smul_zero, Finset.sum_const_zero,
    add_zero] at insertion
  rw [insertion, singletonLinear_coefficient, finsum_eq_single _ k]
  · simp only [flatTerm, flatCoefficient, Module.End.mul_apply]
    split_ifs <;> simp only [Module.End.mul_apply,
      show -2*k-3+2*k+2*(0:ℕ)+3 = 0 by omega,
      vacuum_coeff, ite_true, jetCurrent, LinearMap.smul_apply, jetScalar,
      Finset.range_zero, Finset.prod_empty, Nat.factorial_zero, Nat.cast_one,
      div_one, one_smul]
  · intro m hm
    have different : -2*k-3+2*m+2*(0:ℕ)+3 ≠ 0 := by omega
    simp only [flatTerm, flatCoefficient]
    split_ifs <;> simp only [Module.End.mul_apply, vacuum_coeff, ite_eq_right different, map_zero]
private theorem source_current (D : LatticeData) (i : Fin D.rank) (n : ℤ) (b : Carrier D) :
    LatticeAllStateReconstruction.mu D (neutralMode D i (-1) (vacuum D)) n b =
      neutralMode D i n b := by
  unfold LatticeAllStateReconstruction.mu
  rw [← neutralField_ncoeff D i (-1), LatticeAllStateField.stateField_current,
    neutralField_ncoeff]

def currentLeftTerm (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (b : Carrier D) (delta p q r : ℤ) (x : ActualTensor D hu) (j : ℕ) : ActualTensor D hu :=
  Ring.choose ((p : ℂ) + 1 / 2) j •
    (correctedField D hu (neutralMode D i (r + j) b)).coeff
      (-2 * (p + q - j) - delta - 3) x

def currentRightFirstTerm (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (b : Carrier D) (delta p q r : ℤ) (x : ActualTensor D hu) (j : ℕ) : ActualTensor D hu :=
  ((-1 : ℂ) ^ j * Ring.choose (r : ℂ) j) •
    LatticeHalfFock.tensorCurrent D (ActualGround D hu) i (p + r - j)
      ((correctedField D hu b).coeff (-2 * (q + j) - delta - 2) x)

def currentRightSecondTerm (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (b : Carrier D) (delta p q r : ℤ) (x : ActualTensor D hu) (j : ℕ) : ActualTensor D hu :=
  ((-1 : ℂ) ^ j * Ring.choose (r : ℂ) j) •
    ((-1 : ℂ) ^ r • (correctedField D hu b).coeff
      (-2 * (q + r - j) - delta - 2)
      (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i (p + j) x))

private theorem source_sequence_finite
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank) (b : Carrier D)
    (delta p q r : ℤ) (x : ActualTensor D hu) :
    Function.HasFiniteSupport (fun j : ℕ =>
      (correctedField D hu (neutralMode D i (r + j) b)).coeff
        (-2 * (p + q - j) - delta - 3) x) := by
  classical
  let state := neutralMode D i (-1) (vacuum D)
  let O := ((HahnModule.of ℂ).symm (LatticeAllStateField.Y D state b)).order
  refine (Finset.range ((-r - 1 - O).toNat + 1)).finite_toSet.subset ?_
  intro j hj
  by_contra outside
  have low : -(r + (j : ℤ)) - 1 < O := by
    simp only [Finset.mem_coe, Finset.mem_range] at outside
    omega
  have zero : LatticeAllStateReconstruction.mu D state (r + j) b = 0 :=
    VertexOperator.ncoeff_eq_zero_of_lt_order _ _ _ low
  change LatticeAllStateReconstruction.mu D
    (neutralMode D i (-1) (vacuum D)) (r + j) b = 0 at zero
  rw [source_current] at zero
  exact hj (by dsimp only; rw [zero, map_zero]; simp)

private theorem first_sequence_finite
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank) (b : Carrier D)
    (delta p q r : ℤ) (x : ActualTensor D hu) :
    Function.HasFiniteSupport (fun j : ℕ =>
      LatticeHalfFock.tensorCurrent D (ActualGround D hu) i (p + r - j)
        ((correctedField D hu b).coeff (-2 * (q + j) - delta - 2) x)) := by
  classical
  let O := ((HahnModule.of ℂ).symm (correctedField D hu b x)).order
  refine (Finset.range ((-2 * q - delta - 2 - O).toNat + 1)).finite_toSet.subset ?_
  intro j hj
  by_contra outside
  have low : -2 * (q + (j : ℤ)) - delta - 2 < O := by
    simp only [Finset.mem_coe, Finset.mem_range] at outside
    omega
  have zero : (correctedField D hu b).coeff (-2 * (q + (j : ℤ)) - delta - 2) x = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_order low
  exact hj (by dsimp only; rw [zero, map_zero])

private theorem second_sequence_finite
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank) (b : Carrier D)
    (delta p q r : ℤ) (x : ActualTensor D hu) :
    Function.HasFiniteSupport (fun j : ℕ =>
      (correctedField D hu b).coeff (-2 * (q + r - j) - delta - 2)
        (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i (p + j) x)) := by
  classical
  let field := correctedField D hu (neutralMode D i (-1) (vacuum D))
  let O := ((HahnModule.of ℂ).symm (field x)).order
  refine (Finset.range ((-2 * p - 3 - O).toNat + 1)).finite_toSet.subset ?_
  intro j hj
  by_contra outside
  have low : -2 * (p + (j : ℤ)) - 3 < O := by
    simp only [Finset.mem_coe, Finset.mem_range] at outside
    omega
  have zero : field.coeff (-2 * (p + (j : ℤ)) - 3) x = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_order low
  change (correctedField D hu (neutralMode D i (-1) (vacuum D))).coeff
    (-2 * (p + (j : ℤ)) - 3) x = 0 at zero
  rw [current_coeff] at zero
  exact hj (by dsimp only; rw [zero, map_zero])

private theorem three_supports
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank) (b : Carrier D)
    (delta p q r : ℤ) (x : ActualTensor D hu) :
    Function.HasFiniteSupport (currentLeftTerm D hu i b delta p q r x) ∧
    Function.HasFiniteSupport (currentRightFirstTerm D hu i b delta p q r x) ∧
    Function.HasFiniteSupport (currentRightSecondTerm D hu i b delta p q r x) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (source_sequence_finite D hu i b delta p q r x).smul_right
      (fun j : ℕ => Ring.choose ((p : ℂ) + 1 / 2) j)
  · exact (first_sequence_finite D hu i b delta p q r x).smul_right
      (fun j : ℕ => (-1 : ℂ) ^ j * Ring.choose (r : ℂ) j)
  · have h := (second_sequence_finite D hu i b delta p q r x).smul_right
      (fun _ : ℕ => (-1 : ℂ) ^ r)
    exact h.smul_right (fun j : ℕ => (-1 : ℂ) ^ j * Ring.choose (r : ℂ) j)

private def discrepancy
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank) (b : Carrier D)
    (delta p q r : ℤ) (x : ActualTensor D hu) : ActualTensor D hu :=
  (∑ᶠ j : ℕ, currentLeftTerm D hu i b delta p q r x j) -
    (∑ᶠ j : ℕ, currentRightFirstTerm D hu i b delta p q r x j) +
    (∑ᶠ j : ℕ, currentRightSecondTerm D hu i b delta p q r x j)

private theorem zero_seed
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank) (b : Carrier D)
    (delta q r : ℤ) (x : ActualTensor D hu) :
    discrepancy D hu i b delta 0 q r x = 0 := by
  classical
  let K := ((vectorFrequencyBound D b + 1 : ℤ) - r).toNat
  have hK : (vectorFrequencyBound D b + 1 : ℤ) ≤ r + K := by dsimp [K]; omega
  have left : (∑ᶠ j : ℕ, currentLeftTerm D hu i b delta 0 q r x j) =
      ∑ j ∈ Finset.range K, Ring.choose (1 / 2 : ℂ) j •
        (correctedField D hu (neutralMode D i (r + j) b)).coeff
          (-2 * (q - j) - delta - 3) x := by
    simp only [currentLeftTerm, Int.cast_zero, zero_add]
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra outside
    have high : K ≤ j := by simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using outside
    exact hj (by dsimp only; rw [source_tail D hu i b delta r q x K hK j high, smul_zero])
  have right : currentResidue D hu i (correctedField D hu b) delta r q x =
      (∑ᶠ j : ℕ, currentRightFirstTerm D hu i b delta 0 q r x j) -
      (∑ᶠ j : ℕ, currentRightSecondTerm D hu i b delta 0 q r x j) := by
    rw [currentResidue, smul_finsum' _ (current_residue_right_finite D hu i
      (correctedField D hu b) delta r q x)]
    simp only [currentRightFirstTerm, currentRightSecondTerm, zero_add]
    congr 1
    apply finsum_congr
    intro j
    rw [smul_comm ((-1 : ℂ) ^ r), add_comm r q]
  unfold discrepancy
  rw [left, ← forward_seed D hu i b delta r q x K hK, right]
  abel

private theorem positive_ordered_commutators
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank) (b : Carrier D)
    (delta p q : ℤ) (s : ℕ) (x : ActualTensor D hu) :
    (∑ᶠ j : ℕ, currentRightFirstTerm D hu i b delta p q s x j) -
      (∑ᶠ j : ℕ, currentRightSecondTerm D hu i b delta p q s x j) =
    ∑ l ∈ Finset.range (s + 1), ((-1 : ℂ) ^ l * (s.choose l : ℂ)) •
      (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i (p + s - l)
        ((correctedField D hu b).coeff (-2 * (q + l) - delta - 2) x) -
      (correctedField D hu b).coeff (-2 * (q + l) - delta - 2)
        (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i (p + s - l) x)) := by
  classical
  have firstSum : (∑ᶠ j : ℕ, currentRightFirstTerm D hu i b delta p q s x j) =
      ∑ l ∈ Finset.range (s + 1), ((-1 : ℂ) ^ l * (s.choose l : ℂ)) •
        LatticeHalfFock.tensorCurrent D (ActualGround D hu) i (p + s - l)
          ((correctedField D hu b).coeff (-2 * (q + l) - delta - 2) x) := by
    simp only [currentRightFirstTerm, Int.cast_natCast, Ring.choose_natCast]
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra outside
    have zero := Nat.choose_eq_zero_of_lt (by simpa using outside : s < j)
    exact hj (by simp [zero])
  have secondSum : (∑ᶠ j : ℕ, currentRightSecondTerm D hu i b delta p q s x j) =
      (-1 : ℂ) ^ s • ∑ l ∈ Finset.range (s + 1),
        ((-1 : ℂ) ^ l * (s.choose l : ℂ)) •
          (correctedField D hu b).coeff (-2 * (q + s - l) - delta - 2)
            (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i (p + l) x) := by
    simp only [currentRightSecondTerm, Int.cast_natCast, Ring.choose_natCast,
      zpow_natCast, Finset.smul_sum]
    simp_rw [smul_comm ((-1 : ℂ) ^ s)]
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra outside
    have zero := Nat.choose_eq_zero_of_lt (by simpa using outside : s < j)
    exact hj (by simp [zero])
  rw [firstSum, secondSum, Finset.smul_sum]
  have reflect :
      (∑ l ∈ Finset.range (s + 1), (-1 : ℂ) ^ s •
        (((-1 : ℂ) ^ l * (s.choose l : ℂ)) •
          (correctedField D hu b).coeff (-2 * (q + s - l) - delta - 2)
            (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i (p + l) x))) =
      ∑ l ∈ Finset.range (s + 1), ((-1 : ℂ) ^ l * (s.choose l : ℂ)) •
        (correctedField D hu b).coeff (-2 * (q + l) - delta - 2)
          (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i (p + s - l) x) := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro l hl
    have within : l ≤ s := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hl
    simp only [Nat.add_sub_cancel, Nat.choose_symm within, smul_smul]
    have signs : (-1 : ℂ) ^ s * ((-1 : ℂ) ^ (s - l) * (s.choose l : ℂ)) =
        (-1 : ℂ) ^ l * (s.choose l : ℂ) := by
      have split : (-1 : ℂ) ^ s = (-1 : ℂ) ^ l * (-1 : ℂ) ^ (s - l) := by
        rw [← pow_add, Nat.add_sub_of_le within]
      have square : ((-1 : ℂ) ^ (s - l)) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [split]
      calc
        _ = (-1 : ℂ) ^ l * ((-1 : ℂ) ^ (s - l)) ^ 2 * (s.choose l : ℂ) := by ring
        _ = _ := by rw [square]; ring
    rw [signs, Int.natCast_sub within,
      show q + (s : ℤ) - ((s : ℤ) - l) = q + l by ring,
      show p + ((s : ℤ) - l) = p + s - l by ring]
  rw [reflect, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  rw [smul_sub]

set_option maxHeartbeats 4000000 in
-- Finite dependent sums retain both orderings and the original source cutoff.
private theorem high_seed
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank) (b : Carrier D)
    (delta p q r : ℤ) (x : ActualTensor D hu)
    (hr : (vectorFrequencyBound D b + 1 : ℤ) ≤ r) :
    discrepancy D hu i b delta p q r x = 0 := by
  classical
  have leftZero : (∑ᶠ j : ℕ, currentLeftTerm D hu i b delta p q r x j) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    dsimp only [currentLeftTerm]
    rw [neutralMode_vanish D i b (r + j) (by omega), map_zero]
    simp
  have rightZero : (∑ᶠ j : ℕ, currentRightFirstTerm D hu i b delta p q r x j) -
      (∑ᶠ j : ℕ, currentRightSecondTerm D hu i b delta p q r x j) = 0 := by
    obtain ⟨s, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ r by omega)
    rw [positive_ordered_commutators]
    simp_rw [correctedField_current_ward, Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro n hn
    have exponent (l : ℕ) :
        -2 * (q + l) - delta - 2 - (2 * (p + s - l) + 1) + 2 * (n : ℤ) =
        -2 * (p + q + s - n) - delta - 3 := by ring
    simp_rw [exponent, smul_smul]
    have freq (l : ℕ) : LatticeHalfFock.frequency (p + s - l) =
        (s : ℂ) - l + ((p : ℂ) + 1 / 2) := by
      simp only [LatticeHalfFock.frequency, Int.cast_add, Int.cast_sub, Int.cast_natCast]
      ring
    simp_rw [freq]
    rw [← Finset.sum_smul]
    have difference := positivePascal ((p : ℂ) + 1 / 2) s n
    rw [ite_eq_right (by have := Finset.mem_range.mp hn; omega : ¬ s ≤ n)] at difference
    have scalar : (∑ l ∈ Finset.range (s + 1),
        (((-1 : ℂ) ^ l * (s.choose l : ℂ)) *
          Ring.choose ((s : ℂ) - l + ((p : ℂ) + 1 / 2)) n)) = 0 := by
      convert difference using 1
      apply Finset.sum_congr rfl
      intro l hl
      ring
    rw [scalar, zero_smul]
  unfold discrepancy
  rw [leftZero, sub_eq_zero.mp rightZero]
  abel

/- The finite Pascal propagation follows the organization of LatticeAllStateJacobi;
   its scalar parameter and its two distinct carrier actions are re-elaborated here. -/
set_option maxHeartbeats 4000000 in
-- Finite dependent sums retain both orderings and the original source cutoff.
private theorem discrepancy_recurrence
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank) (b : Carrier D)
    (delta p q r : ℤ) (x : ActualTensor D hu) :
    discrepancy D hu i b delta (p + 1) q r x =
      discrepancy D hu i b delta p (q + 1) r x +
      discrepancy D hu i b delta p q (r + 1) x := by
  classical
  let weight (parameter : ℤ) (offset : ℕ) :=
    (-1 : ℂ) ^ offset * Ring.choose (parameter : ℂ) offset
  let zeroSucc : Option ℕ ≃ ℕ := {
    toFun value := match value with | none => 0 | some offset => offset + 1
    invFun value := match value with | 0 => none | offset + 1 => some offset
    left_inv value := by cases value <;> rfl
    right_inv value := by cases value <;> rfl }
  have splitSum (term : ℕ → ActualTensor D hu) (finite : Function.HasFiniteSupport term) : ∑ᶠ offset : ℕ, term offset = term 0 + ∑ᶠ offset : ℕ, term (offset + 1) := by
    rw [← finsum_comp_equiv zeroSucc, finsum_option]
    · rfl
    · exact finite.fun_comp_of_injective (g := fun offset : ℕ => offset + 1) (fun first second equality => Nat.add_right_cancel equality)
  have pascal (parameter : ℂ) (offset : ℕ) :
      Ring.choose (parameter + 1) (offset + 1) =
        Ring.choose parameter offset + Ring.choose parameter (offset + 1) :=
    Ring.choose_succ_succ parameter offset
  have weightedPascal (parameter : ℤ) (offset : ℕ) : weight (parameter + 1) (offset + 1) = weight parameter (offset + 1) - weight parameter offset := by
    dsimp only [weight]; rw [Int.cast_add, Int.cast_one, pascal, pow_succ]; ring
  have chooseZero (parameter : ℂ) : Ring.choose parameter 0 = 1 := by simp
  have weightZero (parameter : ℤ) : weight parameter 0 = 1 := by simp [weight, chooseZero]
  have sumPascal (parameter : ℂ) (sequence : ℕ → ActualTensor D hu) (finite : Function.HasFiniteSupport sequence) : (∑ᶠ offset : ℕ, Ring.choose (parameter + 1) offset • sequence offset) =
    (∑ᶠ offset : ℕ, Ring.choose parameter offset • sequence offset) + (∑ᶠ offset : ℕ, Ring.choose parameter offset • sequence (offset + 1)) := by
    have tailFinite := finite.fun_comp_of_injective (g := fun offset : ℕ => offset + 1) (fun first second equality => Nat.add_right_cancel equality)
    have nextFinite : Function.HasFiniteSupport (fun offset : ℕ =>
        Ring.choose (parameter + 1) offset • sequence offset) :=
      finite.smul_right (Ring.choose (parameter + 1))
    have currentFinite : Function.HasFiniteSupport (fun offset : ℕ =>
        Ring.choose parameter offset • sequence offset) :=
      finite.smul_right (Ring.choose parameter)
    rw [splitSum _ nextFinite, splitSum _ currentFinite]; simp only [chooseZero, one_smul]; simp_rw [pascal, add_smul]
    have firstTail : Function.HasFiniteSupport (fun offset : ℕ =>
        Ring.choose parameter offset • sequence (offset + 1)) :=
      tailFinite.smul_right (Ring.choose parameter)
    have secondTail : Function.HasFiniteSupport (fun offset : ℕ =>
        Ring.choose parameter (offset + 1) • sequence (offset + 1)) :=
      tailFinite.smul_right (fun offset => Ring.choose parameter (offset + 1))
    rw [finsum_add_distrib firstTail secondTail]; abel
  have sumWeightedPascal (parameter : ℤ) (sequence : ℕ → ActualTensor D hu) (finite : Function.HasFiniteSupport sequence) : (∑ᶠ offset : ℕ, weight (parameter + 1) offset • sequence offset) =
    (∑ᶠ offset : ℕ, weight parameter offset • sequence offset) - (∑ᶠ offset : ℕ, weight parameter offset • sequence (offset + 1)) := by
    have tailFinite := finite.fun_comp_of_injective (g := fun offset : ℕ => offset + 1) (fun first second equality => Nat.add_right_cancel equality)
    have nextFinite : Function.HasFiniteSupport (fun offset : ℕ =>
        weight (parameter + 1) offset • sequence offset) :=
      finite.smul_right (weight (parameter + 1))
    have currentFinite : Function.HasFiniteSupport (fun offset : ℕ =>
        weight parameter offset • sequence offset) := finite.smul_right (weight parameter)
    rw [splitSum _ nextFinite, splitSum _ currentFinite]; simp only [weightZero, one_smul]; simp_rw [weightedPascal, sub_smul]
    have firstTail : Function.HasFiniteSupport (fun offset : ℕ =>
        weight parameter (offset + 1) • sequence (offset + 1)) :=
      tailFinite.smul_right (fun offset => weight parameter (offset + 1))
    have secondTail : Function.HasFiniteSupport (fun offset : ℕ =>
        weight parameter offset • sequence (offset + 1)) :=
      tailFinite.smul_right (weight parameter)
    rw [finsum_sub_distrib firstTail secondTail]; abel
  have leftLaw :
      (∑ᶠ j : ℕ, currentLeftTerm D hu i b delta (p + 1) q r x j) =
      (∑ᶠ j : ℕ, currentLeftTerm D hu i b delta p (q + 1) r x j) +
      (∑ᶠ j : ℕ, currentLeftTerm D hu i b delta p q (r + 1) x j) := by
    let sequence (j : ℕ) :=
      (correctedField D hu (neutralMode D i (r + j) b)).coeff
        (-2 * (p + 1 + q - j) - delta - 3) x
    have initial (j : ℕ) : currentLeftTerm D hu i b delta (p + 1) q r x j =
        Ring.choose (((p : ℂ) + 1 / 2) + 1) j • sequence j := by
      dsimp only [currentLeftTerm, sequence]
      congr 2
      push_cast
      ring
    have current (j : ℕ) : currentLeftTerm D hu i b delta p (q + 1) r x j =
        Ring.choose ((p : ℂ) + 1 / 2) j • sequence j := by
      dsimp only [currentLeftTerm, sequence]
      rw [show p + (q + 1) = p + 1 + q by omega]
    have shifted (j : ℕ) : currentLeftTerm D hu i b delta p q (r + 1) x j =
        Ring.choose ((p : ℂ) + 1 / 2) j • sequence (j + 1) := by
      dsimp only [currentLeftTerm, sequence]
      push_cast
      rw [show r + ((j : ℤ) + 1) = r + 1 + j by omega,
        show p + 1 + q - ((j : ℤ) + 1) = p + q - j by omega]
    simp_rw [initial, current, shifted]
    exact sumPascal ((p : ℂ) + 1 / 2) sequence
      (source_sequence_finite D hu i b delta (p + 1) q r x)
  have firstRightLaw :
      (∑ᶠ j : ℕ, currentRightFirstTerm D hu i b delta (p + 1) q r x j) =
      (∑ᶠ j : ℕ, currentRightFirstTerm D hu i b delta p (q + 1) r x j) +
      (∑ᶠ j : ℕ, currentRightFirstTerm D hu i b delta p q (r + 1) x j) := by
    let sequence (j : ℕ) :=
      LatticeHalfFock.tensorCurrent D (ActualGround D hu) i (p + (r + 1) - j)
        ((correctedField D hu b).coeff (-2 * (q + j) - delta - 2) x)
    have initial (j : ℕ) : currentRightFirstTerm D hu i b delta (p + 1) q r x j =
        weight r j • sequence j := by
      dsimp only [currentRightFirstTerm, weight, sequence]
      rw [show p + 1 + r = p + (r + 1) by omega]
    have current (j : ℕ) : currentRightFirstTerm D hu i b delta p q (r + 1) x j =
        weight (r + 1) j • sequence j := by rfl
    have shifted (j : ℕ) : currentRightFirstTerm D hu i b delta p (q + 1) r x j =
        weight r j • sequence (j + 1) := by
      dsimp only [currentRightFirstTerm, weight, sequence]
      push_cast
      rw [show p + (r + 1) - ((j : ℤ) + 1) = p + r - j by omega,
        show q + ((j : ℤ) + 1) = q + 1 + j by omega]
    simp_rw [initial, current, shifted]
    exact sub_eq_iff_eq_add'.mp (sumWeightedPascal r sequence
      (first_sequence_finite D hu i b delta p q (r + 1) x)).symm
  have sign : (-1 : ℂ) ^ (r + 1) = -((-1 : ℂ) ^ r) := by
    rw [zpow_add₀ (by norm_num)]
    norm_num
  have secondRightLaw :
      (∑ᶠ j : ℕ, currentRightSecondTerm D hu i b delta (p + 1) q r x j) =
      (∑ᶠ j : ℕ, currentRightSecondTerm D hu i b delta p (q + 1) r x j) +
      (∑ᶠ j : ℕ, currentRightSecondTerm D hu i b delta p q (r + 1) x j) := by
    let sequence (j : ℕ) :=
      (correctedField D hu b).coeff (-2 * (q + (r + 1) - j) - delta - 2)
        (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i (p + j) x)
    have initial (j : ℕ) : currentRightSecondTerm D hu i b delta p (q + 1) r x j =
        (-1 : ℂ) ^ r • (weight r j • sequence j) := by
      dsimp only [currentRightSecondTerm, weight, sequence]
      rw [show q + 1 + r = q + (r + 1) by omega, smul_comm]
    have current (j : ℕ) : currentRightSecondTerm D hu i b delta p q (r + 1) x j =
        -((-1 : ℂ) ^ r) • (weight (r + 1) j • sequence j) := by
      dsimp only [currentRightSecondTerm, weight, sequence]
      rw [sign, smul_comm]
    have shifted (j : ℕ) : currentRightSecondTerm D hu i b delta (p + 1) q r x j =
        (-1 : ℂ) ^ r • (weight r j • sequence (j + 1)) := by
      dsimp only [currentRightSecondTerm, weight, sequence]
      push_cast
      rw [show q + (r + 1) - ((j : ℤ) + 1) = q + r - j by omega,
        show p + ((j : ℤ) + 1) = p + 1 + j by omega, smul_comm]
    simp_rw [initial, current, shifted, ← smul_finsum]
    rw [sumWeightedPascal r sequence (second_sequence_finite D hu i b delta p q (r + 1) x)]
    module
  unfold discrepancy
  rw [leftLaw, firstRightLaw, secondRightLaw]
  abel

/- proof_shape: current_borcherds: content
   admission_basis: escape-witness
   escape_witness: Finite half-binomial inversion supplies the zero-p seed;
   Ward and arbitrary-parameter Pascal cancellation supply the high-r seed;
   a supported fractional recurrence propagates both signed indices on the
   distinct original source and actual target, without a module-law premise.
   Literature status: classical twisted-lattice calculus; no novelty claim. -/
set_option maxHeartbeats 4000000 in
-- Signed propagation uses both the original-source high seed and the finite inverse.
/-- The full all-signed current Borcherds identity, with three independent supports. -/
theorem current_borcherds
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank) (b : Carrier D)
    (delta p q r : ℤ) (x : ActualTensor D hu) :
    Function.HasFiniteSupport (currentLeftTerm D hu i b delta p q r x) ∧
    Function.HasFiniteSupport (currentRightFirstTerm D hu i b delta p q r x) ∧
    Function.HasFiniteSupport (currentRightSecondTerm D hu i b delta p q r x) ∧
    (∑ᶠ j : ℕ, currentLeftTerm D hu i b delta p q r x j) =
      (∑ᶠ j : ℕ, currentRightFirstTerm D hu i b delta p q r x j) -
      (∑ᶠ j : ℕ, currentRightSecondTerm D hu i b delta p q r x j) := by
  classical
  let cutoff := vectorFrequencyBound D b + 1
  let E (p q r : ℤ) := discrepancy D hu i b delta p q r x
  have highSeed (p q r : ℤ) (high : (cutoff : ℤ) ≤ r) : E p q r = 0 :=
    high_seed D hu i b delta p q r x high
  have zeroSeed (q r : ℤ) : E 0 q r = 0 := zero_seed D hu i b delta q r x
  have recurrence (p q r : ℤ) : E (p + 1) q r = E p (q + 1) r + E p q (r + 1) :=
    discrepancy_recurrence D hu i b delta p q r x
  have allIndices : ∀ p q r : ℤ, E p q r = 0 := by
    have positive (degree : ℕ) : ∀ q r : ℤ, E degree q r = 0 := by
      induction degree with
      | zero => exact zeroSeed
      | succ degree inductionHypothesis =>
        intro q r; rw [Nat.cast_add, Nat.cast_one, recurrence, inductionHypothesis, inductionHypothesis, add_zero]
    have negative (distance : ℕ) : ∀ magnitude : ℕ, ∀ q : ℤ, E (-(magnitude : ℤ)) q ((cutoff : ℤ) - distance) = 0 := by
      induction distance with
      | zero =>
        intro magnitude q; exact highSeed _ _ _ (by omega)
      | succ distance outerHypothesis =>
        intro magnitude
        induction magnitude with
        | zero => intro q; exact zeroSeed _ _
        | succ magnitude innerHypothesis =>
          intro q
          have law := recurrence (-((magnitude + 1 : ℕ) : ℤ)) (q - 1) ((cutoff : ℤ) - (distance + 1 : ℕ))
          rw [show -((magnitude + 1 : ℕ) : ℤ) + 1 = -(magnitude : ℤ) by omega, show q - 1 + 1 = q by omega, show (cutoff : ℤ) - (distance + 1 : ℕ) + 1 = (cutoff : ℤ) - distance by
            omega, innerHypothesis, outerHypothesis, add_zero] at law
          exact law.symm
    intro p q r
    by_cases nonnegative : 0 ≤ p
    · obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le nonnegative
      exact positive degree q r
    · by_cases high : (cutoff : ℤ) ≤ r
      · exact highSeed p q r high
      · let magnitude := (-p).toNat
        let distance := ((cutoff : ℤ) - r).toNat
        have pEquality : p = -(magnitude : ℤ) := by dsimp [magnitude]; omega
        have rEquality : r = (cutoff : ℤ) - distance := by dsimp [distance]; omega
        rw [pEquality, rEquality]; exact negative distance magnitude q
  obtain ⟨hl, hf, hs⟩ := three_supports D hu i b delta p q r x
  refine ⟨hl, hf, hs, ?_⟩
  have law := allIndices p q r
  change (∑ᶠ j : ℕ, currentLeftTerm D hu i b delta p q r x j) -
    (∑ᶠ j : ℕ, currentRightFirstTerm D hu i b delta p q r x j) +
    (∑ᶠ j : ℕ, currentRightSecondTerm D hu i b delta p q r x j) = 0 at law
  apply sub_eq_zero.mp
  calc
    _ = (∑ᶠ j : ℕ, currentLeftTerm D hu i b delta p q r x j) -
        (∑ᶠ j : ℕ, currentRightFirstTerm D hu i b delta p q r x j) +
        (∑ᶠ j : ℕ, currentRightSecondTerm D hu i b delta p q r x j) := by abel
    _ = 0 := law

end
end D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds
