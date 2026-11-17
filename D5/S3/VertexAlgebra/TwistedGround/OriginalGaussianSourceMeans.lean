/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceMeans
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceMeans
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual opposite-charge Gaussian source means and charge constant. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalBlocks

/-! Ordinary bilinear source contractions, with no occupation-series assertion. -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology ENNReal Matrix Matrix.Norms.L2Operator Kronecker
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceMeans

open LatticeGeneratingFieldLocality LatticeHalfFock OriginalCurrentMetric
open OriginalGaussianMatrix OriginalGaussianResolvent OriginalGaussianDifferentiation
open OriginalGaussianAllIndexResolvent OriginalGaussianExternalResolvent
open OriginalGaussianExternalBlocks OriginalCorrectedRowRecompositionSource
open OriginalNormalRowSource OriginalSourceInverseCoefficient NativeAffineTransport
open D5.S3.Analytic.OriginalHalfBinomialPeriod
open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

def sourceCoordinate (z : ℂ) (n : ℕ) : ℂ :=
  halfBinomial (n + 1) * z ^ (n + 1) / (Real.sqrt (n + 1 : ℝ) : ℂ)

def sourceCutoff (N : ℕ) (z : ℂ) : H :=
  ∑ n ∈ Finset.range N, lp.single 2 n (sourceCoordinate z n)

def sourceExternal (out : Bool) (p : ℕ) (z : ℂ) : ℂ :=
  -∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * externalBinomial out p (n + 1) *
    z ^ (2 * (n + 1)) * shiftedCentralSeries (z ^ 2) (n + 1) / period (z ^ 2)

def sourceConstant (z : ℂ) : ℂ :=
  ∑' n : ℕ, (centralWeight (n + 1) : ℂ) * z ^ (2 * (n + 1)) *
    shiftedCentralSeries (z ^ 2) (n + 1) / ((n + 1 : ℂ) * period (z ^ 2))

private lemma sourceCoordinate_bound {ρ : ℝ} (hρ : 0 ≤ ρ) {z : ℂ} (hz : ‖z‖ ≤ ρ)
    (n : ℕ) : ‖sourceCoordinate z n‖ ≤ ρ ^ (n + 1) := by
  have hc : ‖halfBinomial (n + 1) / (Real.sqrt (n + 1 : ℝ) : ℂ)‖ ≤ 1 := by
    simpa [sourceValue] using sourceValue_bound 1 n
  rw [sourceCoordinate, show halfBinomial (n + 1) * z ^ (n + 1) /
      (Real.sqrt (n + 1 : ℝ) : ℂ) =
      (halfBinomial (n + 1) / (Real.sqrt (n + 1 : ℝ) : ℂ)) * z ^ (n + 1) by ring,
    norm_mul, norm_pow]
  exact (mul_le_mul hc (pow_le_pow_left₀ (norm_nonneg z) hz _) (by positivity) zero_le_one).trans_eq (one_mul _)

private lemma source_summable {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖(lp.single 2 n (sourceCoordinate z n) : H)‖) := by
  simpa only [sourceFamilyTerm, sourceCoefficient, pow_zero, one_mul,
    ← lp.single_smul, sourceCoordinate, smul_eq_mul, mul_div_assoc, mul_comm]
    using sourceFamily_summable 0 hz

private lemma source_tsum {z : ℂ} (hz : ‖z‖ < 1) :
    (∑' n : ℕ, lp.single 2 n (sourceCoordinate z n) : H) = sourceFamily 0 z := by
  ext n
  change (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n) (∑' k : ℕ,
    lp.single 2 k (sourceCoordinate z k)) = _
  rw [(lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).map_tsum (source_summable hz).of_norm,
    sourceFamily_apply 0 hz]
  simp only [pow_zero, one_mul]
  rw [tsum_eq_single n]
  · change (lp.single (E := fun _ : ℕ => ℂ) 2 n (sourceCoordinate z n)) n = _
    simp [sourceCoordinate]
  · intro k hk
    change (lp.single (E := fun _ : ℕ => ℂ) 2 k (sourceCoordinate z k)) n = 0
    simp [lp.single_apply, hk]

private lemma bilinear_series (u v : H) :
    innerSL ℂ (star u) v = ∑' n : ℕ, u n * v n := by
  rw [innerSL_apply_apply, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [lp.star_apply, RCLike.inner_apply', ← RCLike.star_def, star_star]

private lemma bilinear_summable (u v : H) : Summable (fun n : ℕ => ‖u n * v n‖) := by
  simpa only [norm_mul] using (lp.summable_mul (p := 2) (q := 2)
    (by simpa using Real.HolderConjugate.two_two) u v)

private lemma source_external_term {z : ℂ} (hz : ‖z‖ < 1) (out : Bool) (p n : ℕ) :
    externalVector out p z n * columnSeries z n =
      -((-1 : ℂ) ^ (n + 1) * externalBinomial out p (n + 1) *
        z ^ (2 * (n + 1)) * shiftedCentralSeries (z ^ 2) (n + 1) / period (z ^ 2)) := by
  rw [externalVector_apply out p hz, columnSeries_entry_explicit_complex hz]
  have hs : (Real.sqrt (n + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < n + 1)).ne'
  unfold externalColumn
  rw [show 2 * (n + 1) = (n + 1) + (n + 1) by omega, pow_add]
  field_simp [hs]
  <;> ring

private lemma source_constant_term {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) :
    sourceFamily 0 z n * columnSeries z n =
      (centralWeight (n + 1) : ℂ) * z ^ (2 * (n + 1)) *
        shiftedCentralSeries (z ^ 2) (n + 1) / ((n + 1 : ℂ) * period (z ^ 2)) := by
  rw [sourceFamily_apply 0 hz, columnSeries_entry_explicit_complex hz,
    halfBinomial_eq_signed_centralWeight]
  have hs : (Real.sqrt (n + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < n + 1)).ne'
  have he : (Real.sqrt (n + 1 : ℝ) : ℂ) ^ 2 = (n + 1 : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1)
  simp only [pow_zero, one_mul]
  rw [show 2 * (n + 1) = (n + 1) + (n + 1) by omega, pow_add, ← he]
  field_simp [hs]
  simp only [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  ring_nf
  simp [← pow_mul, Nat.mul_comm n 2, pow_mul]

/-- The actual complex source column gives both the external affine shift
and the unweighted charge constant by absolutely convergent series. -/
theorem source_pairings_explicit {z : ℂ} (hz : ‖z‖ < 1) (out : Bool) (p : ℕ) :
    Summable (fun n : ℕ => ‖(-1 : ℂ) ^ (n + 1) * externalBinomial out p (n + 1) *
      z ^ (2 * (n + 1)) * shiftedCentralSeries (z ^ 2) (n + 1) / period (z ^ 2)‖) ∧
    Summable (fun n : ℕ => ‖(centralWeight (n + 1) : ℂ) * z ^ (2 * (n + 1)) *
      shiftedCentralSeries (z ^ 2) (n + 1) / ((n + 1 : ℂ) * period (z ^ 2))‖) ∧
    innerSL ℂ (star (externalVector out p z)) (columnSeries z) = sourceExternal out p z ∧
    innerSL ℂ (star (sourceFamily 0 z)) (columnSeries z) = sourceConstant z := by
  have hU := bilinear_summable (externalVector out p z) (columnSeries z)
  have hS := bilinear_summable (sourceFamily 0 z) (columnSeries z)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [source_external_term hz, norm_neg] using hU
  · simpa only [source_constant_term hz] using hS
  · rw [bilinear_series]
    simp_rw [source_external_term hz]
    exact tsum_neg
  · rw [bilinear_series]
    simp_rw [source_constant_term hz]
    rfl

private def root (N : ℕ) (s : Fin N) : ℂ := Real.sqrt (s.val + 1 : ℝ)

private lemma root_ne (N : ℕ) (s : Fin N) : root N s ≠ 0 := by
  unfold root
  exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < s.val + 1)).ne'

private lemma root_sq (N : ℕ) (s : Fin N) : root N s ^ 2 = (s.val + 1 : ℂ) := by
  unfold root
  exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ s.val + 1)

private def chargeVector (D : LatticeData) (a : Charge D) : Fin D.rank → ℂ :=
  fun i => a i

private def chargeCovector (D : LatticeData) (a : Charge D) : Fin D.rank → ℂ :=
  (gramComplex D).mulVec (chargeVector D a)

private lemma chargeCovector_apply (D : LatticeData) (a : Charge D) (i : Fin D.rank) :
    chargeCovector D a i = (bilinear D (unitCharge D i) a : ℂ) ∧
      chargeCovector D a i = (bilinear D a (unitCharge D i) : ℂ) := by
  constructor
  · simp [chargeCovector, chargeVector, Matrix.mulVec, dotProduct, gramComplex,
      bilinear, unitCharge, ite_mul]
  · simp only [bilinear, unitCharge, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, Int.cast_sum, Int.cast_mul]
    unfold chargeCovector chargeVector
    simp only [Matrix.mulVec, dotProduct, gramComplex, Matrix.map_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [D.symmetric j i]
    ring

def leftMean (D : LatticeData) (a : Charge D) (N : ℕ) {X : Type*}
    (e : X → External D) (z : ℂ) : Internal D N ⊕ X → ℂ :=
  fun i => damp D N z i * correctedMean D a (Function.Embedding.refl (Index D))
    (Sum.elim (fun i => .inl (boxLabel D N i))
      (fun x => if (e x).1 then .inr (.inr (e x).2) else .inr (.inl (e x).2)) i)

def rightMean (D : LatticeData) (a : Charge D) (N : ℕ) {X : Type*}
    [Fintype X] [DecidableEq X] (e : X → External D) (z : ℂ) : Internal D N ⊕ X → ℂ :=
  fun i => damp D N z i * transportMean (sourceBlock (J := X) (inverseSubstitution D N))
    (leftMean D (-a) N e 1) i

private lemma leftMean_entries (D : LatticeData) (a : Charge D) (N : ℕ) {X : Type*}
    (e : X → External D) (z : ℂ) :
    (∀ i : Internal D N, leftMean D a N e z (.inl i) =
      chargeCovector D a i.1 * root N i.2 * sourceCoordinate z i.2.val) ∧
    (∀ x : X, leftMean D a N e z (.inr x) = -chargeCovector D a (e x).2.1) := by
  constructor
  · intro i
    change z ^ (i.2.val + 1) * (halfBinomial (i.2.val + 1) *
      (bilinear D (unitCharge D i.1) a : ℂ)) = _
    rw [← (chargeCovector_apply D a i.1).1]
    unfold sourceCoordinate root
    field_simp [root_ne]
    <;> ring
  · intro x
    cases hx : (e x).1 <;>
      simp only [leftMean, damp, Sum.elim_inr, hx, Bool.false_eq_true, ↓reduceIte,
        correctedMean, normalMean, Function.Embedding.refl_apply, one_mul]
    all_goals rw [← (chargeCovector_apply D a (e x).2.1).2]

private lemma rightMean_entries (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (N : ℕ) {X : Type*} [Fintype X] [DecidableEq X] (e : X → External D) (z : ℂ) :
    (∀ i : Internal D N, rightMean D a N e z (.inl i) =
      chargeVector D a i.1 * (root N i.2)⁻¹ * sourceCoordinate z i.2.val) ∧
    (∀ x : X, rightMean D a N e z (.inr x) = chargeCovector D a (e x).2.1) := by
  have hneg : chargeCovector D (-a) = -chargeCovector D a := by
    have ha : chargeVector D (-a) = -chargeVector D a := by ext i; simp [chargeVector]
    unfold chargeCovector
    rw [ha, Matrix.mulVec_neg]
  have hInv : (gramComplex D)⁻¹ * gramComplex D = 1 :=
    Matrix.nonsing_inv_mul _ (SignedOscillatorWick.complex_det_unit D hu)
  constructor
  · intro ⟨i,s⟩
    simp only [rightMean, damp, transportMean, sourceBlock, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
      zero_mul, Finset.sum_const_zero, add_zero, (leftMean_entries D (-a) N e 1).1,
      inverseSubstitution, boxMatrix, Matrix.transpose_apply, Matrix.smul_apply,
      smul_eq_mul, Fintype.sum_prod_type, sourceCoordinate, one_pow, mul_one,
      inv_neg, hneg, Pi.neg_apply]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    have hi : ((gramComplex D)⁻¹).mulVec (chargeCovector D a) i = chargeVector D a i := by
      change ((gramComplex D)⁻¹).mulVec ((gramComplex D).mulVec (chargeVector D a)) i = _
      rw [Matrix.mulVec_mulVec, hInv, Matrix.one_mulVec]
    change z ^ (s.val + 1) *
        (∑ j : Fin D.rank, -(s.val + 1 : ℂ)⁻¹ * (gramComplex D)⁻¹ j i *
        (-chargeCovector D a j * root N s *
          (halfBinomial (s.val + 1) / (Real.sqrt (s.val + 1 : ℝ) : ℂ)))) = _
    have hs (j : Fin D.rank) : (gramComplex D)⁻¹ j i = (gramComplex D)⁻¹ i j := by
      have ht : ((gramComplex D)⁻¹).transpose = (gramComplex D)⁻¹ := by
        rw [Matrix.transpose_nonsing_inv]
        congr 1
        ext j k
        change (D.G k j : ℂ) = (D.G j k : ℂ)
        exact_mod_cast D.symmetric k j
      exact congrArg (fun M => M i j) ht
    simp_rw [hs]
    have hf : (∑ j : Fin D.rank, -(s.val + 1 : ℂ)⁻¹ * (gramComplex D)⁻¹ i j *
        (-chargeCovector D a j * root N s *
          (halfBinomial (s.val + 1) / (Real.sqrt (s.val + 1 : ℝ) : ℂ)))) =
        ((s.val + 1 : ℂ)⁻¹ * halfBinomial (s.val + 1)) *
          ((gramComplex D)⁻¹).mulVec (chargeCovector D a) i := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      unfold root
      field_simp [root_ne]
      <;> ring
    rw [hf, hi]
    rw [← root_sq N s]
    change _ = chargeVector D a i * (root N s)⁻¹ *
      (halfBinomial (s.val + 1) * z ^ (s.val + 1) / root N s)
    field_simp [root_ne]
    <;> ring
  · intro x
    simp only [rightMean, damp, transportMean, sourceBlock, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
      Matrix.one_apply, zero_mul, Finset.sum_const_zero, zero_add, ite_mul,
      one_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      (leftMean_entries D (-a) N e 1).2, hneg, Pi.neg_apply, neg_neg]
    simp

private def tensorVector (D : LatticeData) (N : ℕ)
    (c : Fin D.rank → ℂ) (g : Fin N → ℂ) : Internal D N → ℂ :=
  fun i => c i.1 * g i.2

private lemma tensor_action (D : LatticeData) (N : ℕ)
    (C : Matrix (Fin D.rank) (Fin D.rank) ℂ) (M : Matrix (Fin N) (Fin N) ℂ)
    (c : Fin D.rank → ℂ) (g : Fin N → ℂ) :
    (C ⊗ₖ M).mulVec (tensorVector D N c g) =
      tensorVector D N (C.mulVec c) (M.mulVec g) := by
  ext ⟨i,s⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, tensorVector,
    Matrix.kronecker_apply, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro t _
  ring

private lemma normalized_sources (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (N : ℕ) {X : Type*} [Fintype X] [DecidableEq X]
    (e : X → External D) (z : ℂ) :
    (fun i : Internal D N => leftMean D a N e z (.inl i)) =
      tensorVector D N (chargeCovector D a)
        ((frequencyRoot N).mulVec (fun s : Fin N => sourceCoordinate z s.val)) ∧
    (fun i : Internal D N => rightMean D a N e z (.inl i)) =
      tensorVector D N (chargeVector D a)
        ((inverseFrequencyRoot N).mulVec (fun s : Fin N => sourceCoordinate z s.val)) := by
  constructor <;> ext i
  · rw [(leftMean_entries D a N e z).1]
    simp [tensorVector, frequencyRoot, Matrix.mulVec_diagonal, root, mul_assoc]
  · rw [(rightMean_entries D hu a N e z).1]
    simp [tensorVector, inverseFrequencyRoot, Matrix.mulVec_diagonal, root, mul_assoc]

private def finiteR (N : ℕ) (z : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Ring.inverse (1 - finiteSection N z)

private lemma finite_factor (N : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    finiteSquare N z * (1 + finiteSection N z) = finiteR N z := by
  let K := finiteSection N z
  let T := finiteSquare N z
  have hk : ‖K‖ < 1 := (finiteSection_opNorm_le N z hz).trans_lt
    (pow_lt_one₀ (norm_nonneg z) hz (by norm_num))
  have hu : IsUnit (1 - K ^ 2) := by
    apply isUnit_one_sub_of_norm_lt_one
    rw [pow_two]
    exact (norm_mul_le _ _).trans_lt
      (by simpa [pow_two] using pow_lt_one₀ (norm_nonneg K) hk (by norm_num : (2 : ℕ) ≠ 0))
  have ht : T * (1 - K ^ 2) = 1 := Ring.inverse_mul_cancel _ hu
  have hr : (1 - K) * finiteR N z = 1 :=
    Ring.mul_inverse_cancel _ (isUnit_one_sub_of_norm_lt_one hk)
  calc
    T * (1 + K) = T * (1 + K) * ((1 - K) * finiteR N z) := by rw [hr, mul_one]
    _ = (T * (1 - K ^ 2)) * finiteR N z := by noncomm_ring
    _ = _ := by rw [ht, one_mul]

def effectiveMean (D : LatticeData) (a : Charge D) (N : ℕ) {X : Type*}
    [Fintype X] [DecidableEq X] (e : X → External D) (z : ℂ) : X ⊕ X → ℂ :=
  let A := (leftRow D N e z).submatrix Sum.inl Sum.inl
  let B := (rightRow D N e z).submatrix Sum.inl Sum.inl
  let μ := fun i => leftMean D a N e z (.inl i)
  let ν := fun i => rightMean D a N e z (.inl i)
  Sum.elim
    (fun x => leftMean D a N e z (.inr x) +
      ((leftRow D N e z).submatrix Sum.inr Sum.inl).mulVec
        ((Ring.inverse (1 - B * A)).mulVec (ν + B.mulVec μ)) x)
    (fun x => rightMean D a N e z (.inr x) +
      (((rightRow D N e z).submatrix Sum.inl Sum.inr).transpose).mulVec
        ((Ring.inverse (1 - A * B)).mulVec (μ + A.mulVec ν)) x)

def effectiveConstant (D : LatticeData) (a : Charge D) (N : ℕ) {X : Type*}
    [Fintype X] [DecidableEq X] (e : X → External D) (z : ℂ) : ℂ :=
  let A := (leftRow D N e z).submatrix Sum.inl Sum.inl
  let B := (rightRow D N e z).submatrix Sum.inl Sum.inl
  let μ := fun i => leftMean D a N e z (.inl i)
  let ν := fun i => rightMean D a N e z (.inl i)
  let C := FiniteGaussianSewing.effectiveKernel (0 : Matrix Unit Unit ℂ) (0 : Matrix Unit Unit ℂ)
    A B (fun _ i => μ i) (fun i _ => ν i)
  (C (.inl ()) (.inl ()) + C (.inl ()) (.inr ()) +
    C (.inr ()) (.inl ()) + C (.inr ()) (.inr ())) / 2

private lemma dressed_sources (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (N : ℕ) {X : Type*} [Fintype X] [DecidableEq X]
    (e : X → External D) {z : ℂ} (hz : ‖z‖ < 1) :
    let A := (leftRow D N e z).submatrix Sum.inl Sum.inl
    let B := (rightRow D N e z).submatrix Sum.inl Sum.inl
    let μ := fun i => leftMean D a N e z (.inl i)
    let ν := fun i => rightMean D a N e z (.inl i)
    let f := (finiteR N z).mulVec (fun s : Fin N => sourceCoordinate z s.val)
    (Ring.inverse (1 - B * A)).mulVec (ν + B.mulVec μ) =
      tensorVector D N (chargeVector D a) ((inverseFrequencyRoot N).mulVec f) ∧
    (Ring.inverse (1 - A * B)).mulVec (μ + A.mulVec ν) =
      tensorVector D N (chargeCovector D a) ((frequencyRoot N).mulVec f) := by
  dsimp only
  rw [(normalized_sources D hu a N e z).1, (normalized_sources D hu a N e z).2,
    (original_internal_inverse_similarities D hu N e hz).1,
    (original_internal_inverse_similarities D hu N e hz).2,
    original_source, original_inverse_source D hu]
  have hc : ((gramComplex D)⁻¹).mulVec (chargeCovector D a) = chargeVector D a := by
    change ((gramComplex D)⁻¹).mulVec ((gramComplex D).mulVec _) = _
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
      (SignedOscillatorWick.complex_det_unit D hu), Matrix.one_mulVec]
  have hadd (c : Fin D.rank → ℂ) (v w : Fin N → ℂ) :
      tensorVector D N c v + tensorVector D N c w = tensorVector D N c (v + w) := by
    ext i
    simp [tensorVector, mul_add]
  have hfreq (P Q : Matrix (Fin N) (Fin N) ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1)
      (g : Fin N → ℂ) :
      (P * finiteSquare N z * Q).mulVec (P.mulVec g +
        (P * finiteSection N z * P).mulVec (Q.mulVec g)) =
      P.mulVec ((finiteR N z).mulVec g) := by
    have he : (P * finiteSection N z * P).mulVec (Q.mulVec g) =
        P.mulVec ((finiteSection N z).mulVec g) := by
      simp only [Matrix.mulVec_mulVec]
      congr 1
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hPQ, Matrix.mul_one]
    rw [he, ← Matrix.mulVec_add]
    have hg : g + (finiteSection N z).mulVec g = (1 + finiteSection N z).mulVec g := by
      simp [Matrix.add_mulVec, Matrix.one_mulVec]
    rw [hg]
    simp only [Matrix.mulVec_mulVec]
    congr 1
    calc
      _ = P * (finiteSquare N z * (Q * P)) * (1 + finiteSection N z) := by noncomm_ring
      _ = _ := by rw [hQP, Matrix.mul_one, Matrix.mul_assoc, finite_factor N hz]
  have hcc : (gramComplex D).mulVec (chargeVector D a) = chargeCovector D a := rfl
  simp only [tensor_action, hc, hcc, hadd, Matrix.one_mulVec]
  constructor
  · rw [hfreq _ _ (OriginalGaussianExternalBlocks.root_units N).2 (OriginalGaussianExternalBlocks.root_units N).1]
  · rw [hfreq _ _ (OriginalGaussianExternalBlocks.root_units N).1 (OriginalGaussianExternalBlocks.root_units N).2]

private def finiteU (N : ℕ) (out : Bool) (p : ℕ) (z : ℂ) : ℂ :=
  ∑ s : Fin N, externalColumn out p z s.val *
    (finiteR N z).mulVec (fun t : Fin N => sourceCoordinate z t.val) s

private def finiteS (N : ℕ) (z : ℂ) : ℂ :=
  ∑ s : Fin N, sourceCoordinate z s.val *
    (finiteR N z).mulVec (fun t : Fin N => sourceCoordinate z t.val) s

private lemma mixed_mean_left (D : LatticeData) (a : Charge D) (N : ℕ)
    {X : Type*} [Fintype X] [DecidableEq X] (e : X → External D) (z : ℂ)
    (f : Fin N → ℂ) (x : X) :
    ((leftRow D N e z).submatrix Sum.inr Sum.inl).mulVec
      (tensorVector D N (chargeVector D a) ((inverseFrequencyRoot N).mulVec f)) x =
      chargeCovector D a (e x).2.1 * ∑ s : Fin N, externalColumn (e x).1 (e x).2.2 z s.val * f s := by
  change (∑ i : Internal D N, leftRow D N e z (.inr x) (.inl i) *
    (chargeVector D a i.1 * ((inverseFrequencyRoot N).mulVec f) i.2)) = _
  simp only [original_mixed_transpose, original_mixed, inverseFrequencyRoot, Matrix.mulVec_diagonal,
    Fintype.sum_prod_type]
  have hs (i : Fin D.rank) (s : Fin N) :
      (Real.sqrt (s.val + 1 : ℝ) : ℂ) * externalColumn (e x).1 (e x).2.2 z s.val *
        gramComplex D i (e x).2.1 * (chargeVector D a i *
          ((Real.sqrt (s.val + 1 : ℝ) : ℂ)⁻¹ * f s)) =
      (gramComplex D (e x).2.1 i * chargeVector D a i) *
        (externalColumn (e x).1 (e x).2.2 z s.val * f s) := by
    rw [show gramComplex D i (e x).2.1 = gramComplex D (e x).2.1 i by
      change (D.G i (e x).2.1 : ℂ) = (D.G (e x).2.1 i : ℂ)
      exact_mod_cast D.symmetric i (e x).2.1]
    have hn : (Real.sqrt (s.val + 1 : ℝ) : ℂ) ≠ 0 := root_ne N s
    field_simp [hn]
    <;> ring
  simp_rw [hs, ← Finset.mul_sum]
  rw [← Finset.sum_mul]
  rfl

private lemma mixed_mean_right (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D) (N : ℕ)
    {X : Type*} [Fintype X] [DecidableEq X] (e : X → External D) (z : ℂ)
    (f : Fin N → ℂ) (x : X) :
    (((rightRow D N e z).submatrix Sum.inl Sum.inr).transpose).mulVec
      (tensorVector D N (chargeCovector D a) ((frequencyRoot N).mulVec f)) x =
      -chargeCovector D a (e x).2.1 * ∑ s : Fin N, externalColumn (e x).1 (e x).2.2 z s.val * f s := by
  change (∑ i : Internal D N, rightRow D N e z (.inl i) (.inr x) *
    (chargeCovector D a i.1 * ((frequencyRoot N).mulVec f) i.2)) = _
  simp only [original_inverse_mixed D hu, frequencyRoot, Matrix.mulVec_diagonal,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte, mul_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hn : (Real.sqrt (s.val + 1 : ℝ) : ℂ) ≠ 0 := root_ne N s
  field_simp [hn]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

private lemma finite_means (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D) (N : ℕ)
    {X : Type*} [Fintype X] [DecidableEq X] (e : X → External D)
    {z : ℂ} (hz : ‖z‖ < 1) (x : X) :
    effectiveMean D a N e z (.inl x) = chargeCovector D a (e x).2.1 *
      (-1 + finiteU N (e x).1 (e x).2.2 z) ∧
    effectiveMean D a N e z (.inr x) = chargeCovector D a (e x).2.1 *
      (1 - finiteU N (e x).1 (e x).2.2 z) := by
  constructor
  · simp only [effectiveMean, Sum.elim_inl]
    rw [(dressed_sources D hu a N e hz).1, mixed_mean_left,
      (leftMean_entries D a N e z).2]
    unfold finiteU
    ring
  · simp only [effectiveMean, Sum.elim_inr]
    rw [(dressed_sources D hu a N e hz).2, mixed_mean_right D hu,
      (rightMean_entries D hu a N e z).2]
    unfold finiteU
    ring

private lemma tensor_dot (D : LatticeData) (N : ℕ)
    (c d : Fin D.rank → ℂ) (g h : Fin N → ℂ) :
    dotProduct (tensorVector D N c g) (tensorVector D N d h) =
      dotProduct c d * dotProduct g h := by
  simp only [dotProduct, tensorVector, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro s _
  ring

private lemma root_dot (N : ℕ) (g h : Fin N → ℂ) :
    dotProduct ((frequencyRoot N).mulVec g) ((inverseFrequencyRoot N).mulVec h) = dotProduct g h ∧
    dotProduct ((inverseFrequencyRoot N).mulVec g) ((frequencyRoot N).mulVec h) = dotProduct g h := by
  constructor <;>
    simp only [dotProduct, frequencyRoot, inverseFrequencyRoot, Matrix.mulVec_diagonal]
  all_goals
    apply Finset.sum_congr rfl
    intro s _
    have hn : (Real.sqrt (s.val + 1 : ℝ) : ℂ) ≠ 0 := root_ne N s
    field_simp [hn]
    <;> ring

private lemma charge_dot (D : LatticeData) (a : Charge D) :
    dotProduct (chargeCovector D a) (chargeVector D a) =
      (LatticeHalfFockChargedTensorCoefficients.chargeNorm D a : ℂ) := by
  simp only [chargeCovector, chargeVector, Matrix.mulVec, dotProduct, gramComplex,
    Matrix.map_apply, Finset.sum_mul, LatticeHalfFockChargedTensorCoefficients.chargeNorm,
    bilinear, Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma finite_constant (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D) (N : ℕ)
    {X : Type*} [Fintype X] [DecidableEq X] (e : X → External D)
    {z : ℂ} (hz : ‖z‖ < 1) :
    effectiveConstant D a N e z =
      (LatticeHalfFockChargedTensorCoefficients.chargeNorm D a : ℂ) * finiteS N z := by
  let A := (leftRow D N e z).submatrix Sum.inl Sum.inl
  let B := (rightRow D N e z).submatrix Sum.inl Sum.inl
  let Q := Ring.inverse (1 - B * A)
  let W := Ring.inverse (1 - A * B)
  let μ := fun i => leftMean D a N e z (.inl i)
  let ν := fun i => rightMean D a N e z (.inl i)
  have he : effectiveConstant D a N e z =
      (dotProduct μ (Q.mulVec (ν + B.mulVec μ)) +
        dotProduct ν (W.mulVec (μ + A.mulVec ν))) / 2 := by
    have hrow (L : Matrix Unit (Internal D N) ℂ)
        (M : Matrix (Internal D N) (Internal D N) ℂ)
        (V : Matrix (Internal D N) Unit ℂ) :
        (L * M * V) () () = dotProduct (L ()) (M.mulVec (fun i => V i ())) := by
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp only [effectiveConstant, FiniteGaussianSewing.effectiveKernel,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.add_apply, Matrix.zero_apply, zero_add,
      Matrix.mulVec_add, dotProduct_add]
    let L : Matrix Unit (Internal D N) ℂ := fun _ i => μ i
    let M : Matrix Unit (Internal D N) ℂ := fun _ i => ν i
    let U : Matrix (Internal D N) Unit ℂ := fun i _ => μ i
    let V : Matrix (Internal D N) Unit ℂ := fun i _ => ν i
    change ((L * Q * B * U) () () + (L * Q * V) () () +
      (M * W * U) () () + (M * W * A * V) () ()) / 2 = _
    rw [Matrix.mul_assoc L Q B, Matrix.mul_assoc M W A]
    simp only [hrow, L, M, U, V, Matrix.mulVec_add, dotProduct_add, Matrix.mulVec_mulVec]
    ring
  rw [he]
  dsimp only [μ, ν]
  change (_ + _) / 2 = _
  rw [(dressed_sources D hu a N e hz).1, (dressed_sources D hu a N e hz).2,
    (normalized_sources D hu a N e z).1, (normalized_sources D hu a N e z).2,
    tensor_dot, tensor_dot, (root_dot N _ _).1, (root_dot N _ _).2,
    charge_dot, dotProduct_comm (chargeVector D a) (chargeCovector D a), charge_dot]
  unfold finiteS dotProduct
  ring

private def sourceMass (ρ : ℝ) : ℝ := ∑' n : ℕ, ρ ^ (n + 1)

private lemma source_control {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (∀ z : ℂ, ‖z‖ ≤ ρ → ‖sourceFamily 0 z‖ ≤ sourceMass ρ ∧
      ∀ N, ‖sourceCutoff N z‖ ≤ sourceMass ρ) ∧
    TendstoUniformly (fun N => fun z : {z : ℂ | ‖z‖ ≤ ρ} => sourceCutoff N z)
      (fun z : {z : ℂ | ‖z‖ ≤ ρ} => sourceFamily 0 z) atTop := by
  have hs := (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hρ hρ1)
  have hb n (z : {z : ℂ | ‖z‖ ≤ ρ}) :
      ‖(lp.single 2 n (sourceCoordinate z n) : H)‖ ≤ ρ ^ (n + 1) := by
    rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
    exact sourceCoordinate_bound hρ z.property n
  constructor
  · intro z hz
    have hb' n := hb n ⟨z, hz⟩
    constructor
    · rw [← source_tsum (hz.trans_lt hρ1)]
      exact (norm_tsum_le_tsum_norm (source_summable (hz.trans_lt hρ1))).trans
        ((source_summable (hz.trans_lt hρ1)).tsum_le_tsum hb' hs)
    · intro N
      exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun n _ => hb' n)).trans
        (hs.sum_le_tsum _ (fun n _ => by positivity)))
  · have ht := tendstoUniformly_tsum_nat hs hb
    have heq : (fun z : {z : ℂ | ‖z‖ ≤ ρ} =>
        (∑' n : ℕ, lp.single 2 n (sourceCoordinate z n) : H)) =
        (fun z : {z : ℂ | ‖z‖ ≤ ρ} => sourceFamily 0 z) :=
      funext (fun z => source_tsum (z.property.trans_lt hρ1))
    rwa [heq] at ht

private lemma source_zeroExtend (N : ℕ) (z : ℂ) :
    zeroExtend N (WithLp.toLp 2 (fun s : Fin N => sourceCoordinate z s.val)) = sourceCutoff N z := by
  classical
  ext n
  simp only [zeroExtend_apply, sourceCutoff, lp.coeFn_sum, Finset.sum_apply,
    lp.single_apply, Pi.single_apply, PiLp.toLp_apply]
  by_cases hn : n < N <;> simp [Finset.mem_range, hn, eq_comm]

private lemma zeroExtend_pair (N : ℕ) (x y : EuclideanSpace ℂ (Fin N)) :
    innerSL ℂ (star (zeroExtend N x)) (zeroExtend N y) = ∑ s : Fin N, x s * y s := by
  classical
  rw [bilinear_series]
  rw [tsum_eq_sum (s := Finset.range N)]
  · simp only [zeroExtend_apply]
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro n hn
    simp [n.isLt]
  · intro n hn
    have hn' : ¬n < N := by simpa only [Finset.mem_range] using hn
    simp [zeroExtend_apply, hn']

private lemma finite_pairings (N : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (out : Bool) (p : ℕ) :
    finiteU N out p z = innerSL ℂ (star (externalCutoff N out p z))
      (OriginalGaussianUniformCutoff.sectionSignedResolvent N 1 z (sourceCutoff N z)) ∧
    finiteS N z = innerSL ℂ (star (sourceCutoff N z))
      (OriginalGaussianUniformCutoff.sectionSignedResolvent N 1 z (sourceCutoff N z)) := by
  have h := OriginalGaussianDisplacement.zeroExtend_signed N (by simp : ‖(1 : ℂ)‖ = 1) hz
    (WithLp.toLp 2 (fun s : Fin N => sourceCoordinate z s.val))
  change OriginalGaussianUniformCutoff.sectionSignedResolvent N 1 z
    (zeroExtend N (WithLp.toLp 2 (fun s : Fin N => sourceCoordinate z s.val))) =
      zeroExtend N (WithLp.toLp 2 ((Ring.inverse (1 - (1 : ℂ) • finiteSection N z)).mulVec
        (fun s : Fin N => sourceCoordinate z s.val))) at h
  simp only [one_smul] at h
  rw [source_zeroExtend] at h
  constructor
  · rw [h, ← cutoff_zeroExtend, zeroExtend_pair]
    rfl
  · rw [h, ← source_zeroExtend, zeroExtend_pair]
    rfl

private lemma source_pair_uniform {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (v : ℂ → H) (vN : ℕ → ℂ → H) (M : ℝ)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ ρ → ‖v z‖ ≤ M)
    (hv : TendstoUniformly (fun N => fun z : {z : ℂ | ‖z‖ ≤ ρ} => vN N z)
      (fun z : {z : ℂ | ‖z‖ ≤ ρ} => v z) atTop) :
    TendstoUniformlyOn
      (fun N z => innerSL ℂ (star (vN N z))
        (OriginalGaussianUniformCutoff.sectionSignedResolvent N 1 z (sourceCutoff N z)))
      (fun z => innerSL ℂ (star (v z)) (columnSeries z)) atTop {z : ℂ | ‖z‖ ≤ ρ} := by
  let C := max 1 (max M (max (sourceMass ρ) (1 - ρ ^ 2)⁻¹))
  have hC : 1 ≤ C := le_max_left _ _
  have hMC : M ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hgC : sourceMass ρ ≤ C := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hRC : (1 - ρ ^ 2)⁻¹ ≤ C := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hg := source_control hρ hρ1
  have hR := OriginalGaussianUniformCutoff.sectionSignedResolvent_tendstoUniformlyOn
    hρ hρ1 1 (by simp)
  simp only [one_smul] at hR
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ := ε / (3 * C ^ 2 + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  filter_upwards [Metric.tendstoUniformly_iff.mp hv δ hδ,
    Metric.tendstoUniformly_iff.mp hg.2 δ hδ,
    Metric.tendstoUniformlyOn_iff.mp hR δ hδ] with N hvN hgN hRN
  intro z hz
  have hq := pow_lt_one₀ hρ hρ1 (by norm_num : (2 : ℕ) ≠ 0)
  have hRnorm : ‖OriginalGaussianResolvent.resolvent z‖ ≤ (1 - ρ ^ 2)⁻¹ :=
    OriginalGaussianUniformCutoff.traceNeumann_norm_le (sq_nonneg ρ) hq
      ((operator_norm_le (hz.trans_lt hρ1)).trans (pow_le_pow_left₀ (norm_nonneg _) hz 2))
  have hRNnorm : ‖OriginalGaussianUniformCutoff.sectionSignedResolvent N 1 z‖ ≤ (1 - ρ ^ 2)⁻¹ := by
    have hb := OriginalGaussianUniformCutoff.traceNeumann_norm_le (sq_nonneg ρ) hq
      ((sectionOp_norm_le N (hz.trans_lt hρ1)).trans (pow_le_pow_left₀ (norm_nonneg _) hz 2))
    change ‖∑' k : ℕ, sectionOp N z ^ k‖ ≤ (1 - ρ ^ 2)⁻¹ at hb
    simpa only [OriginalGaussianUniformCutoff.sectionSignedResolvent, one_smul] using hb
  have he := external_pair_error (v z) (vN N z) (sourceFamily 0 z) (sourceCutoff N z)
    (OriginalGaussianResolvent.resolvent z) (OriginalGaussianUniformCutoff.sectionSignedResolvent N 1 z)
    (zero_le_one.trans hC) ((hbound z hz).trans hMC) (((hg.1 z hz).2 N).trans hgC)
    (hRnorm.trans hRC) (hRNnorm.trans hRC)
  have h1 := hvN ⟨z, hz⟩
  have h2 := hgN ⟨z, hz⟩
  have h3 := hRN z hz
  rw [dist_comm, dist_eq_norm] at h1 h2 h3 ⊢
  change ‖OriginalGaussianUniformCutoff.sectionSignedResolvent N 1 z -
    OriginalGaussianResolvent.resolvent z‖ < δ at h3
  apply he.trans_lt
  have hCp : 0 < C ^ 2 := sq_pos_of_pos (zero_lt_one.trans_le hC)
  calc
    _ < C ^ 2 * (3 * δ) := mul_lt_mul_of_pos_left (by linarith) hCp
    _ < ε := by
      dsimp [δ]
      rw [show C ^ 2 * (3 * (ε / (3 * C ^ 2 + 1))) =
        (3 * C ^ 2 * ε) / (3 * C ^ 2 + 1) by ring]
      exact (div_lt_iff₀ (by positivity : 0 < 3 * C ^ 2 + 1)).mpr (by nlinarith)

/-- Opposite-charge elimination for the literal corrected source arrays.
The means and the actual two-auxiliary constant converge locally uniformly;
their limits contain only the explicit convergent central-binomial series. -/
theorem original_opposite_charge_means_explicit (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) {X : Type*} [Fintype X] [DecidableEq X] (e : X → External D)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (∀ x : X,
      TendstoUniformlyOn (fun N z => effectiveMean D a N e z (.inl x))
        (fun z => (bilinear D (unitCharge D (e x).2.1) a : ℂ) *
          (-1 + sourceExternal (e x).1 (e x).2.2 z)) atTop {z : ℂ | ‖z‖ ≤ ρ} ∧
      TendstoUniformlyOn (fun N z => effectiveMean D a N e z (.inr x))
        (fun z => (bilinear D (unitCharge D (e x).2.1) a : ℂ) *
          (1 - sourceExternal (e x).1 (e x).2.2 z)) atTop {z : ℂ | ‖z‖ ≤ ρ}) ∧
    TendstoUniformlyOn (fun N z => effectiveConstant D a N e z)
      (fun z => (LatticeHalfFockChargedTensorCoefficients.chargeNorm D a : ℂ) * sourceConstant z)
      atTop {z : ℂ | ‖z‖ ≤ ρ} := by
  have hg := source_control hρ hρ1
  have hS := source_pair_uniform hρ hρ1 (sourceFamily 0) sourceCutoff (sourceMass ρ)
    (fun z hz => (hg.1 z hz).1) hg.2
  have hs : TendstoUniformlyOn finiteS sourceConstant atTop {z : ℂ | ‖z‖ ≤ ρ} := by
    exact (hS.congr (Eventually.of_forall (fun N z hz =>
      (finite_pairings N (hz.trans_lt hρ1) false 0).2.symm))).congr_right
      (fun z hz => (source_pairings_explicit (hz.trans_lt hρ1) false 0).2.2.2)
  have hu' (out : Bool) (p : ℕ) : TendstoUniformlyOn (fun N => finiteU N out p)
      (sourceExternal out p) atTop {z : ℂ | ‖z‖ ≤ ρ} := by
    have hc := externalCutoff_control hρ hρ1 out p
    have hh := source_pair_uniform hρ hρ1 (externalVector out p) (fun N => externalCutoff N out p)
      (externalMass p ρ) (fun z hz => (hc.1 z hz).1) hc.2
    exact (hh.congr (Eventually.of_forall (fun N z hz =>
      (finite_pairings N (hz.trans_lt hρ1) out p).1.symm))).congr_right
      (fun z hz => (source_pairings_explicit (hz.trans_lt hρ1) out p).2.2.1)
  constructor
  · intro x
    have hc := (chargeCovector_apply D a (e x).2.1).1
    constructor
    · have h := (uniformContinuous_const_smul (chargeCovector D a (e x).2.1)).comp_tendstoUniformlyOn
        (((uniformContinuous_const (b := (-1 : ℂ))).add uniformContinuous_id).comp_tendstoUniformlyOn (hu' (e x).1 (e x).2.2))
      exact (h.congr (Eventually.of_forall (fun N z hz => (finite_means D hu a N e (hz.trans_lt hρ1) x).1.symm))).congr_right
        (fun z _ => by rw [hc]; rfl)
    · have h := (uniformContinuous_const_smul (chargeCovector D a (e x).2.1)).comp_tendstoUniformlyOn
        (((uniformContinuous_const (b := (1 : ℂ))).sub uniformContinuous_id).comp_tendstoUniformlyOn (hu' (e x).1 (e x).2.2))
      exact (h.congr (Eventually.of_forall (fun N z hz => (finite_means D hu a N e (hz.trans_lt hρ1) x).2.symm))).congr_right
        (fun z _ => by rw [hc]; rfl)
  · exact ((uniformContinuous_const_smul
      (LatticeHalfFockChargedTensorCoefficients.chargeNorm D a : ℂ)).comp_tendstoUniformlyOn hs).congr
        (Eventually.of_forall (fun N z hz => (finite_constant D hu a N e (hz.trans_lt hρ1)).symm))

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceMeans
