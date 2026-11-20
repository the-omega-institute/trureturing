/- GID: D5/S3/Quantum/Recovery/PetzExponentialBoundaryEvaluation
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PetzExponentialBoundaryEvaluation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite modular frequencies control upper-strip boundary and Gram trace errors. -/

import D5.S3.Analytic.ExponentialGramWeightedEvaluation
import D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM

/-!
# Finite modular-frequency evaluation on the Petz upper boundary

Tai-Hsuan Yang, *Quantum data processing equality*, arXiv:2609.33815v2,
Lemma IV.2, gives the scalar Poisson-weight estimate. Here equal frequencies
are merged before the estimate is applied, and orthogonal blocks have their
own finite frequency lists. The modular-ratio curve and its Gram products
are expressed in abstract mixed spectral coordinates.
-/

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory Set
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open scoped BigOperators Matrix.Norms.Frobenius

namespace PetzExponentialBoundaryEvaluation

open ExponentialGramWeightedEvaluation

/-- The upper-boundary weight in the strip of width one half. -/
def petzWeight (s : ℝ) : ℝ := Real.pi / (Real.cosh (2 * Real.pi * s) + 1)

private theorem petzWeight_pos (s : ℝ) : 0 < petzWeight s :=
  div_pos Real.pi_pos (add_pos (Real.cosh_pos _) zero_lt_one)

private theorem petzWeight_neg (s : ℝ) : petzWeight (-s) = petzWeight s := by
  simp only [petzWeight, mul_neg, Real.cosh_neg]

private theorem continuous_petzWeight : Continuous petzWeight := by
  unfold petzWeight
  exact continuous_const.div
    ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).add continuous_const)
    (fun s => (add_pos (Real.cosh_pos (2 * Real.pi * s)) zero_lt_one).ne')

private theorem petzWeight_bounds {s : ℝ} (hs : 0 ≤ s) :
    (Real.pi / 2) * Real.exp (-(2 * Real.pi * s)) ≤ petzWeight s ∧
      petzWeight s ≤ (2 * Real.pi) * Real.exp (-(2 * Real.pi * s)) := by
  let x : ℝ := 2 * Real.pi * s
  have hx : 0 ≤ x := mul_nonneg (by positivity) hs
  have he0 : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  have he1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)
  have he : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hsq0 : 0 ≤ Real.exp (-x) * Real.exp (-x) := mul_nonneg he0 he0
  have hsq1 : Real.exp (-x) * Real.exp (-x) ≤ 1 :=
    (mul_le_of_le_one_left he0 he1).trans he1
  have hlo : 1 / 2 ≤ Real.exp (-x) * (Real.cosh x + 1) := by
    rw [Real.cosh_eq]
    nlinarith only [he, hsq0, he0]
  have hhi : Real.exp (-x) * (Real.cosh x + 1) ≤ 2 := by
    rw [Real.cosh_eq]
    nlinarith only [he, hsq1, he1]
  have hden : 0 < Real.cosh x + 1 := add_pos (Real.cosh_pos _) zero_lt_one
  change (Real.pi / 2) * Real.exp (-x) ≤ Real.pi / (Real.cosh x + 1) ∧
    Real.pi / (Real.cosh x + 1) ≤ (2 * Real.pi) * Real.exp (-x)
  constructor
  · apply (le_div_iff₀ hden).2
    calc
      _ = (Real.pi / 2) * (Real.exp (-x) * (Real.cosh x + 1)) := by ring
      _ ≤ (Real.pi / 2) * 2 := mul_le_mul_of_nonneg_left hhi (by positivity)
      _ = Real.pi := by ring
  · apply (div_le_iff₀ hden).2
    calc
      Real.pi = (2 * Real.pi) * (1 / 2) := by ring
      _ ≤ (2 * Real.pi) * (Real.exp (-x) * (Real.cosh x + 1)) :=
        mul_le_mul_of_nonneg_left hlo (by positivity)
      _ = _ := by ring

section Scalar

variable {ι : Type*} [Fintype ι]

private def boundaryDensity (ω : ι → ℝ) (a : ι → ℂ) (s : ℝ) : ℝ :=
  petzWeight s * ‖exponentialSum ω a (s : ℂ)‖ ^ 2

private theorem boundaryDensity_neg (ω : ι → ℝ) (a : ι → ℂ) (s : ℝ) :
    boundaryDensity ω a (-s) = boundaryDensity (fun i => -ω i) a s := by
  have hsum : exponentialSum ω a ((-s : ℝ) : ℂ) =
      exponentialSum (fun i => -ω i) a (s : ℂ) := by
    simp only [exponentialSum, frequency, Complex.ofReal_neg]
    apply Finset.sum_congr rfl
    intro i _
    have harg : Complex.I * (ω i : ℂ) * -(s : ℂ) =
        Complex.I * -(ω i : ℂ) * (s : ℂ) := by ring
    rw [harg]
  simp only [boundaryDensity, petzWeight_neg, hsum]

private theorem boundaryDensity_halfLine (ω : ι → ℝ) (a : ι → ℂ) :
    IntegrableOn (boundaryDensity ω a) (Ioi 0) ∧
      (Real.pi / 2) * weightedEnergy (2 * Real.pi) ω a ≤
        ∫ s : ℝ in Ioi 0, boundaryDensity ω a s := by
  have hExp := (weightedEnergy_eq_gram (2 * Real.pi) ω (by positivity) a).1
  have hCont : Continuous (boundaryDensity ω a) := by
    unfold boundaryDensity
    apply continuous_petzWeight.mul
    unfold exponentialSum
    fun_prop
  have hInt : IntegrableOn (boundaryDensity ω a) (Ioi 0) := by
    refine (hExp.const_mul (2 * Real.pi)).mono' hCont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with s hs
    have hpos : 0 ≤ boundaryDensity ω a s :=
      mul_nonneg (petzWeight_pos s).le (sq_nonneg _)
    rw [Real.norm_of_nonneg hpos]
    have h := mul_le_mul_of_nonneg_right (petzWeight_bounds (le_of_lt hs)).2
      (sq_nonneg ‖exponentialSum ω a (s : ℂ)‖)
    simpa only [boundaryDensity, weightedDensity, neg_mul, mul_assoc] using h
  refine ⟨hInt, ?_⟩
  rw [weightedEnergy, ← integral_const_mul]
  refine integral_mono_ae (hExp.const_mul (Real.pi / 2)) hInt ?_
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with s hs
  have h := mul_le_mul_of_nonneg_right (petzWeight_bounds (le_of_lt hs)).1
    (sq_nonneg ‖exponentialSum ω a (s : ℂ)‖)
  simpa only [boundaryDensity, weightedDensity, neg_mul, mul_assoc] using h

/-- Evaluation at zero on the whole real line, with its integrable upper
boundary density. The half-line estimate applies even to an empty family. -/
private theorem weighted_evaluation_two_sided (ω : ι → ℝ) (a : ι → ℂ)
    (hω : Function.Injective ω) :
    Integrable (fun s : ℝ => petzWeight s * ‖exponentialSum ω a (s : ℂ)‖ ^ 2) ∧
      ‖exponentialSum ω a 0‖ ^ 2 ≤ (2 * (Fintype.card ι : ℝ)) *
        (∫ s : ℝ, petzWeight s * ‖exponentialSum ω a (s : ℂ)‖ ^ 2) := by
  classical
  let ωneg : ι → ℝ := fun i => -ω i
  have hωneg : Function.Injective ωneg := fun _ _ hij => hω (neg_injective hij)
  obtain ⟨hPos, hEnergyPos⟩ := boundaryDensity_halfLine ω a
  obtain ⟨hNegReflected, hEnergyNeg⟩ := boundaryDensity_halfLine ωneg a
  have hNeg : IntegrableOn (boundaryDensity ω a) (Iic 0) := by
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simp only [Function.comp_def, neg_preimage, neg_Iic, neg_zero, boundaryDensity_neg]
    exact (integrableOn_Ici_iff_integrableOn_Ioi (f := boundaryDensity ωneg a)
      (b := (0 : ℝ)) (by finiteness)).2 hNegReflected
  have hAll : Integrable (boundaryDensity ω a) := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
    exact ⟨hNeg, hPos⟩
  have hReflect : (∫ s : ℝ in Iic 0, boundaryDensity ω a s) =
      ∫ s : ℝ in Ioi 0, boundaryDensity ωneg a s := by
    simpa only [boundaryDensity_neg, neg_zero] using
      (integral_comp_neg_Ioi (0 : ℝ) (boundaryDensity ω a)).symm
  have hSplit : (∫ s : ℝ, boundaryDensity ω a s) =
      (∫ s : ℝ in Ioi 0, boundaryDensity ω a s) +
        ∫ s : ℝ in Ioi 0, boundaryDensity ωneg a s := by
    simpa only [compl_Ioi, hReflect] using (integral_add_compl measurableSet_Ioi hAll
      (s := Ioi (0 : ℝ))).symm
  have hRate : 0 < 2 * Real.pi := by positivity
  have hEvalPos := (weighted_evaluation (2 * Real.pi) ω hRate hω).1 a
  have hEvalNeg := (weighted_evaluation (2 * Real.pi) ωneg hRate hωneg).1 a
  refine ⟨hAll, ?_⟩
  change ‖exponentialSum ω a 0‖ ^ 2 ≤ (2 * (Fintype.card ι : ℝ)) *
    (∫ s : ℝ, boundaryDensity ω a s)
  calc
    _ = (‖∑ i, a i‖ ^ 2 + ‖∑ i, a i‖ ^ 2) / 2 := by
      simp only [exponentialSum, mul_zero, Complex.exp_zero, mul_one]
      ring
    _ ≤ (((2 * Real.pi) * (Fintype.card ι : ℝ)) * weightedEnergy (2 * Real.pi) ω a +
        ((2 * Real.pi) * (Fintype.card ι : ℝ)) * weightedEnergy (2 * Real.pi) ωneg a) / 2 :=
      div_le_div_of_nonneg_right (add_le_add hEvalPos hEvalNeg) (by norm_num)
    _ = (2 * (Fintype.card ι : ℝ)) *
        ((Real.pi / 2) * weightedEnergy (2 * Real.pi) ω a +
          (Real.pi / 2) * weightedEnergy (2 * Real.pi) ωneg a) := by ring
    _ ≤ _ := by
      rw [hSplit]
      exact mul_le_mul_of_nonneg_left (add_le_add hEnergyPos hEnergyNeg) (by positivity)

/-- The literal range of the frequency list, including any zero frequency. -/
def distinctFrequencies (ω : ι → ℝ) : Finset ℝ := by
  classical
  exact Finset.univ.image ω

/-- Merge equal frequencies by adding their amplitudes. The estimate uses
the cardinality of the resulting finite set. -/
private theorem weighted_evaluation_distinct_frequencies (ω : ι → ℝ) (a : ι → ℂ) :
    Integrable (fun s : ℝ => petzWeight s * ‖exponentialSum ω a (s : ℂ)‖ ^ 2) ∧
      ‖exponentialSum ω a 0‖ ^ 2 ≤ (2 * ((distinctFrequencies ω).card : ℝ)) *
        (∫ s : ℝ, petzWeight s * ‖exponentialSum ω a (s : ℂ)‖ ^ 2) := by
  classical
  let S := distinctFrequencies ω
  let coeff (r : ℝ) := ∑ i ∈ Finset.univ with ω i = r, a i
  let freq : S → ℝ := Subtype.val
  have hSum : exponentialSum freq (fun r => coeff r) = exponentialSum ω a := by
    funext z
    change (∑ r : S, coeff (r : ℝ) * Complex.exp (Complex.I * (r : ℂ) * z)) =
      ∑ i, a i * Complex.exp (Complex.I * (ω i : ℂ) * z)
    rw [Finset.sum_coe_sort S (fun r : ℝ => coeff r * Complex.exp (Complex.I * (r : ℂ) * z))]
    calc
      _ = ∑ r ∈ S, ∑ i ∈ Finset.univ with ω i = r,
          a i * Complex.exp (Complex.I * (ω i : ℂ) * z) := by
        apply Finset.sum_congr rfl
        intro r _
        dsimp only [coeff]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
      _ = _ := Finset.sum_fiberwise_of_maps_to
        (fun i hi => (show ω i ∈ S from Finset.mem_image_of_mem ω hi)) _
  have h := weighted_evaluation_two_sided freq (fun r => coeff r) Subtype.val_injective
  rw [hSum, Fintype.card_coe] at h
  exact h

end Scalar

private theorem sum_evaluations {ι : Type*} [Fintype ι] (K : ℝ)
    (e : ι → ℝ → ℝ) (v : ι → ℝ)
    (h : ∀ i, Integrable (e i) ∧ v i ≤ K * ∫ s : ℝ, e i s) :
    Integrable (fun s : ℝ => ∑ i, e i s) ∧
      (∑ i, v i) ≤ K * ∫ s : ℝ, ∑ i, e i s := by
  refine ⟨integrable_finsetSum _ (fun i _ => (h i).1), ?_⟩
  rw [integral_finsetSum _ (fun i _ => (h i).1), Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => (h i).2)

/-- The finite exponential curve with coefficients in a complex vector space. -/
def hilbertCurve {ι H : Type*} [Fintype ι] [AddCommMonoid H] [SMul ℂ H]
    (ω : ι → ℝ) (a : ι → H) (s : ℝ) : H :=
  ∑ i, Complex.exp (frequency ω i * (s : ℂ)) • a i

private theorem weighted_evaluation_hilbert {ι H : Type*} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ω : ι → ℝ) (a : ι → H) :
    Integrable (fun s : ℝ => petzWeight s * ‖hilbertCurve ω a s‖ ^ 2) ∧
      ‖hilbertCurve ω a 0‖ ^ 2 ≤ (2 * ((distinctFrequencies ω).card : ℝ)) *
        (∫ s : ℝ, petzWeight s * ‖hilbertCurve ω a s‖ ^ 2) := by
  classical
  let V := Submodule.span ℂ (Set.range a)
  let : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range a)
  let v (i : ι) : V := ⟨a i, Submodule.subset_span (Set.mem_range_self i)⟩
  let b := stdOrthonormalBasis ℂ V
  have hNorm (s : ℝ) :
      ‖hilbertCurve ω a s‖ ^ 2 =
        ∑ j, ‖exponentialSum ω (fun i => b.repr (v i) j) (s : ℂ)‖ ^ 2 := by
    have hCoe : V.subtype (hilbertCurve ω v s) = hilbertCurve ω a s := by
      simp only [hilbertCurve, map_sum, map_smul, V, v, Submodule.subtype_apply]
    rw [← hCoe]
    change ‖hilbertCurve ω v s‖ ^ 2 = _
    rw [← b.repr.norm_map, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro j _
    change ‖PiLp.projₗ 2 (𝕜 := ℂ) (β := fun _ => ℂ) j (b.repr (hilbertCurve ω v s))‖ ^ 2 = _
    simp only [hilbertCurve, exponentialSum, map_sum, map_smul, PiLp.projₗ_apply,
      smul_eq_mul, mul_comm]
  have hDensity : (fun s : ℝ => petzWeight s * ‖hilbertCurve ω a s‖ ^ 2) =
      fun s => ∑ j, petzWeight s *
        ‖exponentialSum ω (fun i => b.repr (v i) j) (s : ℂ)‖ ^ 2 := by
    funext s
    rw [hNorm, Finset.mul_sum]
  rw [hDensity, hNorm 0]
  apply sum_evaluations
  intro j
  simpa only [Complex.ofReal_zero] using
    weighted_evaluation_distinct_frequencies ω (fun i => b.repr (v i) j)

section Blocks

variable {β : Type*} [Fintype β] {ν : β → Type*} [∀ b, Fintype (ν b)]
variable {H : β → Type*} [∀ b, NormedAddCommGroup (H b)] [∀ b, InnerProductSpace ℂ (H b)]

/-- Assemble the finite curves in the orthogonal Hilbert sum. -/
def blockCurve (ω : (b : β) → ν b → ℝ) (a : (b : β) → ν b → H b) (s : ℝ) :
    PiLp 2 H :=
  WithLp.toLp 2 (fun b => hilbertCurve (ω b) (a b) s)

/-- Evaluation at zero in the orthogonal Hilbert sum. Each block can have its
own frequency list, with repeated frequencies and empty lists allowed. -/
theorem weighted_evaluation_blocks (ω : (b : β) → ν b → ℝ)
    (a : (b : β) → ν b → H b) (m : ℕ) (hm : ∀ b, (distinctFrequencies (ω b)).card ≤ m) :
    Integrable (fun s : ℝ => petzWeight s * ‖blockCurve ω a s‖ ^ 2) ∧
      ‖blockCurve ω a 0‖ ^ 2 ≤ (2 * (m : ℝ)) *
        (∫ s : ℝ, petzWeight s * ‖blockCurve ω a s‖ ^ 2) := by
  have hNorm (s : ℝ) : ‖blockCurve ω a s‖ ^ 2 = ∑ b, ‖hilbertCurve (ω b) (a b) s‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 _ _
  have hDensity : (fun s : ℝ => petzWeight s * ‖blockCurve ω a s‖ ^ 2) =
      fun s => ∑ b, petzWeight s * ‖hilbertCurve (ω b) (a b) s‖ ^ 2 := by
    funext s
    rw [hNorm, Finset.mul_sum]
  rw [hDensity, hNorm 0]
  apply sum_evaluations
  intro b
  obtain ⟨hInt, hEval⟩ := weighted_evaluation_hilbert (ω b) (a b)
  have hEnergy : 0 ≤ ∫ s : ℝ, petzWeight s * ‖hilbertCurve (ω b) (a b) s‖ ^ 2 :=
    integral_nonneg (fun s => mul_nonneg (petzWeight_pos s).le (sq_nonneg _))
  exact ⟨hInt, hEval.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hm b)) (by norm_num)) hEnergy)⟩

end Blocks

private theorem frobenius_sq {r c : Type*} [Fintype r] [Fintype c] (X : Matrix r c ℂ) :
    ‖X‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

section RetainedSpectrum

variable {r c β P Q : Type*} [Fintype r] [Fintype c] [Finite β] [Fintype P] [Fintype Q]

/-- A constant mode and the literal retained modular ratios `q/p` for a
fixed outer modular eigenvalue. -/
def retainedFrequency (outer : ℝ) (q : Q → ℝ) (p : P → ℝ) : Option (Q × P) → ℝ
  | none => 0
  | some k => Real.log (outer / (q k.1 / p k.2))

/-- The upper-boundary error in mixed spectral coordinates. For the physical
application `A` is the coordinate matrix of the input square root and
`C k` gives the coordinates of the image under the modular isometry of
the retained component indexed by the pair `k`. -/
def petzBoundary (block : r → c → β) (outer : β → ℝ) (q : Q → ℝ) (p : P → ℝ)
    (A : Matrix r c ℂ) (C : Q × P → Matrix r c ℂ) (s : ℝ) : Matrix r c ℂ :=
  Matrix.of fun i j => A i j - ∑ k : Q × P,
    (Real.sqrt (outer (block i j) / (q k.1 / p k.2)) : ℂ) * C k i j *
      Complex.exp (Complex.I * (retainedFrequency (outer (block i j)) q p (some k) : ℂ) *
        (s : ℂ))

/-- Mixed spectral coordinates give a frequency-count bound on the upper
boundary. Coincident ratios and collisions with the constant mode are counted
only once in each block. -/
theorem weighted_evaluation_petz_boundary (block : r → c → β) (outer : β → ℝ)
    (q : Q → ℝ) (p : P → ℝ) (A : Matrix r c ℂ) (C : Q × P → Matrix r c ℂ)
    (m : ℕ) (hm : ∀ b, (distinctFrequencies (retainedFrequency (outer b) q p)).card ≤ m) :
    Integrable (fun s : ℝ => petzWeight s * ‖petzBoundary block outer q p A C s‖ ^ 2) ∧
      ‖petzBoundary block outer q p A C 0‖ ^ 2 ≤ (2 * (m : ℝ)) *
        (∫ s : ℝ, petzWeight s * ‖petzBoundary block outer q p A C s‖ ^ 2) := by
  classical
  let : Fintype β := Fintype.ofFinite β
  let ω := fun b : β => retainedFrequency (outer b) q p
  let fiber (b : β) := (Finset.univ : Finset (r × c)).filter (fun k => block k.1 k.2 = b)
  let coeff (b : β) (k : Option (Q × P)) : EuclideanSpace ℂ (fiber b) :=
    WithLp.toLp 2 fun i =>
      match k with
      | none => A i.val.1 i.val.2
      | some k => -((Real.sqrt (outer b / (q k.1 / p k.2)) : ℂ) * C k i.val.1 i.val.2)
  have hEntry (b : β) (i : fiber b) (s : ℝ) :
      hilbertCurve (ω b) (coeff b) s i = petzBoundary block outer q p A C s i.val.1 i.val.2 := by
    have hi : block i.val.1 i.val.2 = b := (Finset.mem_filter.mp i.property).2
    change PiLp.projₗ 2 (𝕜 := ℂ) (β := fun _ => ℂ) i (hilbertCurve (ω b) (coeff b) s) = _
    simp only [hilbertCurve, petzBoundary, Matrix.of_apply, Fintype.sum_option,
      map_add, map_sum, map_smul, PiLp.projₗ_apply, coeff,
      smul_eq_mul, ω, frequency, retainedFrequency,
      Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul, mul_neg,
      Finset.sum_neg_distrib, sub_eq_add_neg, hi]
    congr 2
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _
  have hNorm (s : ℝ) :
      ‖blockCurve ω coeff s‖ ^ 2 = ‖petzBoundary block outer q p A C s‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, frobenius_sq]
    change (∑ b, ‖hilbertCurve (ω b) (coeff b) s‖ ^ 2) = _
    let f (k : r × c) := ‖petzBoundary block outer q p A C s k.1 k.2‖ ^ 2
    calc
      _ = ∑ b : β, ∑ k ∈ fiber b, f k := by
        apply Finset.sum_congr rfl
        intro b _
        simp only [PiLp.norm_sq_eq_of_L2, hEntry, f]
        exact Finset.sum_coe_sort (fiber b) f
      _ = ∑ k : r × c, f k := Finset.sum_fiberwise Finset.univ (fun k => block k.1 k.2) f
      _ = _ := Fintype.sum_prod_type f
  simpa only [hNorm] using weighted_evaluation_blocks ω coeff m hm

end RetainedSpectrum

section Trace

open D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound (entryNormSq)

variable {r c : Type*} [Fintype r] [Fintype c]

private theorem traceNorm_cross_gram_le (F G : Matrix r c ℂ) :
    traceNorm (F * Gᴴ) ≤ ‖F‖ * ‖G‖ := by
  simpa only [Matrix.conjTranspose_conjTranspose, entryNormSq, ← frobenius_sq,
    Real.sqrt_sq_eq_abs, abs_norm, Matrix.frobenius_norm_conjTranspose] using
    D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.traceNorm_gram_le Fᴴ Gᴴ

/-- The trace-norm difference of two Gram products is controlled by the
Hilbert–Schmidt difference of the amplitudes. -/
private theorem traceNorm_gram_sub_le (A B : Matrix r c ℂ) :
    traceNorm (B * Bᴴ - A * Aᴴ) ≤ (‖A‖ + ‖B‖) * ‖B - A‖ := by
  classical
  calc
    traceNorm (B * Bᴴ - A * Aᴴ) =
        traceNorm ((B - A) * Bᴴ + A * (Bᴴ - Aᴴ)) := by
      congr 1
      rw [Matrix.sub_mul, Matrix.mul_sub]
      abel
    _ ≤ traceNorm ((B - A) * Bᴴ) + traceNorm (A * (Bᴴ - Aᴴ)) :=
      traceNorm_add_le _ _
    _ ≤ ‖B - A‖ * ‖B‖ + ‖A‖ * ‖B - A‖ :=
      add_le_add (traceNorm_cross_gram_le _ _)
        (by rw [← Matrix.conjTranspose_sub B A]; exact traceNorm_cross_gram_le _ _)
    _ = (‖A‖ + ‖B‖) * ‖B - A‖ := by ring

/-- The squared trace error of the two endpoint Gram products for abstract
unit Hilbert–Schmidt amplitudes. The right side uses the same frequency bound
and the same upper-boundary energy as the Hilbert–Schmidt estimate. -/
theorem traceNorm_gram_sub_sq_le_petz_boundary
    {β P Q : Type*} [Finite β] [Fintype P] [Fintype Q]
    (block : r → c → β) (outer : β → ℝ) (q : Q → ℝ) (p : P → ℝ)
    (A : Matrix r c ℂ) (C : Q × P → Matrix r c ℂ)
    (m : ℕ) (hm : ∀ b, (distinctFrequencies (retainedFrequency (outer b) q p)).card ≤ m)
    (hA : ‖A‖ = 1) (hB : ‖A - petzBoundary block outer q p A C 0‖ = 1) :
    let B := A - petzBoundary block outer q p A C 0
    traceNorm (B * Bᴴ - A * Aᴴ) ^ 2 ≤ (8 * (m : ℝ)) *
      (∫ s : ℝ, petzWeight s * ‖petzBoundary block outer q p A C s‖ ^ 2) := by
  let E := petzBoundary block outer q p A C 0
  let B := A - E
  have hBA : B - A = -E := by
    dsimp only [B]
    abel
  have hTrace : traceNorm (B * Bᴴ - A * Aᴴ) ≤ 2 * ‖E‖ := by
    simpa only [hBA, norm_neg, hA, (show ‖B‖ = 1 from hB), one_add_one_eq_two] using
      traceNorm_gram_sub_le A B
  calc
    traceNorm (B * Bᴴ - A * Aᴴ) ^ 2 ≤ (2 * ‖E‖) ^ 2 :=
      pow_le_pow_left₀ (traceNorm_nonneg _) hTrace 2
    _ = 4 * ‖E‖ ^ 2 := by ring
    _ ≤ 4 * ((2 * (m : ℝ)) *
        (∫ s : ℝ, petzWeight s * ‖petzBoundary block outer q p A C s‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (weighted_evaluation_petz_boundary block outer q p A C m hm).2 (by norm_num)
    _ = _ := by ring

end Trace

end PetzExponentialBoundaryEvaluation
