import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.BigOperators
import D5.S3.Analytic.ExponentialGramWeightedEvaluation

/-!
# Weighted evaluation on the ordinary Petz upper boundary

The verified exponential Gram estimate on each half-line gives the factor
`2m` for the strip weight on the whole real line. In mixed left and right
spectral coordinates the Frobenius square is the sum of the coordinate
squares. The reduced modular ratios supply a common frequency bound for
every outer spectral block, as in the ordinary Petz audit and Yang's
finite-frequency method.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
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
theorem weighted_evaluation_two_sided (ω : ι → ℝ) (a : ι → ℂ)
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

theorem distinctFrequencies_card_le (ω : ι → ℝ) :
    (distinctFrequencies ω).card ≤ Fintype.card ι := by
  classical
  unfold distinctFrequencies
  exact Finset.card_image_le.trans_eq Finset.card_univ

/-- Merge equal frequencies by adding their amplitudes. The estimate uses
the cardinality of the resulting finite set. -/
theorem weighted_evaluation_distinct_frequencies (ω : ι → ℝ) (a : ι → ℂ) :
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

section Blocks

variable {r c β : Type*} [Fintype r] [Fintype c] [Fintype β]
variable {ν : β → Type*} [∀ b, Fintype (ν b)]

/-- A matrix in Hilbert–Schmidt coordinates. The fibers of `block` are the
orthogonal coordinate subspaces and each fiber has its own frequency list. -/
def blockCurve (block : r → c → β) (ω : (b : β) → ν b → ℝ)
    (a : (i : r) → (j : c) → ν (block i j) → ℂ) (s : ℝ) : Matrix r c ℂ :=
  Matrix.of fun i j => exponentialSum (ω (block i j)) (a i j) (s : ℂ)

private theorem frobenius_sq (X : Matrix r c ℂ) :
    ‖X‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- The Frobenius square is the sum over the finite coordinate blocks.
The inner sum is the squared norm of the coordinate projection to that block. -/
theorem frobenius_sq_sum_blocks [DecidableEq β] (block : r → c → β) (X : Matrix r c ℂ) :
    ‖X‖ ^ 2 = ∑ b : β,
      ∑ k ∈ (Finset.univ : Finset (r × c)) with block k.1 k.2 = b, ‖X k.1 k.2‖ ^ 2 := by
  rw [Finset.sum_fiberwise Finset.univ (fun k : r × c => block k.1 k.2)]
  exact (frobenius_sq X).trans (Fintype.sum_prod_type (fun k : r × c => ‖X k.1 k.2‖ ^ 2)).symm

/-- Sum the scalar estimates in the Frobenius norm with a common bound on
the distinct frequency count in each block. -/
theorem weighted_evaluation_blocks (block : r → c → β) (ω : (b : β) → ν b → ℝ)
    (a : (i : r) → (j : c) → ν (block i j) → ℂ) (m : ℕ)
    (hm : ∀ b, (distinctFrequencies (ω b)).card ≤ m) :
    Integrable (fun s : ℝ => petzWeight s * ‖blockCurve block ω a s‖ ^ 2) ∧
      ‖blockCurve block ω a 0‖ ^ 2 ≤ (2 * (m : ℝ)) *
        (∫ s : ℝ, petzWeight s * ‖blockCurve block ω a s‖ ^ 2) := by
  classical
  let X := blockCurve block ω a
  let fiber (b : β) : Finset (r × c) := Finset.univ.filter (fun k => block k.1 k.2 = b)
  let density (k : r × c) (s : ℝ) := petzWeight s * ‖X s k.1 k.2‖ ^ 2
  have hEntry (k : r × c) :
      Integrable (density k) ∧
        ‖X 0 k.1 k.2‖ ^ 2 ≤ (2 * ((distinctFrequencies (ω (block k.1 k.2))).card : ℝ)) *
          (∫ s : ℝ, density k s) := by
    simpa only [density, X, blockCurve, Matrix.of_apply, Complex.ofReal_zero] using
      weighted_evaluation_distinct_frequencies (ω (block k.1 k.2)) (a k.1 k.2)
  have hBlock (b : β) : Integrable (fun s : ℝ => ∑ k ∈ fiber b, density k s) :=
    integrable_finsetSum (fiber b) (fun k _ => (hEntry k).1)
  have hBlockIntegral (b : β) : (∫ s : ℝ, ∑ k ∈ fiber b, density k s) =
      ∑ k ∈ fiber b, ∫ s : ℝ, density k s :=
    integral_finsetSum (fiber b) (fun k _ => (hEntry k).1)
  have hSq (s : ℝ) : ‖X s‖ ^ 2 = ∑ b : β, ∑ k ∈ fiber b, ‖X s k.1 k.2‖ ^ 2 :=
    frobenius_sq_sum_blocks block (X s)
  have hDensity : (fun s : ℝ => petzWeight s * ‖X s‖ ^ 2) =
      fun s => ∑ b : β, ∑ k ∈ fiber b, density k s := by
    funext s
    rw [hSq s]
    simp only [density, Finset.mul_sum]
  change Integrable (fun s : ℝ => petzWeight s * ‖X s‖ ^ 2) ∧
    ‖X 0‖ ^ 2 ≤ (2 * (m : ℝ)) * (∫ s : ℝ, petzWeight s * ‖X s‖ ^ 2)
  rw [hDensity]
  refine ⟨integrable_finsetSum Finset.univ (fun b _ => hBlock b), ?_⟩
  rw [hSq 0, integral_finsetSum Finset.univ (fun b _ => hBlock b)]
  simp only [hBlockIntegral, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  apply Finset.sum_le_sum
  intro k hk
  have hk' : block k.1 k.2 = b := (Finset.mem_filter.mp hk).2
  have hEnergy : 0 ≤ ∫ s : ℝ, density k s :=
    integral_nonneg (fun s => mul_nonneg (petzWeight_pos s).le (sq_nonneg _))
  have hCard : ((distinctFrequencies (ω (block k.1 k.2))).card : ℝ) ≤ (m : ℝ) := by
    rw [hk']
    exact Nat.cast_le.mpr (hm b)
  exact (hEntry k).2.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hCard (by norm_num)) hEnergy)

end Blocks

section RetainedSpectrum

variable {r c β P Q : Type*} [Fintype r] [Fintype c] [Fintype β] [Fintype P] [Fintype Q]

/-- A constant mode and the literal retained modular ratios `q/p` for a
fixed outer modular eigenvalue. -/
def retainedFrequency (outer : ℝ) (q : Q → ℝ) (p : P → ℝ) : Option (Q × P) → ℝ
  | none => 0
  | some k => Real.log (outer / (q k.1 / p k.2))

theorem retainedFrequency_card_le (outer : ℝ) (q : Q → ℝ) (p : P → ℝ) :
    (distinctFrequencies (retainedFrequency outer q p)).card ≤
      1 + Fintype.card Q * Fintype.card P := by
  calc
    _ ≤ Fintype.card (Option (Q × P)) := distinctFrequencies_card_le _
    _ = _ := by rw [Fintype.card_option, Fintype.card_prod, Nat.add_comm]

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

/-- The Frobenius-square estimate has a frequency bound given entirely by
the two retained spectra. Repeated ratios and collisions with the constant
mode are included by exact addition of amplitudes. -/
theorem weighted_evaluation_petz_boundary (block : r → c → β) (outer : β → ℝ)
    (q : Q → ℝ) (p : P → ℝ) (A : Matrix r c ℂ) (C : Q × P → Matrix r c ℂ) :
    Integrable (fun s : ℝ => petzWeight s * ‖petzBoundary block outer q p A C s‖ ^ 2) ∧
      ‖petzBoundary block outer q p A C 0‖ ^ 2 ≤
        (2 * ((1 + Fintype.card Q * Fintype.card P : ℕ) : ℝ)) *
          (∫ s : ℝ, petzWeight s * ‖petzBoundary block outer q p A C s‖ ^ 2) := by
  let ω := fun b : β => retainedFrequency (outer b) q p
  let coeff : r → c → Option (Q × P) → ℂ := fun i j k =>
    match k with
    | none => A i j
    | some k => -((Real.sqrt (outer (block i j) / (q k.1 / p k.2)) : ℂ) * C k i j)
  have hCurve : blockCurve (ν := fun _ => Option (Q × P)) block ω coeff =
      petzBoundary block outer q p A C := by
    funext s
    apply Matrix.ext
    intro i j
    simp only [blockCurve, petzBoundary, Matrix.of_apply, exponentialSum, Fintype.sum_option,
      ω, coeff, frequency, retainedFrequency, Complex.ofReal_zero, mul_zero, zero_mul,
      Complex.exp_zero, mul_one, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  have h := weighted_evaluation_blocks (ν := fun _ => Option (Q × P)) block ω coeff
    (1 + Fintype.card Q * Fintype.card P) (fun b => retainedFrequency_card_le (outer b) q p)
  rw [hCurve] at h
  exact h

/-- The common retained dimension gives the coefficient `2(1+d²)`. -/
theorem weighted_evaluation_petz_boundary_dim (d : ℕ) (block : r → c → β) (outer : β → ℝ)
    (q p : Fin d → ℝ) (A : Matrix r c ℂ) (C : Fin d × Fin d → Matrix r c ℂ) :
    Integrable (fun s : ℝ => petzWeight s * ‖petzBoundary block outer q p A C s‖ ^ 2) ∧
      ‖petzBoundary block outer q p A C 0‖ ^ 2 ≤ (2 * ((1 + d ^ 2 : ℕ) : ℝ)) *
        (∫ s : ℝ, petzWeight s * ‖petzBoundary block outer q p A C s‖ ^ 2) := by
  simpa only [Fintype.card_fin, pow_two] using
    weighted_evaluation_petz_boundary block outer q p A C

end RetainedSpectrum

end PetzExponentialBoundaryEvaluation
