/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ArithmeticTransferDefs
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ArithmeticTransferDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime correlations and quadratic formal interval moments are defined. -/

import D5.S3.Analytic.PrimeProducts.FiniteOffsetSingularSeries

/-! Shared arithmetic hypotheses and formal values for overlapping-interval moments. -/

open scoped BigOperators Topology
open Set Filter MeasureTheory

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false

/-- The full integer-offset singular series transported along the natural-to-integer inclusion. -/
def concreteSS (D : Finset ℕ) : ℝ :=
  D5.S3.Analytic.PrimeProducts.FiniteOffsetSingularSeries.offsetSingularSeries
    (D.image (fun n : ℕ => (n : ℤ)))

/-- The strong Hardy–Littlewood bound for all ordered tuples of one to four distinct positive
shifts, with constants uniform in shifts and real cutoffs. -/
def HL4 (SS : Finset ℕ → ℝ) (β : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ M : ℝ, 1 ≤ M →
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∀ r : ℕ, 1 ≤ r → r ≤ 4 → ∀ d : Fin r → ℕ,
        Function.Injective d → (∀ i, 1 ≤ d i ∧ (d i : ℝ) ≤ M * N ^ β) →
        ∀ y : ℝ, 0 ≤ y → y ≤ 3 * N →
          |(∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
            ∏ i, ArithmeticFunction.vonMangoldt (n + d i)) -
            y * SS (Finset.univ.image d)| ≤ C * N ^ (1 / 2 + ε)

/-- The centered subset transform of a real function on finite subsets
of an arbitrary index type. -/
def centerFinite {ι : Type*} [DecidableEq ι]
    (C : Finset ι → ℝ) (D : Finset ι) : ℝ :=
  ∑ J ∈ D.powerset, (-1 : ℝ) ^ (D.card - J.card) * C J

/-- The centered singular series obtained by inclusion–exclusion over subsets. -/
def center (SS : Finset ℕ → ℝ) (D : Finset ℕ) : ℝ :=
  centerFinite SS D

/-- The positive integer shifts in the half-open scaled interval, using natural floors. -/
def points (H a b : ℝ) : Finset ℕ := Finset.Ioc ⌊a * H⌋₊ ⌊b * H⌋₊

/-- The ordered distinct-shift sum of centered singular series for a family of intervals. -/
def corr {k : ℕ} (SS : Finset ℕ → ℝ) (H : ℝ)
    (a b : Fin k → ℝ) : ℝ :=
  ∑ d ∈ Fintype.piFinset (fun i => points H (a i) (b i))
    with Function.Injective d, center SS (Finset.univ.image d)

/-- All interval endpoints lie in the fixed window and are ordered. -/
def admissible {k : ℕ} (M : ℝ) (a b : Fin k → ℝ) : Prop :=
  ∀ i, 0 ≤ a i ∧ a i ≤ b i ∧ b i ≤ M

/-- The length of the overlap of two half-open intervals. -/
def sigma (a b c d : ℝ) : ℝ := max 0 (min b d - max a c)

/-- The sum of the three products of pairwise overlap lengths. -/
def W4 (a b : Fin 4 → ℝ) : ℝ :=
  sigma (a 0) (b 0) (a 1) (b 1) * sigma (a 2) (b 2) (a 3) (b 3) +
  sigma (a 0) (b 0) (a 2) (b 2) * sigma (a 1) (b 1) (a 3) (b 3) +
  sigma (a 0) (b 0) (a 3) (b 3) * sigma (a 1) (b 1) (a 2) (b 2)

/-- The sum of the three products of second-order distinct-shift correlations. -/
def pairCorr (SS : Finset ℕ → ℝ) (H : ℝ) (a b : Fin 4 → ℝ) : ℝ :=
  corr SS H ![a 0,a 1] ![b 0,b 1] * corr SS H ![a 2,a 3] ![b 2,b 3] +
  corr SS H ![a 0,a 2] ![b 0,b 2] * corr SS H ![a 1,a 3] ![b 1,b 3] +
  corr SS H ![a 0,a 3] ![b 0,b 3] * corr SS H ![a 1,a 2] ![b 1,b 2]

/-- A compactly supported weight has bounded variation, with its supremum bound plus total
variation at most B. -/
def BVBound (w : ℝ → ℝ) (B : ℝ) : Prop :=
  BoundedVariationOn w Set.univ ∧
  (∀ t, t ∉ Icc (1 : ℝ) 2 → w t = 0) ∧
  0 ≤ B ∧ ∃ U : ℝ, 0 ≤ U ∧ (∀ t, |w t| ≤ U) ∧
    U + (eVariationOn w Set.univ).toReal ≤ B

/-- Uniform second-order errors and third- and fourth-order asymptotics, with one nonnegative
modulus antitone from two and tending to zero. -/
def IntervalCorrelations (SS : Finset ℕ → ℝ) : Prop :=
  ∀ M : ℝ, 1 ≤ M → ∃ C : ℝ, 0 ≤ C ∧
    (∀ H : ℝ, 1 ≤ H → ∀ a b : Fin 2 → ℝ, admissible M a b →
      |corr SS H a b + H * Real.log H * sigma (a 0) (b 0) (a 1) (b 1)| ≤ C * H) ∧
    ∃ η : ℝ → ℝ, (∀ H, 0 ≤ η H) ∧ AntitoneOn η (Ici 2) ∧
      Tendsto η atTop (nhds 0) ∧
      (∀ H : ℝ, 2 ≤ H → ∀ a b : Fin 3 → ℝ, admissible M a b →
        |corr SS H a b| ≤ η H * (H * Real.log H) ^ (3 / 2 : ℝ)) ∧
      (∀ H : ℝ, 2 ≤ H → ∀ a b : Fin 4 → ℝ, admissible M a b →
        |corr SS H a b - pairCorr SS H a b| ≤ η H * H ^ 2 * (Real.log H) ^ 2) ∧
      (∀ H : ℝ, 2 ≤ H → ∀ a b : Fin 4 → ℝ, admissible M a b →
        |corr SS H a b - H ^ 2 * (Real.log H) ^ 2 * W4 a b| ≤
          η H * H ^ 2 * (Real.log H) ^ 2)

/-- The centered Chebyshev increment on the physical interval. -/
def Delta (H a b x : ℝ) : ℝ :=
  Chebyshev.psi (x + b * H) - Chebyshev.psi (x + a * H) - (b - a) * H

/-- The variance ratio at scale H and sampling scale N. -/
def kappa (N H : ℝ) : ℝ := Real.log (N / H) / Real.log N

/-- The centered Chebyshev increment divided by the square root of H log N. -/
def Z (H a b x N : ℝ) : ℝ :=
  Delta H a b x /
    Real.sqrt (H * Real.log N)

/-- The normalized continuous mixed moment over the real dyadic sampling interval. -/
def weightedMoment {k : ℕ} (N H : ℝ) (a b : Fin k → ℝ) (w : ℝ → ℝ) : ℝ :=
  (∫ x in N..2 * N, w (x / N) * ∏ i, Z H (a i) (b i) x N) / N

/-- The two coefficients reducing a power by the quadratic relation, including exponent zero and
parameter zero. -/
def red : ℕ → ℝ → ℝ × ℝ
  | 0, _ => (0, 1)
  | r + 1, s => ((s - 2) * (red r s).1 + (red r s).2,
              (s - 1) * (red r s).1)

/-- The multiplicity of an index in an ordered tuple. -/
def mult {ι : Type*} [DecidableEq ι] {k : ℕ} (d : Fin k → ι) (e : ι) : ℕ :=
  (Finset.univ.filter (fun i => d i = e)).card

/-- The quadratic formal value of a tuple in an arbitrary index type. -/
def reducedFinite {ι : Type*} [DecidableEq ι] {k : ℕ}
    (C : Finset ι → ℝ) (s : ℝ) (d : Fin k → ι) : ℝ :=
  let D := Finset.univ.image d
  ∑ J ∈ D.powerset, centerFinite C J *
    (∏ e ∈ J, (red (mult d e) s).1) * (∏ e ∈ D \ J, (red (mult d e) s).2)

/-- The formal value of a shift tuple after reducing repeated indices and assigning centered
singular series to distinct products. -/
def reducedTuple {k : ℕ} (SS : Finset ℕ → ℝ) (s : ℝ) (d : Fin k → ℕ) : ℝ :=
  reducedFinite SS s d

/-- The formal interval moment summed over every ordered tuple of shifts, including repeated
indices. -/
def Phi {k : ℕ} (SS : Finset ℕ → ℝ) (H s : ℝ) (a b : Fin k → ℝ) : ℝ :=
  ∑ d ∈ Fintype.piFinset (fun i => points H (a i) (b i)), reducedTuple SS s d

/-- The sum of von Mangoldt minus one over the integer shifts in an interval. -/
def S (H a b : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ points H a b, (ArithmeticFunction.vonMangoldt (n + d) - 1)

/-- The weighted unnormalized discrete mixed moment over the dyadic sampling range. -/
def discreteRaw {k : ℕ} (N H : ℝ) (a b : Fin k → ℝ) (w : ℝ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, w ((n : ℝ) / N) * ∏ i, S H (a i) (b i) n

/-- The arithmetical value of a tuple after quadratic reduction at the specified logarithmic
parameter. -/
def reducedAt {k : ℕ} (s : ℝ) (n : ℕ) (d : Fin k → ℕ) : ℝ :=
  let D := Finset.univ.image d
  ∑ J ∈ D.powerset,
    (∏ e ∈ J, (red (mult d e) s).1) *
    (∏ e ∈ D \ J, (red (mult d e) s).2) *
    (∏ e ∈ J, (ArithmeticFunction.vonMangoldt (n + e) - 1))

/-- The formal moment of coefficient functions, summed over all tuples with their coefficient
products. -/
def formalMoment {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (C : Finset ι → ℝ) (s : ℝ) (f : Fin k → ι → ℝ) : ℝ :=
  ∑ d : Fin k → ι, (∏ i, f i (d i)) * reducedFinite C s d

/-- The formal distinct-index moment of coefficient functions, summed over ordered injective
tuples. -/
def formalDistinct {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (C : Finset ι → ℝ) (f : Fin k → ι → ℝ) : ℝ :=
  ∑ d : Fin k → ι with Function.Injective d,
    (∏ i, f i (d i)) * centerFinite C (Finset.univ.image d)

/-- Powers reduce to a linear expression under the quadratic relation. -/
theorem red_pow (s y : ℝ) (hy : y ^ 2 = (s - 2) * y + (s - 1)) (r : ℕ) :
    y ^ r = (red r s).1 * y + (red r s).2 := by
  induction r with
  | zero => simp [red]
  | succ r ih =>
    rw [pow_succ, ih]
    change ((red r s).1 * y + (red r s).2) * y =
      ((s - 2) * (red r s).1 + (red r s).2) * y + (s - 1) * (red r s).1
    linear_combination (red r s).1 * hy

/-- Both reduction coefficients are polynomial of degree at most one less than the exponent. -/
theorem reduction_polynomial (r : ℕ) :
    ∃ A B : Polynomial ℝ, A.natDegree ≤ r - 1 ∧ B.natDegree ≤ r - 1 ∧
      ∀ z : ℝ, (red r z).1 = A.eval z ∧ (red r z).2 = B.eval z := by
  induction r with
  | zero => exact ⟨0, 1, by simp, by simp, by simp [red]⟩
  | succ r ih =>
    rcases ih with ⟨A, B, hA, hB, heval⟩
    cases r with
    | zero => exact ⟨1, 0, by simp, by simp, by simp [red]⟩
    | succ n =>
      refine ⟨(Polynomial.X - Polynomial.C 2) * A + B,
        (Polynomial.X - Polynomial.C 1) * A, ?_, ?_, ?_⟩
      · exact (Polynomial.natDegree_add_le _ _).trans (max_le
          ((Polynomial.natDegree_mul_le).trans (by simp only [Polynomial.natDegree_X_sub_C]; omega))
          (by omega))
      · exact (Polynomial.natDegree_mul_le).trans (by
          simp only [Polynomial.natDegree_X_sub_C]; omega)
      · intro z
        simpa only [red, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using
          And.intro (congrArg (fun t => (z - 2) * t + (red (n + 1) z).2) (heval z).1 |>.trans
            (congrArg (fun t => (z - 2) * A.eval z + t) (heval z).2))
            (congrArg (fun t => (z - 1) * t) (heval z).1)

/-- The transported singular series of the empty shift set is one. -/
theorem concreteSS_empty : concreteSS ∅ = 1 := by
  simp [concreteSS,
    D5.S3.Analytic.PrimeProducts.FiniteOffsetSingularSeries.offsetSingularSeries,
    D5.S3.Analytic.PrimeProducts.FiniteOffsetSingularSeries.offsetLocalFactor,
    D5.S3.Analytic.PrimeProducts.FiniteLocalResidueBlockingCriterion.localResidueCount,
    D5.S3.Analytic.PrimeProducts.FiniteLocalResidueBlockingCriterion.localResidueSet]

/-- The transported singular series of any singleton shift set is one. -/
theorem concreteSS_singleton (d : ℕ) : concreteSS {d} = 1 := by
  unfold concreteSS
  simp only [Finset.image_singleton]
  unfold D5.S3.Analytic.PrimeProducts.FiniteOffsetSingularSeries.offsetSingularSeries
  have hfactor (p : Nat.Primes) :
      D5.S3.Analytic.PrimeProducts.FiniteOffsetSingularSeries.offsetLocalFactor
        {(d : ℤ)} p = 1 := by
    have hp : (1 : ℝ) < p.val := by exact_mod_cast p.property.one_lt
    have hn : 1 - 1 / (p.val : ℝ) ≠ 0 := by
      have : 1 / (p.val : ℝ) < 1 := (div_lt_one (by linarith)).mpr hp
      linarith
    simpa [D5.S3.Analytic.PrimeProducts.FiniteOffsetSingularSeries.offsetLocalFactor,
      D5.S3.Analytic.PrimeProducts.FiniteLocalResidueBlockingCriterion.localResidueCount,
      D5.S3.Analytic.PrimeProducts.FiniteLocalResidueBlockingCriterion.localResidueSet] using
      div_self hn
  simp only [hfactor, tprod_one]

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
