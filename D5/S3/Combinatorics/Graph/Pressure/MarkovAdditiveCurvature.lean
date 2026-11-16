/- GID: D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveCurvature
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Pressure/MarkovAdditiveCurvature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized finite irreducible Markov Poisson equations and additive pressure. -/
import D5.S3.Combinatorics.Graph.Pressure.WeightedWalks
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Normalized Markov Poisson equations and additive pressure -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Matrix Topology
open Matrix

namespace D5.S3.Combinatorics.Graph.Pressure.MarkovAdditive

universe u
variable {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]

/-- A strictly positive normalized stationary row, with source-state row convention. -/
structure Stationary (P : Matrix V V ℝ) where
  prob : V → ℝ
  positive : ∀ i, 0 < prob i
  total : ∑ i, prob i = 1
  invariant : prob ᵥ* P = prob

private theorem exists_stationary (P : Matrix V V ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible) :
    Nonempty (Stationary P) := by
  obtain ⟨a, z, ha, hz, he, _⟩ :=
    Matrix.perron_root_eq_positive_eigenvalue hI.transpose hI.transpose.nonneg
  have hZ : 0 < ∑ i, z i := Finset.sum_pos (fun i _ => hz i) Finset.univ_nonempty
  have hv : z ᵥ* P = a • z := by
    ext j
    have hj := congrFun he j
    simpa [Matrix.vecMul, Matrix.mulVec, Matrix.transpose_apply, dotProduct, mul_comm] using hj
  have hs : (∑ i, z i) = a * (∑ i, z i) := by
    calc
      (∑ i, z i) = ∑ j, (z ᵥ* P) j := by
        simp only [Matrix.vecMul, dotProduct]
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum, Matrix.sum_row_of_mem_rowStochastic hP, mul_one]
      _ = a * (∑ i, z i) := by rw [hv]; simp [Finset.mul_sum]
  have ha1 : a = 1 := by nlinarith
  have hv1 : z ᵥ* P = z := by simpa [ha1] using hv
  refine ⟨⟨fun i => z i / ∑ j, z j, fun i => div_pos (hz i) hZ, ?_, ?_⟩⟩
  · rw [← Finset.sum_div]
    exact div_self hZ.ne'
  · ext j
    have hj := congrFun hv1 j
    simpa [Matrix.vecMul, dotProduct, div_mul_eq_mul_div, ← Finset.sum_div] using
      congrArg (fun x : ℝ => x / ∑ i, z i) hj

/-- Stationarity is obtained from transpose Perron data rather than postulated. -/
def stationary (P : Matrix V V ℝ) (hP : P ∈ Matrix.rowStochastic ℝ V)
    (hI : P.IsIrreducible) : Stationary P :=
  Classical.choice (exists_stationary P hP hI)

private theorem harmonic_constant (P : Matrix V V ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible)
    (x : V → ℝ) (hx : P *ᵥ x = x) : ∃ c, x = fun _ => c := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ x Finset.univ_nonempty
  have hmax (j : V) : x j ≤ x i := hi j (Finset.mem_univ j)
  have step {a b : V} (hab : 0 < P a b) (ha : x a = x i) : x b = x i := by
    have hs : ∑ j, P a j * (x i - x j) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      rw [Matrix.sum_row_of_mem_rowStochastic hP, one_mul]
      have hh := congrFun hx a
      change (∑ j, P a j * x j) = x a at hh
      rw [hh, ha, sub_self]
    have hn (j : V) : 0 ≤ P a j * (x i - x j) :=
      mul_nonneg (hI.nonneg a j) (sub_nonneg.mpr (hmax j))
    have hb : P a b * (x i - x b) = 0 := by
      apply le_antisymm
      · calc
          P a b * (x i - x b) ≤ ∑ j, P a j * (x i - x j) :=
            Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ b)
          _ = 0 := hs
      · exact hn b
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hb).resolve_left hab.ne')).symm
  have along {a b : V} (p : @Quiver.Path V (Matrix.toQuiver P) a b) :
      x a = x i → x b = x i := by
    induction p with
    | nil => exact id
    | cons p e ih => exact fun ha => step e.down (ih ha)
  refine ⟨x i, funext fun j => ?_⟩
  obtain ⟨p, _⟩ := hI.connected i j
  exact along p rfl

namespace Stationary
variable {P : Matrix V V ℝ} (π : Stationary P)

private theorem average_const (c : ℝ) : π.prob ⬝ᵥ (fun _ => c) = c := by
  simp [dotProduct, ← Finset.sum_mul, π.total]

private theorem average_mulVec (x : V → ℝ) : π.prob ⬝ᵥ (P *ᵥ x) = π.prob ⬝ᵥ x := by
  rw [Matrix.dotProduct_mulVec, π.invariant]

/-- The normalized eigenproblem's square Jacobian on a vector and a scalar. -/
def normalizedBlock : ((V → ℝ) × ℝ) →ₗ[ℝ] ((V → ℝ) × ℝ) where
  toFun z := (P *ᵥ z.1 - z.1 - (fun _ => z.2), π.prob ⬝ᵥ z.1)
  map_add' z w := by
    ext i <;> simp [Matrix.mulVec_add, dotProduct_add] <;> ring
  map_smul' c z := by
    ext i <;> simp [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul] <;> ring

private theorem normalizedBlock_injective
    (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible) :
    Function.Injective π.normalizedBlock := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro z hz
  have hv : P *ᵥ z.1 - z.1 - (fun _ => z.2) = 0 := congrArg Prod.fst hz
  have hc : π.prob ⬝ᵥ z.1 = 0 := congrArg Prod.snd hz
  have he := congrArg (fun x => π.prob ⬝ᵥ x) hv
  simp only [dotProduct_sub, π.average_mulVec, π.average_const, dotProduct_zero,
    sub_self, zero_sub, neg_eq_zero] at he
  have hh : P *ᵥ z.1 = z.1 := by
    apply sub_eq_zero.mp
    simpa only [he, ← Pi.zero_def, sub_zero] using hv
  obtain ⟨c, hx⟩ := harmonic_constant P hP hI z.1 hh
  have hcz : c = 0 := by simpa [hx, π.average_const] using hc
  exact Prod.ext (by rw [hx, hcz]; rfl) he

/-- A genuine continuous inverse, valid also for periodic nonreversible chains. -/
def normalizedEquiv (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible) :
    ((V → ℝ) × ℝ) ≃L[ℝ] ((V → ℝ) × ℝ) :=
  (LinearEquiv.ofInjectiveEndo π.normalizedBlock
    (π.normalizedBlock_injective hP hI)).toContinuousLinearEquiv

/-- Centered inverse of `I-P`, using the same block as the Perron eigenproblem. -/
def poisson (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible)
    (b : V → ℝ) : V → ℝ :=
  ((π.normalizedEquiv hP hI).symm (-b, 0)).1

theorem poisson_spec (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible)
    (b : V → ℝ) (hb : π.prob ⬝ᵥ b = 0) :
    π.poisson hP hI b - P *ᵥ π.poisson hP hI b = b ∧
      π.prob ⬝ᵥ π.poisson hP hI b = 0 := by
  let z := (π.normalizedEquiv hP hI).symm (-b, 0)
  have hz : π.normalizedBlock z = (-b, 0) :=
    (π.normalizedEquiv hP hI).apply_symm_apply _
  have hf : P *ᵥ z.1 - z.1 - (fun _ => z.2) = -b := congrArg Prod.fst hz
  have hs : π.prob ⬝ᵥ z.1 = 0 := congrArg Prod.snd hz
  have hc := congrArg (fun x => π.prob ⬝ᵥ x) hf
  simp only [dotProduct_sub, π.average_mulVec, π.average_const, sub_self,
    zero_sub, dotProduct_neg, hb, neg_zero, neg_eq_zero] at hc
  refine ⟨?_, hs⟩
  change z.1 - P *ᵥ z.1 = b
  have hh : P *ᵥ z.1 - z.1 = -b := by simpa only [hc, ← Pi.zero_def, sub_zero] using hf
  have := congrArg Neg.neg hh
  simpa only [neg_sub, neg_neg] using this

theorem poisson_unique (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible)
    (b x : V → ℝ) (hx : x - P *ᵥ x = b) (hc : π.prob ⬝ᵥ x = 0) :
    x = π.poisson hP hI b := by
  have hx' : π.normalizedBlock (x, 0) = (-b, 0) := by
    apply Prod.ext
    · change P *ᵥ x - x - (fun _ => (0 : ℝ)) = -b
      have := congrArg Neg.neg hx
      simpa only [← Pi.zero_def, sub_zero, neg_sub] using this
    · exact hc
  have hz := (π.normalizedEquiv hP hI).symm_apply_apply (x, 0)
  change (π.normalizedEquiv hP hI).symm (π.normalizedBlock (x, 0)) = (x, 0) at hz
  rw [hx'] at hz
  exact (congrArg Prod.fst hz).symm

end Stationary

/-- Exponential tilt of the given transition matrix; unsupported rewards disappear. -/
def tilt (P : Matrix V V ℝ) (g : V → V → ℝ) (t : ℝ) : Matrix V V ℝ :=
  fun i j => P i j * Real.exp (t * g i j)

/-- The original positive support, including every permitted loop and return. -/
def supportNetwork (P : Matrix V V ℝ) (hI : P.IsIrreducible) : Network V where
  edge i j := 0 < P i j
  connected := by
    letI : Quiver V := Matrix.toQuiver P
    exact hI.connected.isStronglyConnected
  hasEdge := Matrix.Irreducible.exists_pos_entry hI

private theorem tilt_eq_weights (P : Matrix V V ℝ) (hI : P.IsIrreducible)
    (g : V → V → ℝ) (t : ℝ) :
    (supportNetwork P hI).W (fun i j => -Real.log (P i j) - t * g i j) 1 = tilt P g t := by
  ext i j
  by_cases hp : 0 < P i j
  · simp [Network.W, supportNetwork, hp, tilt, Real.exp_add, Real.exp_log hp, mul_comm]
  · have hz : P i j = 0 := le_antisymm (le_of_not_gt hp) (hI.nonneg i j)
    simp [Network.W, supportNetwork, hp, hz, tilt]

/-- Real value of the actual complex spectral radius, whose positivity is proved below. -/
def eigenvalue (P : Matrix V V ℝ) (g : V → V → ℝ) (t : ℝ) : ℝ :=
  (spectralRadius ℂ ((tilt P g t).map (algebraMap ℝ ℂ))).toReal

/-- Pressure uses the actual complex spectrum of the exponential tilt. -/
def pressure (P : Matrix V V ℝ) (g : V → V → ℝ) (t : ℝ) : ℝ :=
  Real.log (eigenvalue P g t)

private theorem positive_eigenpair_identifies_radius
    (P : Matrix V V ℝ) (hI : P.IsIrreducible) (g : V → V → ℝ) (t a : ℝ)
    (r : V → ℝ) (ha : 0 < a) (hr : ∀ i, 0 < r i)
    (he : tilt P g t *ᵥ r = a • r) :
    spectralRadius ℂ ((tilt P g t).map (algebraMap ℝ ℂ)) = ENNReal.ofReal a ∧
      eigenvalue P g t = a := by
  let c : V → V → ℝ := fun i j => -Real.log (P i j) - t * g i j
  let G := supportNetwork P hI
  have hw : G.W c 1 = tilt P g t := tilt_eq_weights P hI g t
  have hn (i j : V) : 0 ≤ tilt P g t i j :=
    mul_nonneg (hI.nonneg i j) (Real.exp_pos _).le
  have ha' : Matrix.CollatzWielandt.perronRoot (tilt P g t) = a :=
    le_antisymm
      (Matrix.CollatzWielandt.eigenvalue_is_ub_of_positive_eigenvector hn ha hr he)
      (Matrix.CollatzWielandt.eigenvalue_le_perron_root_of_positive_eigenvector hn ha hr he)
  have hb : Matrix.CollatzWielandt.perronRoot (tilt P g t) = (G.perron c 1).root := by
    apply le_antisymm
    · apply Matrix.CollatzWielandt.eigenvalue_is_ub_of_positive_eigenvector hn
        (G.perron c 1).root_pos (G.perron c 1).right_pos
      simpa [hw] using (G.perron c 1).eigen
    · apply Matrix.CollatzWielandt.eigenvalue_le_perron_root_of_positive_eigenvector hn
        (G.perron c 1).root_pos (G.perron c 1).right_pos
      simpa [hw] using (G.perron c 1).eigen
  have hroot : (G.perron c 1).root = a := hb.symm.trans ha'
  have hs := (G.perron c 1).radius
  rw [hw, hroot] at hs
  refine ⟨hs, ?_⟩
  change (spectralRadius ℂ ((tilt P g t).map (algebraMap ℝ ℂ))).toReal = a
  rw [hs, ENNReal.toReal_ofReal ha.le]

namespace Stationary
variable {P : Matrix V V ℝ} (π : Stationary P)

/-- Stationary mean per transition, with both edge endpoints retained. -/
def meanReward (g : V → V → ℝ) : ℝ := ∑ i, ∑ j, π.prob i * P i j * g i j

/-- Centered one-step conditional drift. -/
def drift (g : V → V → ℝ) (i : V) : ℝ :=
  ∑ j, P i j * (g i j - π.meanReward g)

private theorem drift_centered (hP : P ∈ Matrix.rowStochastic ℝ V) (g : V → V → ℝ) :
    π.prob ⬝ᵥ π.drift g = 0 := by
  have hd (i : V) : π.drift g i = (∑ j, P i j * g i j) - π.meanReward g := by
    simp [drift, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      Matrix.sum_row_of_mem_rowStochastic hP]
  change (∑ i, π.prob i * π.drift g i) = 0
  simp_rw [hd, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, π.total, one_mul]
  simp only [Finset.mul_sum, ← mul_assoc, meanReward, sub_self]

/-- First and second centered correctors use the identical normalized inverse. -/
def corrector (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible)
    (g : V → V → ℝ) : V → ℝ := π.poisson hP hI (π.drift g)

def secondCorrector (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible)
    (g : V → V → ℝ) : V → ℝ := π.poisson hP hI (π.corrector hP hI g)

private theorem corrector_spec (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible)
    (g : V → V → ℝ) :
    π.corrector hP hI g - P *ᵥ π.corrector hP hI g = π.drift g ∧
      π.prob ⬝ᵥ π.corrector hP hI g = 0 :=
  π.poisson_spec hP hI (π.drift g) (π.drift_centered hP g)

private theorem secondCorrector_spec (hP : P ∈ Matrix.rowStochastic ℝ V)
    (hI : P.IsIrreducible) (g : V → V → ℝ) :
    π.secondCorrector hP hI g - P *ᵥ π.secondCorrector hP hI g = π.corrector hP hI g ∧
      π.prob ⬝ᵥ π.secondCorrector hP hI g = 0 :=
  π.poisson_spec hP hI _ (π.corrector_spec hP hI g).2

/-- Supported additive increment after Poisson correction. -/
def score (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible)
    (g : V → V → ℝ) (i j : V) : ℝ :=
  g i j - π.meanReward g + π.corrector hP hI g j - π.corrector hP hI g i

/-- Stationary square of the corrected increment. -/
def varianceRate (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible)
    (g : V → V → ℝ) : ℝ :=
  ∑ i, ∑ j, π.prob i * P i j * (π.score hP hI g i j) ^ 2

private theorem score_centered (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible)
    (g : V → V → ℝ) (i : V) : ∑ j, P i j * π.score hP hI g i j = 0 := by
  have hh := congrFun (π.corrector_spec hP hI g).1 i
  change π.corrector hP hI g i - ∑ j, P i j * π.corrector hP hI g j = π.drift g i at hh
  simp only [score, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hP, one_mul]
  simp only [drift, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    Matrix.sum_row_of_mem_rowStochastic hP, one_mul] at hh
  linarith

theorem varianceRate_eq_zero_iff (hP : P ∈ Matrix.rowStochastic ℝ V)
    (hI : P.IsIrreducible) (g : V → V → ℝ) :
    π.varianceRate hP hI g = 0 ↔
      ∀ i j, 0 < P i j → g i j = π.meanReward g +
        π.corrector hP hI g i - π.corrector hP hI g j := by
  have hn (i j : V) : 0 ≤ π.prob i * P i j * (π.score hP hI g i j)^2 :=
    mul_nonneg (mul_nonneg (π.positive i).le (hI.nonneg i j)) (sq_nonneg _)
  constructor
  · intro hv i j hij
    have ht : π.prob i * P i j * (π.score hP hI g i j)^2 = 0 := by
      apply le_antisymm
      · calc
          _ ≤ ∑ k, π.prob i * P i k * (π.score hP hI g i k)^2 :=
            Finset.single_le_sum (fun k _ => hn i k) (Finset.mem_univ j)
          _ ≤ π.varianceRate hP hI g :=
            Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => hn k l))
              (Finset.mem_univ i)
          _ = 0 := hv
      · exact hn i j
    have hz : π.score hP hI g i j = 0 :=
      (sq_eq_zero_iff).mp ((mul_eq_zero.mp ht).resolve_left (mul_pos (π.positive i) hij).ne')
    dsimp [score] at hz
    linarith
  · intro hc
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    by_cases hij : 0 < P i j
    · have hs : π.score hP hI g i j = 0 := by dsimp [score]; rw [hc i j hij]; ring
      simp [hs]
    · have hz : P i j = 0 := le_antisymm (le_of_not_gt hij) (hI.nonneg i j)
      simp [hz]

/-- The normalized eigenproblem, including its scalar normalization equation. -/
def eigenproblem (g : V → V → ℝ) (z : ℝ × ((V → ℝ) × ℝ)) : (V → ℝ) × ℝ :=
  (tilt P g z.1 *ᵥ z.2.1 - z.2.2 • z.2.1, π.prob ⬝ᵥ z.2.1 - 1)

private theorem eigenproblem_contDiff (g : V → V → ℝ) :
    ContDiff ℝ 2 (π.eigenproblem g) := by
  unfold eigenproblem tilt Matrix.mulVec dotProduct
  fun_prop

/-- Total derivative at the stochastic base point, with parameter direction retained. -/
def eigenproblemDerivative (g : V → V → ℝ) :
    (ℝ × ((V → ℝ) × ℝ)) →ₗ[ℝ] ((V → ℝ) × ℝ) where
  toFun z := (fun i => z.1 * (∑ j, P i j * g i j) +
    (P *ᵥ z.2.1) i - z.2.1 i - z.2.2, π.prob ⬝ᵥ z.2.1)
  map_add' z w := by
    apply Prod.ext
    · ext i; simp [Matrix.mulVec_add]; ring
    · simp [dotProduct_add]
  map_smul' c z := by
    apply Prod.ext
    · ext i; simp [Matrix.mulVec_smul, smul_eq_mul]; ring
    · simp [dotProduct_smul, smul_eq_mul]

private theorem eigenproblem_hasFDerivAt (g : V → V → ℝ) :
    HasFDerivAt (π.eigenproblem g) (π.eigenproblemDerivative g).toContinuousLinearMap
      (0, ((fun _ => 1), 1)) := by
  let A := ℝ × ((V → ℝ) × ℝ)
  let z₀ : A := (0, ((fun _ => 1), 1))
  let ds : A →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ((V → ℝ) × ℝ)
  let dr : A →L[ℝ] (V → ℝ) :=
    (ContinuousLinearMap.fst ℝ (V → ℝ) ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ ((V → ℝ) × ℝ))
  let dc : A →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (V → ℝ) ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ ((V → ℝ) × ℝ))
  have hr (j : V) : HasFDerivAt (fun z : A => z.2.1 j)
      ((ContinuousLinearMap.proj j).comp dr) z₀ :=
    ((ContinuousLinearMap.proj j).comp dr).hasFDerivAt
  have hc : HasFDerivAt (fun z : A => z.2.2) dc z₀ := dc.hasFDerivAt
  have ht (i j : V) : HasFDerivAt (fun z : A => P i j * Real.exp (z.1 * g i j))
      ((P i j * g i j) • ds) z₀ := by
    convert (((ds.hasFDerivAt.mul_const (g i j)).exp).const_mul (P i j)) using 1
    · funext z; rfl
    · apply ContinuousLinearMap.ext; intro z
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      have hs : ds z₀ = 0 := rfl
      rw [hs]
      simp [mul_assoc]
  have hf (i : V) :=
    (HasFDerivAt.sum (u := Finset.univ) (fun j _ => (ht i j).mul (hr j))).sub
      (hc.mul (hr i))
  have hn : HasFDerivAt (fun z : A => π.prob ⬝ᵥ z.2.1 - 1)
      (((dotProductBilin ℝ ℝ π.prob).toContinuousLinearMap).comp dr) z₀ := by
    convert ((((dotProductBilin ℝ ℝ π.prob).toContinuousLinearMap).hasFDerivAt.comp
      z₀ dr.hasFDerivAt).sub_const 1) using 1
    funext z; rfl
  have hv := (hasFDerivAt_pi.mpr hf).prodMk hn
  convert hv using 1
  · funext z
    apply Prod.ext
    · ext i
      simp [eigenproblem, tilt, Matrix.mulVec, dotProduct, Finset.sum_apply]
    · rfl
  · apply ContinuousLinearMap.ext
    intro z
    apply Prod.ext
    · ext i
      simp [eigenproblemDerivative, Matrix.mulVec, dotProduct, z₀, ds, dr, dc,
        Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm,
        mul_assoc]
      <;> ring
    · rfl

private theorem eigenproblem_partial (g : V → V → ℝ) :
    fderiv ℝ (π.eigenproblem g) (0, ((fun _ => 1), 1)) ∘L
      ContinuousLinearMap.inr ℝ ℝ ((V → ℝ) × ℝ) = π.normalizedBlock.toContinuousLinearMap := by
  rw [(π.eigenproblem_hasFDerivAt g).fderiv]
  ext z i <;> simp [eigenproblemDerivative, normalizedBlock]

private theorem eigenproblem_partial_invertible
    (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible) (g : V → V → ℝ) :
    (fderiv ℝ (π.eigenproblem g) (0, ((fun _ => 1), 1)) ∘L
      ContinuousLinearMap.inr ℝ ℝ ((V → ℝ) × ℝ)).IsInvertible := by
  rw [π.eigenproblem_partial]
  exact ⟨π.normalizedEquiv hP hI, rfl⟩

/-- A branch obtained from the actual normalized implicit equation. -/
def eigenbranch (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible)
    (g : V → V → ℝ) : ℝ → ((V → ℝ) × ℝ) :=
  (π.eigenproblem_contDiff g).contDiffAt.implicitFunction (by norm_num)
    (π.eigenproblem_partial_invertible hP hI g)

private theorem eigenbranch_base
    (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible) (g : V → V → ℝ) :
    π.eigenbranch hP hI g 0 = ((fun _ => 1), 1) :=
  (π.eigenproblem_contDiff g).contDiffAt.implicitFunction_apply_self (by norm_num)
    (π.eigenproblem_partial_invertible hP hI g)

private theorem eigenbranch_contDiffAt
    (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible) (g : V → V → ℝ) :
    ContDiffAt ℝ 2 (π.eigenbranch hP hI g) 0 :=
  (π.eigenproblem_contDiff g).contDiffAt.contDiffAt_implicitFunction (by norm_num)
    (π.eigenproblem_partial_invertible hP hI g)

open Filter in
private theorem eigenbranch_eventually
    (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible) (g : V → V → ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      tilt P g t *ᵥ (π.eigenbranch hP hI g t).1 =
        (π.eigenbranch hP hI g t).2 • (π.eigenbranch hP hI g t).1 ∧
      π.prob ⬝ᵥ (π.eigenbranch hP hI g t).1 = 1 := by
  have hh := (π.eigenproblem_contDiff g).contDiffAt.eventually_apply_implicitFunction
    (u := (0, ((fun _ => 1), 1))) (by norm_num)
    (π.eigenproblem_partial_invertible hP hI g)
  filter_upwards [hh] with t ht
  have hb : π.eigenproblem g (0, ((fun _ => 1), 1)) = 0 := by
    have ht0 : tilt P g 0 = P := by ext i j; simp [tilt]
    simp [eigenproblem, ht0, ← Pi.one_def, π.average_const,
      Matrix.one_vecMul_of_mem_rowStochastic hP, dotProduct, π.total]
  rw [hb] at ht
  exact ⟨sub_eq_zero.mp (congrArg Prod.fst ht),
    sub_eq_zero.mp (congrArg Prod.snd ht)⟩

open Filter in
private theorem eigenbranch_positive_eventually
    (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible) (g : V → V → ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (π.eigenbranch hP hI g t).2 ∧
      ∀ i, 0 < (π.eigenbranch hP hI g t).1 i := by
  have hc := (π.eigenbranch_contDiffAt hP hI g).continuousAt
  have hb := π.eigenbranch_base hP hI g
  have hs : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (π.eigenbranch hP hI g t).2 :=
    (hc.snd.eventually (lt_mem_nhds (by simp [hb] : (0 : ℝ) <
      (π.eigenbranch hP hI g 0).2)))
  have hv : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, 0 < (π.eigenbranch hP hI g t).1 i := by
    rw [Filter.eventually_all]
    intro i
    exact ((continuousAt_apply i _).comp hc.fst).eventually (lt_mem_nhds (by simp [hb]))
  exact hs.and hv

open Filter in
private theorem eigenbranch_radius_eventually
    (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible) (g : V → V → ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), eigenvalue P g t = (π.eigenbranch hP hI g t).2 := by
  filter_upwards [π.eigenbranch_eventually hP hI g,
    π.eigenbranch_positive_eventually hP hI g] with t he hp
  exact (positive_eigenpair_identifies_radius P hI g t _ _ hp.1 hp.2 he.1).2

private theorem eigenbranch_hasDerivAt
    (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible) (g : V → V → ℝ) :
    HasDerivAt (π.eigenbranch hP hI g)
      (π.corrector hP hI g, π.meanReward g) 0 := by
  let ψ := π.eigenbranch hP hI g
  have hψ : HasDerivAt ψ (deriv ψ 0) 0 :=
    ((π.eigenbranch_contDiffAt hP hI g).differentiableAt (by norm_num)).hasDerivAt
  have hF := (π.eigenproblem_hasFDerivAt g).comp_hasDerivAt 0
    ((hasDerivAt_id (0 : ℝ)).prodMk hψ)
  have hb : π.eigenproblem g (0, ((fun _ => 1), 1)) = 0 := by
    have ht0 : tilt P g 0 = P := by ext i j; simp [tilt]
    simp [eigenproblem, ht0, ← Pi.one_def, Matrix.one_vecMul_of_mem_rowStochastic hP,
      dotProduct, π.total]
  have heq : (fun t => π.eigenproblem g (t, ψ t)) =ᶠ[nhds (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [π.eigenbranch_eventually hP hI g] with t ht
    apply Prod.ext
    · exact sub_eq_zero.mpr ht.1
    · exact sub_eq_zero.mpr ht.2
  have hz : (π.eigenproblemDerivative g) (1, deriv ψ 0) = 0 := by
    exact (hF.congr_of_eventuallyEq heq).unique (hasDerivAt_const (0 : ℝ) 0)
  have hd : π.normalizedBlock (deriv ψ 0) =
      (- (fun i => ∑ j, P i j * g i j), 0) := by
    apply Prod.ext
    · ext i
      have hi := congrFun (congrArg Prod.fst hz) i
      simp only [eigenproblemDerivative, LinearMap.coe_mk, AddHom.coe_mk, one_mul,
        Pi.zero_apply] at hi
      change (P *ᵥ (deriv ψ 0).1) i - (deriv ψ 0).1 i - (deriv ψ 0).2 =
        -(∑ j, P i j * g i j)
      linarith
    · exact congrArg Prod.snd hz
  have hh : π.normalizedBlock (π.corrector hP hI g, π.meanReward g) =
      (-(fun i => ∑ j, P i j * g i j), 0) := by
    apply Prod.ext
    · ext i
      have hi := congrFun (π.corrector_spec hP hI g).1 i
      simp only [drift, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
        Matrix.sum_row_of_mem_rowStochastic hP, one_mul] at hi
      change (P *ᵥ π.corrector hP hI g) i - π.corrector hP hI g i - π.meanReward g =
        -(∑ j, P i j * g i j)
      change π.corrector hP hI g i - (P *ᵥ π.corrector hP hI g) i = _ at hi
      linarith
    · exact (π.corrector_spec hP hI g).2
  have hval := π.normalizedBlock_injective hP hI (hd.trans hh.symm)
  rwa [← hval]

include π in
theorem pressure_contDiffAt_zero
    (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible) (g : V → V → ℝ) :
    ContDiffAt ℝ 2 (pressure P g) 0 := by
  have hc := (π.eigenbranch_contDiffAt hP hI g).snd
  have hn : (π.eigenbranch hP hI g 0).2 ≠ 0 := by rw [π.eigenbranch_base]; norm_num
  apply (hc.log hn).congr_of_eventuallyEq
  exact (π.eigenbranch_radius_eventually hP hI g).mono fun t ht => congrArg Real.log ht

theorem pressure_hasDerivAt_zero
    (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible) (g : V → V → ℝ) :
    HasDerivAt (pressure P g) (π.meanReward g) 0 := by
  have hψ := π.eigenbranch_hasDerivAt hP hI g
  have hc := (ContinuousLinearMap.snd ℝ (V → ℝ) ℝ).hasFDerivAt.comp_hasDerivAt 0 hψ
  have hb := π.eigenbranch_base hP hI g
  have hl := hc.log (by simp [hb])
  simp only [ContinuousLinearMap.snd_apply, hb, div_one] at hl
  exact hl.congr_of_eventuallyEq
    ((π.eigenbranch_radius_eventually hP hI g).mono fun t ht => congrArg Real.log ht.symm)

end Stationary
end D5.S3.Combinatorics.Graph.Pressure.MarkovAdditive
