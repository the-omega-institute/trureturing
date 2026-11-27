/- GID: D5/S3/Quantum/Semigroups/WuCubicOccupationTaylor
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicOccupationTaylor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gibbs-relative signed Taylor lower bound for Wu's normalized cubic occupation deficit. -/

import D5.S3.Divergence.GrandmotherTheorem
import D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap
import D5.S3.Quantum.Semigroups.WuCubicEntropyRemainders
import D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
import D5.S3.Quantum.Semigroups.WuCubicSignedTransfer
import Batteries.Tactic.OpenPrivate
import OmegaBuild.Commands

/-! The Gibbs-relative occupation estimate in the all-temperature Wu cubic
proof. The normalized source is evaluated in the literal occupation basis.
Both the energy and the Taylor bound carry a factor `d ^ 2`. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Matrix

namespace D5.S3.Quantum.Semigroups.WuCubicOccupationTaylor

open D5.S3.Divergence.ClassicalDPI (klDivergence)
open D5.S3.Divergence.GrandmotherTheorem (kl_divergence_nonneg)
open TwistedTwoModeOUComparison (modeJump)
open WuRepeatedMiddleCubic (Frame Occupation alpha weight)
open WuCubicDirectedOccupationCap (lowering)
open WuCubicEntropyRemainders (mass_mul_klDivergence_eq mass_normalized_cubic_entropy_le)
open WuCubicOperatorBridge (G GInv generator)
open WuCubicSignedTransfer (sourceDeficitAt)
open private occupationBasis basis_zero basis_one basis_two basis_three lowering_zero lowering_one
  from D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap
open private gibbsOccupation gibbsLow gibbsHigh gibbsLogColumn gamma energyKernel
  from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private spectralEntropy weighted_spectral_energy from
  D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
open private levelsAt totalAt alpha_bounds from D5.S3.Quantum.Semigroups.WuCubicSignedTransfer

private abbrev Mat := Matrix (Fin 4) (Fin 4) ℂ

/-- The identity spectral frame, with rows indexed by the two occupations.
This is the identity-unitary specialization of the angular physical frame. -/
def occupationFrame : Frame := (1 : Mat).submatrix occupationBasis id

private theorem occupationFrame_adjoint :
    occupationFrameᴴ = (1 : Mat).submatrix id occupationBasis := by
  rw [occupationFrame, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]

private theorem occupationFrame_columns : occupationFrameᴴ * occupationFrame = 1 := by
  rw [occupationFrame_adjoint, occupationFrame, Matrix.submatrix_mul_equiv, Matrix.one_mul]
  rfl

private theorem occupationFrame_rows : occupationFrame * occupationFrameᴴ = 1 := by
  rw [occupationFrame_adjoint, occupationFrame,
    ← Matrix.submatrix_mul (1 : Mat) 1 occupationBasis id occupationBasis Function.bijective_id,
    Matrix.one_mul]
  exact Matrix.submatrix_one_equiv occupationBasis

private theorem occupationFrame_jump (k : Fin 2) :
    occupationFrameᴴ * modeJump k * occupationFrame = lowering k := by
  have hjump : (lowering k).submatrix occupationBasis occupationBasis = modeJump k := by
    ext i j
    simp [lowering, Matrix.reindex_apply]
  rw [occupationFrame_adjoint, occupationFrame, ← hjump,
    Matrix.submatrix_mul_equiv _ _ id occupationBasis occupationBasis,
    Matrix.submatrix_mul_equiv _ _ id occupationBasis id, Matrix.one_mul, Matrix.mul_one]
  rfl

private theorem occupation_weight (i j : Fin 4) :
    weight occupationFrame i j =
      if (i = 0 ∧ (j = 1 ∨ j = 2)) ∨ ((i = 1 ∨ i = 2) ∧ j = 3) then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [weight, occupationFrame_jump, Fin.sum_univ_two, lowering_zero, lowering_one,
      Complex.normSq_neg, Complex.normSq_one, Complex.normSq_zero]

/-- The four directed occupation edges, from the lower occupation to the higher one. -/
def occupationEdgeSum (f : Fin 4 → Fin 4 → ℝ) : ℝ :=
  f 0 1 + f 0 2 + f 1 3 + f 2 3

/-- The equilibrium levels with largest level one. -/
def gibbsLevels (r : ℝ) : Fin 4 → ℝ := ![(r ^ 2)⁻¹, r⁻¹, r⁻¹, 1]

/-- The total mass of the cubed levels. -/
def cubicMass (x : Fin 4 → ℝ) : ℝ := ∑ i, x i ^ 3

private theorem cubicMass_pos {x : Fin 4 → ℝ} (hx : ∀ i, 0 < x i) : 0 < cubicMass x :=
  Finset.sum_pos (fun i _ => pow_pos (hx i) 3) Finset.univ_nonempty

private theorem gibbsLevels_pos {r : ℝ} (hr : 1 ≤ r) (i : Fin 4) : 0 < gibbsLevels r i := by
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  fin_cases i
  · change 0 < (r ^ 2)⁻¹
    positivity
  · change 0 < r⁻¹
    positivity
  · change 0 < r⁻¹
    positivity
  · change 0 < (1 : ℝ)
    exact zero_lt_one

/-- The literal two-mode Gibbs probabilities in the occupation order. -/
def occupationGibbsProb (r : ℝ) (i : Fin 4) : ℝ :=
  gibbsOccupation r (occupationBasis.symm i).1 * gibbsOccupation r (occupationBasis.symm i).2

/-- The product Gibbs probabilities are the normalized cubes of the Gibbs levels. -/
theorem occupationGibbsProb_eq {r : ℝ} (hr : 1 ≤ r) (i : Fin 4) :
    occupationGibbsProb r i = gibbsLevels r i ^ 3 / cubicMass (gibbsLevels r) := by
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have hden : 0 < 1 + r ^ 3 := by positivity
  have hmass : cubicMass (gibbsLevels r) = (1 + r ^ 3) ^ 2 / r ^ 6 := by
    norm_num [cubicMass, gibbsLevels, Fin.sum_univ_four]
    field_simp [hrpos.ne']
    ring
  rw [hmass]
  fin_cases i <;>
    norm_num [occupationGibbsProb, basis_zero, basis_one, basis_two, basis_three,
      gibbsLevels, gibbsOccupation, gibbsLow, gibbsHigh] <;>
    field_simp [hrpos.ne', hden.ne']

private theorem occupationGibbsProb_fun_eq {r : ℝ} (hr : 1 ≤ r) :
    occupationGibbsProb r = fun i => gibbsLevels r i ^ 3 / cubicMass (gibbsLevels r) :=
  funext (occupationGibbsProb_eq hr)

private theorem gibbs_log_column_occupation (r : ℝ) (i : Fin 4) :
    gibbsLogColumn r occupationFrame i = Real.log (occupationGibbsProb r i) := by
  have hentry (o : Occupation) :
      occupationFrame o i = if o = occupationBasis.symm i then 1 else 0 := by
    simp only [occupationFrame, Matrix.submatrix_apply, id_eq, Matrix.one_apply,
      ← occupationBasis.eq_symm_apply]
  simp only [gibbsLogColumn, hentry, apply_ite, Complex.normSq_one, Complex.normSq_zero,
    ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq', occupationGibbsProb]

/-- The occupation entropy is the mass times the KL divergence to the literal Gibbs distribution. -/
def occupationEntropy (r : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  cubicMass x *
    klDivergence (fun i => x i ^ 3 / cubicMass x) (occupationGibbsProb r)

private theorem spectral_entropy_eq_occupationEntropy {r : ℝ} (hr : 1 ≤ r)
    (x : Fin 4 → ℝ) (hx : ∀ i, 0 < x i) :
    spectralEntropy r occupationFrame x = occupationEntropy r x := by
  have hT := cubicMass_pos hx
  have hq (i : Fin 4) : 0 < occupationGibbsProb r i := by
    rw [occupationGibbsProb_eq hr]
    exact div_pos (pow_pos (gibbsLevels_pos hr i) 3) (cubicMass_pos (gibbsLevels_pos hr))
  have hterm (i : Fin 4) :
      cubicMass x * (x i ^ 3 / cubicMass x *
        Real.log ((x i ^ 3 / cubicMass x) / occupationGibbsProb r i)) =
      x i ^ 3 * Real.log (x i ^ 3) - x i ^ 3 * Real.log (cubicMass x) -
        gibbsLogColumn r occupationFrame i * x i ^ 3 := by
    have hxi := (pow_pos (hx i) 3).ne'
    rw [Real.log_div (div_ne_zero hxi hT.ne') (hq i).ne', Real.log_div hxi hT.ne',
      ← mul_assoc, mul_div_cancel₀ _ hT.ne', gibbs_log_column_occupation]
    ring
  rw [occupationEntropy, klDivergence, Finset.mul_sum]
  simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rfl

/-- The exact Gibbs-relative entropy, including the subtracted mass remainder. -/
theorem occupation_entropy_eq_remainders {r : ℝ} (hr : 1 ≤ r)
    (x : Fin 4 → ℝ) (hx : ∀ i, 0 < x i) :
    let g := gibbsLevels r
    let T := cubicMass x
    let Tg := cubicMass g
    occupationEntropy r x =
      (∑ i, (3 * x i ^ 3 * Real.log (x i / g i) - (x i ^ 3 - g i ^ 3))) -
        (T * Real.log (T / Tg) - (T - Tg)) := by
  dsimp only
  simp only [occupationEntropy, occupationGibbsProb_fun_eq hr]
  rw [show
    cubicMass x *
      klDivergence (fun i => x i ^ 3 / cubicMass x)
        (fun i => gibbsLevels r i ^ 3 / cubicMass (gibbsLevels r)) =
      (∑ i, (x i ^ 3 * Real.log (x i ^ 3 / gibbsLevels r i ^ 3) - x i ^ 3 +
        gibbsLevels r i ^ 3)) -
          (cubicMass x * Real.log (cubicMass x / cubicMass (gibbsLevels r)) -
            cubicMass x + cubicMass (gibbsLevels r)) from
    mass_mul_klDivergence_eq (fun i => x i ^ 3) (fun i => gibbsLevels r i ^ 3)
      (fun i => pow_pos (hx i) 3) (fun i => pow_pos (gibbsLevels_pos hr i) 3)]
  simp_rw [← div_pow, Real.log_pow]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · ring

private theorem occupation_entropy_nonneg {r : ℝ} (hr : 1 ≤ r)
    (x : Fin 4 → ℝ) (hx : ∀ i, 0 < x i) : 0 ≤ occupationEntropy r x := by
  rw [occupationEntropy]
  have hT := cubicMass_pos hx
  have hTg := cubicMass_pos (gibbsLevels_pos hr)
  apply mul_nonneg hT.le
  rw [occupationGibbsProb_fun_eq hr]
  apply kl_divergence_nonneg
  · refine ⟨fun i => div_nonneg (pow_pos (hx i) 3).le hT.le, ?_⟩
    rw [← Finset.sum_div]
    exact div_self hT.ne'
  · refine ⟨fun i => div_nonneg (pow_pos (gibbsLevels_pos hr i) 3).le hTg.le, ?_⟩
    rw [← Finset.sum_div]
    exact div_self hTg.ne'
  · intro i hi
    exact False.elim ((div_pos (pow_pos (gibbsLevels_pos hr i) 3) hTg).ne' hi)

/-- The Wu coefficient lies in the interval used by the occupation bound,
including the tracial temperature. -/
theorem alpha_bounds_of_one_le {r : ℝ} (hr : 1 ≤ r) : 0 ≤ alpha r ∧ alpha r ≤ 1 / 2 := by
  rcases eq_or_lt_of_le hr with h | h
  · rw [← h]
    norm_num [alpha]
  · exact alpha_bounds h

/-- The coefficient of `d ^ 2` in the exact occupation energy at `g + d • h`. -/
def occupationEnergyFactor (r d : ℝ) (h : Fin 4 → ℝ) : ℝ :=
  gamma r * occupationEdgeSum (fun i j =>
    (r * h i - h j) ^ 2 * (2 * gibbsLevels r j + d * (r * h i + h j)))

private theorem occupation_spectral_energy_eq (r : ℝ) (x : Fin 4 → ℝ) :
    (∑ i, ∑ j, weight occupationFrame i j * energyKernel r (x i) (x j)) =
      occupationEdgeSum (fun i j => energyKernel r (x i) (x j)) := by
  norm_num [occupationEdgeSum, Fin.sum_univ_four, occupation_weight]

private theorem occupation_edge_energy_factor {r : ℝ} (hr : 1 ≤ r) (d : ℝ) (h : Fin 4 → ℝ) :
    let x := fun i => gibbsLevels r i + d * h i
    occupationEdgeSum (fun i j => energyKernel r (x i) (x j)) =
      d ^ 2 * occupationEnergyFactor r d h := by
  intro x
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have hg01 : r * gibbsLevels r 0 = gibbsLevels r 1 := by
    change r * (r ^ 2)⁻¹ = r⁻¹
    field_simp [hrpos.ne']
  have hg13 : r * gibbsLevels r 1 = gibbsLevels r 3 := by
    change r * r⁻¹ = 1
    exact mul_inv_cancel₀ hrpos.ne'
  have hkernel (i j : Fin 4) (hij : r * gibbsLevels r i = gibbsLevels r j) :
      energyKernel r (x i) (x j) =
        d ^ 2 * (gamma r * ((r * h i - h j) ^ 2 *
          (2 * gibbsLevels r j + d * (r * h i + h j)))) := by
    have hsub : r * x i - x j = d * (r * h i - h j) := by
      dsimp [x]
      linear_combination hij
    have hadd : r * x i + x j = 2 * gibbsLevels r j + d * (r * h i + h j) := by
      dsimp [x]
      linear_combination hij
    calc
      energyKernel r (x i) (x j) =
        gamma r * (r * x i - x j) ^ 2 * (r * x i + x j) := by rw [energyKernel]; ring
      _ = _ := by rw [hsub, hadd]; ring
  simp only [occupationEnergyFactor, occupationEdgeSum]
  rw [hkernel 0 1 hg01, hkernel 0 2 hg01, hkernel 1 3 hg13, hkernel 2 3 hg13]
  ring

/-- Exact ordinary-trace cubic energy in the occupation frame. -/
theorem occupation_operator_energy_eq {r : ℝ} (hr : 1 ≤ r) (d : ℝ) (h : Fin 4 → ℝ) :
    let x := fun i => gibbsLevels r i + d * h i
    let M := occupationFrame * diagonal (fun i => (x i : ℂ)) * occupationFrameᴴ
    (9 / 8 : ℝ) * (M ^ 2 *
      (G r * generator r (GInv r * M * GInv r) * G r)).trace.re =
      d ^ 2 * occupationEnergyFactor r d h := by
  dsimp only
  rw [weighted_spectral_energy hr occupationFrame occupationFrame_columns occupationFrame_rows,
    occupation_spectral_energy_eq]
  exact occupation_edge_energy_factor hr d h

/-- The actual normalized source in occupation placement is the exact edge
energy minus the mass-normalized Gibbs KL term with coefficient `alpha r`. -/
theorem occupation_source_deficit_eq {r d : ℝ} (hr : 1 ≤ r) (h : Fin 4 → ℝ) (hh : h 3 = 0)
    (hx : ∀ i, 0 < gibbsLevels r i + d * h i) :
    let x := fun i => gibbsLevels r i + d * h i
    sourceDeficitAt r occupationFrame (x 0) (x 1) (x 2) =
      d ^ 2 * occupationEnergyFactor r d h - alpha r * occupationEntropy r x := by
  intro x
  have hx3 : x 3 = 1 := by simp [x, gibbsLevels, hh]
  have hlevels : levelsAt (x 0) (x 1) (x 2) = x := by
    funext i
    fin_cases i <;> simp [levelsAt, hx3]
  have hsource (m n q : ℝ) :
      sourceDeficitAt r occupationFrame m n q =
        (∑ i, ∑ j, weight occupationFrame i j *
          energyKernel r (levelsAt m n q i) (levelsAt m n q j)) -
          alpha r * spectralEntropy r occupationFrame (levelsAt m n q) := by
    have hsum : (∑ i, levelsAt m n q i ^ 3) = totalAt m n q := by
      simp [totalAt, levelsAt, Fin.sum_univ_four]
    have hlog : (∑ i, levelsAt m n q i ^ 3 * Real.log (levelsAt m n q i ^ 3)) =
        m ^ 3 * Real.log (m ^ 3) + n ^ 3 * Real.log (n ^ 3) + q ^ 3 * Real.log (q ^ 3) := by
      simp [levelsAt, Fin.sum_univ_four]
    rw [sourceDeficitAt, spectralEntropy, hsum, hlog]
  rw [hsource, hlevels, occupation_spectral_energy_eq, occupation_edge_energy_factor hr d h,
    spectral_entropy_eq_occupationEntropy hr x hx]

/-- The coefficient of `d` in the change of mass of the cubic levels. -/
def massDisplacement (g h : Fin 4 → ℝ) (d : ℝ) : ℝ :=
  ∑ i, (3 * g i ^ 2 * h i + d * (3 * g i * h i ^ 2 + d * h i ^ 3))

/-- Exact mass factorization, also valid at the equilibrium displacement `d = 0`. -/
theorem cubic_mass_sub_eq (g h : Fin 4 → ℝ) (d : ℝ) :
    cubicMass (fun i => g i + d * h i) - cubicMass g = d * massDisplacement g h d := by
  simp only [cubicMass, massDisplacement, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The rational occupation coefficient in the Gibbs-relative Taylor lower bound. -/
def occupationTaylorCoefficient (r d : ℝ) (h : Fin 4 → ℝ) : ℝ :=
  let g := gibbsLevels r
  let Tg := cubicMass g
  let μ := massDisplacement g h d
  occupationEnergyFactor r d h -
    (9 / 4) * (∑ i, g i * h i ^ 2) - (9 / 4) * d * (∑ i, h i ^ 3) -
    (3 / 4) * d ^ 2 * (∑ i, h i ^ 4) + μ ^ 2 / (4 * Tg) - d * μ ^ 3 / (12 * Tg ^ 2)

/-- Gibbs-relative occupation Taylor lower bound for the normalized Wu cubic source deficit.
The cubic displacement terms retain their signs, and the formula applies at `d = 0`. -/
theorem occupation_taylor_lower_bound {r d : ℝ} (hr : 1 ≤ r) (_hd : 0 ≤ d)
    (h : Fin 4 → ℝ) (hh : h 3 = 0)
    (hx : ∀ i, 1 / 2 ≤ gibbsLevels r i + d * h i)
    (hg : ∀ i, 1 / 2 ≤ gibbsLevels r i) :
    let x := fun i => gibbsLevels r i + d * h i
    d ^ 2 * occupationTaylorCoefficient r d h ≤
      sourceDeficitAt r occupationFrame (x 0) (x 1) (x 2) := by
  intro x
  let g := gibbsLevels r
  let Tg := cubicMass g
  let μ := massDisplacement g h d
  have hxpos (i : Fin 4) : 0 < x i := by change 0 < gibbsLevels r i + d * h i; linarith [hx i]
  have hmass : cubicMass x - Tg = d * μ := cubic_mass_sub_eq g h d
  have hscalar :
      (∑ i, ((9 / 2) * g i * (x i - g i) ^ 2 + (9 / 2) * (x i - g i) ^ 3 +
        (3 / 2) * (x i - g i) ^ 4)) =
      d ^ 2 * ((9 / 2) * (∑ i, g i * h i ^ 2) + (9 / 2) * d * (∑ i, h i ^ 3) +
        (3 / 2) * d ^ 2 * (∑ i, h i ^ 4)) := by
    simp only [x, g, Fin.sum_univ_four]
    ring
  have hent :
      occupationEntropy r x ≤
        (∑ i, ((9 / 2) * g i * (x i - g i) ^ 2 + (9 / 2) * (x i - g i) ^ 3 +
          (3 / 2) * (x i - g i) ^ 4)) -
          (cubicMass x - Tg) ^ 2 / (2 * Tg) + (cubicMass x - Tg) ^ 3 / (6 * Tg ^ 2) := by
    rw [occupationEntropy, occupationGibbsProb_fun_eq hr]
    exact mass_normalized_cubic_entropy_le x g hx hg
  rw [hscalar, hmass] at hent
  have hweighted :=
    (mul_le_mul_of_nonneg_right (alpha_bounds_of_one_le hr).2
      (occupation_entropy_nonneg hr x hxpos)).trans
      (mul_le_mul_of_nonneg_left hent (show 0 ≤ (1 / 2 : ℝ) by norm_num))
  rw [occupation_source_deficit_eq hr h hh hxpos]
  have hTg := (cubicMass_pos (gibbsLevels_pos hr)).ne'
  convert sub_le_sub_left hweighted (d ^ 2 * occupationEnergyFactor r d h) using 1
  dsimp only [occupationTaylorCoefficient, Tg, μ, g]
  field_simp [hTg]
  ring

#print axioms occupation_operator_energy_eq
#print axioms occupation_entropy_eq_remainders
#print axioms occupation_taylor_lower_bound

end D5.S3.Quantum.Semigroups.WuCubicOccupationTaylor
