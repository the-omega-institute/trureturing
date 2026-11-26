/- GID: D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Algebra.MatrixExponential]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.claim; result=D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.result; claim=D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.claim
   digest: Full port heat at known unequal masses identifies neither the hidden heat readout nor the port-to-hidden resistance. -/

import D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceInvariantWeightsRefutation
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.FinCases

/-! Positive triangles of prescribed unequal masses with identical port heat and
distinct labelled hidden response and effective resistance. -/

set_option autoImplicit false

open Matrix
open scoped Matrix

namespace D5.S3.Combinatorics.SpectralGraph.UnequalMassPortHeatResistance

open FiedlerResistanceInvariantWeightsRefutation (wLap Harmonic harmonicExt effRes)
open NormedSpace (exp)

noncomputable section

abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ
abbrev Weights := Sym2 (Fin 3) → ℝ
abbrev triangle : SimpleGraph (Fin 3) := ⊤

/-- The positive square roots of the prescribed masses are 1, 1 and 2. -/
def rootMass : Fin 3 → ℝ := ![1, 1, 2]

/-- The diagonal inverse of a vector of square roots of masses. -/
def inverseRootMassFor (roots : Fin 3 → ℝ) : Mat :=
  Matrix.diagonal fun i => (roots i)⁻¹

def inverseRootMass : Mat := inverseRootMassFor rootMass

/-- The physical stiffness uses negative off-diagonal weights and weighted degrees. -/
def stiffness (w : Weights) : Mat := wLap triangle w

/-- Mass-normalized stiffness for a given diagonal inverse square root of the mass matrix. -/
def normalizedWith (D : Mat) (w : Weights) : Mat := D * stiffness w * D

/-- Physical impulse response for a given diagonal inverse square root of the mass matrix. -/
def physicalHeatWith (D : Mat) (w : Weights) (t : ℝ) : Mat :=
  D * exp ((-t) • normalizedWith D w) * D

def normalized (w : Weights) : Mat := normalizedWith inverseRootMass w

/-- Temperature at each output per unit physical impulse at each input. -/
def physicalHeat (w : Weights) (t : ℝ) : Mat :=
  physicalHeatWith inverseRootMass w t

def PositiveWeights (w : Weights) : Prop :=
  ∀ i j : Fin 3, triangle.Adj i j → 0 < w s(i, j)

def edgeWeights (a b c : ℝ) : Weights :=
  Sym2.lift ⟨fun i j => (!![0, a, b; a, 0, c; b, c, 0] : Mat) i j, by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl⟩

/-- The plus network is selected by true and the minus network by false. -/
def conductances (plus : Bool) : Weights :=
  if plus then edgeWeights (4/15) (17/30) (91/150) else edgeWeights (1/15) (23/30) (109/150)

def reflection : Mat := !![1, 0, 0; 0, -3/5, 4/5; 0, 4/5, 3/5]

def groundedPotential (plus : Bool) : Fin 3 → ℝ :=
  if plus then ![352/197, 0, 170/197] else ![448/197, 0, 230/197]

/-- Would full heat at port 0 force either the hidden heat curve or the resistance
from the port to vertex 1 to agree? -/
def claim : Prop :=
  ∀ w u : Weights, PositiveWeights w → PositiveWeights u →
    (∀ t : ℝ, physicalHeat w t 0 0 = physicalHeat u t 0 0) →
    ((∀ t : ℝ, physicalHeat w t 1 0 = physicalHeat u t 1 0) ∨
      effRes triangle w 0 1 = effRes triangle u 0 1)

private theorem conductances_positive (plus : Bool) : PositiveWeights (conductances plus) := by
  intro i j hij
  change i ≠ j at hij
  cases plus <;> fin_cases i <;> fin_cases j <;> try contradiction
  all_goals norm_num [conductances, edgeWeights, Sym2.lift_mk]

theorem stiffness_edges (a b c : ℝ) :
    stiffness (edgeWeights a b c) = !![a+b, -a, -b; -a, a+c, -c; -b, -c, b+c] := by
  ext i j
  simp only [stiffness, wLap, Finset.sum_filter, SimpleGraph.top_adj]
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_three, edgeWeights, Sym2.lift_mk]

private theorem stiffness_entries (plus : Bool) :
    stiffness (conductances plus) =
      if plus then !![5/6, -4/15, -17/30; -4/15, 131/150, -91/150; -17/30, -91/150, 88/75]
      else !![5/6, -1/15, -23/30; -1/15, 119/150, -109/150; -23/30, -109/150, 112/75] := by
  cases plus <;> simp only [conductances, Bool.false_eq_true, ↓reduceIte, stiffness_edges]
  all_goals ext i j
  all_goals fin_cases i <;> fin_cases j <;> norm_num

private theorem normalized_entries (plus : Bool) :
    normalized (conductances plus) =
      if plus then !![5/6, -4/15, -17/60; -4/15, 131/150, -91/300; -17/60, -91/300, 22/75]
      else !![5/6, -1/15, -23/60; -1/15, 119/150, -109/300; -23/60, -109/300, 28/75] := by
  rw [normalized, normalizedWith, stiffness_entries]
  cases plus <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [inverseRootMass, inverseRootMassFor, rootMass, Matrix.diagonal_mul, Matrix.mul_diagonal]

private theorem reflection_symm : reflectionᵀ = reflection := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem reflection_sq : reflection * reflection = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reflection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]

private theorem reflection_mass : reflection *ᵥ rootMass = rootMass := by
  ext i
  fin_cases i <;> norm_num [reflection, rootMass, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem reflection_port : reflection *ᵥ (![1, 0, 0] : Fin 3 → ℝ) = ![1, 0, 0] := by
  ext i
  fin_cases i <;> norm_num [reflection, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem reflection_conj :
    normalized (conductances false) =
      reflection * normalized (conductances true) * reflectionᵀ := by
  rw [reflection_symm, normalized_entries false, normalized_entries true]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reflection, Matrix.mul_apply, Fin.sum_univ_three]

private theorem port_heat_equal (t : ℝ) :
    physicalHeat (conductances true) t 0 0 = physicalHeat (conductances false) t 0 0 := by
  have hs : (-t) • normalized (conductances false) =
      reflection * ((-t) • normalized (conductances true)) * reflection := by
    rw [reflection_conj, reflection_symm, Matrix.mul_smul, Matrix.smul_mul]
  have hunit : IsUnit reflection :=
    (Matrix.isUnit_iff_isUnit_det reflection).2 (Matrix.isUnit_det_of_left_inverse reflection_sq)
  have hexp : ∀ A : Mat, exp (reflection * A * reflection) = reflection * exp A * reflection := by
    intro A
    simpa only [Matrix.inv_eq_left_inv reflection_sq] using Matrix.exp_conj' reflection A hunit
  change (inverseRootMass * exp ((-t) • normalized (conductances true)) * inverseRootMass) 0 0 =
    (inverseRootMass * exp ((-t) • normalized (conductances false)) * inverseRootMass) 0 0
  simp only [hs, hexp, inverseRootMass, inverseRootMassFor, Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp [reflection, rootMass, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

open scoped Matrix.Norms.Operator in
private theorem hidden_derivative (plus : Bool) :
    HasDerivAt (fun t => physicalHeat (conductances plus) t 1 0)
      (if plus then 4/15 else 1/15) 0 := by
  let L := normalized (conductances plus)
  let entry : Mat →L[ℝ] ℝ :=
    (show Mat →ₗ[ℝ] ℝ from
      { toFun := fun A => A 1 0
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }).toContinuousLinearMap
  have h := entry.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_exp_smul_const (-L) (0 : ℝ))
  simp only [Function.comp_def, zero_smul, smul_neg, neg_zero, NormedSpace.exp_zero, one_mul] at h
  change HasDerivAt (fun t : ℝ => exp (-(t • L)) 1 0) (-L 1 0) 0 at h
  have hf : (fun t => physicalHeat (conductances plus) t 1 0) =
      (fun t => exp (-(t • L)) 1 0) := by
    funext t
    change (inverseRootMass * exp ((-t) • L) * inverseRootMass) 1 0 = exp (-(t • L)) 1 0
    simp [inverseRootMass, inverseRootMassFor, rootMass, Matrix.diagonal_mul, Matrix.mul_diagonal,
      neg_smul]
  have hslope : -L 1 0 = (if plus then 4/15 else 1/15) := by
    cases plus <;> norm_num [L, normalized_entries]
  rw [hf, ← hslope]
  exact h

private theorem grounded_iff (plus : Bool) (v : Fin 3 → ℝ) :
    (stiffness (conductances plus) *ᵥ v = ![1, -1, 0] ∧ v 1 = 0) ↔
      v = groundedPotential plus := by
  constructor
  · rintro ⟨heq, hground⟩
    have h0 := congrFun heq 0
    have h2 := congrFun heq 2
    cases plus <;>
      norm_num [stiffness_entries, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hground] at h0 h2
    all_goals
      ext i
      fin_cases i
      · dsimp [groundedPotential]
        linarith only [h0, h2]
      · exact hground
      · dsimp [groundedPotential]
        linarith only [h0, h2]
  · rintro rfl
    constructor
    · cases plus <;> ext i <;> fin_cases i <;>
        norm_num [stiffness_entries, groundedPotential, Matrix.mulVec, dotProduct,
          Fin.sum_univ_three]
    · cases plus <;> rfl

private def dirichletPotential (plus : Bool) : Fin 3 → ℝ :=
  if plus then ![1, 0, 85/176] else ![1, 0, 115/224]

private theorem harmonic_iff (plus : Bool) (v : Fin 3 → ℝ) :
    Harmonic triangle (conductances plus) 0 1 v ↔ v = dirichletPotential plus := by
  constructor
  · rintro ⟨h0, h1, hinterior⟩
    have h2 := hinterior 2 (by decide) (by decide)
    change (stiffness (conductances plus) *ᵥ v) 2 = 0 at h2
    cases plus <;>
      norm_num [stiffness_entries, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h0, h1] at h2
    all_goals
      ext i
      fin_cases i
      · exact h0
      · exact h1
      · dsimp [dirichletPotential]
        linarith only [h2]
  · rintro rfl
    refine ⟨by cases plus <;> rfl, by cases plus <;> rfl, ?_⟩
    intro k h0 h1
    change (stiffness (conductances plus) *ᵥ dirichletPotential plus) k = 0
    fin_cases k
    · exact (h0 rfl).elim
    · exact (h1 rfl).elim
    · cases plus <;>
        norm_num [stiffness_entries, dirichletPotential, Matrix.mulVec, dotProduct,
          Fin.sum_univ_three]

private theorem resistance_value (plus : Bool) :
    effRes triangle (conductances plus) 0 1 = if plus then 352/197 else 448/197 := by
  classical
  have hex : ∃ v, Harmonic triangle (conductances plus) 0 1 v :=
    ⟨dirichletPotential plus, (harmonic_iff _ _).2 rfl⟩
  have hext : harmonicExt triangle (conductances plus) 0 1 = dirichletPotential plus := by
    unfold harmonicExt
    rw [dite_eq_left hex]
    exact (harmonic_iff _ _).1 (Classical.choose_spec hex)
  rw [effRes, ite_eq_right (by decide : (0 : Fin 3) ≠ 1), hext]
  change 1 / (stiffness (conductances plus) *ᵥ dirichletPotential plus) 0 = _
  cases plus <;>
    norm_num [stiffness_entries, dirichletPotential, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The same positive pair has equal full port heat and two different
hidden responses, certified by exact initial slopes and grounded voltages. -/
theorem triangle_certificate (plus : Bool) :
    (effRes triangle (conductances plus) 0 1 = if plus then 352/197 else 448/197) ∧
    PositiveWeights (conductances plus) ∧
    reflectionᵀ = reflection ∧ reflection * reflection = 1 ∧
    reflection *ᵥ rootMass = rootMass ∧
    reflection *ᵥ (![1, 0, 0] : Fin 3 → ℝ) = ![1, 0, 0] ∧
    normalized (conductances false) = reflection * normalized (conductances true) * reflectionᵀ ∧
    (∀ t : ℝ, physicalHeat (conductances true) t 0 0 = physicalHeat (conductances false) t 0 0) ∧
    HasDerivAt (fun t => physicalHeat (conductances plus) t 1 0)
      (if plus then 4/15 else 1/15) 0 ∧
    (∀ v : Fin 3 → ℝ,
      (stiffness (conductances plus) *ᵥ v = ![1, -1, 0] ∧ v 1 = 0) ↔
        v = groundedPotential plus) :=
  ⟨resistance_value plus, conductances_positive plus, reflection_symm, reflection_sq,
    reflection_mass, reflection_port, reflection_conj, port_heat_equal,
    hidden_derivative plus, grounded_iff plus⟩

theorem result : ¬ claim := by
  intro h
  obtain ⟨rPlus, pPlus, _, _, _, _, _, heat, dPlus, _⟩ := triangle_certificate true
  obtain ⟨rMinus, pMinus, _, _, _, _, _, _, dMinus, _⟩ := triangle_certificate false
  rcases h _ _ pPlus pMinus heat with hHidden | hEqual
  · rw [funext hHidden] at dPlus
    have heq := dPlus.unique dMinus
    norm_num at heq
  · rw [rPlus, rMinus] at hEqual
    norm_num at hEqual

end

end UnequalMassPortHeatResistance
end SpectralGraph
end Combinatorics
end S3
end D5
