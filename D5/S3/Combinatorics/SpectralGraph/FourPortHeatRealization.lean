/- GID: D5/S3/Combinatorics/SpectralGraph/FourPortHeatRealization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/FourPortHeatRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Algebra.MatrixExponential]
   utility: none
   digest: A complete four-port heat network has linear order seven and physical order eight. -/

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! A strict, perturbation-stable physical order gap for finite heat networks. -/

set_option autoImplicit false

open Matrix
open scoped Matrix BigOperators

namespace D5.S3.Combinatorics.SpectralGraph.FourPortHeatRealization

noncomputable section

abbrev Port := Fin 4
abbrev Vertex (m : ℕ) := Port ⊕ Fin m
abbrev Generator (m : ℕ) := Matrix (Vertex m) (Vertex m) ℝ
abbrev PortMatrix := Matrix Port Port ℝ

/-- Bounds on the diagonal, oriented cycle edges, and the two opposite pairs. -/
def CycleBounds (Q : PortMatrix) : Prop :=
  (∀ i, Q i i ≤ 4) ∧ (∀ i : Port, 1 ≤ Q i (i + 1)) ∧
    Q 0 2 < 1 / 36 ∧ Q 1 3 < 1 / 36

private theorem repeated_edge_has_opposite (i j : Port) (h : i ≠ j) :
    ((0 = i ∨ 0 = i + 1 ∨ 0 = j ∨ 0 = j + 1) ∧
     (2 = i ∨ 2 = i + 1 ∨ 2 = j ∨ 2 = j + 1)) ∨
    ((1 = i ∨ 1 = i + 1 ∨ 1 = j ∨ 1 = j + 1) ∧
     (3 = i ∨ 3 = i + 1 ∨ 3 = j ∨ 3 = j + 1)) := by
  fin_cases i <;> fin_cases j <;> first | exact (h rfl).elim | decide

/-- An entrywise nonnegative Gram factor under the cycle bounds needs at least four columns. -/
theorem cycle_gram_width (m : ℕ) (A : Matrix Port (Fin m) ℝ)
    (hnonneg : ∀ i k, 0 ≤ A i k) (hb : CycleBounds (A * Aᵀ)) : 4 ≤ m := by
  classical
  by_contra! hm
  have entry_le (i : Port) (k : Fin m) : A i k ≤ 2 := by
    have hk : A i k * A i k ≤ (A * Aᵀ) i i :=
      Finset.single_le_sum (f := fun l => A i l * A i l)
        (fun l _ => mul_self_nonneg _) (Finset.mem_univ k)
    have hdiag := hb.1 i
    nlinarith [hnonneg i k, mul_self_nonneg (A i k - 2)]
  have witness (i : Port) : ∃ k, (1 : ℝ) / 6 ≤ A i k ∧ 1 / 6 ≤ A (i + 1) k := by
    have hprod : ∃ k, (1 : ℝ) / 3 ≤ A i k * A (i + 1) k := by
      by_contra! hsmall
      have hedge := hb.2.1 i
      change (1 : ℝ) ≤ ∑ k, A i k * A (i + 1) k at hedge
      cases m with
      | zero => norm_num at hedge
      | succ m =>
        have hsum : (∑ k : Fin (m + 1), A i k * A (i + 1) k) <
            ∑ _ : Fin (m + 1), (1 : ℝ) / 3 :=
          Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun k _ => hsmall k)
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
        have hm' : ((m + 1 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (show m + 1 ≤ 3 by omega)
        linarith
    obtain ⟨k, hk⟩ := hprod
    exact ⟨k,
      by linarith [mul_le_mul_of_nonneg_left (entry_le (i+1) k) (hnonneg i k)],
      by linarith [mul_le_mul_of_nonneg_right (entry_le i k) (hnonneg (i+1) k)]⟩
  choose f hf using witness
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simpa using hm)
  have lower (a : Port) (ha : a = i ∨ a = i+1 ∨ a = j ∨ a = j+1) : 1/6 ≤ A a (f i) := by
    rcases ha with h | h | h | h
    · simpa only [h] using (hf i).1
    · simpa only [h] using (hf i).2
    · simpa only [h, heq] using (hf j).1
    · simpa only [h, heq] using (hf j).2
  have gram_lower (a b : Port) (ha : 1/6 ≤ A a (f i)) (hb' : 1/6 ≤ A b (f i)) :
      1/36 ≤ (A * Aᵀ) a b := by
    calc
      (1 : ℝ) / 36 = (1/6) * (1/6) := by norm_num
      _ ≤ A a (f i) * A b (f i) :=
        mul_le_mul ha hb' (by norm_num) (hnonneg a (f i))
      _ ≤ _ := Finset.single_le_sum (f := fun k => A a k * A b k)
        (fun k _ => mul_nonneg (hnonneg a k) (hnonneg b k)) (Finset.mem_univ _)
  rcases repeated_edge_has_opposite i j hij with h | h
  · exact (not_le_of_gt hb.2.2.1) (gram_lower 0 2 (lower 0 h.1) (lower 2 h.2))
  · exact (not_le_of_gt hb.2.2.2) (gram_lower 1 3 (lower 1 h.1) (lower 3 h.2))

/-- The mass-normalized generator of a physical network with unit port masses.
The vector z consists of the positive square roots of all vertex masses. -/
def IsPhysical {m : ℕ} (S : Generator m) (z : Vertex m → ℝ) : Prop :=
  S.IsSymm ∧ (∀ i, 0 < z i) ∧ (∀ i, z (.inl i) = 1) ∧
    S *ᵥ z = 0 ∧ ∀ i j, i ≠ j → S i j ≤ 0

/-- Insertion at the four marked ports. -/
def ports (m : ℕ) : Matrix (Vertex m) Port ℝ :=
  Matrix.fromRows 1 0

/-- The stationary-inclusive, normalized moments at the marked ports. -/
def moment {m : ℕ} (S : Generator m) (k : ℕ) : PortMatrix :=
  (ports m)ᵀ * S ^ k * ports m

/-- The defect in the second moment after subtracting the square of the first. -/
def defect {m : ℕ} (S : Generator m) : PortMatrix :=
  moment S 2 - moment S 1 * moment S 1

private theorem moment_apply {m : ℕ} (S : Generator m) (k : ℕ) (i j : Port) :
    moment S k i j = (S ^ k) (.inl i) (.inl j) := by
  simp [moment, Matrix.mul_apply, ports, Fintype.sum_sum_type, Matrix.one_apply,
    Matrix.transpose_apply, Finset.sum_ite_eq, Finset.sum_ite_eq']

private theorem defect_cross_gram {m : ℕ} (S : Generator m) (hS : S.IsSymm) :
    defect S = (-S.toBlocks₁₂) * (-S.toBlocks₁₂)ᵀ := by
  ext i j
  simp [defect, Matrix.sub_apply, moment_apply, pow_two, Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.toBlocks₁₂, ← hS.apply (.inl j) (.inr _)]

private def cross : PortMatrix :=
  (1 / 1000 : ℝ) • !![1001, 1, 1, 1001; 1001, 1001, 1, 1; 1, 1001, 1001, 1; 1, 1, 1001, 1001]

private def within : PortMatrix :=
  (1 / 1000 : ℝ) • !![2007, -1, -1, -1; -1, 2007, -1, -1; -1, -1, 2007, -1; -1, -1, -1, 2007]

/-- Eight-vertex generator with unit masses and every distinct pair coupled. -/
def cycleGenerator : Generator 4 :=
  Matrix.fromBlocks within (-cross) (-crossᵀ) within

private theorem cycle_physical : IsPhysical cycleGenerator (fun _ => 1) := by
  refine ⟨?_, fun _ => zero_lt_one, fun _ => rfl, ?_, ?_⟩
  · change cycleGeneratorᵀ = cycleGenerator
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;> norm_num [cycleGenerator, within, cross]
  · ext i
    rcases i with i | i <;> fin_cases i <;>
      norm_num [Matrix.mulVec, dotProduct, cycleGenerator, cross, within,
        Fintype.sum_sum_type, Fin.sum_univ_four]
  · intro i j h
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      first | exact (h rfl).elim | norm_num [cycleGenerator, cross, within]

private theorem cycle_complete (i j : Vertex 4) (h : i ≠ j) : cycleGenerator i j < 0 := by
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    first | exact (h rfl).elim | norm_num [cycleGenerator, cross, within]

private theorem cycle_defect (i j : Port) :
    defect cycleGenerator i j =
      (if i = j then 2 else if j = i + 1 ∨ i = j + 1 then 1 else 0) + 1001/250000 := by
  rw [defect_cross_gram _ cycle_physical.1]
  fin_cases i <;> fin_cases j <;>
    norm_num [cycleGenerator, cross, Matrix.toBlocks₁₂, Matrix.mul_apply, Fin.sum_univ_four]

/-- The physical lower bound holds for every candidate in the defect band around the
complete unit-mass cycle network, with arbitrary hidden masses and nonnegative conductances. -/
private theorem robust_physical_order (m : ℕ) (S : Generator m) (z : Vertex m → ℝ)
    (hS : IsPhysical S z)
    (hclose : ∀ i j, |defect S i j - defect cycleGenerator i j| ≤ 1 / 250) :
    8 ≤ Fintype.card (Vertex m) := by
  have hdiag (i : Port) : defect S i i ≤ 4 := by
    have h := (abs_le.mp (hclose i i)).2
    rw [cycle_defect, ite_eq_left rfl] at h
    linarith
  have hedge (i : Port) : 1 ≤ defect S i (i+1) := by
    have h := (abs_le.mp (hclose i (i+1))).1
    have hne : i ≠ i+1 := by fin_cases i <;> decide
    rw [cycle_defect, ite_eq_right hne, ite_eq_left (Or.inl rfl)] at h
    linarith
  have hopposite : defect S 0 2 < 1/36 ∧ defect S 1 3 < 1/36 := by
    have h02 := (abs_le.mp (hclose 0 2)).2
    have h13 := (abs_le.mp (hclose 1 3)).2
    rw [cycle_defect] at h02 h13
    norm_num [show ¬ ((2 : Port) = 0 + 1 ∨ 0 = 2 + 1) by decide,
      show ¬ ((3 : Port) = 1 + 1 ∨ 1 = 3 + 1) by decide] at h02 h13
    constructor <;> linarith
  have hbounds : CycleBounds (defect S) := ⟨hdiag, hedge, hopposite⟩
  rw [defect_cross_gram S hS.1] at hbounds
  have hm := cycle_gram_width m (-S.toBlocks₁₂)
    (fun i k => neg_nonneg.mpr (hS.2.2.2.2 _ _ (by simp))) hbounds
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

/-- The impulse response of a finite linear system with dynamics u' = -T u + B a. -/
def linearHeat {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n ℝ)
    (B : Matrix n Port ℝ) (C : Matrix Port n ℝ) (t : ℝ) : PortMatrix :=
  C * NormedSpace.exp ((-t) • T) * B

/-- Physical heat impulse response when the four marked port masses are one. -/
def portHeat {m : ℕ} (S : Generator m) : ℝ → PortMatrix :=
  linearHeat S (ports m) (ports m)ᵀ

open scoped Matrix.Norms.Operator in
private def sandwich {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix Port n ℝ) (B : Matrix n Port ℝ) : Matrix n n ℝ →L[ℝ] PortMatrix :=
  (show Matrix n n ℝ →ₗ[ℝ] PortMatrix from
    { toFun := fun X => C * X * B
      map_add' := fun X Y => by
        change C * (X + Y) * B = C * X * B + C * Y * B
        rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by
        change C * (c • X) * B = c • (C * X * B)
        rw [Matrix.mul_smul, Matrix.smul_mul] }).toContinuousLinearMap

open scoped Matrix.Norms.Operator in
private theorem same_heat_of_moments {n d : Type*}
    [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d]
    (T : Matrix n n ℝ) (B : Matrix n Port ℝ) (C : Matrix Port n ℝ)
    (R : Matrix d d ℝ) (B' : Matrix d Port ℝ) (C' : Matrix Port d ℝ)
    (h : ∀ k : ℕ, C * T ^ k * B = C' * R ^ k * B') :
    linearHeat T B C = linearHeat R B' C' := by
  funext t
  change sandwich C B (NormedSpace.exp ((-t) • T)) =
    sandwich C' B' (NormedSpace.exp ((-t) • R))
  simp only [NormedSpace.exp_eq_tsum ℝ]
  rw [(sandwich C B).map_tsum (NormedSpace.expSeries_summable' (𝕂 := ℝ) _),
    (sandwich C' B').map_tsum (NormedSpace.expSeries_summable' (𝕂 := ℝ) _)]
  apply tsum_congr
  intro k
  rw [map_smul, map_smul, smul_pow, smul_pow, map_smul, map_smul]
  exact congrArg (fun X : PortMatrix => (k.factorial⁻¹ : ℝ) • (-t)^k • X) (h k)

open scoped Matrix.Norms.Operator in
private theorem heat_deriv {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n ℝ) (B : Matrix n Port ℝ) (C : Matrix Port n ℝ) (t : ℝ) :
    deriv (linearHeat T B C) t = linearHeat T (-(T * B)) C t := by
  have h := (sandwich C B).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const (-T) t)
  simpa [linearHeat, sandwich, Function.comp_def, smul_neg, neg_smul, mul_assoc] using h.deriv

open scoped Matrix.Norms.Operator in
private theorem first_moments_of_same_heat {n d : Type*}
    [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d]
    (T : Matrix n n ℝ) (B : Matrix n Port ℝ) (C : Matrix Port n ℝ)
    (R : Matrix d d ℝ) (B' : Matrix d Port ℝ) (C' : Matrix Port d ℝ)
    (h : linearHeat T B C = linearHeat R B' C') :
    (∀ k ≤ 2, C * T ^ k * B = C' * R ^ k * B') := by
  have h0 := congrFun h 0
  have h' : linearHeat T (-(T * B)) C = linearHeat R (-(R * B')) C' := by
    funext t
    rw [← heat_deriv, ← heat_deriv, h]
  have h1 := congrFun h' 0
  have h2 := congrArg (fun H : ℝ → PortMatrix => deriv H 0) h'
  rw [heat_deriv, heat_deriv] at h2
  have hz (k : ℕ) (hk : k ≤ 2) : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  intro k hk
  rcases hz k hk with rfl | rfl | rfl
  · simpa [linearHeat] using h0
  · simpa [linearHeat, ← Matrix.mul_assoc] using h1
  · simpa [linearHeat, pow_two, ← Matrix.mul_assoc] using h2

abbrev Reduced := Vertex 3

/-- Embed the three hidden coordinates in the hyperplane x₀ − x₁ + x₂ − x₃ = 0. -/
private def hiddenLift : Matrix (Fin 4) (Fin 3) ℝ :=
  !![1, 0, 0; 0, 1, 0; 0, 0, 1; 1, -1, 1]

private def lift : Matrix (Vertex 4) Reduced ℝ :=
  Matrix.fromBlocks 1 0 0 hiddenLift

private def firstThree : Reduced → Vertex 4 :=
  Sum.map id Fin.castSucc

private def reducedGenerator : Matrix Reduced Reduced ℝ :=
  (cycleGenerator * lift).submatrix firstThree id

private theorem invariant_lift : cycleGenerator * lift = lift * reducedGenerator := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [cycleGenerator, lift, reducedGenerator, firstThree, hiddenLift, within, cross,
      Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_three,
      Matrix.one_apply]

private theorem lift_ports : lift * ports 3 = ports 4 := by
  simp [lift, ports, Matrix.fromBlocks_mul_fromRows]

private theorem ports_lift : (ports 4)ᵀ * lift = (ports 3)ᵀ := by
  simp [lift, ports, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromBlocks]

private theorem reduced_heat : linearHeat reducedGenerator (ports 3) (ports 3)ᵀ =
    portHeat cycleGenerator := by
  apply same_heat_of_moments
  intro k
  have hp (j : ℕ) : cycleGenerator ^ j * lift = lift * reducedGenerator ^ j := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, invariant_lift,
        Matrix.mul_assoc]
  calc
    _ = ((ports 4)ᵀ * lift) * reducedGenerator ^ k * ports 3 := by rw [ports_lift]
    _ = (ports 4)ᵀ * (lift * reducedGenerator ^ k) * ports 3 := by rw [Matrix.mul_assoc]
    _ = (ports 4)ᵀ * cycleGenerator ^ k * (lift * ports 3) := by
      rw [← hp, ← Matrix.mul_assoc, Matrix.mul_assoc ((ports 4)ᵀ * cycleGenerator ^ k)]
    _ = _ := by rw [lift_ports]

private def firstColumns {n : Type*} (M : Matrix n Port ℝ) : Matrix n (Fin 3) ℝ :=
  M.submatrix id Fin.castSucc

private def firstRows {n : Type*} (M : Matrix Port n ℝ) : Matrix (Fin 3) n ℝ :=
  M.submatrix Fin.castSucc id

private def controlFrame {n : Type*} [Fintype n] (T : Matrix n n ℝ)
    (B : Matrix n Port ℝ) : Matrix n Reduced ℝ :=
  Matrix.fromCols B (firstColumns (T * B))

private def outputFrame {n : Type*} [Fintype n] (T : Matrix n n ℝ)
    (C : Matrix Port n ℝ) : Matrix Reduced n ℝ :=
  Matrix.fromRows C (firstRows (C * T))

private theorem two_step_hankel {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n ℝ) (B : Matrix n Port ℝ) (C : Matrix Port n ℝ) :
    outputFrame T C * controlFrame T B =
      Matrix.fromBlocks (C * T^0 * B) (firstColumns (C * T^1 * B))
        (firstRows (C * T^1 * B)) (firstRows (firstColumns (C * T^2 * B))) := by
  rw [controlFrame, outputFrame, Matrix.fromRows_mul_fromCols]
  have h₁ : C * T * B = C * (T * B) := Matrix.mul_assoc _ _ _
  have h₂ : C * (T * T) * B = (C * T) * (T * B) := by simp only [Matrix.mul_assoc]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [pow_two, h₂, firstColumns, firstRows, Matrix.mul_apply] <;>
    exact congrFun (congrFun h₁ _) _

private theorem cycle_frame_rank : (controlFrame cycleGenerator (ports 4)).rank = 7 := by
  let minor : Matrix (Fin 3) (Fin 3) ℝ :=
    (1 / 1000 : ℝ) • !![-1001, -1001, -1; -1, -1001, -1001; -1, -1, -1001]
  have hblock :
      (controlFrame cycleGenerator (ports 4)).submatrix firstThree id =
        Matrix.fromBlocks 1 (firstColumns within) 0 minor := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      norm_num [controlFrame, firstColumns, firstThree, ports, cycleGenerator, within,
        cross, minor, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_four, Matrix.one_apply]
  have hminor : minor.det ≠ 0 := by
    norm_num [minor, Matrix.det_fin_three]
  have hunit : IsUnit ((controlFrame cycleGenerator (ports 4)).submatrix firstThree id) := by
    rw [hblock, Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
    exact isUnit_iff_ne_zero.mpr hminor
  obtain ⟨U, hU⟩ := hunit
  apply le_antisymm
  · simpa using (controlFrame cycleGenerator (ports 4)).rank_le_card_width
  · have hsub := Matrix.rank_submatrix_le (controlFrame cycleGenerator (ports 4)) firstThree id
    rw [← hU, Matrix.rank_unit] at hsub
    simpa using hsub

private theorem cycle_hankel_rank :
    (outputFrame cycleGenerator (ports 4)ᵀ * controlFrame cycleGenerator (ports 4)).rank = 7 := by
  have h : outputFrame cycleGenerator (ports 4)ᵀ =
      (controlFrame cycleGenerator (ports 4))ᵀ := by
    rw [outputFrame, controlFrame, Matrix.transpose_fromCols]
    simp [firstRows, firstColumns, Matrix.transpose_submatrix, Matrix.transpose_mul, cycle_physical.1.eq]
  rw [h, Matrix.rank_transpose_mul_self, cycle_frame_rank]

/-- The exact heat order of the cycle network, with a physical lower bound in the
defect band centered at Q. -/
def CycleHeatOrderGap (Q : PortMatrix) : Prop :=
    IsPhysical cycleGenerator (fun _ => 1) ∧
    (∀ i j, i ≠ j → cycleGenerator i j < 0) ∧
    (∃ (T : Matrix Reduced Reduced ℝ) (B : Matrix Reduced Port ℝ) (C : Matrix Port Reduced ℝ),
      linearHeat T B C = portHeat cycleGenerator) ∧
    (∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) Port ℝ)
      (C : Matrix Port (Fin n) ℝ), linearHeat T B C = portHeat cycleGenerator → 7 ≤ n) ∧
    (∀ (m : ℕ) (S : Generator m) (z : Vertex m → ℝ), IsPhysical S z →
      (portHeat S = portHeat cycleGenerator ∨
        (∀ i j, |defect S i j - Q i j| ≤ 1/250)) →
      8 ≤ Fintype.card (Vertex m))

/-- The complete unit-mass eight-vertex network has an exact seven-state linear
realization of its full heat curve. Every linear realization of that curve needs
at least seven states. Physical candidates in the certified defect band need
at least eight vertices, attained by this network for the exact data. -/
theorem cycle_heat_order_gap : CycleHeatOrderGap (defect cycleGenerator) := by
  refine ⟨cycle_physical, cycle_complete, ⟨reducedGenerator, ports 3, (ports 3)ᵀ, reduced_heat⟩,
    ?_, ?_⟩
  · intro n T B C heq
    have hm := first_moments_of_same_heat T B C cycleGenerator (ports 4) (ports 4)ᵀ heq
    have hh : outputFrame T C * controlFrame T B =
        outputFrame cycleGenerator (ports 4)ᵀ * controlFrame cycleGenerator (ports 4) := by
      rw [two_step_hankel, two_step_hankel, hm 0 (by decide), hm 1 (by decide), hm 2 (by decide)]
    calc
      7 = (outputFrame T C * controlFrame T B).rank := by rw [hh, cycle_hankel_rank]
      _ ≤ (outputFrame T C).rank := rank_mul_le_left _ _
      _ ≤ n := by simpa using (outputFrame T C).rank_le_card_width
  · intro m S z hp h
    apply robust_physical_order m S z hp
    rcases h with heq | hclose
    · have hm := first_moments_of_same_heat S (ports m) (ports m)ᵀ
        cycleGenerator (ports 4) (ports 4)ᵀ heq
      have hd : defect S = defect cycleGenerator := by
        unfold defect moment
        rw [hm 1 (by decide), hm 2 (by decide)]
      intro i j
      rw [hd, sub_self, abs_zero]
      norm_num
    · exact hclose

end

end D5.S3.Combinatorics.SpectralGraph.FourPortHeatRealization
