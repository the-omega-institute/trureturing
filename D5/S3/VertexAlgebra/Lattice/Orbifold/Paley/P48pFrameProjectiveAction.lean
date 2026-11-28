/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pFrameProjectiveAction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pFrameProjectiveAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The two signed P48p frame generators act as two copies of the quadratic-character projective action of SL(2,23). -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.Lattice.Orbifold.Paley.P48pFrameData
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import OmegaBuild.Commands

/-!
# The signed projective-line action on the P48p frame

Right multiplication of a normalized row by an element of SL(2,23) gives a new
direction and a nonzero scale. The quadratic character of the scale gives
the sign at the destination. The two frame orbits use the same action, in
coordinates recovered from their infinity rows 0 and 16.
-/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48pFrameProjectiveAction

open scoped Matrix
open P48pSymmetricCommutantCertificate
open private tIndex tSign uIndex uSign from
  D5.S3.VertexAlgebra.Lattice.Orbifold.Paley.P48pFrameData

abbrev F23 := ZMod 23
abbrev SL23 := Matrix.SpecialLinearGroup (Fin 2) F23
abbrev Row := Fin 2 → F23
abbrev FrameMatrix := Matrix (Fin 48) (Fin 48) ℤ

/-- The slope of `(1,k)` is `some k`, and the direction of `(0,1)` is `none`. -/
abbrev Direction := Option F23

private instance prime23 : Fact (Nat.Prime 23) := ⟨by decide⟩

def normalizedRow : Direction → Row
  | none => ![0, 1]
  | some k => ![1, k]

/-- The normalization returns the direction and the coefficient of its normalized row. -/
def normalize (v : Row) : Direction × F23 :=
  if v 0 = 0 then (none, v 1) else (some (v 1 / v 0), v 0)

private theorem normalizedRow_ne_zero (d : Direction) : normalizedRow d ≠ 0 := by
  intro h
  cases d with
  | none => exact one_ne_zero (congrFun h (1 : Fin 2))
  | some k => exact one_ne_zero (congrFun h (0 : Fin 2))

private theorem normalize_scale_ne {v : Row} (hv : v ≠ 0) : (normalize v).2 ≠ 0 := by
  by_cases hx : v 0 = 0
  · simp only [normalize, if_pos hx]
    intro hy
    apply hv
    funext i
    fin_cases i
    · exact hx
    · exact hy
  · simpa only [normalize, if_neg hx] using hx

private theorem normalize_factor (v : Row) :
    v = (normalize v).2 • normalizedRow (normalize v).1 := by
  by_cases hx : v 0 = 0
  · funext i
    fin_cases i <;> simp [normalize, normalizedRow, hx, Pi.smul_apply, smul_eq_mul]
  · funext i
    fin_cases i
    · simp [normalize, normalizedRow, hx, Pi.smul_apply, smul_eq_mul]
    · have h : v 0 * (v 1 / v 0) = v 1 :=
        (mul_comm _ _).trans (div_mul_cancel₀ (v 1) hx)
      simpa [normalize, normalizedRow, hx, Pi.smul_apply, smul_eq_mul] using h.symm

private theorem normalize_smul (d : Direction) {c : F23} (hc : c ≠ 0) :
    normalize (c • normalizedRow d) = (d, c) := by
  cases d <;> simp [normalize, normalizedRow, Pi.smul_apply, smul_eq_mul, hc]

theorem existsUnique_normalizedRow {v : Row} (hv : v ≠ 0) :
    ∃! p : Direction × F23ˣ, v = (↑p.2 : F23) • normalizedRow p.1 := by
  refine ⟨((normalize v).1, Units.mk0 _ (normalize_scale_ne hv)), normalize_factor v, ?_⟩
  intro p hp
  have h := (congrArg normalize hp).trans (normalize_smul p.1 p.2.ne_zero)
  exact Prod.ext (congrArg Prod.fst h).symm (Units.ext (congrArg Prod.snd h).symm)

def transformedRow (g : SL23) (d : Direction) : Row :=
  normalizedRow d ᵥ* (g : Matrix (Fin 2) (Fin 2) F23)

/-- The destination and scale obtained by multiplying a row on the right by `g`. -/
def projectiveStep (g : SL23) (d : Direction) : Direction × F23 :=
  normalize (transformedRow g d)

theorem projectiveStep_factor (g : SL23) (d : Direction) :
    transformedRow g d = (projectiveStep g d).2 • normalizedRow (projectiveStep g d).1 :=
  normalize_factor _

theorem projectiveStep_scale_ne (g : SL23) (d : Direction) : (projectiveStep g d).2 ≠ 0 := by
  change (normalize (transformedRow g d)).2 ≠ 0
  apply normalize_scale_ne
  intro hz
  have h := congrArg (fun v : Row => v ᵥ* ((g⁻¹ : SL23) : Matrix (Fin 2) (Fin 2) F23)) hz
  apply normalizedRow_ne_zero d
  simpa only [transformedRow, Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul,
    mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one,
    Matrix.zero_vecMul] using h

theorem projectiveStep_sign (g : SL23) (d : Direction) :
    quadraticChar F23 (projectiveStep g d).2 = 1 ∨
      quadraticChar F23 (projectiveStep g d).2 = -1 :=
  quadraticChar_dichotomy (projectiveStep_scale_ne g d)

private theorem projectiveStep_one (d : Direction) : projectiveStep 1 d = (d, 1) := by
  unfold projectiveStep transformedRow
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one,
    ← one_smul F23 (normalizedRow d), normalize_smul d one_ne_zero]

private theorem projectiveStep_mul (g h : SL23) (d : Direction) :
    projectiveStep (g * h) d =
      ((projectiveStep h (projectiveStep g d).1).1,
        (projectiveStep g d).2 * (projectiveStep h (projectiveStep g d).1).2) := by
  have hrow : transformedRow (g * h) d =
      ((projectiveStep g d).2 * (projectiveStep h (projectiveStep g d).1).2) •
        normalizedRow (projectiveStep h (projectiveStep g d).1).1 := by
    change normalizedRow d ᵥ* ((g * h : SL23) : Matrix (Fin 2) (Fin 2) F23) = _
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.vecMul_vecMul]
    change transformedRow g d ᵥ* (h : Matrix (Fin 2) (Fin 2) F23) = _
    rw [projectiveStep_factor g d, Matrix.smul_vecMul]
    change (projectiveStep g d).2 • transformedRow h (projectiveStep g d).1 = _
    rw [projectiveStep_factor h (projectiveStep g d).1, smul_smul]
  exact (congrArg normalize hrow).trans
    (normalize_smul _ (mul_ne_zero (projectiveStep_scale_ne g d) (projectiveStep_scale_ne h _)))

private def projectiveMatrix (g : SL23) : Matrix Direction Direction ℤ :=
  fun d e => if (projectiveStep g d).1 = e then quadraticChar F23 (projectiveStep g d).2 else 0

/-- Right multiplication acts on rows in the same order as multiplication in SL(2,23). -/
def projectiveAction : SL23 →* Matrix Direction Direction ℤ where
  toFun := projectiveMatrix
  map_one' := by
    apply Matrix.ext
    intro d e
    change projectiveMatrix 1 d e = _
    simp only [projectiveMatrix, projectiveStep_one, map_one, Matrix.one_apply]
  map_mul' g h := by
    apply Matrix.ext
    intro d e
    change projectiveMatrix (g * h) d e = (projectiveMatrix g * projectiveMatrix h) d e
    simp only [Matrix.mul_apply, projectiveMatrix, projectiveStep_mul, map_mul]
    rw [Fintype.sum_eq_single (projectiveStep g d).1]
    · simp only [if_true, mul_ite, mul_zero]
    · intro j hj
      rw [ite_eq_right (Ne.symm hj), zero_mul]

private theorem char_ne_two : ringChar F23 ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  decide

theorem projectiveAction_injective : Function.Injective projectiveAction := by
  apply (injective_iff_map_eq_one projectiveAction).2
  intro g hg
  have hfix (d : Direction) : (projectiveStep g d).1 = d := by
    by_contra hn
    have hz := congrFun (congrFun hg d) (projectiveStep g d).1
    change projectiveMatrix g d (projectiveStep g d).1 = _ at hz
    rw [projectiveMatrix, if_pos rfl, Matrix.one_apply, if_neg (Ne.symm hn)] at hz
    exact projectiveStep_scale_ne g d (quadraticChar_eq_zero_iff.mp hz)
  have hrow (d : Direction) :
      transformedRow g d = (projectiveStep g d).2 • normalizedRow d := by
    calc
      transformedRow g d = (projectiveStep g d).2 • normalizedRow (projectiveStep g d).1 :=
        projectiveStep_factor g d
      _ = _ := congrArg (fun e => (projectiveStep g d).2 • normalizedRow e) (hfix d)
  have h01 : g 0 1 = 0 := by
    simpa [transformedRow, normalizedRow, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Pi.smul_apply, smul_eq_mul] using congrFun (hrow (some 0)) (1 : Fin 2)
  have h10 : g 1 0 = 0 := by
    simpa [transformedRow, normalizedRow, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Pi.smul_apply, smul_eq_mul] using congrFun (hrow none) (0 : Fin 2)
  have hdiag : g 0 0 = g 1 1 := by
    have h0 := congrFun (hrow (some 1)) (0 : Fin 2)
    have h1 := congrFun (hrow (some 1)) (1 : Fin 2)
    simp [transformedRow, normalizedRow, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Pi.smul_apply, smul_eq_mul, h01, h10] at h0 h1
    exact h0.trans h1.symm
  have hscale : g 0 0 = (projectiveStep g (some 0)).2 := by
    simpa [transformedRow, normalizedRow, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Pi.smul_apply, smul_eq_mul] using congrFun (hrow (some 0)) (0 : Fin 2)
  have hchar : quadraticChar F23 (g 0 0) = 1 := by
    have h := congrFun (congrFun hg (some 0 : Direction)) (some 0 : Direction)
    change projectiveMatrix g (some 0) (some 0) = _ at h
    simpa only [projectiveMatrix, ite_eq_left (hfix (some 0)), Matrix.one_apply_eq, hscale]
      using h
  have hdet := g.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hsq : (g 0 0) ^ 2 = 1 := by
    simpa only [h01, zero_mul, sub_zero, ← hdiag, pow_two] using hdet
  have hneg : quadraticChar F23 (-1) = -1 := by
    rw [quadraticChar_eq_pow_of_char_ne_two char_ne_two (neg_ne_zero.mpr one_ne_zero), ZMod.card]
    decide +kernel
  have h00 : g 0 0 = 1 := by
    rcases sq_eq_one_iff.mp hsq with h | h
    · exact h
    · rw [h, hneg] at hchar
      exact ((by decide : (-1 : ℤ) ≠ 1) hchar).elim
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply, h00, h01, h10, ← hdiag]

/-- The upper transvection `[[1,1],[0,1]]`. -/
def t : SL23 := Matrix.SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) 1

/-- The lower transvection `[[1,0],[-1,1]]`. -/
def u : SL23 := Matrix.SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (-1)

private def chartSlope : Fin 48 → Fin 24 := ![
  23, 0, 19, 9, 20, 18, 9, 13, 17, 5, 0, 8,
  2, 22, 15, 17, 23, 19, 1, 22, 11, 10, 20, 4,
  4, 1, 12, 8, 7, 13, 5, 7, 16, 6, 16, 21,
  3, 3, 2, 10, 14, 11, 15, 14, 18, 6, 12, 21]

private def chartCopy : Fin 48 → Fin 2 := ![
  0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
  1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1,
  0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0,
  1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1]

/-- The sign of the chart row, with positive signs at both infinity seeds. -/
def chartSign : Fin 48 → ℤ := ![
  1, -1, 1, 1, 1, -1, -1, -1, 1, 1, 1, -1,
  1, -1, -1, -1, 1, -1, 1, -1, -1, 1, 1, 1,
  -1, -1, -1, 1, 1, -1, 1, -1, 1, -1, 1, -1,
  -1, -1, 1, -1, 1, 1, 1, -1, -1, -1, 1, 1]

private def chartCoordinate (i : Fin 48) : Direction × Fin 2 :=
  (if chartSlope i = 23 then none else some ((chartSlope i).val : F23), chartCopy i)

private def chartRow (p : Direction × Fin 2) : Fin 48 :=
  let slope : Fin 24 := match p.1 with
    | none => 23
    | some k => ⟨k.val, lt_trans k.val_lt (by decide : 23 < 24)⟩
  let copy0 : Fin 24 → Fin 48 := ![
    10, 18, 38, 37, 24, 30, 45, 31, 27, 6, 21, 41,
    26, 29, 40, 42, 34, 8, 44, 2, 4, 35, 19, 0]
  let copy1 : Fin 24 → Fin 48 := ![
    1, 25, 12, 36, 23, 9, 33, 28, 11, 3, 39, 20,
    46, 7, 43, 14, 32, 15, 5, 17, 22, 47, 13, 16]
  if p.2 = 0 then copy0 slope else copy1 slope

private theorem chartRow_leftInverse : Function.LeftInverse chartRow chartCoordinate := by
  intro i
  fin_cases i <;> decide +kernel

/-- Both chart blocks contain every projective direction exactly once. -/
def frameChart : Fin 48 ≃ Direction × Fin 2 where
  toFun := chartCoordinate
  invFun := chartRow
  left_inv := chartRow_leftInverse
  right_inv := chartRow_leftInverse.rightInverse_of_surjective
    ((Fintype.bijective_iff_injective_and_card chartCoordinate).2
      ⟨chartRow_leftInverse.injective, by simp [Direction, F23]⟩).surjective

theorem frameChart_seeds :
    frameChart 0 = (none, 0) ∧ chartSign 0 = 1 ∧
      frameChart 16 = (none, 1) ∧ chartSign 16 = 1 := by
  change chartCoordinate 0 = (none, 0) ∧ chartSign 0 = 1 ∧
    chartCoordinate 16 = (none, 1) ∧ chartSign 16 = 1
  decide +kernel

private theorem chartSign_sq (i : Fin 48) : chartSign i * chartSign i = 1 := by
  fin_cases i <;> decide +kernel

private def chartDiagonal : FrameMatrix := Matrix.diagonal chartSign

private theorem chartDiagonal_sq : chartDiagonal * chartDiagonal = 1 := by
  rw [chartDiagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  exact congrArg Matrix.diagonal (funext chartSign_sq)

private def chartDiagonalUnit : FrameMatrixˣ :=
  ⟨chartDiagonal, chartDiagonal, chartDiagonal_sq, chartDiagonal_sq⟩

private def doubleAction : SL23 →* Matrix (Direction × Fin 2) (Direction × Fin 2) ℤ where
  toFun g := Matrix.blockDiagonal fun _ => projectiveAction g
  map_one' := by
    change Matrix.blockDiagonal (fun _ : Fin 2 => projectiveAction 1) = 1
    rw [map_one]
    exact Matrix.blockDiagonal_one
  map_mul' g h := by
    change Matrix.blockDiagonal (fun _ : Fin 2 => projectiveAction (g * h)) = _
    rw [map_mul]
    exact Matrix.blockDiagonal_mul _ _

private def unsignedChartAction : SL23 →* FrameMatrix :=
  (Matrix.reindexRingEquiv ℤ frameChart.symm).toMonoidHom.comp doubleAction

/-- Two identical projective actions, reindexed and conjugated by the chart signs. -/
def frameActionUnits : SL23 →* FrameMatrixˣ :=
  (MulAut.conj chartDiagonalUnit).toMonoidHom.comp unsignedChartAction.toHomUnits

def frameAction : SL23 →* FrameMatrix :=
  (Units.coeHom FrameMatrix).comp frameActionUnits

theorem frameAction_injective : Function.Injective frameAction := by
  intro g h hEq
  have hu : frameActionUnits g = frameActionUnits h := Units.ext hEq
  have hc : unsignedChartAction.toHomUnits g = unsignedChartAction.toHomUnits h :=
    (MulAut.conj chartDiagonalUnit).injective hu
  have hr : unsignedChartAction g = unsignedChartAction h :=
    congrArg (fun A : FrameMatrixˣ => (A : FrameMatrix)) hc
  have hb : doubleAction g = doubleAction h :=
    (Matrix.reindexRingEquiv ℤ frameChart.symm).injective hr
  have hp : (fun _ : Fin 2 => projectiveAction g) = fun _ : Fin 2 => projectiveAction h :=
    Matrix.blockDiagonal_injective hb
  exact projectiveAction_injective (congrFun hp 0)

/-- The coordinate formula for the signed change of basis from two projective copies. -/
theorem frameAction_apply (g : SL23) (i j : Fin 48) :
    frameAction g i j =
      if (projectiveStep g (frameChart i).1).1 = (frameChart j).1 ∧
          (frameChart i).2 = (frameChart j).2 then
        chartSign i * quadraticChar F23 (projectiveStep g (frameChart i).1).2 * chartSign j
      else 0 := by
  change (chartDiagonal * unsignedChartAction g * chartDiagonal) i j = _
  rw [chartDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  change chartSign i *
    (if (frameChart i).2 = (frameChart j).2 then
      (if (projectiveStep g (frameChart i).1).1 = (frameChart j).1 then
        quadraticChar F23 (projectiveStep g (frameChart i).1).2 else 0)
      else 0) * chartSign j = _
  by_cases hd : (projectiveStep g (frameChart i).1).1 = (frameChart j).1 <;>
    by_cases hc : (frameChart i).2 = (frameChart j).2 <;> simp [hd, hc]

private def Transition (g : SL23) (index : Fin 48 → Fin 48) (sign : Fin 48 → ℤ)
    (i : Fin 48) : Prop :=
  chartCoordinate (index i) = ((projectiveStep g (chartCoordinate i).1).1, (chartCoordinate i).2) ∧
    chartSign i * quadraticChar F23 (projectiveStep g (chartCoordinate i).1).2 *
      chartSign (index i) = sign i

private theorem frameAction_of_transitions (g : SL23) (index : Fin 48 → Fin 48)
    (sign : Fin 48 → ℤ) (h : ∀ i, Transition g index sign i) :
    frameAction g = signedFrameMatrix index sign := by
  apply Matrix.ext
  intro i j
  have hi := h i
  unfold Transition at hi
  obtain ⟨hc, hs⟩ := hi
  have hd : (frameChart (index i)).1 = (projectiveStep g (frameChart i).1).1 :=
    congrArg Prod.fst hc
  have hb : (frameChart (index i)).2 = (frameChart i).2 := by
    have hcopy := congrArg (fun p : Direction × Fin 2 => p.2) hc.symm
    exact show (chartCoordinate (index i)).2 = (chartCoordinate i).2 from hcopy.symm
  rw [frameAction_apply, signedFrameMatrix]
  by_cases hij : index i = j
  · subst j
    rw [ite_eq_left rfl, ite_eq_left (And.intro hd.symm hb.symm)]
    exact hs
  · rw [if_neg hij]
    refine if_neg ?_
    rintro ⟨hd', hb'⟩
    exact hij (frameChart.injective (Prod.ext (hd.trans hd') (hb.trans hb')))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem frameAction_t : frameAction t = tFrameMatrix := by
  change frameAction t = signedFrameMatrix tIndex tSign
  apply frameAction_of_transitions
  intro i
  unfold Transition
  rw [quadraticChar_eq_pow_of_char_ne_two char_ne_two (projectiveStep_scale_ne t _), ZMod.card]
  fin_cases i <;> decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem frameAction_u : frameAction u = uFrameMatrix := by
  change frameAction u = signedFrameMatrix uIndex uSign
  apply frameAction_of_transitions
  intro i
  unfold Transition
  rw [quadraticChar_eq_pow_of_char_ne_two char_ne_two (projectiveStep_scale_ne u _), ZMod.card]
  fin_cases i <;> decide +kernel

private theorem transvection_pow {i j : Fin 2} (hij : i ≠ j) (c : F23) (n : ℕ) :
    Matrix.SpecialLinearGroup.transvection hij c ^ n =
      Matrix.SpecialLinearGroup.transvection hij ((n : F23) * c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ← Matrix.SpecialLinearGroup.transvection_add, Nat.cast_succ, add_mul, one_mul]

/-- The two transvections generate SL(2,23). -/
theorem generators_generate : Subgroup.closure ({t, u} : Set SL23) = ⊤ := by
  let H := Subgroup.closure ({t, u} : Set SL23)
  have ht : t ∈ H := Subgroup.subset_closure (by simp)
  have hu : u ∈ H := Subgroup.subset_closure (by simp)
  have upper (c : F23) :
      Matrix.SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c ∈ H := by
    have h := H.pow_mem ht c.val
    rw [t, transvection_pow, ZMod.natCast_zmod_val, mul_one] at h
    exact h
  have lower (c : F23) :
      Matrix.SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) c ∈ H := by
    have h := H.pow_mem hu (-c).val
    rw [u, transvection_pow, ZMod.natCast_zmod_val, mul_neg_one, neg_neg] at h
    exact h
  apply le_antisymm le_top
  intro g _
  change g ∈ H
  refine Matrix.SL2.transvection_induction (fun x => x ∈ H) ?_ (fun _ _ => H.mul_mem) g
  intro i j hij c
  fin_cases i
  · obtain rfl : j = 1 := by fin_cases j <;> tauto
    exact upper c
  · obtain rfl : j = 0 := by fin_cases j <;> tauto
    exact lower c

/-- The subgroup generated by the signed frame matrices is the image of SL(2,23). -/
theorem frame_group_eq_range :
    Subgroup.closure ({frameActionUnits t, frameActionUnits u} : Set FrameMatrixˣ) =
      frameActionUnits.range := by
  simpa only [generators_generate, Subgroup.map_top, Set.image_pair]
    using (MonoidHom.map_closure frameActionUnits ({t, u} : Set SL23)).symm

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48pFrameProjectiveAction
