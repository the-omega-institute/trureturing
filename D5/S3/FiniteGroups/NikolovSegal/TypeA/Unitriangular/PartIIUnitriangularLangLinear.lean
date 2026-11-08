import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularLayers
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Ring.GeomSum

set_option autoImplicit false

/- Source candidate only; no elaboration or kernel verification has been run.
   Requires the public exports specified in owner-exports.json, without changing
   any existing statement or proof. -/
namespace NikolovSegal.PartIIUnitriangularLang

open PartIIUnitriangularLayers
open scoped BigOperators

universe u
variable {F : Type u} [Field F] {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) F

/-- Exactly the positive-root nonresonance condition, including ranks zero/one. -/
def Nonresonant (a : Fˣ) : Prop :=
  ∀ d : ℕ, 1 ≤ d ∧ d < n → (a : F) ^ d ≠ 1

/-- The difference of the height action and identity on strict-upper matrices.
    This entry formula is used only on the actual strict-upper filtration. -/
def delta (a : Fˣ) (X : Mat) : Mat :=
  fun i j => ((a : F) ^ (j.val - i.val) - 1) * X i j

/-- Division is confined to strict-upper positions. Outside them the result
    is zero, even for an input not belonging to the strict-upper subspace. -/
noncomputable def deltaInv (a : Fˣ) : Module.End F Mat where
  toFun X i j := if i.val < j.val then
    X i j / ((a : F) ^ (j.val - i.val) - 1) else 0
  map_add' X Y := by
    ext i j
    change (if i.val < j.val then
      (X + Y) i j / ((a : F) ^ (j.val - i.val) - 1) else 0) =
      (if i.val < j.val then X i j / ((a : F) ^ (j.val - i.val) - 1) else 0) +
        (if i.val < j.val then Y i j / ((a : F) ^ (j.val - i.val) - 1) else 0)
    by_cases h : i.val < j.val
    · simp [h, Matrix.add_apply, add_div]
    · simp [h]
  map_smul' c X := by
    ext i j
    change (if i.val < j.val then
      (c • X) i j / ((a : F) ^ (j.val - i.val) - 1) else 0) =
      c • (if i.val < j.val then X i j / ((a : F) ^ (j.val - i.val) - 1) else 0)
    by_cases h : i.val < j.val
    · simp [h, Matrix.smul_apply, smul_eq_mul, mul_div_assoc]
    · simp [h]

theorem deltaInv_apply (a : Fˣ) (X : Mat) (i j : Fin n) :
    deltaInv a X i j = if i.val < j.val then
      X i j / ((a : F) ^ (j.val - i.val) - 1) else 0 := rfl

theorem deltaInv_strict (a : Fˣ) (X : Mat) : LayerDepth 1 (deltaInv a X) := by
  intro i j hij
  rw [deltaInv_apply, if_neg (by omega)]

theorem deltaInv_depth (a : Fˣ) {r : ℕ} {X : Mat}
    (hX : LayerDepth r X) : LayerDepth r (deltaInv a X) := by
  intro i j hij
  rw [deltaInv_apply]
  by_cases h : i.val < j.val
  · rw [if_pos h, hX i j hij, zero_div]
  · rw [if_neg h]

theorem delta_deltaInv (a : Fˣ) (ha : Nonresonant (n := n) a)
    {X : Mat} (hX : LayerDepth 1 X) : delta a (deltaInv a X) = X := by
  ext i j
  change ((a : F) ^ (j.val - i.val) - 1) * deltaInv a X i j = X i j
  rw [deltaInv_apply]
  by_cases hij : i.val < j.val
  · rw [if_pos hij]
    have hd : (a : F) ^ (j.val - i.val) - 1 ≠ 0 :=
      sub_ne_zero.mpr (ha _ ⟨by omega, by have := j.isLt; omega⟩)
    calc
      _ = X i j * (((a : F) ^ (j.val - i.val) - 1) /
          ((a : F) ^ (j.val - i.val) - 1)) := by ring
      _ = X i j := by rw [div_self hd, mul_one]
  · rw [if_neg hij, mul_zero, hX i j (by omega)]

theorem deltaInv_delta (a : Fˣ) (ha : Nonresonant (n := n) a)
    {X : Mat} (hX : LayerDepth 1 X) : deltaInv a (delta a X) = X := by
  ext i j
  rw [deltaInv_apply]
  by_cases hij : i.val < j.val
  · rw [if_pos hij]
    change (((a : F) ^ (j.val - i.val) - 1) * X i j) /
      ((a : F) ^ (j.val - i.val) - 1) = X i j
    have hd : (a : F) ^ (j.val - i.val) - 1 ≠ 0 :=
      sub_ne_zero.mpr (ha _ ⟨by omega, by have := j.isLt; omega⟩)
    calc
      _ = X i j * (((a : F) ^ (j.val - i.val) - 1) /
          ((a : F) ^ (j.val - i.val) - 1)) := by ring
      _ = X i j := by rw [div_self hd, mul_one]
  · rw [if_neg hij, hX i j (by omega)]

/-- Target-dependent operator: first LEFT multiplication by b, then division
    by root weights. No commutation between the two operators is asserted. -/
noncomputable def targetOp (a : Fˣ) (b : Mat) : Module.End F Mat :=
  (deltaInv a).comp (LinearMap.mulLeft F b)

theorem targetOp_apply (a : Fˣ) (b X : Mat) :
    targetOp a b X = deltaInv a (b * X) := rfl

/-- In particular this holds for r ≥ 1; the stronger r = 0 case costs nothing. -/
theorem targetOp_raises (a : Fˣ) {b X : Mat} {r : ℕ}
    (hb : LayerDepth 1 b) (hX : LayerDepth r X) :
    LayerDepth (r + 1) (targetOp a b X) := by
  rw [targetOp_apply]
  exact deltaInv_depth a (by simpa only [Nat.add_comm] using depth_mul hb hX)

theorem targetOp_pow_depth (a : Fˣ) {b X : Mat} {r : ℕ}
    (hb : LayerDepth 1 b) (hX : LayerDepth r X) (k : ℕ) :
    LayerDepth (r + k) (((targetOp a b) ^ k) X) := by
  induction k with
  | zero => simpa only [pow_zero, Module.End.one_apply, Nat.add_zero] using hX
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    simpa only [Nat.add_assoc] using targetOp_raises a hb ih

/-- Nilpotence is proved on strict-upper inputs, rather than assumed on an
    unrelated group or on the whole ambient endomorphism ring. For n = 0/1
    these inputs are zero and exponent n-1 = 0 is correct. -/
theorem targetOp_nilpotent (a : Fˣ) {b X : Mat}
    (hb : LayerDepth 1 b) (hX : LayerDepth 1 X) :
    (((targetOp a b) ^ (n - 1)) X) = 0 := by
  exact depth_n_zero (depth_mono (targetOp_pow_depth a hb hX (n - 1)) (by omega))

noncomputable def neumannEnd (a : Fˣ) (b : Mat) : Module.End F Mat :=
  ∑ k ∈ Finset.range (n - 1), (targetOp a b) ^ k

/-- The actual finite nonlinear inverse coordinate, depending on target b. -/
noncomputable def finiteSolution (a : Fˣ) (b : Mat) : Mat :=
  neumannEnd a b (deltaInv a b)

theorem finiteSolution_eq_sum (a : Fˣ) (b : Mat) :
    finiteSolution a b =
      ∑ k ∈ Finset.range (n - 1), ((targetOp a b) ^ k) (deltaInv a b) := by
  simp only [finiteSolution, neumannEnd, LinearMap.sum_apply]

theorem finiteSolution_depth (a : Fˣ) {b : Mat} (hb : LayerDepth 1 b) :
    LayerDepth 1 (finiteSolution a b) := by
  rw [finiteSolution_eq_sum]
  apply depth_sum
  intro k hk
  exact depth_mono (targetOp_pow_depth a hb (deltaInv_strict a b) k) (by omega)

theorem finiteSolution_fixed (a : Fˣ) {b : Mat} (hb : LayerDepth 1 b) :
    finiteSolution a b = deltaInv a b + targetOp a b (finiteSolution a b) := by
  have h := congrArg (fun f : Module.End F Mat => f (deltaInv a b))
    (mul_neg_geom_sum (targetOp a b) (n - 1))
  change finiteSolution a b - targetOp a b (finiteSolution a b) =
    deltaInv a b - (((targetOp a b) ^ (n - 1)) (deltaInv a b)) at h
  rw [targetOp_nilpotent a hb (deltaInv_strict a b), sub_zero] at h
  exact sub_eq_iff_eq_add.mp h

theorem finiteSolution_equation (a : Fˣ) (ha : Nonresonant (n := n) a)
    {b : Mat} (hb : LayerDepth 1 b) :
    delta a (finiteSolution a b) = b + b * finiteSolution a b := by
  have hstrict : LayerDepth 1 (b + b * finiteSolution a b) :=
    depth_add hb (depth_mono (depth_mul hb (finiteSolution_depth a hb)) (by omega))
  have hfix : finiteSolution a b = deltaInv a (b + b * finiteSolution a b) := by
    rw [map_add]
    exact finiteSolution_fixed a hb
  calc
    delta a (finiteSolution a b) =
        delta a (deltaInv a (b + b * finiteSolution a b)) := congrArg (delta a) hfix
    _ = b + b * finiteSolution a b := delta_deltaInv a ha hstrict

theorem finiteSolution_unique (a : Fˣ) (ha : Nonresonant (n := n) a)
    {b X : Mat} (hb : LayerDepth 1 b) (hX : LayerDepth 1 X)
    (he : delta a X = b + b * X) : X = finiteSolution a b := by
  have hfixed := congrArg (deltaInv a) he
  rw [deltaInv_delta a ha hX, map_add] at hfixed
  have hsub : X - targetOp a b X = deltaInv a b :=
    sub_eq_iff_eq_add.mpr hfixed
  have h := congrArg (fun f : Module.End F Mat => f X)
    (geom_sum_mul_neg (targetOp a b) (n - 1))
  change neumannEnd a b (X - targetOp a b X) =
    X - (((targetOp a b) ^ (n - 1)) X) at h
  rw [hsub, targetOp_nilpotent a hb hX, sub_zero] at h
  exact h.symm

end NikolovSegal.PartIIUnitriangularLang
