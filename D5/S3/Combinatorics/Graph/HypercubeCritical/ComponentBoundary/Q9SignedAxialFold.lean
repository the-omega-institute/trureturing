/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedAxialFold
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedAxialFold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Projected parity gauges the axial layers and gives complementary signed Huang rows. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OccupiedFibreParity
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance

/-! The first coordinate splits the Huang operator into two axial layers with
opposite transverse signs. Projected parity conjugates the false layer so
both layers use the same transverse operator. The sum and difference of the
gauged layers satisfy complementary row equations on the eight-cube.

The intended application is the normalized order-ninety cylinder for
Hong–Wu–Xia, arXiv:2610.09483 §7, Problem 2. The folded words give signed rows
for its projected dimer and singleton fibres. The theorem applies to any
coherently switched induced cubic support in this coordinate convention. -/

set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedAxialFold
open scoped BigOperators Matrix
open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip IsSwitching switchingVector ambient_eigenvector)
open Q9IsotropicHuang (flipSign)
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private flip_cons_zero flip_cons_succ matrix_row from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance
open private flipSign_cast from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang
open private parity_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OccupiedFibreParity
attribute [local instance] Classical.propDecidable

/-- The sign of deleted-coordinate parity. -/
def paritySign (x : Q 8) : ℤ := if (∑ i, x i) then -1 else 1

/-- Flipping a retained coordinate reverses the projected parity sign. -/
theorem paritySign_flip (x : Q 8) (i : Fin 8) :
    paritySign (flip x i) = -paritySign x := by
  unfold paritySign
  have h : (∑ j, flip x i j) = !(∑ j, x j) := parity_flip x i
  rw [h]
  cases (∑ i, x i) <;> decide

private theorem paritySign_sq (x : Q 8) : paritySign x * paritySign x = 1 := by
  unfold paritySign
  split_ifs <;> decide

/-- The eight-cube signed transverse row in the native Huang convention. -/
def transverse (f : Q 8 → ℤ) (x : Q 8) : ℤ :=
  ∑ i : Fin 8, flipSign i x * f (flip x i)

private theorem transverse_add (f g : Q 8 → ℤ) (x : Q 8) :
    transverse (f + g) x = transverse f x + transverse g x := by
  simp [transverse, mul_add, sum_add_distrib]

private theorem transverse_sub (f g : Q 8 → ℤ) (x : Q 8) :
    transverse (f - g) x = transverse f x - transverse g x := by
  simp [transverse, mul_sub, sum_sub_distrib]

private theorem transverse_gauge (f : Q 8 → ℤ) (x : Q 8) :
    transverse (fun y => paritySign y * f y) x = -paritySign x * transverse f x := by
  unfold transverse
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  dsimp only
  rw [paritySign_flip]
  ring

/-- On the support `C`, the integer word is `1` when `s x = 1` and `-1` otherwise.
It is zero outside `C`. -/
def signedWord (C : Finset (Q 9)) (s : Q 9 → ℝ) (x : Q 9) : ℤ :=
  if x ∈ C then if s x = 1 then 1 else -1 else 0

private theorem cast_signedWord {C : Finset (Q 9)} {s : Q 9 → ℝ}
    (hs : IsSwitching C s) (x : Q 9) :
    (signedWord C s x : ℝ) = switchingVector C s x := by
  by_cases hx : x ∈ C
  · rcases hs.1 x hx with h | h <;> norm_num [signedWord, switchingVector, hx, h]
  · simp [signedWord, switchingVector, hx]

private theorem signed_word_row {C : Finset (Q 9)} {s : Q 9 → ℝ}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C s) (x : Q 9) :
    (∑ i : Fin 9, flipSign i x * signedWord C s (flip x i)) = 3 * signedWord C s x := by
  apply Int.cast_injective (α := ℝ)
  have h := congrFun (ambient_eigenvector (d := 3) C s hr hs) x
  change (huangMatrix 9).mulVec (switchingVector C s) x = 3 * switchingVector C s x at h
  rw [matrix_row] at h
  simpa only [Int.cast_sum, Int.cast_mul, cast_signedWord hs, flipSign_cast,
    Int.cast_ofNat] using h

/-- The two layers after changing the sign of the false layer by projected parity. -/
def gaugeLayer (f : Q 9 → ℤ) (b : Bool) (x : Q 8) : ℤ :=
  if b then f (Fin.cons true x) else paritySign x * f (Fin.cons false x)

private theorem layer_row (f : Q 9 → ℤ)
    (h : ∀ x, (∑ i : Fin 9, flipSign i x * f (flip x i)) = 3 * f x)
    (b : Bool) (x : Q 8) :
    f (Fin.cons (!b) x) + (if b then 1 else -1) * transverse (fun y => f (Fin.cons b y)) x =
      3 * f (Fin.cons b x) := by
  have hr := h (Fin.cons b x)
  rw [Fin.sum_univ_succ] at hr
  simp only [flip_cons_zero, flip_cons_succ] at hr
  change 1 * f (Fin.cons (!b) x) +
    (∑ i : Fin 8, ((if b then 1 else -1) * flipSign i x) * f (Fin.cons b (flip x i))) =
      _ at hr
  simpa only [one_mul, transverse, mul_sum, mul_assoc] using hr

private theorem gauge_row (f : Q 9 → ℤ)
    (h : ∀ x, (∑ i : Fin 9, flipSign i x * f (flip x i)) = 3 * f x)
    (b : Bool) (x : Q 8) :
    transverse (gaugeLayer f b) x + paritySign x * gaugeLayer f (!b) x =
      3 * gaugeLayer f b x := by
  have hr := layer_row f h b x
  cases b
  · simp only [gaugeLayer, Bool.false_eq_true, ite_false, Bool.not_false, ite_true,
      neg_one_mul] at hr ⊢
    change transverse (fun y => paritySign y * f (Fin.cons false y)) x + _ = _
    rw [transverse_gauge]
    linear_combination paritySign x * hr
  · simp only [gaugeLayer, Bool.not_true, Bool.false_eq_true, ite_false, ite_true, one_mul] at hr ⊢
    rw [← mul_assoc, paritySign_sq, one_mul]
    change transverse (fun y => f (Fin.cons true y)) x + f (Fin.cons false x) = _
    linarith

/-- The axial sum and difference of the actual integer switching word satisfy
distinct complementary equations, indexed by deleted-coordinate parity. -/
theorem signed_fold {C : Finset (Q 9)} {s : Q 9 → ℝ}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C s) (x : Q 8) :
    let a := gaugeLayer (signedWord C s) true
    let b := gaugeLayer (signedWord C s) false
    transverse (a + b) x = (3 - paritySign x) * (a + b) x ∧
      transverse (a - b) x = (3 + paritySign x) * (a - b) x := by
  dsimp only
  have ht := gauge_row _ (signed_word_row hr hs) true x
  have hf := gauge_row _ (signed_word_row hr hs) false x
  simp only [Bool.not_true, Bool.not_false] at ht hf
  constructor
  · rw [transverse_add, Pi.add_apply]
    linear_combination ht + hf
  · rw [transverse_sub, Pi.sub_apply]
    linear_combination ht - hf

#print axioms signed_fold
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedAxialFold
