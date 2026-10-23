/- GID: D5/S3/ObserverMemory/Prediction/QuantizedWordApproximation
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/QuantizedWordApproximation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quantized controlled trajectories obey finite-word and uniform contraction error bounds. -/

import D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.ObserverMemory.Prediction.QuantizedWordApproximation

universe u v w

open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

/-- Apply an action at the stored center and quantize the resulting source state. -/
def quantizedUpdate {X A : Type*} {s : ℕ}
    (F : A → X → X) (z : Fin s → X) (Q : X → Fin s) : A → Fin s → Fin s :=
  fun a i => Q (F a (z i))

/-- Read the original observation at the stored center. -/
def quantizedReadout {X Y : Type*} {s : ℕ}
    (o : X → Y) (z : Fin s → X) : Fin s → Y := fun i => o (z i)

/-- Every finite action word has the geometric output-error bound. Under contraction,
the same machine has the uniform bound. The supplied quantizer initializes the machine;
no positivity of its radius or nonemptiness of any carrier is assumed. -/
theorem quantized_word_approximation
    {X : Type u} {Y : Type v} {A : Type w} [MetricSpace X] [MetricSpace Y]
    (F : A → X → X) (o : X → Y) (s : ℕ)
    (z : Fin s → X) (Q : X → Fin s) (L M δ : ℝ)
    (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hF : ∀ a x y, dist (F a x) (F a y) ≤ L * dist x y)
    (ho : ∀ x y, dist (o x) (o y) ≤ M * dist x y)
    (hQ : ∀ x, dist x (z (Q x)) ≤ δ) (x : X) (word : List A) :
    dist (o (runWord F word x))
        (quantizedReadout o z (runWord (quantizedUpdate F z Q) word (Q x))) ≤
      M * δ * ∑ j ∈ Finset.range (word.length + 1), L ^ j ∧
    (L < 1 →
      dist (o (runWord F word x))
          (quantizedReadout o z (runWord (quantizedUpdate F z Q) word (Q x))) ≤
        M * δ / (1 - L)) := by
  have trajectory : ∀ (w : List A) (y : X) (i : Fin s),
      dist (runWord F w y) (z (runWord (quantizedUpdate F z Q) w i)) ≤
        L ^ w.length * dist y (z i) + δ * ∑ j ∈ Finset.range w.length, L ^ j := by
    intro w
    induction w with
    | nil => intro y i; simp [runWord]
    | cons a w ih =>
      intro y i
      have step : dist (F a y) (z (quantizedUpdate F z Q a i)) ≤
          L * dist y (z i) + δ :=
        (dist_triangle (F a y) (F a (z i))
          (z (Q (F a (z i))))).trans (add_le_add (hF a y (z i)) (hQ (F a (z i))))
      calc
        dist (runWord F (a :: w) y)
            (z (runWord (quantizedUpdate F z Q) (a :: w) i)) ≤
            L ^ w.length * dist (F a y) (z (quantizedUpdate F z Q a i)) +
              δ * ∑ j ∈ Finset.range w.length, L ^ j :=
          ih (F a y) (quantizedUpdate F z Q a i)
        _ ≤ L ^ w.length * (L * dist y (z i) + δ) +
              δ * ∑ j ∈ Finset.range w.length, L ^ j :=
          add_le_add (mul_le_mul_of_nonneg_left step (pow_nonneg hL _)) le_rfl
        _ = L ^ (a :: w).length * dist y (z i) +
              δ * ∑ j ∈ Finset.range (a :: w).length, L ^ j := by
          simp only [List.length_cons, Finset.sum_range_succ, pow_succ]
          ring
  have stateBound :
      dist (runWord F word x) (z (runWord (quantizedUpdate F z Q) word (Q x))) ≤
        δ * ∑ j ∈ Finset.range (word.length + 1), L ^ j := by
    calc
      _ ≤ L ^ word.length * dist x (z (Q x)) +
          δ * ∑ j ∈ Finset.range word.length, L ^ j := trajectory word x (Q x)
      _ ≤ L ^ word.length * δ + δ * ∑ j ∈ Finset.range word.length, L ^ j :=
        add_le_add (mul_le_mul_of_nonneg_left (hQ x) (pow_nonneg hL _)) le_rfl
      _ = δ * ∑ j ∈ Finset.range (word.length + 1), L ^ j := by
        rw [Finset.sum_range_succ]
        ring
  have finiteBound :
      dist (o (runWord F word x))
          (quantizedReadout o z (runWord (quantizedUpdate F z Q) word (Q x))) ≤
        M * δ * ∑ j ∈ Finset.range (word.length + 1), L ^ j := by
    calc
      _ ≤ M * dist (runWord F word x)
          (z (runWord (quantizedUpdate F z Q) word (Q x))) := ho _ _
      _ ≤ M * (δ * ∑ j ∈ Finset.range (word.length + 1), L ^ j) :=
        mul_le_mul_of_nonneg_left stateBound hM
      _ = _ := (mul_assoc _ _ _).symm
  refine ⟨finiteBound, fun hcontract => finiteBound.trans ?_⟩
  have hδ : 0 ≤ δ := dist_nonneg.trans (hQ x)
  have hsum : (∑ j ∈ Finset.range (word.length + 1), L ^ j) ≤ 1 / (1 - L) := by
    apply (le_div_iff₀ (sub_pos.mpr hcontract)).mpr
    rw [geom_sum_mul_neg]
    exact sub_le_self _ (pow_nonneg hL _)
  calc
    M * δ * (∑ j ∈ Finset.range (word.length + 1), L ^ j) ≤
        M * δ * (1 / (1 - L)) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hM hδ)
    _ = M * δ / (1 - L) := by ring

end D5.S3.ObserverMemory.Prediction.QuantizedWordApproximation
