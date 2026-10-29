/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/FeasibleWordKernels
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/FeasibleWordKernels
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original word conditionals factor through feasible normalized transitions with structural zeros. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureScreening
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveRectangleLaw
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators Classical
open Matrix MeasureTheory
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureCylinders
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureScreening

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Rectangles.FeasibleWordKernels
variable {H : Type*} [Fintype H]

/-- The original likelihood of a word followed by an arbitrary terminal message. -/
def message (θ : Presentation H) (n : ℕ) (w : Fin n → Bool) (z : H → ℝ) : H → ℝ :=
  wordMatrix θ.matrix n w *ᵥ z

/-- Zero-denominator rows are zero, and are never asserted to be probability rows. -/
def transition (θ : Presentation H) (x : Bool) (z : H → ℝ) : Matrix H H ℝ :=
  fun s t => θ.matrix x s t * z t / (θ.matrix x *ᵥ z) s

/-- Chronological normalized transitions, with each suffix evaluated before normalization. -/
def forwardProduct (θ : Presentation H) :
    (n : ℕ) → (Fin n → Bool) → (H → ℝ) → Matrix H H ℝ
  | 0, _, _ => 1
  | n+1, w, z => transition θ (w 0) (message θ n (Fin.tail w) z) *
      forwardProduct θ n (Fin.tail w) z

/-- The same chronological transitions evaluated on one original hidden path. -/
def forwardPath (θ : Presentation H) :
    (n : ℕ) → (Fin n → Bool) → (H → ℝ) → (Fin (n+1) → H) → ℝ
  | 0, _, _, _ => 1
  | n+1, w, z, h => transition θ (w 0) (message θ n (Fin.tail w) z) (h 0) (h 1) *
      forwardPath θ n (Fin.tail w) z (Fin.tail h)

private theorem message_nonneg (θ : Presentation H) (n : ℕ) (w : Fin n → Bool)
    (z : H → ℝ) (hz : ∀ s, 0 ≤ z s) : ∀ s, 0 ≤ message θ n w z s := by
  intro s
  exact Finset.sum_nonneg fun t _ => mul_nonneg
    (by rw [← PositiveRectangleLaw.product_ofFn]; exact PositiveRectangleLaw.product_nonneg θ _ s t)
    (hz t)

private theorem weighted_transition (θ : Presentation H) (x : Bool) (z : H → ℝ)
    (hz : ∀ s, 0 ≤ z s) (s t : H) :
    (θ.matrix x *ᵥ z) s * transition θ x z s t = θ.matrix x s t * z t := by
  have hn (t : H) : 0 ≤ θ.matrix x s t * z t := mul_nonneg (θ.matrix_nonneg x s t) (hz t)
  by_cases he : (θ.matrix x *ᵥ z) s = 0
  · have ht : θ.matrix x s t * z t = 0 :=
      le_antisymm (he ▸ Finset.single_le_sum (fun t _ => hn t) (Finset.mem_univ t)) (hn t)
    simp [he,ht]
  · dsimp [transition]
    field_simp

private theorem weighted_product (θ : Presentation H) (z : H → ℝ) (hz : ∀ s, 0 ≤ z s)
    (n : ℕ) (w : Fin n → Bool) (s t : H) :
    message θ n w z s * forwardProduct θ n w z s t = wordMatrix θ.matrix n w s t * z t := by
  induction n generalizing w s with
  | zero =>
    simp only [message,wordMatrix,Matrix.one_mulVec,forwardProduct,Matrix.one_apply]
    split_ifs with h
    · subst t; ring
    · ring
  | succ n ih =>
    have hm : message θ (n+1) w z = θ.matrix (w 0) *ᵥ message θ n (Fin.tail w) z := by
      simp only [message,wordMatrix,Matrix.mulVec_mulVec]
    rw [forwardProduct,Matrix.mul_apply,Finset.mul_sum,Matrix.mul_apply,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    rw [hm]
    calc
      _ = ((θ.matrix (w 0) *ᵥ message θ n (Fin.tail w) z) s *
          transition θ (w 0) (message θ n (Fin.tail w) z) s r) *
          forwardProduct θ n (Fin.tail w) z r t := by ring
      _ = (θ.matrix (w 0) s r * message θ n (Fin.tail w) z r) *
          forwardProduct θ n (Fin.tail w) z r t := by
        rw [weighted_transition θ _ _ (message_nonneg θ n _ z hz)]
      _ = θ.matrix (w 0) s r * (wordMatrix θ.matrix n (Fin.tail w) r t * z t) := by
        rw [mul_assoc,ih]
      _ = _ := by ring

private theorem weighted_path (θ : Presentation H) (z : H → ℝ) (hz : ∀ s, 0 ≤ z s)
    (n : ℕ) (w : Fin n → Bool) (h : Fin (n+1) → H) :
    message θ n w z (h 0) * forwardPath θ n w z h =
      pathMass θ.matrix n h w * z (h (Fin.last n)) := by
  induction n with
  | zero => simp [message,wordMatrix,forwardPath,pathMass]
  | succ n ih =>
    have hm : message θ (n+1) w z = θ.matrix (w 0) *ᵥ message θ n (Fin.tail w) z := by
      simp only [message,wordMatrix,Matrix.mulVec_mulVec]
    rw [forwardPath,hm,← mul_assoc,weighted_transition θ _ _ (message_nonneg θ n _ z hz)]
    rw [mul_assoc,ih (Fin.tail w) (Fin.tail h),path_step]
    rfl

/-- On precisely the positive-likelihood states, the chronological product is the original
word kernel, is a probability row, and assigns zero mass to infeasible endpoints. -/
theorem feasible_word_product (θ : Presentation H) (n : ℕ) (w : Fin n → Bool)
    (z : H → ℝ) (hz : ∀ s, 0 ≤ z s) (s : H) (hs : 0 < message θ n w z s) :
    (∀ t, forwardProduct θ n w z s t =
      wordMatrix θ.matrix n w s t * z t / message θ n w z s) ∧
    (∑ t, forwardProduct θ n w z s t) = 1 ∧
    (∀ t, z t = 0 → forwardProduct θ n w z s t = 0) := by
  have he (t : H) := (eq_div_iff hs.ne').mpr
    (by simpa only [mul_comm] using weighted_product θ z hz n w s t)
  refine ⟨he,?_,?_⟩
  · simp_rw [he]
    rw [← Finset.sum_div]
    exact div_self hs.ne'
  · intro t ht
    rw [he,ht,mul_zero,zero_div]

section Actual
variable [MeasurableSpace H] [MeasurableSingletonClass H]

/-- The actual observed word and future, with the initial hidden state retained. -/
def startingRecord (t : ℤ) (m n : ℕ) (s : H) (w : Fin m → Bool) (v : Fin n → Bool) :
    Set (PathSpace H) :=
  state t ⁻¹' {s} ∩ Prod.snd ⁻¹' visibleCylinder t (m+n) (Fin.append w v)

private theorem starting_mass (θ : Presentation H) (J : Measure (PathSpace H))
    [IsProbabilityMeasure J] (hc : HasOriginalCylinders J θ) (t : ℤ) (m n : ℕ)
    (s : H) (w : Fin m → Bool) (v : Fin n → Bool) :
    J.real (startingRecord t m n s w v) =
      θ.initial s * message θ m w (fun h => futureMass θ.matrix h n v) s := by
  have hm := future_state_mass θ J hc t s (m+n) (Fin.append w v)
  have he : (state t ⁻¹' {s}) ∩ (future t ⁻¹' (readPrefix (m+n) ⁻¹' {Fin.append w v})) =
      startingRecord t m n s w v := by
    ext z
    simp [startingRecord,future,readPrefix,visibleCylinder,funext_iff]
  rw [he] at hm
  rw [hm]
  congr 1
  have hp : wordMatrix θ.matrix (m+n) (Fin.append w v) =
      wordMatrix θ.matrix m w * wordMatrix θ.matrix n v := by
    simp only [← PositiveRectangleLaw.product_ofFn, List.ofFn_fin_append,
      PositiveRectangleLaw.product,List.map_append,List.prod_append]
  simp only [futureMass,message,hp,Matrix.mul_apply,Finset.sum_mul,Finset.mul_sum,Matrix.mulVec,dotProduct]
  exact Finset.sum_comm

/-- On the same original law, a positive observed record has exactly the chronological
normalized hidden-path probability. No positive-coordinate hypothesis is imposed. -/
theorem actual_conditioned_word_path (θ : Presentation H) (J : Measure (PathSpace H))
    [IsProbabilityMeasure J] (hc : HasOriginalCylinders J θ) (t : ℤ) (m n : ℕ)
    (h : Fin (m+1) → H) (w : Fin m → Bool) (v : Fin n → Bool)
    (hpos : 0 < J.real (startingRecord t m n (h 0) w v)) :
    J.real (MarkedPredictiveQuotient.cylinder t m h w ∩
      Prod.snd ⁻¹' visibleCylinder (t+m) n v) /
      J.real (startingRecord t m n (h 0) w v) =
        forwardPath θ m w (fun s => futureMass θ.matrix s n v) h := by
  let z : H → ℝ := fun s => futureMass θ.matrix s n v
  have hz (s : H) : 0 ≤ z s := by
    dsimp [z,futureMass]
    exact Finset.sum_nonneg fun j _ => by
      rw [← PositiveRectangleLaw.product_ofFn]
      exact PositiveRectangleLaw.product_nonneg θ _ s j
  have hm := past_future_mass θ J hc (t+m) m n h w v
  simp only [add_sub_cancel_right] at hm
  rw [starting_mass θ J hc] at hpos
  rw [hm,starting_mass θ J hc]
  have he := weighted_path θ z hz m w h
  change message θ m w z (h 0) * forwardPath θ m w z h = _ at he
  change _ / (θ.initial (h 0) * message θ m w z (h 0)) = _
  apply (div_eq_iff (ne_of_gt hpos)).mpr
  rw [mul_comm (forwardPath θ m w z h),mul_assoc,he]
  ring

#print axioms feasible_word_product
#print axioms actual_conditioned_word_path
end Actual
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Rectangles.FeasibleWordKernels
