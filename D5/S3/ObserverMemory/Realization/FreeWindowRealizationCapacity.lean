/- GID: D5/S3/ObserverMemory/Realization/FreeWindowRealizationCapacity
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Realization/FreeWindowRealizationCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary representative successors attain the exact finite-window state capacity. -/

import D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
import Mathlib.SetTheory.Cardinal.NatCard

namespace D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity

open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v z

/-- The actually occurring words through time `n`. -/
abbrev WindowState {S : Type u} {A : Type v} (D : S → S) (q : S → A) (n : ℕ) :=
  Set.range (futureReadoutWord D q n)

/-- Prepare the complete finite output word once. -/
def prepare {S : Type u} {A : Type v} (D : S → S) (q : S → A) (n : ℕ) :
    S → WindowState D q n := Set.rangeFactorization (futureReadoutWord D q n)

/-- The output of a word state is its first letter. -/
def firstLetter {S : Type u} {A : Type v} {D : S → S} {q : S → A} {n : ℕ}
    (w : WindowState D q n) : A := w.1 0

/-- Choose a source representative, update it, and prepare its next word. -/
def representativeUpdate {S : Type u} {A : Type v} (D : S → S) (q : S → A) (n : ℕ)
    (r : WindowState D q n → S) : WindowState D q n → WindowState D q n :=
  fun w => prepare D q n (D (r w))

/-- One fixed internal update and readout reproduce the requested finite horizon. -/
def WindowCorrect {S : Type u} {A : Type v} {M : Type z}
    (D : S → S) (q : S → A) (n : ℕ) (I : S → M) (F : M → M) (g : M → A) : Prop :=
  ∀ s (j : Fin (n + 1)), g (F^[j.val] (I s)) = q (D^[j.val] s)

/-- Adjacent overlapping labels determine the whole output window, on any
state space and for every horizon, including the empty overlap at horizon zero. -/
theorem overlap_output_window {X : Type u} {A : Type v} (n : ℕ)
    (U : X → X) (L : X → Fin (n + 1) → A)
    (hoverlap : ∀ x k (hk : k < n),
      L (U x) ⟨k, by omega⟩ = L x ⟨k + 1, by omega⟩) :
    ∀ x (j : Fin (n + 1)), L (U^[j.val] x) 0 = L x j := by
  have hshift : ∀ j k : ℕ, ∀ h : k + j ≤ n, ∀ x : X,
      L (U^[j] x) ⟨k, by omega⟩ = L x ⟨k + j, by omega⟩ := by
    intro j
    induction j with
    | zero => intro k h x; rfl
    | succ j ih =>
      intro k h x
      rw [Function.iterate_succ_apply']
      calc
        L (U (U^[j] x)) ⟨k, by omega⟩ =
            L (U^[j] x) ⟨k + 1, by omega⟩ := hoverlap _ k (by omega)
        _ = L x ⟨k + 1 + j, by omega⟩ := ih (k + 1) (by omega) x
        _ = L x ⟨k + (j + 1), by omega⟩ := by
          simp only [Nat.add_assoc, Nat.add_comm 1 j]
  intro x j
  simpa using hshift j.val 0 (by omega) x

/-- The number of realized words is a lower bound for every finite total carrier.
Every choice of one representative per word attains the bound, with surjective
preparation. At all later times, the complete output window is still its state label.
A four-state source at horizon zero witnesses failure to commute with the source. -/
theorem free_window_realization_capacity {S : Type u} {A : Type v} [Finite S]
    (D : S → S) (q : S → A) (n : ℕ) :
    (∀ (M : Type z) [Finite M] (I : S → M) (F : M → M) (g : M → A),
      WindowCorrect D q n I F g → Nat.card (WindowState D q n) ≤ Nat.card M) ∧
    (Finite (WindowState D q n) ∧ Function.Surjective (prepare D q n)) ∧
    (∃ r : WindowState D q n → S, Function.RightInverse r (prepare D q n)) ∧
    (∀ r : WindowState D q n → S, Function.RightInverse r (prepare D q n) →
      WindowCorrect D q n (prepare D q n) (representativeUpdate D q n r) firstLetter ∧
      ∀ (w : WindowState D q n) (t : ℕ),
        futureReadoutWord (representativeUpdate D q n r) firstLetter n
            ((representativeUpdate D q n r)^[t] w) =
          ((representativeUpdate D q n r)^[t] w).1) ∧
    (∃ (D₀ : Bool × Bool → Bool × Bool) (q₀ : Bool × Bool → Bool)
        (r₀ : WindowState D₀ q₀ 0 → Bool × Bool),
      Function.RightInverse r₀ (prepare D₀ q₀ 0) ∧
      prepare D₀ q₀ 0 ∘ D₀ ≠ representativeUpdate D₀ q₀ 0 r₀ ∘ prepare D₀ q₀ 0) := by
  classical
  have honto : Function.Surjective (prepare D q n) := Set.rangeFactorization_surjective
  refine ⟨?_, ⟨inferInstance, honto⟩,
    ⟨Function.surjInv honto, Function.rightInverse_surjInv honto⟩, ?_, ?_⟩
  · intro M _ I F g hcorrect
    let r : WindowState D q n → S := Function.surjInv honto
    have hr : Function.RightInverse r (prepare D q n) :=
      Function.rightInverse_surjInv honto
    apply Nat.card_le_card_of_injective (I ∘ r)
    intro w v heq
    apply Subtype.ext
    have hw := congrArg Subtype.val (hr w)
    have hv := congrArg Subtype.val (hr v)
    rw [← hw, ← hv]
    funext j
    change q (D^[j.val] (r w)) = q (D^[j.val] (r v))
    rw [← hcorrect (r w) j, ← hcorrect (r v) j]
    exact congrArg (fun x => g (F^[j.val] x)) heq
  · intro r hr
    let U := representativeUpdate D q n r
    have hoverlap (w : WindowState D q n) (k : ℕ) (hk : k < n) :
        (U w).1 ⟨k, by omega⟩ = w.1 ⟨k + 1, by omega⟩ := by
      have hlabel := congrArg (fun v : WindowState D q n => v.1 ⟨k + 1, by omega⟩)
        (hr w)
      simpa only [U, representativeUpdate, prepare, Set.rangeFactorization,
        futureReadoutWord, Function.iterate_succ_apply] using hlabel
    have hword (w : WindowState D q n) : futureReadoutWord U firstLetter n w = w.1 := by
      funext j
      exact overlap_output_window n U Subtype.val hoverlap w j
    constructor
    · intro s j
      exact congrFun (hword (prepare D q n s)) j
    · intro w t
      exact hword (U^[t] w)
  · let D₀ : Bool × Bool → Bool × Bool := fun s => (s.2, s.2)
    let q₀ : Bool × Bool → Bool := Prod.fst
    let r₀ : WindowState D₀ q₀ 0 → Bool × Bool := fun w => (w.1 0, false)
    refine ⟨D₀, q₀, r₀, ?_, ?_⟩
    · intro w
      apply Subtype.ext
      funext j
      have hj : j = 0 := Fin.ext (by omega)
      subst j
      rfl
    · intro hcommute
      have h := congrArg (fun f => (f (false, true)).1 0) hcommute
      change (true : Bool) = false at h
      exact Bool.noConfusion h

#print axioms overlap_output_window
#print axioms free_window_realization_capacity

end D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity
