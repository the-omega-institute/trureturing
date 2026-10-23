/- GID: D5/S3/Observer/LinearMemory/FiniteWordReachability
   generality: G
   mirror-B: D5/B/S3/Observer/LinearMemory/FiniteWordReachability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered endomorphism words reach the full seed span by the reachable rank gap. -/

import D5.S3.Quantum.PredictionDepth.FiniteSequentialWordCertificate
import Mathlib.Order.Iterate

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.LinearMemory.FiniteWordReachability

universe u v w
variable {K : Type u} {E : Type v} {I : Type w}
  [DivisionRing K] [AddCommGroup E] [Module K E]

/-- Products use left composition: the head of a word acts after its tail. -/
def boundedSpan (A : I → Module.End K E) (U : Submodule K E) (n : ℕ) :
    Submodule K E :=
  Submodule.span K {x | ∃ word : List I, word.length ≤ n ∧
    ∃ z ∈ U, x = (word.map A).prod z}

/-- The span of every finite ordered word applied to the seed submodule. -/
def reachableSpan (A : I → Module.End K E) (U : Submodule K E) : Submodule K E :=
  Submodule.span K {x | ∃ word : List I, ∃ z ∈ U, x = (word.map A).prod z}

def step (A : I → Module.End K E) (S : Submodule K E) : Submodule K E :=
  S ⊔ ⨆ i, S.map (A i)

private theorem bounded_zero (A : I → Module.End K E) (U : Submodule K E) :
    boundedSpan A U 0 = U := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨word, hword, z, hz, rfl⟩
    have : word = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hword)
    subst word
    simpa using hz
  · intro x hx
    exact Submodule.subset_span ⟨[], by simp, x, hx, by simp⟩

private theorem step_bounded (A : I → Module.End K E) (U : Submodule K E) (n : ℕ) :
    step A (boundedSpan A U n) = boundedSpan A U (n + 1) := by
  apply le_antisymm
  · refine sup_le (Submodule.span_mono ?_) (iSup_le fun i => ?_)
    · rintro x ⟨word, hw, z, hz, rfl⟩
      exact ⟨word, hw.trans (Nat.le_succ n), z, hz, rfl⟩
    · rw [boundedSpan, Submodule.map_span]
      apply Submodule.span_le.mpr
      rintro x ⟨y, ⟨word, hw, z, hz, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨i :: word, by simpa using Nat.succ_le_succ hw,
        z, hz, by simp [Module.End.mul_apply]⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨word, hw, z, hz, rfl⟩
    cases word with
    | nil =>
        apply le_sup_left (b := ⨆ i, (boundedSpan A U n).map (A i))
        exact Submodule.subset_span ⟨[], Nat.zero_le n, z, hz, rfl⟩
    | cons i word =>
        have htail : word.length ≤ n := by simpa using hw
        apply le_sup_right (a := boundedSpan A U n)
        apply (le_iSup (fun j => (boundedSpan A U n).map (A j)) i)
        exact ⟨(word.map A).prod z,
          Submodule.subset_span ⟨word, htail, z, hz, rfl⟩,
          by simp [Module.End.mul_apply]⟩

theorem iterate_eq_bounded (A : I → Module.End K E) (U : Submodule K E)
    (n : ℕ) : (step A)^[n] U = boundedSpan A U n := by
  induction n with
  | zero => exact (bounded_zero A U).symm
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      exact step_bounded A U n

theorem bounded_le_reachable (A : I → Module.End K E) (U : Submodule K E)
    (n : ℕ) : boundedSpan A U n ≤ reachableSpan A U := by
  apply Submodule.span_mono
  rintro x ⟨word, _, z, hz, rfl⟩
  exact ⟨word, z, hz, rfl⟩

private theorem reachable_le_fixed (A : I → Module.End K E) (U S : Submodule K E)
    (hU : U ≤ S) (hfixed : step A S = S) : reachableSpan A U ≤ S := by
  apply Submodule.span_le.mpr
  rintro x ⟨word, z, hz, rfl⟩
  induction word with
  | nil => simpa using hU hz
  | cons i word ih =>
      rw [← hfixed]
      apply le_sup_right (a := S)
      apply (le_iSup (fun j => S.map (A j)) i)
      exact ⟨(word.map A).prod z, ih, by simp [Module.End.mul_apply]⟩

/-- The full reachable space is attained by the reachable rank minus the seed
rank. The alphabet can be empty or infinite, and the seed can be zero. -/
theorem bounded_span_eq_reachable [FiniteDimensional K E]
    (A : I → Module.End K E) (U : Submodule K E) :
    boundedSpan A U (Module.finrank K (reachableSpan A U) - Module.finrank K U) =
      reachableSpan A U := by
  let V := fun n : ℕ => (step A)^[n] U
  have hmono : Monotone V := fun _ _ h =>
    Function.monotone_iterate_of_id_le (fun S => (le_sup_left : S ≤ step A S)) h U
  have hbound : ∀ n, V n ≤ reachableSpan A U := by
    intro n
    change (step A)^[n] U ≤ reachableSpan A U
    rw [iterate_eq_bounded]
    exact bounded_le_reachable A U n
  obtain ⟨m, hm, hrank⟩ :=
    D5.S3.Quantum.PredictionDepth.FiniteSequentialWordCertificate.bounded_monotone_has_equal_step
      (fun n => Module.finrank K (V n)) (Module.finrank K (reachableSpan A U))
      (fun _ _ h => Submodule.finrank_mono (hmono h))
      (fun n => Submodule.finrank_mono (hbound n))
  have hplateau : V m = V (m + 1) :=
    Submodule.eq_of_le_of_finrank_eq (hmono (Nat.le_succ m)) hrank
  have hfixed : step A (V m) = V m := by
    simpa only [V, Function.iterate_succ_apply'] using hplateau.symm
  have hreachable : reachableSpan A U = V m :=
    le_antisymm (reachable_le_fixed A U (V m) (hmono (Nat.zero_le m)) hfixed)
      (hbound m)
  have hm' : m ≤ Module.finrank K (reachableSpan A U) - Module.finrank K U := hm
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hm'
  rw [← iterate_eq_bounded, hd, Nat.add_comm m d, Function.iterate_add_apply]
  exact (Function.iterate_fixed hfixed d).trans hreachable.symm

#print axioms bounded_span_eq_reachable

end D5.S3.Observer.LinearMemory.FiniteWordReachability
