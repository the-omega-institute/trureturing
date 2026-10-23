/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeAlphaSpineObservation
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Native alpha-spine observation locality with the shifted Fibonacci support boundary. -/

import D5.S3.Arith.FibonacciAtomic.Observer.ActualFibonacciSupportChain
import D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns
import D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeAlphaSpineObservation

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)
open ActualFibonacciSupportChain


/-- The original hole address reaches the supplied subtree in the alpha-sibling context. -/
theorem native_alpha_spine_at (p : Address) (x : Source) :
      subtree p (p.foldr (fun b t => if b then .mul (.of true) t else .mul t (.of true)) x) = some x := by
    revert x
    induction p with
    | nil => simp [subtree]
    | cons b p ih => cases b <;> simp only [List.foldr, subtree] <;> exact ih

/-- The three native sources on an alpha-spine hole have distinct original
replies, equal current replies outside the hole cone, and the ABT44 support
radius shifted by the hole depth. -/
theorem native_alpha_spine_observation :
    ∀ (p : Address) (k : Nat), 1 ≤ k →
    let E := fun (p : Address) (x : Source) =>
      p.foldr (fun b t => if b then .mul (.of true) t else .mul t (.of true)) x
    let U := E p (.of true)
    let V := E p (.of false)
    let W := E p (.mul (.of true) (.of true))
    readout p U = .alpha ∧ readout p V = .beta ∧ readout p W = .branch ∧
      (∀ q : Address, ¬ p.IsPrefix q →
        readout q (substitution^[2*k] U) = readout q (substitution^[2*k] V) ∧
        readout q (substitution^[2*k] V) = readout q (substitution^[2*k] W)) ∧
      (∀ q : Address, q.length ≤ p.length + k →
        (readout q (substitution^[2*k] U) ≠ .absent ↔
          readout q (substitution^[2*k] V) ≠ .absent) ∧
        (readout q (substitution^[2*k] V) ≠ .absent ↔
          readout q (substitution^[2*k] W) ≠ .absent)) ∧
      (∀ q : Address,
        ¬(readout q (substitution^[2*k] U) ≠ .absent ↔
          readout q (substitution^[2*k] V) ≠ .absent) →
        p.length + k + 1 ≤ q.length) ∧
      (∀ q : Address,
        ¬(readout q (substitution^[2*k] V) ≠ .absent ↔
          readout q (substitution^[2*k] W) ≠ .absent) →
        p.length + k + 1 ≤ q.length) := by
  intro p k hk
  dsimp
  have original :
      readout p (p.foldr (fun b t => if b then .mul (.of true) t else .mul t (.of true)) (.of true)) = .alpha ∧
      readout p (p.foldr (fun b t => if b then .mul (.of true) t else .mul t (.of true)) (.of false)) = .beta ∧
      readout p (p.foldr (fun b t => if b then .mul (.of true) t else .mul t (.of true)) (.mul (.of true) (.of true))) = .branch := by
    induction p with
    | nil => simp [readout]
    | cons b p ih =>
      cases b <;> simp only [List.foldr, readout]
      · exact ih
      · exact ih

  have spine_at := native_alpha_spine_at p
  have outside (n : Nat) (x y : Source) (q : Address) (h : ¬ p.IsPrefix q) :
      readout q (substitution^[n] (p.foldr (fun b t => if b then .mul (.of true) t else .mul t (.of true)) x)) =
        readout q (substitution^[n] (p.foldr (fun b t => if b then .mul (.of true) t else .mul t (.of true)) y)) := by
    have iter_mul (n : Nat) (a b : Source) :
        substitution^[n] (.mul a b) = .mul (substitution^[n] a) (substitution^[n] b) :=
      Function.Semiconj₂.iterate (fun s t => substitution.map_mul s t) n a b
    clear original spine_at
    induction p generalizing n q with
    | nil => exact False.elim (h List.nil_prefix)
    | cons b p ih =>
      cases q with
      | nil =>
        cases b with
        | false =>
          have hb : ∀ n (z : Source), readout [] (substitution^[n] (.mul z (.of true))) = .branch := by
            intro n z
            induction n with
            | zero => simp [readout]
            | succ n ih => simp [Function.iterate_succ_apply', substitution, readout]
          exact (hb n _).trans (hb n _).symm
        | true =>
          have hb : ∀ n (z : Source), readout [] (substitution^[n] (.mul (.of true) z)) = .branch := by
            intro n z
            induction n with
            | zero => simp [readout]
            | succ n ih => simp [Function.iterate_succ_apply', substitution, readout]
          exact (hb n _).trans (hb n _).symm
      | cons c q =>
        cases b <;> cases c
        · simp [List.foldr]
          simp only [readout]
          exact ih n q (by simpa using h)
        · simp [List.foldr]
          simp only [readout]
        · simp [List.foldr]
          simp only [readout]
        · simp [List.foldr]
          simp only [readout]
          exact ih n q (by simpa using h)
  have at_prefix (n : Nat) (x : Source) (r : Address) :
      readout (p ++ r) (substitution^[n] (p.foldr (fun b t => if b then .mul (.of true) t else .mul t (.of true)) x)) =
        readout r (substitution^[n] x) := by
    have ht := NativeDepthPatterns.original_present_transport n p
      (p.foldr (fun b t => if b then .mul (.of true) t else .mul t (.of true)) x) x (spine_at x)
    have app := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      p r (substitution^[n] (p.foldr (fun b t => if b then .mul (.of true) t else .mul t (.of true)) x))
    rw [ht] at app
    simpa using app
  have chain := actual_fibonacci_support_chain k hk
  have hab : substitution^[2*k] (.of false) = substitution^[2*k+1] (.of true) := by
    symm
    rw [show 2*k+1 = (2*k)+1 by omega, Function.iterate_succ_apply]
    simp [substitution]
  have hbr : substitution^[2*k] (.mul (.of true) (.of true)) =
      FreeMagma.mul (substitution^[2*k] (.of true)) (substitution^[2*k] (.of true)) :=
    Function.Semiconj₂.iterate (fun s t => substitution.map_mul s t) (2*k) _ _
  have raw : ∀ q : Address, ¬ p.IsPrefix q →
      readout q (substitution^[2*k] (p.foldr (fun b t => if b then .mul (.of true) t else .mul t (.of true)) (.of true))) =
        readout q (substitution^[2*k] (p.foldr (fun b t => if b then .mul (.of true) t else .mul t (.of true)) (.of false))) ∧
      readout q (substitution^[2*k] (p.foldr (fun b t => if b then .mul (.of true) t else .mul t (.of true)) (.of false))) =
        readout q (substitution^[2*k] (p.foldr (fun b t => if b then .mul (.of true) t else .mul t (.of true)) (.mul (.of true) (.of true)))) := by
    intro q hq
    exact ⟨outside _ _ _ q hq, outside _ _ _ q hq⟩
  have support : ∀ q : Address, q.length ≤ p.length + k →
      (readout q (substitution^[2*k] (p.foldr (fun b t => if b then .mul (.of true) t else .mul t (.of true)) (.of true))) ≠ .absent ↔
        readout q (substitution^[2*k] (p.foldr (fun b t => if b then .mul (.of true) t else .mul t (.of true)) (.of false))) ≠ .absent) ∧
      (readout q (substitution^[2*k] (p.foldr (fun b t => if b then .mul (.of true) t else .mul t (.of true)) (.of false))) ≠ .absent ↔
        readout q (substitution^[2*k] (p.foldr (fun b t => if b then .mul (.of true) t else .mul t (.of true)) (.mul (.of true) (.of true)))) ≠ .absent) := by
    intro q hq
    by_cases hpq : p.IsPrefix q
    · rcases hpq with ⟨r, rfl⟩
      have hr : r.length ≤ k := by simpa [List.length_append] using hq
      have hc := chain.2.2 r hr
      rw [at_prefix, at_prefix, at_prefix]
      rw [hab, hbr]
      simpa [Set.mem_setOf_eq] using hc
    · have ho := outside (2*k) (.of true) (.of false) q hpq
      have hw := outside (2*k) (.of false) (.mul (.of true) (.of true)) q hpq
      exact ⟨by rw [ho], by rw [hw]⟩
  refine ⟨original.1, original.2.1, original.2.2, raw, support, ?_, ?_⟩
  · intro q hq
    by_contra hn
    have short : q.length ≤ p.length + k := by omega
    exact hq (support q short).1
  · intro q hq
    by_contra hn
    have short : q.length ≤ p.length + k := by omega
    exact hq (support q short).2

end D5.S3.Arith.FibonacciAtomic.Observer.NativeAlphaSpineObservation

#print axioms D5.S3.Arith.FibonacciAtomic.Observer.NativeAlphaSpineObservation.native_alpha_spine_observation
