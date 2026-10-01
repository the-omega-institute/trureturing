/- GID: D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The two consecutive window readouts have the exact even-modulus kernel. -/

import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.ImmediateWindowStateCapacity

/- The state-capacity construction uses the two readouts attached to the
   three-bit Fibonacci window.  This is the q and q S pair from the source
   contract, with S = M^3. -/
def windowObserve {m : ℕ} (x : ZMod m × ZMod m) : ZMod m × ZMod m :=
  (2 * x.1 + 3 * x.2, 8 * x.1 + 13 * x.2)

/-
proof_shape: window_observe_kernel: content
escape_witness: the active path of `window_observe_kernel` derives the second
  coordinate by the nontrivial integer combination `h₂ - 4 * h₁`, then derives
  the remaining two-torsion condition.  This determinant-two kernel computation
  is not an instance, projection, or normalization of a pinned declaration.
admission_basis: escape-witness
Direct frozen dependencies: none (pinned Mathlib only)
-/
/- This is the actual escape witness for the proposed capacity theorem: the
   determinant-two observation loses exactly the 2-torsion in the first
   composition coordinate. -/
theorem window_observe_kernel (m : ℕ) (x : ZMod m × ZMod m) :
    windowObserve x = 0 ↔
      ∃ a : ZMod m, x = (a, 0) ∧ (2 : ZMod m) * a = 0 := by
  constructor
  · rintro h
    have h₁ : 2 * x.1 + 3 * x.2 = 0 := by
      simpa [windowObserve] using congrArg Prod.fst h
    have h₂ : 8 * x.1 + 13 * x.2 = 0 := by
      simpa [windowObserve] using congrArg Prod.snd h
    refine ⟨x.1, ?_, ?_⟩
    · apply Prod.ext
      · rfl
      · have hb : x.2 = 0 := by
          linear_combination h₂ - 4 * h₁
        exact hb
    · have hb : x.2 = 0 := by
        linear_combination h₂ - 4 * h₁
      rw [hb] at h₁
      simpa using h₁
  · rintro ⟨a, rfl, ha⟩
    apply Prod.ext
    · simp [windowObserve, ha]
    · simp [windowObserve]
      linear_combination 4 * ha

#print axioms window_observe_kernel

end D5.S3.Arith.FibonacciAtomic.ImmediateWindowStateCapacity
