/- GID: D5/S3/Quantum/Entanglement/Marginals/IndependentWordMarginals
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/IndependentWordMarginals
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The common deletion kernel on independent words is governed by agreement on edges. -/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.Marginals.IndependentWordMarginals

open Function (update)

variable {V : Type*} [DecidableEq V]

/-- An independent-word matrix is invisible in all one-site deletion traces exactly when its
entries vanish on agreement at non-isolated vertices and have opposite signs across each
simultaneous isolated-site update. -/
theorem deletion_kernel_iff (G : SimpleGraph V) (R : Matrix (V → Bool) (V → Bool) ℂ)
    (hrow : ∀ {x y : V → Bool} {i j : V}, G.Adj i j →
      x i = true → x j = true → R x y = 0)
    (hcol : ∀ {x y : V → Bool} {i j : V}, G.Adj i j →
      y i = true → y j = true → R x y = 0) :
    (∀ (i : V) (x y : V → Bool),
      R (update x i false) (update y i false) +
        R (update x i true) (update y i true) = 0) ↔
      (∀ (i j : V) (x y : V → Bool), G.Adj i j → x i = y i → R x y = 0) ∧
      (∀ (i : V), (∀ j, ¬ G.Adj i j) → ∀ x y,
        R (update x i false) (update y i false) +
          R (update x i true) (update y i true) = 0) := by
  constructor
  · intro h
    refine ⟨?_, fun i _ => h i⟩
    have vanish (i : V) (x y : V → Bool) (heq : x i = y i)
        (htrue : R (update x i true) (update y i true) = 0) : R x y = 0 := by
      have hfalse := h i x y
      rw [htrue, add_zero] at hfalse
      cases hx : x i
      · have hy : y i = false := heq.symm.trans hx
        have hx' : update x i false = x := by rw [← hx, Function.update_eq_self]
        have hy' : update y i false = y := by rw [← hy, Function.update_eq_self]
        simpa only [hx', hy'] using hfalse
      · have hy : y i = true := heq.symm.trans hx
        have hx' : update x i true = x := by rw [← hx, Function.update_eq_self]
        have hy' : update y i true = y := by rw [← hy, Function.update_eq_self]
        simpa only [hx', hy'] using htrue
    intro i j x y hij heq
    have hne := hij.ne
    apply vanish i x y heq
    by_cases hx : x j = true
    · exact hrow hij (Function.update_self ..) (by rwa [Function.update_of_ne hne.symm])
    by_cases hy : y j = true
    · exact hcol hij (Function.update_self ..) (by rwa [Function.update_of_ne hne.symm])
    have hx' : x j = false := Bool.eq_false_iff.mpr hx
    have hy' : y j = false := Bool.eq_false_iff.mpr hy
    apply vanish j (update x i true) (update y i true)
    · simpa [Function.update_of_ne hne.symm] using hx'.trans hy'.symm
    · apply hrow hij
      · simp [Function.update_of_ne hne]
      · exact Function.update_self ..
  · rintro ⟨hagree, hiso⟩ i x y
    by_cases h : ∃ j, G.Adj i j
    · obtain ⟨j, hj⟩ := h
      rw [hagree i j (update x i false) (update y i false) hj (by simp),
        hagree i j (update x i true) (update y i true) hj (by simp), add_zero]
    · exact hiso i (not_exists.mp h) x y

end D5.S3.Quantum.Entanglement.Marginals.IndependentWordMarginals
