/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/FiniteActionTrivialization
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/FiniteActionTrivialization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuous fibre changes trivialize permutation coboundaries on the original fibre. -/

import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Dynamics.Minimal
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Group.End
import Lean.Elab.Tactic.Omega

/-! A continuous permutation coboundary trivializes a skew step on its original discrete fibre. -/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts

/-- Change coordinates on the original discrete fibre, using a continuous transfer. -/
noncomputable def finiteFibreHomeomorph {X Q : Type*} [TopologicalSpace X]
    [TopologicalSpace Q] [DiscreteTopology Q] (β : X → Equiv.Perm Q)
    (hβ : @Continuous X (Equiv.Perm Q) _ ⊥ β) : (X × Q) ≃ₜ (X × Q) where
  toFun z := (z.1, (β z.1).symm z.2)
  invFun z := (z.1, β z.1 z.2)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := by
    letI : TopologicalSpace (Equiv.Perm Q) := ⊥
    letI : DiscreteTopology (Equiv.Perm Q) := discreteTopology_bot _
    have he : Continuous (fun z : Equiv.Perm Q × Q => z.1.symm z.2) :=
      continuous_of_discreteTopology
    exact continuous_fst.prodMk (he.comp ((hβ.comp continuous_fst).prodMk continuous_snd))
  continuous_invFun := by
    letI : TopologicalSpace (Equiv.Perm Q) := ⊥
    letI : DiscreteTopology (Equiv.Perm Q) := discreteTopology_bot _
    have he : Continuous (fun z : Equiv.Perm Q × Q => z.1 z.2) :=
      continuous_of_discreteTopology
    exact continuous_fst.prodMk (he.comp ((hβ.comp continuous_fst).prodMk continuous_snd))

theorem finiteFibreHomeomorph_conjugacy {X Q : Type*} [TopologicalSpace X]
    [TopologicalSpace Q] [DiscreteTopology Q] (β : X → Equiv.Perm Q)
    (hβ : @Continuous X (Equiv.Perm Q) _ ⊥ β) (T : X → X)
    (α : X → Equiv.Perm Q) (hstep : ∀ y, β (T y) = α y * β y) (y : X) (q : Q) :
    finiteFibreHomeomorph β hβ (T y, α y q) =
      (T y, (finiteFibreHomeomorph β hβ (y, q)).2) := by
  apply Prod.ext
  · rfl
  · change (β (T y)).symm (α y q) = (β y).symm q
    apply (β (T y)).injective
    rw [Equiv.apply_symm_apply, hstep, Equiv.Perm.mul_apply, Equiv.apply_symm_apply]

/-- Invariance under the generator implies invariance under all integer iterates. -/
theorem invariant_of_unitStep {X Q : Type*} [AddAction ℤ X]
    (F : X → Q) (hstep : ∀ x, F ((1 : ℤ) +ᵥ x) = F x) (g : ℤ) (x : X) :
    F (g +ᵥ x) = F x := by
  have hnat (n : ℕ) (z : X) : F ((n : ℤ) +ᵥ z) = F z := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show ((n + 1 : ℕ) : ℤ) = 1 + (n : ℤ) by omega, add_vadd, hstep, ih]
  cases g with
  | ofNat n => exact hnat n x
  | negSucc n =>
    have he := hnat (n + 1) (Int.negSucc n +ᵥ x)
    rw [← add_vadd] at he
    have hz : ((n + 1 : ℕ) : ℤ) + Int.negSucc n = 0 := by omega
    rw [hz, zero_vadd] at he
    exact he.symm

end D5.S1.Dynamics.Symbolic.PermutativeLifts
