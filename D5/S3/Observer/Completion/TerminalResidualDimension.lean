/- GID: D5/S3/Observer/Completion/TerminalResidualDimension
   generality: G
   mirror-B: D5/B/S3/Observer/Completion/TerminalResidualDimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Full-size strict tails meet at zero; empty and singleton top chains do not. -/

/- Library-search audit trail (2026-08-25):
   * The imported `ResidualProgressMeasure` module supplies the exact coordinate-tail witness.
   * Its upstream exact hit `transfinite_basis_residual_tower` identifies the all-stage
     intersection with the residual after every coordinate and proves that residual is zero.
   * Repository and pinned-Mathlib searches found no more direct theorem packaging constant
     stage dimension together with the zero terminal intersection. -/

import D5.S3.Observer.Completion.ResidualProgressMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Cardinal Ordinal
open scoped lp

namespace D5.S3.Observer.Completion.TerminalResidualDimension

open D5.S3.Quantum.Completion.TransfiniteBasisResidualTower

/-- Here the terminal residual means the infimum of all natural-numbered stages. For the exact
coordinate-tail chain used by `bare_dimension_not_progress`, that infimum equals the residual
after all basis coordinates have been consumed, hence is zero. Thus every proper stage remains
linearly isometric to the infinite-dimensional ambient space while the terminal is zero. The
zeroth stage is explicitly the whole space. -/
theorem constant_dimension_with_zero_terminal :
    let H := lp (fun _ : Nat => Real) 2
    ∃ R : Nat → ClosedSubmodule Real H,
      R 0 = ⊤ ∧
        (∀ n, R (n + 1) < R n) ∧
        Antitone R ∧
        (∀ n, Nonempty ((R n).toSubmodule ≃ₗᵢ[Real] H)) ∧
        ¬ FiniteDimensional Real H ∧
        (⨅ n, R n) = ⊥ := by
  dsimp only
  let H := lp (fun _ : Nat => Real) 2
  let b : HilbertBasis Nat Real H := default
  let R : Nat → ClosedSubmodule Real H := fun n => basisResidual b (Set.Iio n)
  have hInitial : Cardinal.ord (#Nat) = typeLT Nat := by simp
  have hTower := transfinite_basis_residual_tower b hInitial
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change basisResidual b (Set.Iio 0) = ⊤
    rw [basisResidual]
    have hPrefix : basisPrefix b (Set.Iio 0) = ⊥ := by
      have hIio : Set.Iio (0 : Nat) = ∅ := by
        ext k
        simp
      rw [basisPrefix, hIio, Set.image_empty, Submodule.span_empty]
      ext x
      change x ∈ (⊥ : Submodule Real H).topologicalClosure ↔ x ∈ (⊥ : Submodule Real H)
      rw [Submodule.topologicalClosure_eq_self]
    rw [hPrefix]
    exact ClosedSubmodule.bot_orthogonal_eq_top
  · intro n
    have hSet : Set.Iic n = Set.Iio (n + 1) := by
      ext k
      simp
    have hCurrent :
        (R n).toSubmodule =
          Real ∙ b n ⊔ (R (n + 1)).toSubmodule := by
      dsimp [R]
      simpa only [hSet] using (hTower.1 n).1
    have hOrthogonal : Real ∙ b n ⟂ (R (n + 1)).toSubmodule := by
      dsimp [R]
      simpa only [hSet] using (hTower.1 n).2
    have hle : R (n + 1) ≤ R n := by
      change (R (n + 1)).toSubmodule ≤ (R n).toSubmodule
      rw [hCurrent]
      exact le_sup_right
    refine lt_of_le_of_ne hle ?_
    intro hEq
    have hbNext : b n ∈ (R (n + 1)).toSubmodule := by
      rw [hEq, hCurrent]
      exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self (b n))
    have hbBot : b n ∈ (⊥ : Submodule Real H) :=
      hOrthogonal.disjoint.le_bot
        ⟨Submodule.mem_span_singleton_self (b n), hbNext⟩
    have hbZero : b n = 0 := by simpa using hbBot
    have hbNorm := b.orthonormal.norm_eq_one n
    rw [hbZero, norm_zero] at hbNorm
    exact zero_ne_one hbNorm
  · apply antitone_nat_of_succ_le
    intro n
    have hSet : Set.Iic n = Set.Iio (n + 1) := by
      ext k
      simp
    have hCurrent :
        (R n).toSubmodule =
          Real ∙ b n ⊔ (R (n + 1)).toSubmodule := by
      dsimp [R]
      simpa only [hSet] using (hTower.1 n).1
    change (R (n + 1)).toSubmodule ≤ (R n).toSubmodule
    rw [hCurrent]
    exact le_sup_right
  · intro n
    exact ⟨residualEquiv b hInitial n⟩
  · intro hFinite
    letI : FiniteDimensional Real H := hFinite
    exact Module.Finite.not_linearIndependent_of_infinite
      b b.orthonormal.linearIndependent
  · change (⨅ n : Nat, basisResidual b (Set.Iio n)) = ⊥
    rw [← hTower.2.1.2.2, hTower.2.2.2]

#print axioms constant_dimension_with_zero_terminal

/- Degenerate audit: empty and singleton stage types make the infimum of a constant top chain
top, while a constant zero chain has zero infimum. The theorem avoids these false generalizations
by fixing the genuinely infinite natural coordinate chain; its `n = 0` clause is `R 0 = ⊤`. -/
example : (⨅ _ : PEmpty, (⊤ : ClosedSubmodule Real Real)) = ⊤ := by simp

example : (⨅ _ : PUnit, (⊤ : ClosedSubmodule Real Real)) = ⊤ := by simp

example : (⨅ _ : Nat, (⊥ : ClosedSubmodule Real Real)) = ⊥ := by simp

end D5.S3.Observer.Completion.TerminalResidualDimension
