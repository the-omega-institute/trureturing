/- GID: D5/S3/Quantum/Fibers/CenteredEffectTowerStability
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/CenteredEffectTowerStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One-step stability of a centered-effect Heisenberg tower is permanent. -/

import D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence

/- Library-search audit trail (2026-08-21):
   * Exact repository hit `TraceZeroReadoutOrthogonalEquivalence.HermitianTraceZero`
     supplies the source's real Hermitian trace-zero carrier and is imported directly.
   * Exact repository hit `FutureWordOrthogonalResidual.future_word_orthogonal_residual`
     supplies the family's real residual/projection machinery, although the present
     stability proof only needs the canonical `Submodule.map` and orthogonal complement.
   * Pinned Mathlib searches found no exact theorem packaging the recursive one-step
     stability induction together with orthogonal-complement congruence; `Nat.add_succ`,
     `Submodule.le_sup_right`, and `Submodule.map` are applied directly.
   * `loogle` and `leansearch` executables are absent from PATH. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix
open ClosedSubmodule

namespace D5.S3.Quantum.Fibers.CenteredEffectTowerStability

open D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence

variable {d : Type*} [Fintype d] [Nonempty d] [DecidableEq d]

local instance matrixNormedAddCommGroup : NormedAddCommGroup (Matrix d d ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixInnerProductSpace : InnerProductSpace ℂ (Matrix d d ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

/-- The recursively generated visible tower from centered effects and the
source Heisenberg linear map. -/
def towerSpace {r : ℕ}
    (heisenberg : HermitianTraceZero (d := d) →ₗ[ℝ] HermitianTraceZero (d := d))
    (effects : Fin (r + 1) → HermitianTraceZero (d := d)) : ℕ →
      Submodule ℝ (HermitianTraceZero (d := d))
  | 0 => Submodule.span ℝ (Set.range effects)
  | n + 1 => towerSpace heisenberg effects n ⊔
      Submodule.map heisenberg (towerSpace heisenberg effects n)

/-- The residual tower is the orthogonal complement of each visible stage. -/
def residualSpace {r : ℕ}
    (heisenberg : HermitianTraceZero (d := d) →ₗ[ℝ] HermitianTraceZero (d := d))
    (effects : Fin (r + 1) → HermitianTraceZero (d := d)) (n : ℕ) :
      Submodule ℝ (HermitianTraceZero (d := d)) :=
  (towerSpace heisenberg effects n)ᗮ

/-- If one visible Heisenberg stage is stable, every later visible stage and
its orthogonal residual are equal to that stage. -/
theorem heisenberg_tower_once_stable_permanently
    {r m : ℕ}
    (heisenberg : HermitianTraceZero (d := d) →ₗ[ℝ] HermitianTraceZero (d := d))
    (effects : Fin (r + 1) → HermitianTraceZero (d := d))
    (hstep : towerSpace heisenberg effects m =
      towerSpace heisenberg effects (m + 1)) :
    (∀ s : ℕ, towerSpace heisenberg effects (m + s) =
      towerSpace heisenberg effects m) ∧
    (∀ s : ℕ, residualSpace heisenberg effects (m + s) =
      residualSpace heisenberg effects m) := by
  have hsup : towerSpace heisenberg effects m ⊔
      Submodule.map heisenberg (towerSpace heisenberg effects m) =
      towerSpace heisenberg effects m := by
    simpa [towerSpace] using hstep.symm
  have hvisible : ∀ s : ℕ, towerSpace heisenberg effects (m + s) =
      towerSpace heisenberg effects m := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
        calc
          towerSpace heisenberg effects (m + Nat.succ s) =
              towerSpace heisenberg effects (m + s + 1) := by
                rw [Nat.add_assoc]
          _ = towerSpace heisenberg effects (m + s) ⊔
              Submodule.map heisenberg (towerSpace heisenberg effects (m + s)) := by
                rfl
          _ = towerSpace heisenberg effects m ⊔
              Submodule.map heisenberg (towerSpace heisenberg effects m) := by
                rw [ih]
          _ = towerSpace heisenberg effects m := hsup
  constructor
  · exact hvisible
  · intro s
    exact congrArg (fun space : Submodule ℝ (HermitianTraceZero (d := d)) => spaceᗮ)
      (hvisible s)

#print axioms heisenberg_tower_once_stable_permanently

end D5.S3.Quantum.Fibers.CenteredEffectTowerStability
