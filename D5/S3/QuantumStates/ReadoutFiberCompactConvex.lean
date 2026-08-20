/- GID: D5/S3/QuantumStates/ReadoutFiberCompactConvex
   generality: G
   mirror-B: D5/B/S3/QuantumStates/ReadoutFiberCompactConvex
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every nonempty finite-dimensional positive readout fiber is compact and convex. -/

import D5.S3.Quantum.Fibers.PhysicalFiber

open Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

namespace D5.S3.QuantumStates.ReadoutFiberCompactConvex

/-- The positive, normalized states with a prescribed finite readout. -/
def readoutFiber {n k : Type*} [Fintype n]
    (readout : Matrix n n ℂ →ₗ[ℂ] (k → ℂ)) (y : k → ℂ) :
    Set (Matrix n n ℂ) :=
  {sigma | readout sigma = y ∧ sigma.PosSemidef ∧ Matrix.trace sigma = 1}

/- Library-search audit trail (2026-08-20):
   * Repository search found the exact positive readout construction and its
     compact-convex theorem in `D5.S3.Quantum.Fibers.PhysicalFiber`.
   * Pinned-Mathlib searches for an arbitrary readout-fiber theorem found no
     exact declaration; the frozen repository theorem is applied directly.
   * The new arbitrary target value is related to a witness state by set extensionality,
     so no compactness or convexity argument is reproved here. -/

/-- Every nonempty finite-dimensional positive readout fiber is compact and convex. -/
theorem readout_fiber_compact_convex {n k : Type*}
    [Fintype n] [Nonempty n] [Finite k]
    (readout : Matrix n n ℂ →ₗ[ℂ] (k → ℂ)) (y : k → ℂ)
    (hfiber : (readoutFiber readout y).Nonempty) :
    IsCompact (readoutFiber readout y) ∧
      Convex ℝ (readoutFiber readout y) := by
  classical
  letI := Fintype.ofFinite k
  obtain ⟨rho, hrho⟩ := hfiber
  have hphysical :=
    D5.S3.Quantum.Fibers.PhysicalFiber.finite_dimensional_physical_fiber
      readout rho hrho.2.1 hrho.2.2
  have hEq : readoutFiber readout y =
      D5.S3.Quantum.Fibers.PhysicalFiber.physicalFiber readout rho := by
    ext sigma
    constructor
    · intro hs
      exact ⟨hs.1.trans hrho.1.symm, hs.2.1, hs.2.2⟩
    · intro hs
      exact ⟨hs.1.trans hrho.1, hs.2.1, hs.2.2⟩
  rw [← hEq] at hphysical
  exact ⟨hphysical.2.1, hphysical.2.2⟩

example :
    (readoutFiber (n := Fin 1) (k := Fin 1)
      (0 : Matrix (Fin 1) (Fin 1) ℂ →ₗ[ℂ] (Fin 1 → ℂ)) (fun _ => 0)).Nonempty := by
  classical
  refine ⟨1, ?_⟩
  simp only [readoutFiber, Set.mem_setOf_eq, LinearMap.zero_apply]
  refine ⟨?_, Matrix.PosSemidef.one, ?_⟩
  · funext x
    rfl
  · simp

#print axioms readout_fiber_compact_convex

end D5.S3.QuantumStates.ReadoutFiberCompactConvex
