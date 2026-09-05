/- GID: D5/S3/Weil/ZetaLinear/QuadraticProbeIrredundance
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:structural-infinite-arena)
   anchors: []
   digest: Give each of the three actual quadratic evaluations a leave-one-out witness. -/

import D5.S3.Weil.ZetaLinear.QuadraticObserverPolarization

/-!
# Simultaneous irredundance of the quadratic evaluation catalog

This module retains the complete Mathlib binary real quadratic-form space.
The three observations are the existing evaluations at e0, e1, and e0+e1.
Each is essential relative to the other two observations in the same catalog.
No historical catalog, theorem truth coordinate, proof identity, finite sample,
or numerical information score is introduced.

This is a structural witness theorem on an infinite arena. It is not a claim
that a finite information-theory seal or repository-wide admission has run.
The underlying polarization result is classical; the present contribution is
its explicit connection to the repository's actual object-level probe family.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaLinear.QuadraticProbeIrredundance

open D5.S3.Weil.ZetaLinear.QuadraticObserverPolarization

/-- The three already-owned evaluations in their fixed current catalog. -/
def probe (i : Fin 3) (Q : BinaryQuadratic) : ℝ :=
  if i = 0 then diagonalProbe 0 Q
  else if i = 1 then diagonalProbe 1 Q
  else mixedProbe Q

/-- Actual quadratic forms isolating each evaluation:
`x0^2-x0*x1`, `x1^2-x0*x1`, and `x0*x1`. -/
def isolatingForm (i : Fin 3) : BinaryQuadratic :=
  if i = 0 then
    QuadraticMap.proj (0 : Fin 2) 0 - QuadraticMap.proj (0 : Fin 2) 1
  else if i = 1 then
    QuadraticMap.proj (1 : Fin 2) 1 - QuadraticMap.proj (0 : Fin 2) 1
  else QuadraticMap.proj (0 : Fin 2) 1

private theorem probe_zero (i : Fin 3) : probe i 0 = 0 := by
  fin_cases i <;> simp [probe, diagonalProbe, mixedProbe]

/-- The witness changes exactly its designated coordinate in the full catalog. -/
theorem probe_isolatingForm (i j : Fin 3) :
    probe j (isolatingForm i) = if j = i then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [probe, isolatingForm, diagonalProbe, mixedProbe, axis,
      QuadraticMap.proj_apply, Pi.single_apply]

/-- Every coordinate has a genuine leave-one-out witness on the unchanged
quadratic-form arena. All three witnesses use the same complete catalog. -/
theorem current_catalog_leave_one_out_witness (i : Fin 3) :
    ∃ Q R : BinaryQuadratic,
      (∀ j : Fin 3, j ≠ i → probe j Q = probe j R) ∧
        probe i Q ≠ probe i R := by
  refine ⟨0, isolatingForm i, ?_, ?_⟩
  · intro j hji
    rw [probe_zero, probe_isolatingForm, if_neg hji]
  · rw [probe_zero, probe_isolatingForm, if_pos rfl]
    exact zero_ne_one

/-- The complete readout is faithful on all binary real quadratic forms. -/
theorem current_catalog_readout_injective :
    Function.Injective (fun Q : BinaryQuadratic => fun i : Fin 3 => probe i Q) := by
  intro Q R h
  have h0 : diagonalProbe 0 Q = diagonalProbe 0 R := by
    simpa [probe] using congrFun h (0 : Fin 3)
  have h1 : diagonalProbe 1 Q = diagonalProbe 1 R := by
    simpa [probe] using congrFun h (1 : Fin 3)
  have hm : mixedProbe Q = mixedProbe R := by
    simpa [probe] using congrFun h (2 : Fin 3)
  apply three_probe_readout_injective
  exact Prod.ext h0 (Prod.ext h1 hm)

#print axioms probe_isolatingForm
#print axioms current_catalog_leave_one_out_witness
#print axioms current_catalog_readout_injective

end D5.S3.Weil.ZetaLinear.QuadraticProbeIrredundance
