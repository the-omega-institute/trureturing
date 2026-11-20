/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCompactIncidence
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCompactIncidence
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactSource]
   utility: none
   digest: The trace-direction incidence persists at every compact limit of five-site states. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactSource

/-! Multiplying by conjugate coordinates writes the trace-direction incidence
directly in the Hermitian projector entries. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactIncidence

open Set PeriodicMPSFiveSiteCoordinates PeriodicMPSFiveSiteCompactSource
  PeriodicMPSProjectiveCoordinates PeriodicMPSFiveSiteAlignedFiber
open scoped ComplexConjugate

open private traceDirection from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactSource

private def left (i : Fin 2) (j : Fin 8) (x : Ambient) : ℂ :=
  x.1.1 0 i * (x.2 4 j - x.2 5 j)

private def right (i : Fin 2) (j : Fin 8) (x : Ambient) : ℂ :=
  x.1.1 1 i * (x.2 2 j - x.2 3 j)

private theorem ordinary_incidence (a : Inputs) (i : Fin 2) (j : Fin 8) :
    left i j (ordinary a) = right i j (ordinary a) := by
  let p := coordinates (a.val 0) (a.val 1) (a.val 2) (a.val 3) (a.val 4)
  let t := traceDirection a.val
  have h : t 0 * (p 4 - p 5) = t 1 * (p 2 - p 3) :=
    trace_direction _ _ _ _ _
  change projector t 0 i * (projector p 4 j - projector p 5 j) =
    projector t 1 i * (projector p 2 j - projector p 3 j)
  simp only [projector, outer, Matrix.smul_apply, Complex.real_smul]
  linear_combination ((↑((mass t)⁻¹) : ℂ) * conj (t i) *
    (↑((mass p)⁻¹) : ℂ) * conj (p j)) * h

/-- The trace direction is constrained by the antisymmetric necklace
differences on the entire compact source. -/
theorem compact_incidence {x : Ambient} (hx : x ∈ source) (i : Fin 2) (j : Fin 8) :
    x.1.1 0 i * (x.2 4 j - x.2 5 j) = x.1.1 1 i * (x.2 2 j - x.2 3 j) := by
  have hc : IsClosed {x | left i j x = right i j x} :=
    isClosed_eq (by unfold left; fun_prop) (by unfold right; fun_prop)
  have hs : range ordinary ⊆ {x | left i j x = right i j x} := by
    rintro _ ⟨a, rfl⟩
    exact ordinary_incidence a i j
  exact closure_minimal hs hc hx

/-- Every compact preimage of either special ray lies in the first trace
direction. In projector coordinates the second trace row vanishes. -/
theorem special_ray_trace_row_zero {x : Ambient} (hx : x ∈ source)
    (s : ℂ) (hp : x.2 = projector (ray s)) (i : Fin 2) :
    x.1.1 1 i = 0 := by
  have h := compact_incidence hx i (3 : Fin 8)
  rw [hp] at h
  have hdiag := (projector_diag_ne_zero_iff (ray s) (3 : Fin 8)).2
    (show ray s 3 ≠ 0 by norm_num [ray])
  have h₂ : projector (ray s) 2 3 = 0 := by
    simp [projector, outer, ray, Matrix.smul_apply]
  have h₄ : projector (ray s) 4 3 = 0 := by
    simp [projector, outer, ray, Matrix.smul_apply]
  have h₅ : projector (ray s) 5 3 = 0 := by
    simp [projector, outer, ray, Matrix.smul_apply]
  simp only [h₂, h₄, h₅, sub_self, mul_zero, zero_sub] at h
  exact (mul_eq_zero.mp h.symm).resolve_right (neg_ne_zero.mpr hdiag)

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactIncidence
