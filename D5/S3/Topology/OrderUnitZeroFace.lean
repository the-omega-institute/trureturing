/- GID: D5/S3/Topology/OrderUnitZeroFace
   generality: G
   mirror-B: D5/B/S3/Topology/OrderUnitZeroFace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.Connected.Clopen]
   utility: none
   digest: Zero-face preservation and second-order unit nilpotence force unit annihilation. -/

module

public import D5.S3.Topology.OrderUnitNorm
public import Mathlib.Topology.Connected.Clopen

/-! Boundary support prevents a nilpotent unit line from leaving the cone. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace D5.S3.Topology.OrderUnitZeroFace

open Set
open scoped _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A linear map preserving every continuous positive zero face annihilates
the specified interior unit if its square annihilates that unit. -/
theorem unit_eq_zero (A : OrderUnitNorm.Data E) (T : E →ₗ[ℝ] E)
    (hface : ∀ φ : E →L[ℝ] ℝ, (∀ x ∈ A.cone, 0 ≤ φ x) →
      ∀ x ∈ A.cone, φ x = 0 → φ (T x) = 0)
    (hsecond : T (T A.unit) = 0) : T A.unit = 0 := by
  let v := T A.unit
  let f : ℝ → E := fun t => A.unit + t • v
  have hf : Continuous f := by fun_prop
  have hfT (t : ℝ) : T (f t) = v := by
    simp [f, v, map_add, map_smul, hsecond]
  have hin (t : ℝ) (ht : f t ∈ A.cone) : f t ∈ interior (A.cone : Set E) := by
    by_contra hboundary
    obtain ⟨φ, hφ, hzero, hunit⟩ := A.boundary_support (f t) ht hboundary
    have hv : φ v = 0 := by simpa only [hfT] using hface φ hφ (f t) ht hzero
    have : φ A.unit = 0 := by simpa [f, map_add, map_smul, hv] using hzero
    exact hunit.ne' this
  have hopen : IsOpen (f ⁻¹' (A.cone : Set E)) := by
    have heq : f ⁻¹' (A.cone : Set E) = f ⁻¹' interior (A.cone : Set E) := by
      ext t
      exact ⟨hin t, fun h => @interior_subset E _ (A.cone : Set E) (f t) h⟩
    rw [heq]
    exact isOpen_interior.preimage hf
  have hall : f ⁻¹' (A.cone : Set E) = univ :=
    (IsClopen.eq_univ ⟨A.closed.preimage hf, hopen⟩
      ⟨0, by simpa [f] using interior_subset A.interior_unit⟩)
  have horbit (t : ℝ) : A.unit + t • v ∈ A.cone := by
    have : t ∈ f ⁻¹' (A.cone : Set E) := by rw [hall]; trivial
    exact this
  apply (A.norm_zero_iff _).mp
  apply le_antisymm _ (A.norm_nonneg v)
  by_contra hn
  have hnpos : 0 < A.orderNorm v := lt_of_not_ge hn
  let r := A.orderNorm v / 2
  have hr : 0 < r := half_pos hnpos
  have hm : r • A.unit - v ∈ A.cone := by
    simpa [smul_add, smul_smul, hr.ne', sub_eq_add_neg] using
      A.cone.smul_mem hr (horbit (-r⁻¹))
  have hp : r • A.unit + v ∈ A.cone := by
    simpa [smul_add, smul_smul, hr.ne'] using
      A.cone.smul_mem hr (horbit r⁻¹)
  have hb : A.orderNorm v ≤ r := (A.norm_le_iff v r).mpr ⟨hr.le, hm, hp⟩
  dsimp [r] at hb
  linarith

end D5.S3.Topology.OrderUnitZeroFace
