/- GID: D5/S3/Geometry/PowerCone/ScalarSection
   generality: I
   mirror-B: D5/B/S3/Geometry/PowerCone/ScalarSection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Formalized power-cone geometry and analytic support module. -/

import D5.S3.Analytic.ConvexBarrier.Basic
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
The actual scalar linear section, for any real normed vector space with a
chosen unit vector (hence in particular every nonzero finite Euclidean space).
The domain and finite boundary below are given by the exact cone inequalities.
No vector upper barrier or vector optimum is asserted.

Topology.lean identifies this explicit finite boundary with the cone frontier.
The restriction theorem uses *every* point in this explicit boundary.
Source only; no Lean execution or acceptance is claimed.
Intended canonical subject: D5/S3/Geometry/PowerCone.
-/

open Set
open D5.S3.Analytic.ConvexBarrier

namespace D5.S3.Geometry.PowerCone

abbrev Point (V : Type*) := (ℝ × ℝ) × V

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def weight (c x y : ℝ) : ℝ := x ^ c * y ^ (1 - c)

def closedCone (c : ℝ) : Set (Point V) :=
  {p | 0 ≤ p.1.1 ∧ 0 ≤ p.1.2 ∧ ‖p.2‖ ≤ weight c p.1.1 p.1.2}

def coneInterior (c : ℝ) : Set (Point V) :=
  {p | 0 < p.1.1 ∧ 0 < p.1.2 ∧ ‖p.2‖ < weight c p.1.1 p.1.2}

/-- The entire explicit finite boundary, including coordinate-zero faces. -/
def coneBoundary (c : ℝ) : Set (Point V) := closedCone c \ coneInterior c

noncomputable def scalarSection (v : V) : Point ℝ →L[ℝ] Point V :=
  (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).prod
    (((ContinuousLinearMap.id ℝ ℝ).smulRight v).comp
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ))

@[simp] theorem scalarSection_apply (v : V) (p : Point ℝ) :
    scalarSection v p = (p.1, p.2 • v) := rfl

theorem scalarSection_injective {v : V} (hv : ‖v‖ = 1) :
    Function.Injective (scalarSection v) := by
  intro p q hpq
  have hxy : p.1 = q.1 := congrArg (fun z : Point V => z.1) hpq
  have hz : p.2 • v = q.2 • v := congrArg (fun z : Point V => z.2) hpq
  have hzero : (p.2 - q.2) • v = 0 := by rw [sub_smul, hz, sub_self]
  have habs : |p.2 - q.2| = 0 := by
    simpa [norm_smul, hv, Real.norm_eq_abs] using congrArg norm hzero
  exact Prod.ext hxy (sub_eq_zero.mp (abs_eq_zero.mp habs))

theorem scalarSection_preimage_interior {v : V} (hv : ‖v‖ = 1) (c : ℝ) :
    scalarSection v ⁻¹' coneInterior c = (coneInterior c : Set (Point ℝ)) := by
  ext p
  simp [coneInterior, norm_smul, hv, Real.norm_eq_abs]

theorem scalarSection_preimage_closed {v : V} (hv : ‖v‖ = 1) (c : ℝ) :
    scalarSection v ⁻¹' closedCone c = (closedCone c : Set (Point ℝ)) := by
  ext p
  simp [closedCone, norm_smul, hv, Real.norm_eq_abs]

theorem scalarSection_boundary {v : V} (hv : ‖v‖ = 1) (c : ℝ) :
    MapsTo (scalarSection v) (coneBoundary c : Set (Point ℝ)) (coneBoundary c) := by
  intro p hp
  change p ∈ scalarSection v ⁻¹' (closedCone c \ coneInterior c)
  rw [preimage_diff, scalarSection_preimage_closed hv, scalarSection_preimage_interior hv]
  exact hp

/-- Restriction preserves all analytic barrier properties, including arbitrary
finite scalar boundary sequences, not only vertical or radial sequences. -/
theorem restrict_to_scalar {c ν : ℝ} {v : V} (hv : ‖v‖ = 1)
    {F : Point V → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) :
    IsLHSCB ν (coneInterior c) (coneBoundary c) (F ∘ scalarSection v) := by
  have h := hF.restrict (scalarSection v) (scalarSection_injective hv)
    (coneBoundary c) (scalarSection_boundary hv c)
  rw [scalarSection_preimage_interior hv c] at h
  exact h

noncomputable def coordinateSwap : Point V →L[ℝ] Point V :=
  (((ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (ContinuousLinearMap.fst ℝ ℝ ℝ)).comp
      (ContinuousLinearMap.fst ℝ (ℝ × ℝ) V)).prod
        (ContinuousLinearMap.snd ℝ (ℝ × ℝ) V)

@[simp] theorem coordinateSwap_apply (p : Point V) :
    coordinateSwap p = ((p.1.2, p.1.1), p.2) := rfl

theorem coordinateSwap_involutive :
    Function.Involutive (coordinateSwap : Point V → Point V) := by
  intro p
  rfl

theorem coordinateSwap_preimage_interior (c : ℝ) :
    coordinateSwap ⁻¹' (coneInterior c : Set (Point V)) = coneInterior (1 - c) := by
  ext p
  simp only [mem_preimage, coneInterior, mem_setOf_eq, coordinateSwap_apply, weight]
  constructor <;> rintro ⟨hx, hy, hz⟩ <;>
    exact ⟨hy, hx, by simpa [sub_sub_cancel, mul_comm] using hz⟩

theorem coordinateSwap_preimage_boundary (c : ℝ) :
    coordinateSwap ⁻¹' (coneBoundary c : Set (Point V)) = coneBoundary (1 - c) := by
  have hclosed : coordinateSwap ⁻¹' (closedCone c : Set (Point V)) = closedCone (1-c) := by
    ext p
    simp only [mem_preimage, closedCone, mem_setOf_eq, coordinateSwap_apply, weight]
    constructor <;> rintro ⟨hx, hy, hz⟩ <;>
      exact ⟨hy, hx, by simpa [sub_sub_cancel, mul_comm] using hz⟩
  rw [coneBoundary, preimage_diff, hclosed, coordinateSwap_preimage_interior]
  rfl

/-- Exact target, intentionally a proposition definition with no inhabitant.
Zhang--Fu--Dai, arXiv:2611.06404v1, Theorem 3.5 (printed pp. 9--12).
There is no declaration claiming this proposition has been proved here. -/
def ScalarLowerClaim : Prop :=
  ∀ c : ℝ, 0 < c → c ≤ 1 / 2 → ∀ ν : ℝ, ∀ F : Point ℝ → ℝ,
    IsLHSCB ν (coneInterior c) (coneBoundary c) F → 3 / (1 + c) ≤ ν

end D5.S3.Geometry.PowerCone
