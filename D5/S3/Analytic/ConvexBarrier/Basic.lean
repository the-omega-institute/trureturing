/- GID: D5/S3/Analytic/ConvexBarrier/Basic
   generality: I
   mirror-B: D5/B/S3/Analytic/ConvexBarrier/Basic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Formalized power-cone geometry and analytic support module. -/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Basic
import Mathlib.Tactic

/-!
Analytic definition of an LHSCB on a specified open domain and specified
finite boundary.  The cone's geometric regularity is separate.  In particular,
no symmetry, minimizer, Dikin estimate, duality theorem, or lower bound is a
field of this definition.  On an open domain the derivatives within the domain
are the ordinary derivatives.  `H * sqrt H` is `H^(3/2)` when `H >= 0`.

Source only: this module has not been elaborated or kernel checked.
Intended canonical subject: D5/S3/Analytic/ConvexBarrier.
-/

open Set Filter
open scoped Topology ContDiff

namespace D5.S3.Analytic.ConvexBarrier

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def diagonal (n : ℕ) (D : Set E) (F : E → ℝ) (x h : E) : ℝ :=
  iteratedFDerivWithin ℝ n F D x (fun _ : Fin n => h)

/-- All finite boundary sequences are quantified; there is no invariance
assumption on `F`.  `B` is not a set of preferred or radial boundary points. -/
structure IsLHSCB (ν : ℝ) (D B : Set E) (F : E → ℝ) : Prop where
  parameter : 1 ≤ ν
  domain_open : IsOpen D
  smooth : ContDiffOn ℝ 3 F D
  hessian_pos : ∀ x ∈ D, ∀ h : E, h ≠ 0 → 0 < diagonal 2 D F x h
  self_concordant : ∀ x ∈ D, ∀ h : E,
    |diagonal 3 D F x h| ≤
      2 * diagonal 2 D F x h * Real.sqrt (diagonal 2 D F x h)
  homogeneous : ∀ x ∈ D, ∀ t : ℝ, 0 < t → F (t • x) = F x - ν * Real.log t
  boundary_blowup : ∀ x ∈ B, ∀ u : ℕ → E, (∀ n, u n ∈ D) →
    Tendsto u atTop (𝓝 x) → Tendsto (F ∘ u) atTop atTop

theorem diagonal_comp_linear (A : E →L[ℝ] V) {D : Set V} {F : V → ℝ}
    (hD : IsOpen D) (hF : ContDiffOn ℝ 3 F D) {x : E} (hx : A x ∈ D)
    (h : E) {n : ℕ} (hn : (n : ℕ∞ω) ≤ 3) :
    diagonal n (A ⁻¹' D) (F ∘ A) x h = diagonal n D F (A x) (A h) := by
  unfold diagonal
  rw [A.iteratedFDerivWithin_comp_right hF hD.uniqueDiffOn
    (hD.preimage A.continuous).uniqueDiffOn hx hn]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]

/-- Restriction along an injective continuous linear map.  The only geometric
hypothesis is that every source finite boundary point maps to the target
finite boundary.  C3 and both derivative inequalities are actually pulled back.
This is a restriction theorem, not a scalar lower-bound supplier. -/
theorem IsLHSCB.restrict {ν : ℝ} {D B : Set V} {F : V → ℝ}
    (hF : IsLHSCB ν D B F) (A : E →L[ℝ] V) (hA : Function.Injective A)
    (Bs : Set E) (hB : MapsTo A Bs B) :
    IsLHSCB ν (A ⁻¹' D) Bs (F ∘ A) := by
  refine ⟨hF.parameter, hF.domain_open.preimage A.continuous,
    hF.smooth.comp_continuousLinearMap A, ?_, ?_, ?_, ?_⟩
  · intro x hx h hh
    rw [diagonal_comp_linear A hF.domain_open hF.smooth hx h (by norm_num)]
    exact hF.hessian_pos (A x) hx (A h) (by
      intro he
      exact hh (hA (by simpa using he)))
  · intro x hx h
    rw [diagonal_comp_linear A hF.domain_open hF.smooth hx h (by norm_num),
      diagonal_comp_linear A hF.domain_open hF.smooth hx h (by norm_num)]
    exact hF.self_concordant (A x) hx (A h)
  · intro x hx t ht
    change F (A (t • x)) = F (A x) - ν * Real.log t
    rw [map_smul]
    exact hF.homogeneous (A x) hx t ht
  · intro x hx u hu hlim
    exact hF.boundary_blowup (A x) (hB hx) (A ∘ u) hu
      (A.continuous.continuousAt.tendsto.comp hlim)

end D5.S3.Analytic.ConvexBarrier
