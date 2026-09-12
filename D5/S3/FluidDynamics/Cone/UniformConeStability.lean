/- GID: D5/S3/FluidDynamics/Cone/UniformConeStability
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Cone/UniformConeStability
   mirror-E: none(waiver:upstream-proof-complete-port)
   anchors: []
   utility: none
   digest: Every compact set of true-cone data admits a uniform positive perturbation radius preserving the lower bound on v and positive definiteness of the cone matrix. -/

import D5.S3.FluidDynamics.Cone.ConePositivity
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open Set
namespace D5.S3.FluidDynamics.Cone

/-! Port of `compact_trueCone_stable` and its minimal prerequisites from the upstream
repository `openai/NavierStokesAndEuler`, commit
8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538, file
`NavierStokes/UniformCone.lean`, licensed under Apache-2.0.
This is a port rather than an import because upstream pins Lean v4.34.0-rc2,
this repository pins v4.33.0, and a repository-wide toolchain change for one
research line is not acceptable.
The matrix stability conclusion is proved locally by composing the port with
`cone_condition_iff_posDef` from `ConePositivity`. -/

/-- Coordinates `(P,J,v)` for a stress cone datum, with the product metric. -/
abbrev ConeDatum := ℝ × ℝ × ℝ

/-- The exact open true cone, retaining the square-root inequality. -/
def trueCone : Set ConeDatum :=
  {z | 2 < z.2.2 ∧ 2 < z.1 ∧ z.2.2 < coneBound z.1 z.2.1}

theorem continuous_coneBound : Continuous (fun z : ConeDatum => coneBound z.1 z.2.1) := by
  unfold coneBound
  exact (continuous_fst.add ((continuous_fst.comp continuous_snd).pow 2 |>.div_const 4)).sub
    (((continuous_fst.comp continuous_snd).abs).mul
      (((continuous_fst.sub continuous_const).div_const 2).add
        ((continuous_fst.comp continuous_snd).pow 2 |>.div_const 16)).sqrt)

theorem isOpen_trueCone : IsOpen trueCone := by
  exact (isOpen_lt continuous_const (continuous_snd.comp continuous_snd)).inter
    ((isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt (continuous_snd.comp continuous_snd) continuous_coneBound))

/-- Every compact subset of the true cone has one positive metric
perturbation tolerance, including perturbations outside the original image. -/
theorem compact_trueCone_stable {S : Set ConeDatum} (hS : IsCompact S)
    (hcone : S ⊆ trueCone) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ S, ∀ z' : ConeDatum,
      dist z' z ≤ ρ → z' ∈ trueCone := by
  obtain ⟨ρ, hρ, hsub⟩ := hS.exists_cthickening_subset_open isOpen_trueCone hcone
  exact ⟨ρ, hρ, fun z hz z' hdist =>
    hsub (Metric.mem_cthickening_of_dist_le z' z ρ S hz hdist)⟩

/-- Every compact set of true-cone data admits one positive perturbation radius
preserving both `v > 2` and positive definiteness of the cone matrix. -/
theorem compact_coneMatrix_posDef_stable {S : Set ConeDatum} (hS : IsCompact S)
    (hcone : S ⊆ trueCone) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ S, ∀ z' : ConeDatum, dist z' z ≤ ρ →
      2 < z'.2.2 ∧ (coneMatrix z'.1 z'.2.1 z'.2.2).PosDef := by
  obtain ⟨ρ, hρ, hstable⟩ := compact_trueCone_stable hS hcone
  refine ⟨ρ, hρ, fun z hz z' hdist => ?_⟩
  obtain ⟨hv, hP, hbound⟩ := hstable z hz z' hdist
  exact ⟨hv, (cone_condition_iff_posDef hv).mp ⟨hP, hbound⟩⟩

#print axioms ConeDatum
#print axioms trueCone
#print axioms continuous_coneBound
#print axioms isOpen_trueCone
#print axioms compact_trueCone_stable
#print axioms compact_coneMatrix_posDef_stable

end D5.S3.FluidDynamics.Cone
