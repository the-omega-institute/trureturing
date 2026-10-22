/- GID: D5/S3/VertexAlgebra/LatticeBcGhostFixedEnergyFiltration
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeBcGhostFixedEnergyFiltration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite original fixed-charge energy support without lattice positivity. -/

import D5.S3.VertexAlgebra.TemporaryTransverseJointBasis17
import D5.S3.VertexAlgebra.TemporaryTransverseJointContraction19

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
  BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

private theorem polarizedWeight_nonnegative (site : ℕ) : 0 ≤ polarizedWeight site := by
  have lower := polarizedWeight_bound site
  split_ifs at lower <;> omega

private theorem polarized_site_bound (subset : Finset ℕ) (site : ℕ)
    (present : site ∈ subset) (bound : ℕ) (levelBound : polarizedLevel subset ≤ bound) :
    site < 2 * bound + 4 := by
  have termBound : polarizedWeight site ≤ polarizedLevel subset :=
    Finset.single_le_sum (fun other _ => polarizedWeight_nonnegative other) present
  by_cases switched : site = 1
  · omega
  · unfold polarizedWeight BcGhostLZeroSpectrum.siteWeight at termBound
    simp only [if_neg switched] at termBound
    split_ifs at termBound <;> omega

private theorem polarized_sublevel_finite (bound : ℕ) :
    Finite {subset : Finset ℕ // polarizedLevel subset ≤ bound} := by
  classical
  let encode (subset : {subset : Finset ℕ // polarizedLevel subset ≤ bound})
      (site : Fin (2 * bound + 4)) : Bool := decide (site.val ∈ subset.val)
  have injective : Function.Injective encode := by
    intro first second equal
    apply Subtype.ext
    apply Finset.ext
    intro site
    by_cases below : site < 2 * bound + 4
    · exact decide_eq_decide.mp (congrFun equal ⟨site, below⟩)
    · have firstAbsent : site ∉ first.val := fun present =>
        below (polarized_site_bound first.val site present bound first.property)
      have secondAbsent : site ∉ second.val := fun present =>
        below (polarized_site_bound second.val site present bound second.property)
      simp [firstAbsent, secondAbsent]
  exact Finite.of_injective encode injective

theorem native_energy_sublevel_finite (D : LatticeData) (bound : ℕ) :
    Finite {index : NativeIndex D // nativeLevel D index.1 index.2 ≤ bound} := by
  classical
  haveI := LatticePositiveEnergy.oscillatorLeFinite D bound
  haveI := polarized_sublevel_finite bound
  have oscillatorBound (index : {index : NativeIndex D // nativeLevel D index.1 index.2 ≤ bound}) :
      LatticePositiveEnergy.oscillatorEnergy index.val.1 ≤ bound := by
    have nonnegative := native_polarizedLevel_nonnegative index.val.2
    have total := index.property
    change (LatticePositiveEnergy.oscillatorEnergy index.val.1 : ℤ) +
      polarizedLevel index.val.2 ≤ bound at total
    omega
  have ghostBound (index : {index : NativeIndex D // nativeLevel D index.1 index.2 ≤ bound}) :
      polarizedLevel index.val.2 ≤ bound := by
    have nonnegative : 0 ≤ (Finsupp.weight (frequencyWeight D) index.val.1 : ℤ) :=
      Int.natCast_nonneg _
    have total := index.property
    unfold nativeLevel at total
    omega
  let encode (index : {index : NativeIndex D // nativeLevel D index.1 index.2 ≤ bound}) :
      {powers : LatticePositiveEnergy.Exponent D // LatticePositiveEnergy.oscillatorEnergy powers ≤ bound} ×
        {subset : Finset ℕ // polarizedLevel subset ≤ bound} :=
    (⟨index.val.1, oscillatorBound index⟩, ⟨index.val.2, ghostBound index⟩)
  apply Finite.of_injective encode
  intro first second equal
  apply Subtype.ext
  exact Prod.ext (congrArg (fun value => value.1.val) equal)
    (congrArg (fun value => value.2.val) equal)

def fixedEnergySpace (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (beta : Charge D) (level : ℤ) :
    Submodule ℂ (State D) :=
  LinearMap.ker (chargeProjection D beta - 1) ⊓
    LinearMap.ker (M D H 0 + G D 0 -
      (chosenH D beta + (level : ℂ) - 1) • (1 : Module.End ℂ (State D)))

theorem original_fixed_energy_finite (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (beta : Charge D) (level : ℤ) :
    Module.Finite ℂ (fixedEnergySpace D H beta level) := by
  classical
  let indices := {index : NativeIndex D // nativeLevel D index.1 index.2 ≤ level.toNat}
  haveI : Finite indices := native_energy_sublevel_finite D level.toNat
  let generators : Set (State D) := Set.range (fun index : indices => nativeWord D frame beta index.val)
  have finiteGenerators : generators.Finite := Set.finite_range _
  haveI : Module.Finite ℂ (Submodule.span ℂ generators) :=
    Module.Finite.span_of_finite ℂ finiteGenerators
  have inclusion : fixedEnergySpace D H beta level ≤ Submodule.span ℂ generators := by
    intro state member
    have sector : chargeProjection D beta state = state := by
      have equation := member.1
      change chargeProjection D beta state - state = 0 at equation
      exact sub_eq_zero.mp equation
    have energy : (M D H 0 + G D 0) state =
        (chosenH D beta + (level : ℂ) - 1) • state := by
      have equation := member.2
      change (M D H 0 + G D 0) state - (chosenH D beta + (level : ℂ) - 1) • state = 0 at equation
      exact sub_eq_zero.mp equation
    rw [← native_sector_finite_expansion D frame inverse leftFrameInverse rightFrameInverse beta state sector]
    apply Submodule.sum_mem
    intro index present
    apply Submodule.smul_mem
    apply Submodule.subset_span
    have exactLevel := nativeT0_support_level D frame inverse leftFrameInverse rightFrameInverse beta H
      leftGramInverse rightGramInverse level state sector energy index (Finsupp.mem_support_iff.mp present)
    exact ⟨⟨index, by rw [exactLevel]; omega⟩, rfl⟩
  exact Module.Finite.of_injective (Submodule.inclusion inclusion)
    (Submodule.inclusion_injective inclusion)

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
