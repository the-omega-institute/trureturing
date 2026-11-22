/- GID: D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2Cofinite
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2Cofinite
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: C₂ cofiniteness of the sign-fixed Leech lattice vertex algebra. -/

import D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2ChargedOrbit
import D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2ChargedOrbitFinite
import D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2NeutralFinite

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.ActualFixedC2

open ActualLeechHyperbolic (leechData)
open LatticeGeneratingFieldLocality LatticeInvolution

noncomputable local instance (D : LatticeData) : AddCommGroup (FixedCarrier D) :=
  (fixedSpace D).addCommGroup

/-- The orbit of zero consists exactly of the fixed states at vacuum charge. -/
theorem fixed_charge_orbit_zero_eq_fixed_neutral_space (D : LatticeData) :
    fixedChargeOrbit D 0 = fixedNeutralSpace D := by
  rw [fixedChargeOrbit, fixedNeutralSpace, neg_zero, Set.pair_eq_singleton]
  apply congrArg (fun S : Submodule ℂ (Carrier D) => S.comap (fixedSpace D).subtype)
  ext p
  rw [Finsupp.mem_supported, LinearMap.mem_range, ← Finset.coe_singleton,
    Finset.coe_subset, Finsupp.support_subset_singleton']
  simp only [Finsupp.lsingle_apply, eq_comm]

/-- The actual sign-fixed Leech lattice vertex algebra is intrinsically C₂-cofinite. -/
theorem leech_fixed_c2_cofinite :
    FiniteDimensional ℂ (FixedCarrier leechData ⧸ fixedC2 leechData) := by
  obtain ⟨hfinite, htop⟩ := leech_fixed_c2_finite_charge_support
  let : Finite (ActualC2Cofinite.shortCharges leechData) := hfinite
  let orbitImage (c : ActualC2Cofinite.shortCharges leechData) :=
    (fixedChargeOrbit leechData c.val).map (fixedC2 leechData).mkQ
  let : ∀ c, Module.Finite ℂ (orbitImage c) := by
    intro c
    change FiniteDimensional ℂ ((fixedChargeOrbit leechData c.val).map (fixedC2 leechData).mkQ)
    by_cases hc : c.val = 0
    · rw [hc, fixed_charge_orbit_zero_eq_fixed_neutral_space]
      exact leech_fixed_neutral_image_finite
    · exact leech_fixed_charge_orbit_image_finite c.val hc
  have finiteSup : Module.Finite ℂ (⨆ c, orbitImage c : Submodule ℂ _) :=
    Submodule.finite_iSup orbitImage
  change (⨆ c, orbitImage c) = ⊤ at htop
  rw [htop] at finiteSup
  exact Module.Finite.of_fg_top (Module.Finite.iff_fg.mp finiteSup)

#print axioms fixed_charge_orbit_zero_eq_fixed_neutral_space
#print axioms leech_fixed_c2_cofinite

end D5.S3.VertexAlgebra.Lattice.ActualFixedC2
