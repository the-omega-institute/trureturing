/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNegativeTwistedSchur
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldNegativeTwistedSchur
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Schur scalarity and vacuum-left fusion for the actual negative twisted Leech slice. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldNegativeTwistedIrreducible
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldVacuumChannel
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldVacuumFirstFusion
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-! A fixed-mode endomorphism preserves the finite weight-two space of the
negative twisted Leech module. A complex eigenvector there gives a nonzero
eigenspace in the whole module, where irreducibility forces scalarity. -/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldNegativeTwistedSchur

open ActualLeechHyperbolic (leechData leech_spec)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open HalfFock.NormFourFirstGradeSpectrum (actual_grade_one_eq_parity_minus_energy_two)
open LatticeInvolution (FixedCarrier)
open LatticeHalfFockChargedTensorCoefficients (ActualTensor)
open LatticeHalfFockGradedTrace
  (actualGrade actualTensorL0 actual_rank24_grade_one_finrank_98304)
open OriginalOrbifoldConformal (conformalVector)
open OriginalOrbifoldNegativeTwistedIrreducible (NegativeTwisted negative_twisted_irreducible)
open OriginalOrbifoldSectorModules (fixedParityY)
open OriginalOrbifoldTwistedModeMorphisms (fixedModeHom fixedParity_conformal_mode_val)
open OriginalOrbifoldVacuumChannel (weightTwo intoTwisted)
open VacuumFirstIntertwinerDraft (leechTwistedVacuumFirstEquiv twistedUnitSpace)
open Module.End (mem_eigenspace_iff)
open scoped VertexOperator

noncomputable section

local notation "hu" => And.left (And.right leech_spec)
local notation "mode" => fun (a : FixedCarrier leechData) (n : ℤ) =>
  (fixedParityY leechData hu (-1) a)[[n]]

set_option maxHeartbeats 1200000 in
-- The conformal mode comparison crosses the two subtypes of the actual tensor space.
private theorem exists_weightTwo_eigenvector (f : fixedModeHom (-1) (-1)) :
    ∃ (c : ℂ) (v : weightTwo), v ≠ 0 ∧ f.val (intoTwisted v) = c • intoTwisted v := by
  let ω := (conformalVector leechData hu).1
  let ambient : weightTwo →ₗ[ℂ] ActualTensor leechData hu :=
    (paritySpace leechData hu (-1)).subtype.comp (f.val.comp intoTwisted)
  have preserves (v : weightTwo) : ambient v ∈ weightTwo := by
    refine ⟨(f.val (intoTwisted v)).property, mem_eigenspace_iff.mpr ?_⟩
    have hv : mode ω 1 (intoTwisted v) = (2 : ℂ) • intoTwisted v := by
      apply Subtype.ext
      rw [fixedParity_conformal_mode_val]
      exact mem_eigenspace_iff.mp v.property.2
    change actualTensorL0 leechData hu (f.val (intoTwisted v)).val =
      (2 : ℂ) • (f.val (intoTwisted v)).val
    rw [← fixedParity_conformal_mode_val]
    exact congrArg Subtype.val (calc
      mode ω 1 (f.val (intoTwisted v)) = f.val (mode ω 1 (intoTwisted v)) :=
        (f.property ω 1 (intoTwisted v)).symm
      _ = (2 : ℂ) • f.val (intoTwisted v) := by rw [hv, map_smul])
  let F : Module.End ℂ weightTwo := ambient.codRestrict weightTwo preserves
  have gradeOne : actualGrade leechData hu 1 = weightTwo :=
    actual_grade_one_eq_parity_minus_energy_two leechData hu leech_spec.1
  let : FiniteDimensional ℂ weightTwo := by
    rw [← gradeOne]
    infer_instance
  have hdim : Module.finrank ℂ weightTwo = 98304 := by
    rw [← gradeOne]
    exact (actual_rank24_grade_one_finrank_98304 leechData hu leech_spec.1).2.1
  have hdegree : 0 < F.charpoly.degree := by
    apply Polynomial.natDegree_pos_iff_degree_pos.mp
    rw [LinearMap.charpoly_natDegree, hdim]
    decide
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root F.charpoly (ne_of_gt hdegree)
  obtain ⟨v, hv⟩ := ((F.hasEigenvalue_iff_isRoot_charpoly c).mpr hc).exists_hasEigenvector
  refine ⟨c, v, hv.2, ?_⟩
  have he := congrArg intoTwisted hv.apply_eq_smul
  rw [map_smul] at he
  exact he

set_option maxHeartbeats 1200000 in
-- The fixed modes and the commutant act on the same parity subtype.
/-- Every linear endomorphism commuting with the fixed physical modes on the
actual negative twisted Leech slice is a unique scalar times the identity. -/
theorem negative_twisted_mode_end_eq_smul (f : fixedModeHom (-1) (-1)) :
    ∃! c : ℂ, f.val = c • (LinearMap.id : Module.End ℂ NegativeTwisted) := by
  obtain ⟨c, v, hv, he⟩ := exists_weightTwo_eigenvector f
  have hv' : intoTwisted v ≠ 0 := fun h =>
    hv (Subtype.ext (congrArg (fun w : NegativeTwisted => w.val) h))
  let K : Submodule ℂ NegativeTwisted := Module.End.eigenspace f.val c
  have mem_K (w : NegativeTwisted) : w ∈ K ↔ f.val w = c • w :=
    mem_eigenspace_iff (f := f.val) (μ := c) (x := w)
  have stable (a : FixedCarrier leechData) (n : ℤ)
      (w : NegativeTwisted) (hw : w ∈ K) : mode a n w ∈ K := by
    apply (mem_K _).mpr
    calc
      f.val (mode a n w) = mode a n (f.val w) := f.property a n w
      _ = mode a n (c • w) := congrArg (mode a n) ((mem_K w).mp hw)
      _ = c • mode a n w := map_smul (mode a n) c w
  have hK : K ≠ ⊥ := by
    intro h
    have hmem : intoTwisted v ∈ K := (mem_K _).mpr he
    rw [h, Submodule.mem_bot] at hmem
    exact hv' hmem
  have htop : K = ⊤ := (negative_twisted_irreducible K stable).resolve_left hK
  refine ⟨c, LinearMap.ext (fun w => (mem_K w).mp (htop.symm ▸ Submodule.mem_top)), ?_⟩
  intro d hd
  exact smul_left_injective ℂ hv' ((LinearMap.congr_fun hd (intoTwisted v)).symm.trans he)

set_option maxHeartbeats 1200000 in
-- The scalar map lands in the submodule cut out by every actual fixed mode.
/-- The linear isomorphism from the complex scalars to the actual fixed-mode
endomorphism space sends each scalar to its multiple of the identity. -/
def negativeTwistedModeEndEquiv : ℂ ≃ₗ[ℂ] fixedModeHom (-1) (-1) := by
  let scalarMap : ℂ →ₗ[ℂ] fixedModeHom (-1) (-1) :=
    (LinearMap.toSpanSingleton ℂ (Module.End ℂ NegativeTwisted) LinearMap.id).codRestrict
      (fixedModeHom (-1) (-1)) (by
        intro c a n v
        exact (map_smul (mode a n) c v).symm)
  apply LinearEquiv.ofBijective scalarMap
  constructor
  · intro c d h
    obtain ⟨s, _, hs⟩ := negative_twisted_mode_end_eq_smul (scalarMap c)
    exact (hs c rfl).trans (hs d (congrArg Subtype.val h)).symm
  · intro f
    obtain ⟨c, hc, _⟩ := negative_twisted_mode_end_eq_smul f
    exact ⟨c, Subtype.ext hc.symm⟩

/-- The full rational vacuum-left channel `V⁺ × T⁻ → T⁻` has dimension one. -/
theorem leech_twisted_negative_unit_finrank :
    Module.finrank ℂ (twistedUnitSpace leechData hu (-1) (-1)) = 1 := by
  rw [(leechTwistedVacuumFirstEquiv (-1) (-1)).finrank_eq,
    ← negativeTwistedModeEndEquiv.finrank_eq, Module.finrank_self]

#print axioms negative_twisted_mode_end_eq_smul
#print axioms negativeTwistedModeEndEquiv
#print axioms leech_twisted_negative_unit_finrank

end
end D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldNegativeTwistedSchur
