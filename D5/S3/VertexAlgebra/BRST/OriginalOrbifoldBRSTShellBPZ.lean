/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTShellBPZ
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTShellBPZ
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.PerfectPairing.Basic]
   utility: none
   digest: Perfect relative BPZ pairing of opposite native mass shells and its cycle annihilator. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTPhysicalPairing
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTRelativeBPZNondegenerate

/-! The native momentum projections reduce relative BPZ nondegeneracy to
opposite mass shells. The relative Ward identity then identifies the left
annihilator of opposite cycles with the native shell boundaries. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTShellBPZ

open OriginalOrbifoldCriticalMatter (Matter State hyperbolicData)
open OriginalOrbifoldBRSTDescent (relativeStates)
open OriginalOrbifoldBRSTBPZWard (betaRelTotal betaRelTotal_ward parityRelative)
open OriginalOrbifoldBRSTRelativeBPZNondegenerate (betaRelTotal_nondegenerate)
open OriginalOrbifoldBRSTSignedLocality (parity)
open OriginalOrbifoldRelativeMassShell (fixedMomentum relativeMassShell
  relativeMassShell_finiteDimensional differential)
open LatticeGeneratingFieldLocality (Charge)

open private relativePart momentumPart_mem momentumPart_of_mem momentumPart_commutes_diagonal
  momentumSupport sum_momentumPart from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTMomentum
open private betaRelTotal_eq_zero_of_momentum from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTPhysicalPairing
open private parity_basis from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTPhysicalLie
open private parity_square from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescent

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private abbrev UCharge := Charge hyperbolicData

private def shellInclusion (p : UCharge) : relativeMassShell p →ₗ[ℂ] relativeStates :=
  Submodule.inclusion (by
    intro x hx
    exact ⟨hx.1.2, hx.2⟩)

private theorem shellInclusion_injective (p : UCharge) :
    Function.Injective (shellInclusion p) := by
  unfold shellInclusion
  exact Submodule.inclusion_injective _

private theorem shell_mem_fixedMomentum {p : UCharge} (x : relativeMassShell p) :
    (x : State) ∈ fixedMomentum p :=
  x.property.1.1

private def shellState (p : UCharge) (x : relativeStates)
    (hx : (x : State) ∈ fixedMomentum p) : relativeMassShell p :=
  ⟨(x : State), ⟨⟨hx, x.property.1⟩, x.property.2⟩⟩

private theorem sum_relativePart (x : relativeStates) :
    ∑ q ∈ momentumSupport (x : State), relativePart q x = x := by
  apply relativeStates.subtype_injective
  change relativeStates.subtype (∑ q ∈ momentumSupport (x : State), relativePart q x) =
    (x : State)
  rw [map_sum]
  exact sum_momentumPart (x : State)

/-- The native relative BPZ form restricted to opposite fixed-momentum mass shells. -/
def shellBPZ (p : UCharge) :
    relativeMassShell p →ₗ[ℂ] relativeMassShell (-p) →ₗ[ℂ] ℂ :=
  betaRelTotal.compl₁₂ (shellInclusion p) (shellInclusion (-p))

private theorem shellBPZ_separatingLeft (p : UCharge) : (shellBPZ p).SeparatingLeft := by
  intro x hx
  apply shellInclusion_injective p
  rw [map_zero]
  refine betaRelTotal_nondegenerate.1 (shellInclusion p x) ?_
  intro y
  rw [← sum_relativePart y, map_sum]
  apply Finset.sum_eq_zero
  intro q _
  by_cases hq : q = -p
  · subst q
    exact hx (shellState (-p) (relativePart (-p) y) (momentumPart_mem (-p) (y : State)))
  · exact betaRelTotal_eq_zero_of_momentum (x := shellInclusion p x) (y := relativePart q y)
      hq (shell_mem_fixedMomentum x) (momentumPart_mem q (y : State))

private theorem shellBPZ_separatingRight (p : UCharge) : (shellBPZ p).SeparatingRight := by
  intro y hy
  apply shellInclusion_injective (-p)
  rw [map_zero]
  refine betaRelTotal_nondegenerate.2 (shellInclusion (-p) y) ?_
  intro x
  change betaRelTotal.flip (shellInclusion (-p) y) x = 0
  rw [← sum_relativePart x, map_sum]
  apply Finset.sum_eq_zero
  intro q _
  by_cases hq : q = p
  · subst q
    exact hy (shellState p (relativePart p x) (momentumPart_mem p (x : State)))
  · have hne : -p ≠ -q := fun he => hq (neg_injective he.symm)
    exact betaRelTotal_eq_zero_of_momentum (x := relativePart q x) (y := shellInclusion (-p) y)
      hne (momentumPart_mem q (x : State)) (shell_mem_fixedMomentum y)

/-- The inserted BPZ pairing on opposite mass shells induces bijections to both duals. -/
theorem shellBPZ_isPerfPair (p : UCharge) : (shellBPZ p).IsPerfPair := by
  let : FiniteDimensional ℂ (relativeMassShell p) := relativeMassShell_finiteDimensional p
  exact LinearMap.IsPerfPair.of_injective
    (LinearMap.ker_eq_bot.mp
      (LinearMap.separatingLeft_iff_ker_eq_bot.mp (shellBPZ_separatingLeft p)))
    (LinearMap.ker_eq_bot.mp
      (LinearMap.separatingRight_iff_flip_ker_eq_bot.mp (shellBPZ_separatingRight p)))

private theorem parity_mem_fixedMomentum {p : UCharge} {x : State}
    (hx : x ∈ fixedMomentum p) : parity x ∈ fixedMomentum p := by
  have h := LinearMap.congr_fun
    (momentumPart_commutes_diagonal p parity _ parity_basis) x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, momentumPart_of_mem hx] at h
  have hmem := momentumPart_mem p (parity x)
  rwa [h] at hmem

private def shellParity (p : UCharge) (x : relativeMassShell p) : relativeMassShell p :=
  shellState p (parityRelative (shellInclusion p x))
    (parity_mem_fixedMomentum (shell_mem_fixedMomentum x))

private theorem shellParity_square (p : UCharge) (x : relativeMassShell p) :
    shellParity p (shellParity p x) = x :=
  Subtype.ext (parity_square (x : State))

private theorem shellBPZ_ward (p : UCharge) (x : relativeMassShell p)
    (y : relativeMassShell (-p)) :
    shellBPZ p (differential p x) y =
      shellBPZ p (shellParity p x) (differential (-p) y) :=
  betaRelTotal_ward (shellInclusion p x) (shellInclusion (-p) y)

/-- The left annihilator of the opposite shell cycles is the image of the native differential. -/
theorem shellBPZ_left_cycle_annihilator (p : UCharge) :
    (LinearMap.ker (differential (-p))).dualAnnihilator.comap (shellBPZ p) =
      LinearMap.range (differential p) := by
  let : (shellBPZ p).IsPerfPair := shellBPZ_isPerfPair p
  apply Submodule.ext
  intro x
  change shellBPZ p x ∈ (LinearMap.ker (differential (-p))).dualAnnihilator ↔
    x ∈ LinearMap.range (differential p)
  constructor
  · intro hx
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hx
    obtain ⟨ψ, hψ⟩ := LinearMap.mem_range.mp hx
    obtain ⟨v, hv⟩ := (LinearMap.IsPerfPair.bijective_left (shellBPZ p)).surjective ψ
    refine LinearMap.mem_range.mpr ⟨shellParity p v, ?_⟩
    apply (LinearMap.IsPerfPair.bijective_left (shellBPZ p)).injective
    apply LinearMap.ext
    intro y
    calc
      shellBPZ p (differential p (shellParity p v)) y =
          shellBPZ p v (differential (-p) y) := by
        rw [shellBPZ_ward, shellParity_square]
      _ = ψ (differential (-p) y) := LinearMap.congr_fun hv _
      _ = shellBPZ p x y := by
        simpa only [LinearMap.dualMap_apply] using LinearMap.congr_fun hψ y
  · intro hx
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hx
    rw [Submodule.mem_dualAnnihilator]
    intro y hy
    rw [shellBPZ_ward, LinearMap.mem_ker.mp hy, map_zero]

#print axioms shellBPZ
#print axioms shellBPZ_isPerfPair
#print axioms shellBPZ_left_cycle_annihilator

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTShellBPZ
