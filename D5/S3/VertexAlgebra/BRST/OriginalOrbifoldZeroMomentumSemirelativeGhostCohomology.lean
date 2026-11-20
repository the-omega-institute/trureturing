import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldZeroMomentumSemirelativeGhostNumber

/-! Ghost number on the original-orbifold zero-momentum semirelative cohomology. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldZeroMomentumSemirelativeGhostCohomology

noncomputable section

open OriginalOrbifoldCriticalMatter (Orbifold Hyperbolic Matter State)
open OriginalOrbifoldClosedSemirelative (ClosedState)
open OriginalOrbifoldGhostDilaton
  (ZeroChiralShell ZeroRelativeTensor zeroMomentumShell zeroShellConnection zeroShellDifferential)
open OriginalOrbifoldZeroMomentumSemirelativeGhostNumber
  (zeroRelativeGhostNumber zeroRelativeGhostNumber_connection zeroShellGhostNumber
    zeroShellGhostNumber_coordinates zeroShellGhostNumber_differential)
open OriginalOrbifoldZeroMomentumSemirelativeSpectrum
open D5.S3.HomologicalAlgebra.FinitePerturbation (Boundaries boundaryMap)

local instance : AddCommGroup Matter := TensorProduct.addCommGroup (M := Orbifold) (N := Hyperbolic)
local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)
local instance : AddCommGroup ClosedState := TensorProduct.addCommGroup (M := State)
local instance : AddCommGroup ZeroRelativeTensor :=
  TensorProduct.addCommGroup (M := ↥ZeroChiralShell)

local notation "Rel" => ZeroRelativeTensor
local notation "T" => zeroShellConnection
local notation "D" => zeroShellDifferential
local notation "B" => Boundaries D zeroShellDifferential_square
local notation "S" => zeroShellCoordinates
local notation "K" => LinearMap.ker T
local notation "N_X" => zeroShellGhostNumber
local notation "N_R" => zeroRelativeGhostNumber

private theorem shellNumber_differential_apply (x : zeroMomentumShell) :
    N_X (D x) = D (N_X x) + D x := by
  simpa only [Module.End.mul_apply, LinearMap.add_apply] using
    LinearMap.congr_fun zeroShellGhostNumber_differential x

private theorem shellNumber_mem_cycles (x : zeroMomentumShell) (hx : x ∈ LinearMap.ker D) :
    N_X x ∈ LinearMap.ker D := by
  change D x = 0 at hx
  change D (N_X x) = 0
  simpa only [hx, map_zero, add_zero] using (shellNumber_differential_apply x).symm

/-- The native closed ghost number restricted to the actual BRST cycles. -/
def zeroShellCycleGhostNumber : Module.End ℂ (LinearMap.ker D) :=
  (N_X).restrict shellNumber_mem_cycles

private theorem cycleNumber_mem_boundaries (x : LinearMap.ker D) (hx : x ∈ B) :
    zeroShellCycleGhostNumber x ∈ B := by
  change ∃ y : zeroMomentumShell, boundaryMap D zeroShellDifferential_square y = x at hx
  obtain ⟨y, rfl⟩ := hx
  refine ⟨N_X y + y, ?_⟩
  apply Subtype.ext
  change D (N_X y + y) = N_X (D y)
  rw [map_add, shellNumber_differential_apply]

/-- The native closed ghost number on the actual BRST kernel/image quotient. -/
def zeroShellCohomologyGhostNumber : Module.End ℂ ZeroShellCohomology :=
  (B).mapQ (B) zeroShellCycleGhostNumber (by
    intro x hx
    exact Submodule.mem_comap.mpr (cycleNumber_mem_boundaries x hx))

theorem zeroShellCohomologyGhostNumber_class (z : LinearMap.ker D) :
    zeroShellCohomologyGhostNumber ((B).mkQ z) = (B).mkQ (zeroShellCycleGhostNumber z) := rfl

/-- A homogeneous cycle gives a class on which ghost number acts by the same scalar. -/
theorem zeroShellCohomologyGhostNumber_homogeneous (z : LinearMap.ker D) (n : ℂ)
    (hz : N_X (z : zeroMomentumShell) = n • (z : zeroMomentumShell)) :
    zeroShellCohomologyGhostNumber ((B).mkQ z) = n • (B).mkQ z := by
  have h : zeroShellCycleGhostNumber z = n • z := Subtype.ext hz
  exact (zeroShellCohomologyGhostNumber_class z).trans
    ((congrArg (B).mkQ h).trans (map_smul (B).mkQ n z))

private theorem relativeNumber_connection_apply (v : Rel) :
    N_R (T v) = T (N_R v) + (2 : ℂ) • T v := by
  simpa only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply] using
    LinearMap.congr_fun zeroRelativeGhostNumber_connection v

/-- Relative ghost number descends through the actual range of the sum connection. -/
def zeroShellCokernelGhostNumber : Module.End ℂ ZeroShellCokernel :=
  (LinearMap.range T).mapQ (LinearMap.range T) N_R (by
    intro u hu
    change N_R u ∈ LinearMap.range T
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hu
    refine ⟨N_R w + (2 : ℂ) • w, ?_⟩
    rw [map_add, map_smul, relativeNumber_connection_apply])

theorem zeroShellCokernelGhostNumber_class (u : Rel) :
    zeroShellCokernelGhostNumber ((LinearMap.range T).mkQ u) =
      (LinearMap.range T).mkQ (N_R u) := rfl

/-- The sum-ghost insertion shifts relative ghost number by one on the kernel coordinate. -/
def zeroShellKernelGhostNumber : Module.End ℂ K :=
  (N_R + LinearMap.id).restrict (by
    intro v hv
    change T v = 0 at hv
    have h : T (N_R v) = 0 := by
      simpa only [hv, map_zero, smul_zero, add_zero] using
        (relativeNumber_connection_apply v).symm
    change T (N_R v + v) = 0
    rw [map_add, h, hv, add_zero])

theorem zeroShellKernelGhostNumber_apply (v : K) :
    (zeroShellKernelGhostNumber v : Rel) = N_R (v : Rel) + (v : Rel) := rfl

private def coordinateCycle (u : Rel) (v : K) : LinearMap.ker D :=
  ⟨S (u, (v : Rel)), by
    change D (S (u, (v : Rel))) = 0
    have hv : T (v : Rel) = 0 := v.property
    rw [zeroShellCoordinates_differential, hv]
    exact (S).map_zero⟩

private theorem coordinateCycle_class (u : Rel) (v : K) :
    zeroShellCohomologyEquiv ((B).mkQ (coordinateCycle u v)) =
      ((LinearMap.range T).mkQ u, v) :=
  zeroShellCohomologyEquiv_class u (v : Rel) v.property

private theorem cycleNumber_coordinateCycle (u : Rel) (v : K) :
    zeroShellCycleGhostNumber (coordinateCycle u v) =
      coordinateCycle (N_R u) (zeroShellKernelGhostNumber v) := by
  apply Subtype.ext
  exact zeroShellGhostNumber_coordinates u (v : Rel)

set_option maxHeartbeats 800000 in
/-- In native coordinates the two components are `([N_R u], N_R v + v)`. -/
theorem zeroShellCohomologyGhostNumber_equiv (c : ZeroShellCohomology) :
    zeroShellCohomologyEquiv (zeroShellCohomologyGhostNumber c) =
      (zeroShellCokernelGhostNumber (zeroShellCohomologyEquiv c).1,
        zeroShellKernelGhostNumber (zeroShellCohomologyEquiv c).2) := by
  obtain ⟨u, hu⟩ := Submodule.mkQ_surjective (LinearMap.range T) (zeroShellCohomologyEquiv c).1
  let v : K := (zeroShellCohomologyEquiv c).2
  have h : (B).mkQ (coordinateCycle u v) = c :=
    zeroShellCohomologyEquiv.injective ((coordinateCycle_class u v).trans (Prod.ext hu rfl))
  calc
    zeroShellCohomologyEquiv (zeroShellCohomologyGhostNumber c) =
        zeroShellCohomologyEquiv (zeroShellCohomologyGhostNumber ((B).mkQ (coordinateCycle u v))) :=
      congrArg (fun q => zeroShellCohomologyEquiv (zeroShellCohomologyGhostNumber q)) h.symm
    _ = zeroShellCohomologyEquiv ((B).mkQ (zeroShellCycleGhostNumber (coordinateCycle u v))) :=
      congrArg zeroShellCohomologyEquiv (zeroShellCohomologyGhostNumber_class (coordinateCycle u v))
    _ = zeroShellCohomologyEquiv ((B).mkQ
          (coordinateCycle (N_R u) (zeroShellKernelGhostNumber v))) :=
      congrArg (fun z : LinearMap.ker D => zeroShellCohomologyEquiv ((B).mkQ z))
        (cycleNumber_coordinateCycle u v)
    _ = ((LinearMap.range T).mkQ (N_R u), zeroShellKernelGhostNumber v) :=
      coordinateCycle_class (N_R u) (zeroShellKernelGhostNumber v)
    _ = (zeroShellCokernelGhostNumber (zeroShellCohomologyEquiv c).1,
          zeroShellKernelGhostNumber (zeroShellCohomologyEquiv c).2) := Prod.ext
      ((zeroShellCokernelGhostNumber_class u).symm.trans
        (congrArg zeroShellCokernelGhostNumber hu)) rfl

#print axioms zeroShellCycleGhostNumber
#print axioms zeroShellCohomologyGhostNumber
#print axioms zeroShellCohomologyGhostNumber_class
#print axioms zeroShellCohomologyGhostNumber_homogeneous
#print axioms zeroShellCokernelGhostNumber
#print axioms zeroShellCokernelGhostNumber_class
#print axioms zeroShellKernelGhostNumber
#print axioms zeroShellKernelGhostNumber_apply
#print axioms zeroShellCohomologyGhostNumber_equiv

end

end D5.S3.VertexAlgebra.OriginalOrbifoldZeroMomentumSemirelativeGhostCohomology
