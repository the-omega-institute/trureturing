import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldZeroMomentumSemirelativeGhostNumber
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Eigenspace.Basic

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
-- Compare maps through the native cycle quotient.
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

section HomogeneousBasis

open OriginalOrbifoldRelativeNull (ShellIndex bottom middle top ghostNumber)

open private chiralShellNumber_basis from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldZeroMomentumSemirelativeGhostNumber
open private tensorBasis connection_basis imageGenerators coord_tensorBasis connection_range from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldZeroMomentumSemirelativeSpectrum

open scoped BigOperators

private def tensorDegree (p : ShellIndex × ShellIndex) : ℕ :=
  ghostNumber p.1 + ghostNumber p.2

private theorem relativeNumber_tensorBasis (p : ShellIndex × ShellIndex) :
    N_R (tensorBasis p) = (tensorDegree p : ℂ) • tensorBasis p := by
  rcases p with ⟨i, j⟩
  change N_R (tensorBasis (i, j)) = ((ghostNumber i + ghostNumber j : ℕ) : ℂ) • tensorBasis (i, j)
  simp only [zeroRelativeGhostNumber, LinearMap.add_apply, Module.Basis.tensorProduct_apply',
    TensorProduct.map_tmul, LinearMap.id_apply, chiralShellNumber_basis, ← TensorProduct.smul_tmul',
    TensorProduct.tmul_smul, ← add_smul, Nat.cast_add]

private def cokernelIndex : Fin 10 → ShellIndex × ShellIndex :=
  ![(bottom, bottom), (bottom, middle 0), (bottom, middle 1), (middle 0, bottom),
    (middle 1, bottom), (bottom, top), (middle 0, middle 0), (middle 0, middle 1),
    (middle 1, middle 0), (middle 1, middle 1)]

private def kernelIndex : Fin 10 → ShellIndex × ShellIndex :=
  ![(top, bottom), (middle 0, middle 0), (middle 0, middle 1), (middle 0, top),
    (middle 1, middle 0), (middle 1, middle 1), (middle 1, top), (top, middle 0),
    (top, middle 1), (top, top)]

private def kernelRepresentative (i : Fin 10) : Rel :=
  tensorBasis (kernelIndex i) - (if i = 0 then tensorBasis (bottom, top) else 0)

private theorem kernelRepresentative_mem (i : Fin 10) : T (kernelRepresentative i) = 0 := by
  by_cases hi : i = 0
  · subst i
    change T (tensorBasis (top, bottom) - tensorBasis (bottom, top)) = 0
    rw [(T).map_sub, connection_basis, connection_basis]
    simp [bottom, top]
  · have h : ∀ j : Fin 10, j ≠ 0 → (kernelIndex j).1 ≠ bottom ∧ (kernelIndex j).2 ≠ bottom := by
      decide
    obtain ⟨h₁, h₂⟩ := h i hi
    rw [kernelRepresentative, ite_eq_right hi, sub_zero]
    change T (tensorBasis ((kernelIndex i).1, (kernelIndex i).2)) = 0
    rw [connection_basis, ite_eq_right h₁, ite_eq_right h₂, zero_add]

private theorem kernelRepresentative_number (i : Fin 10) :
    N_R (kernelRepresentative i) = (tensorDegree (kernelIndex i) : ℂ) • kernelRepresentative i := by
  by_cases hi : i = 0
  · subst i
    change N_R (tensorBasis (top, bottom) - tensorBasis (bottom, top)) =
      (tensorDegree (top, bottom) : ℂ) • (tensorBasis (top, bottom) - tensorBasis (bottom, top))
    have h : tensorDegree (bottom, top) = tensorDegree (top, bottom) := rfl
    rw [(N_R).map_sub, relativeNumber_tensorBasis, relativeNumber_tensorBasis, h, smul_sub]
  · simp only [kernelRepresentative, ite_eq_right hi, sub_zero, relativeNumber_tensorBasis]

private def cokernelVector (i : Fin 10) : ZeroShellCokernel :=
  (LinearMap.range T).mkQ (tensorBasis (cokernelIndex i))

private def kernelVector (i : Fin 10) : K :=
  ⟨kernelRepresentative i, kernelRepresentative_mem i⟩

-- Read the bottom–top coefficient modulo the top–bottom pivot.
private def cokernelCoordinate (i : Fin 10) : Rel →ₗ[ℂ] ℂ :=
  tensorBasis.coord (cokernelIndex i) - (if i = 5 then tensorBasis.coord (top, bottom) else 0)

private theorem cokernelCoordinate_apply_basis (i : Fin 10) (p : ShellIndex × ShellIndex) :
    cokernelCoordinate i (tensorBasis p) =
      (if p = cokernelIndex i then 1 else 0) -
        (if i = 5 ∧ p = (top, bottom) then 1 else 0) := by
  by_cases hi : i = 5
  · rw [cokernelCoordinate, ite_eq_left hi]
    simp only [LinearMap.sub_apply, coord_tensorBasis, hi, true_and]
  · rw [cokernelCoordinate, ite_eq_right hi]
    simp only [LinearMap.sub_apply, coord_tensorBasis, LinearMap.zero_apply, hi, false_and, ite_false]

set_option maxHeartbeats 2000000 in
-- Evaluate the dual coordinates on the six native range generators.
private theorem cokernelCoordinate_kills (i : Fin 10) :
    LinearMap.range T ≤ LinearMap.ker (cokernelCoordinate i) := by
  rw [connection_range]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  change cokernelCoordinate i (imageGenerators j) = 0
  fin_cases j <;>
    simp only [imageGenerators, Matrix.cons_val_zero', Matrix.cons_val_succ',
      LinearMap.map_add, cokernelCoordinate_apply_basis] <;>
    fin_cases i <;> simp [cokernelIndex, bottom, middle, top]

private theorem independent_of_dual {M : Type*} [AddCommGroup M] [Module ℂ M]
    (vectors : Fin 10 → M) (coordinate : Fin 10 → M →ₗ[ℂ] ℂ)
    (h : ∀ i j, coordinate i (vectors j) = if j = i then 1 else 0) :
    LinearIndependent ℂ vectors := by
  apply (Fintype.linearIndependent_iff (R := ℂ) (v := vectors)).mpr
  intro c hc i
  have hi := congrArg (coordinate i) hc
  simp only [map_sum, map_smul, map_zero, h, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hi
  exact hi

set_option maxHeartbeats 800000 in
-- Elaborate the quotient dual basis against the native tensor instances.
private def cokernelBasis : Module.Basis (Fin 10) ℂ ZeroShellCokernel := by
  refine basisOfLinearIndependentOfCardEqFinrank (b := cokernelVector) ?_ ?_
  · refine independent_of_dual cokernelVector
      (fun i => (LinearMap.range T).liftQ (cokernelCoordinate i) (cokernelCoordinate_kills i)) ?_
    intro i j
    change cokernelCoordinate i (tensorBasis (cokernelIndex j)) = _
    have hinj : Function.Injective cokernelIndex := by
      change ∀ a b : Fin 10, cokernelIndex a = cokernelIndex b → a = b
      decide
    have hne : ∀ j : Fin 10, cokernelIndex j ≠ (top, bottom) := by decide
    rw [cokernelCoordinate_apply_basis]
    simp only [hinj.eq_iff, hne j, and_false, ite_false, sub_zero]
  · rw [Fintype.card_fin, zeroShellConnection_coker_finrank]

set_option maxHeartbeats 800000 in
-- Elaborate the restricted dual basis against the native kernel subtype.
private def kernelBasis : Module.Basis (Fin 10) ℂ K := by
  refine basisOfLinearIndependentOfCardEqFinrank (b := kernelVector) ?_ ?_
  · refine independent_of_dual kernelVector
      (fun i => (tensorBasis.coord (kernelIndex i)).comp (K).subtype) ?_
    intro i j
    change tensorBasis.coord (kernelIndex i) (kernelRepresentative j) = _
    have hinj : Function.Injective kernelIndex := by
      change ∀ a b : Fin 10, kernelIndex a = kernelIndex b → a = b
      decide
    have hne : ∀ i : Fin 10, (bottom, top) ≠ kernelIndex i := by decide
    by_cases hj : j = 0
    · simp only [kernelRepresentative, ite_eq_left hj, LinearMap.map_sub,
        coord_tensorBasis, hinj.eq_iff, ite_eq_right (hne i), sub_zero]
    · simp only [kernelRepresentative, ite_eq_right hj, sub_zero, coord_tensorBasis, hinj.eq_iff]
  · rw [Fintype.card_fin, zeroShellConnection_ker_finrank]

/-- The ten unpivoted classes and the ten kernel vectors, transported to native cohomology. -/
def zeroShellCohomologyGhostBasis : Module.Basis (Fin 10 ⊕ Fin 10) ℂ ZeroShellCohomology :=
  (cokernelBasis.prod kernelBasis).map zeroShellCohomologyEquiv.symm

/-- Chiral degrees add in each tensor. The kernel coordinate has the sum ghost inserted. -/
def zeroShellCohomologyGhostDegree : Fin 10 ⊕ Fin 10 → ℕ
  | .inl i => tensorDegree (cokernelIndex i)
  | .inr i => tensorDegree (kernelIndex i) + 1

/-- The basis index determines a cycle in native coordinates, before taking the quotient. -/
def zeroShellCohomologyGhostRepresentative : Fin 10 ⊕ Fin 10 → LinearMap.ker D
  | .inl i => coordinateCycle (tensorBasis (cokernelIndex i)) 0
  | .inr i => coordinateCycle 0 (kernelVector i)

theorem zeroShellCohomologyGhostRepresentative_coordinates (i : Fin 10 ⊕ Fin 10) :
    (zeroShellCohomologyGhostRepresentative i : zeroMomentumShell) =
      S (match i with
        | .inl j => (tensorBasis (cokernelIndex j), 0)
        | .inr j => (0, kernelRepresentative j)) := by
  cases i <;> rfl

set_option maxHeartbeats 800000 in
-- Compare the two quotient classes via the native coordinates equivalence.
theorem zeroShellCohomologyGhostBasis_class (i : Fin 10 ⊕ Fin 10) :
    zeroShellCohomologyGhostBasis i = (B).mkQ (zeroShellCohomologyGhostRepresentative i) := by
  apply zeroShellCohomologyEquiv.injective
  cases i with
  | inl j =>
    change zeroShellCohomologyEquiv (zeroShellCohomologyEquiv.symm
      (cokernelBasis.prod kernelBasis (.inl j))) =
      zeroShellCohomologyEquiv ((B).mkQ (coordinateCycle (tensorBasis (cokernelIndex j)) 0))
    simp only [LinearEquiv.apply_symm_apply, Module.Basis.prod_apply, Sum.elim_inl,
      Function.comp_apply, LinearMap.inl_apply, cokernelBasis,
      coe_basisOfLinearIndependentOfCardEqFinrank, cokernelVector, coordinateCycle_class]
  | inr j =>
    change zeroShellCohomologyEquiv (zeroShellCohomologyEquiv.symm
      (cokernelBasis.prod kernelBasis (.inr j))) =
      zeroShellCohomologyEquiv ((B).mkQ (coordinateCycle 0 (kernelVector j)))
    simp only [LinearEquiv.apply_symm_apply, Module.Basis.prod_apply, Sum.elim_inr,
      Function.comp_apply, LinearMap.inr_apply, kernelBasis,
      coe_basisOfLinearIndependentOfCardEqFinrank, coordinateCycle_class, map_zero]

set_option maxHeartbeats 800000 in
-- Transport scalar multiplication through the native shell equivalence.
theorem zeroShellCohomologyGhostRepresentative_number (i : Fin 10 ⊕ Fin 10) :
    N_X (zeroShellCohomologyGhostRepresentative i : zeroMomentumShell) =
      (zeroShellCohomologyGhostDegree i : ℂ) •
        (zeroShellCohomologyGhostRepresentative i : zeroMomentumShell) := by
  rw [zeroShellCohomologyGhostRepresentative_coordinates, ← (S).map_smul]
  cases i with
  | inl j =>
    rw [zeroShellGhostNumber_coordinates, relativeNumber_tensorBasis, map_zero, add_zero]
    exact congrArg S (Prod.ext rfl (smul_zero (zeroShellCohomologyGhostDegree (.inl j) : ℂ)).symm)
  | inr j =>
    rw [zeroShellGhostNumber_coordinates, map_zero, kernelRepresentative_number]
    apply congrArg S
    exact Prod.ext (smul_zero (zeroShellCohomologyGhostDegree (.inr j) : ℂ)).symm (by
      change (tensorDegree (kernelIndex j) : ℂ) • kernelRepresentative j +
          kernelRepresentative j = ((tensorDegree (kernelIndex j) + 1 : ℕ) : ℂ) •
            kernelRepresentative j
      rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul])

set_option maxHeartbeats 800000 in
-- Rewrite in the native quotient before applying the representative identity.
theorem zeroShellCohomologyGhostBasis_number (i : Fin 10 ⊕ Fin 10) :
    zeroShellCohomologyGhostNumber (zeroShellCohomologyGhostBasis i) =
      (zeroShellCohomologyGhostDegree i : ℂ) • zeroShellCohomologyGhostBasis i := by
  rw [zeroShellCohomologyGhostBasis_class]
  exact zeroShellCohomologyGhostNumber_homogeneous _ _
    (zeroShellCohomologyGhostRepresentative_number i)

/-- The unshifted cokernel degrees and shifted kernel degrees in basis order. -/
theorem zeroShellCohomologyGhostDegree_lists :
    List.ofFn (fun i : Fin 10 => zeroShellCohomologyGhostDegree (.inl i)) =
      [0, 1, 1, 1, 1, 2, 2, 2, 2, 2] ∧
    List.ofFn (fun i : Fin 10 => zeroShellCohomologyGhostDegree (.inr i)) =
      [3, 3, 3, 4, 3, 3, 4, 4, 4, 5] := by
  decide

set_option maxHeartbeats 800000 in
-- Compare linear maps through the native quotient basis.
/-- In the homogeneous basis, each coordinate of ghost number scales by its own degree. -/
private theorem ghostNumber_coord (i : Fin 10 ⊕ Fin 10) :
    ((zeroShellCohomologyGhostBasis.coord i).comp zeroShellCohomologyGhostNumber) =
      (zeroShellCohomologyGhostDegree i : ℂ) • zeroShellCohomologyGhostBasis.coord i := by
  apply zeroShellCohomologyGhostBasis.ext
  intro j
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, zeroShellCohomologyGhostBasis_number,
    map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases h : j = i
  · subst j
    rfl
  · simp only [ite_eq_right h, smul_zero]

set_option maxHeartbeats 800000 in
-- Elaborate the span and coefficient sums in the native quotient.
/-- The native eigenspace is precisely the span of basis classes of that ghost number. -/
theorem zeroShellCohomologyGhostEigenspace_eq_span (μ : ℂ) :
    zeroShellCohomologyGhostNumber.eigenspace μ =
      Submodule.span ℂ (Set.range fun i : {i // (zeroShellCohomologyGhostDegree i : ℂ) = μ} =>
        zeroShellCohomologyGhostBasis i.val) := by
  classical
  apply le_antisymm
  · intro x hx
    have hx' := Module.End.mem_eigenspace_iff.mp hx
    let b := zeroShellCohomologyGhostBasis
    have hzero (i : Fin 10 ⊕ Fin 10) (hi : (zeroShellCohomologyGhostDegree i : ℂ) ≠ μ) :
        b.repr x i = 0 := by
      have h := LinearMap.congr_fun (ghostNumber_coord i) x
      simp only [LinearMap.comp_apply, hx', map_smul, LinearMap.smul_apply, smul_eq_mul,
        Module.Basis.coord_apply] at h
      have hz : ((zeroShellCohomologyGhostDegree i : ℂ) - μ) * b.repr x i = 0 := by
        rw [sub_mul, sub_eq_zero]
        exact h.symm
      exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hi)
    let s := Finset.univ.filter (fun i => (zeroShellCohomologyGhostDegree i : ℂ) = μ)
    have hs : (∑ i ∈ s, b.repr x i • b i) = x :=
      (Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by
        have hne : (zeroShellCohomologyGhostDegree i : ℂ) ≠ μ := by
          intro heq
          exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, heq⟩)
        rw [hzero i hne, zero_smul])).trans (b.sum_repr x)
    rw [← hs]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, (Finset.mem_filter.mp hi).2⟩, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Module.End.mem_eigenspace_iff.mpr
      ((zeroShellCohomologyGhostBasis_number i.val).trans
        (congrArg (fun d : ℂ => d • zeroShellCohomologyGhostBasis i.val) i.property))

private theorem ghostDegree_lt_six : ∀ i, zeroShellCohomologyGhostDegree i < 6 := by decide

private def ghostDegreePopulation (n : ℕ) : ℕ :=
  (Finset.univ.filter fun i => zeroShellCohomologyGhostDegree i = n).card

private theorem ghostDegreePopulation_small :
    ∀ n : Fin 6, ghostDegreePopulation n = (![1, 4, 5, 5, 4, 1] : Fin 6 → ℕ) n := by
  decide

set_option maxHeartbeats 800000 in
-- Compare spans indexed by complex and natural ghost degrees.
/-- Ghost degrees zero through five have populations one, four, five, five, four and one. -/
theorem zeroShellCohomologyGhostEigenspace_finrank (n : ℕ) :
    Module.finrank ℂ (zeroShellCohomologyGhostNumber.eigenspace (n : ℂ)) =
      if h : n < 6 then (![1, 4, 5, 5, 4, 1] : Fin 6 → ℕ) ⟨n, h⟩ else 0 := by
  have hspan : zeroShellCohomologyGhostNumber.eigenspace (n : ℂ) =
      Submodule.span ℂ (Set.range fun i : {i // zeroShellCohomologyGhostDegree i = n} =>
        zeroShellCohomologyGhostBasis i.val) := by
    rw [zeroShellCohomologyGhostEigenspace_eq_span]
    apply congrArg (Submodule.span ℂ)
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨⟨i.val, Nat.cast_injective i.property⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨⟨i.val, congrArg (fun n : ℕ => (n : ℂ)) i.property⟩, rfl⟩
  have hrank : Module.finrank ℂ (zeroShellCohomologyGhostNumber.eigenspace (n : ℂ)) =
      Fintype.card {i // zeroShellCohomologyGhostDegree i = n} := by
    rw [hspan]
    apply finrank_span_eq_card
    exact zeroShellCohomologyGhostBasis.linearIndependent.comp
      (fun i : {i // zeroShellCohomologyGhostDegree i = n} => i.val) Subtype.val_injective
  rw [hrank, Fintype.card_subtype]
  change ghostDegreePopulation n = _
  by_cases hn : n < 6
  · rw [dite_eq_left hn]
    exact ghostDegreePopulation_small ⟨n, hn⟩
  · rw [dite_eq_right hn]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have heq := (Finset.mem_filter.mp hi).2
    exact hn (heq ▸ ghostDegree_lt_six i)

set_option maxHeartbeats 800000 in
-- Rewrite the span of the empty family in the native quotient.
/-- The native eigenspace is zero outside the six ghost degrees. -/
theorem zeroShellCohomologyGhostEigenspace_eq_bot (μ : ℂ)
    (hμ : ∀ n : Fin 6, μ ≠ (n.val : ℂ)) :
    zeroShellCohomologyGhostNumber.eigenspace μ = ⊥ := by
  have : IsEmpty {i // (zeroShellCohomologyGhostDegree i : ℂ) = μ} :=
    ⟨fun i => hμ ⟨zeroShellCohomologyGhostDegree i.val, ghostDegree_lt_six i.val⟩ i.property.symm⟩
  rw [zeroShellCohomologyGhostEigenspace_eq_span, Set.range_eq_empty, Submodule.span_empty]

#print axioms zeroShellCohomologyGhostBasis
#print axioms zeroShellCohomologyGhostDegree
#print axioms zeroShellCohomologyGhostRepresentative
#print axioms zeroShellCohomologyGhostRepresentative_coordinates
#print axioms zeroShellCohomologyGhostBasis_class
#print axioms zeroShellCohomologyGhostRepresentative_number
#print axioms zeroShellCohomologyGhostBasis_number
#print axioms zeroShellCohomologyGhostDegree_lists
#print axioms zeroShellCohomologyGhostEigenspace_eq_span
#print axioms zeroShellCohomologyGhostEigenspace_finrank
#print axioms zeroShellCohomologyGhostEigenspace_eq_bot

end HomogeneousBasis

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
