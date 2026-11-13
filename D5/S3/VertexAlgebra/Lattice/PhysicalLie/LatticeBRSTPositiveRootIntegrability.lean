/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPositiveRootIntegrability
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPositiveRootIntegrability
   mirror-E: none(waiver:source-only-positive-root-integrability)
   anchors: []
   utility: none
   digest: Every positive-charge homogeneous physical-image adjoint is pointwise locally nilpotent. -/

/-
SOURCE_ONLY_UNCOMPILED.  This module keeps the original lattice, both inverse
Gram equations, the rank-26 binder, the original global quotient and the
literal physicalImage carrier.  The supplied private project_physical and
physical_charge_representative proofs are opened below; no replacement
quotient, positivity, finite-dimensional ambient hypothesis, or extra premise
is introduced.

Attribution: the supplied lattice/current/BRST constructions retain their
Bakalov--Kac, Scott Carnahan, Kalle Kytölä, Becchi--Rouet--Stora--Tyutin,
Kato--Ogawa and Lian--Zuckerman attribution. Mathlib and Batteries supply
the finite sums, subtypes, linear maps, iteration and private-name access.
This source repair is not native elaboration or kernel-acceptance evidence.
-/

import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalCharacter
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLieSectors
import Batteries.Tactic.OpenPrivate
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators TensorProduct

open private project_physical physical_charge_representative from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTNeutralPhysicalCartan
open private chargeProject_mem from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology
open private current_classOf from
  D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyBVSecondOrder

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPositiveRootIntegrability

open LatticeGeneratingFieldLocality
open LatticeMatterGhostCoupling (State)
open LatticeSugawaraCurrents (gramComplex)
open LatticePositiveEnergy (chargeEnergy two_chargeEnergy)
open LatticeRelativeMassShell (fixedMomentum)
open LatticeQuartetContraction (chargeProject)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie
  (physicalStates physicalStates_current physicalClass physicalImage)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLieSectors
  (current_charge)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology
  (chargeSupport sum_chargeProject inclusion sectorCycles inclusion_sectorClassOf sectorClassOf)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalChargeFiber
  (physicalChargeFiber)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalCharacter
  (physicalChargeFiber_eq_bot_of_level_neg)
open LatticeBRSTCohomologyField (Cohomology)
open D5.S3.VertexAlgebra.LatticeBRSTCohomologyBVSecondOrder
  (cohomologyCurrent descentCurrent)

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (h26 : D.rank = 26)
  (hHG : H * gramComplex D = 1)
  (hGH : gramComplex D * H = 1)

local notation "C" => Cohomology D H h26 hHG hGH
local notation "Phys" => physicalImage D H h26 hHG hGH
local notation "Fib" => physicalChargeFiber D H h26 hHG hGH

private theorem bilinear_zsmul_right (u v : Charge D) (n : ℤ) :
    bilinear D u (n • v) = n * bilinear D u v := by
  unfold bilinear
  simp only [Pi.smul_apply]
  simp only [zsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Int.cast_id]
  ring

private theorem bilinear_add_left (u v w : Charge D) :
    bilinear D (u + v) w = bilinear D u w + bilinear D v w := by
  calc
    bilinear D (u + v) w = bilinear D w (u + v) :=
      LatticeFiniteNegativeGeneration.bilinear_symmetric D (u + v) w
    _ = bilinear D w u + bilinear D w v :=
      LatticeActualGeneratorLocality.bilinear_add_right D w u v
    _ = bilinear D u w + bilinear D v w := by
      rw [LatticeFiniteNegativeGeneration.bilinear_symmetric D w u,
        LatticeFiniteNegativeGeneration.bilinear_symmetric D w v]

private theorem bilinear_zsmul_left (u v : Charge D) (n : ℤ) :
    bilinear D (n • u) v = n * bilinear D u v := by
  calc
    bilinear D (n • u) v = bilinear D v (n • u) :=
      LatticeFiniteNegativeGeneration.bilinear_symmetric D (n • u) v
    _ = n * bilinear D v u := bilinear_zsmul_right D v u n
    _ = n * bilinear D u v := by
      rw [LatticeFiniteNegativeGeneration.bilinear_symmetric D v u]

private theorem bilinear_quadratic (beta alpha : Charge D) (n : ℤ) :
    bilinear D (beta + n • alpha) (beta + n • alpha) =
      bilinear D beta beta + 2 * n * bilinear D beta alpha +
        n ^ 2 * bilinear D alpha alpha := by
  rw [bilinear_add_left D beta (n • alpha) (beta + n • alpha),
    LatticeActualGeneratorLocality.bilinear_add_right D beta beta (n • alpha),
    LatticeActualGeneratorLocality.bilinear_add_right D (n • alpha) beta (n • alpha),
    bilinear_zsmul_right D beta alpha n,
    bilinear_zsmul_left D alpha beta n,
    bilinear_zsmul_left D alpha (n • alpha) n,
    bilinear_zsmul_right D alpha alpha n,
    LatticeFiniteNegativeGeneration.bilinear_symmetric D alpha beta]
  ring

private theorem chargeEnergy_add_zsmul (beta alpha : Charge D) (n : ℤ) :
    chargeEnergy D (beta + n • alpha) =
      chargeEnergy D beta + n * bilinear D beta alpha +
        n ^ 2 * chargeEnergy D alpha := by
  apply (mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0))
  calc
    2 * chargeEnergy D (beta + n • alpha) =
        bilinear D (beta + n • alpha) (beta + n • alpha) := two_chargeEnergy D _
    _ = bilinear D beta beta + 2 * n * bilinear D beta alpha +
        n ^ 2 * bilinear D alpha alpha := bilinear_quadratic D beta alpha n
    _ = 2 * (chargeEnergy D beta + n * bilinear D beta alpha +
        n ^ 2 * chargeEnergy D alpha) := by
      rw [← two_chargeEnergy D beta, ← two_chargeEnergy D alpha]
      ring

private theorem neg_natAbs_le (z : ℤ) : -(z.natAbs : ℤ) ≤ z := by
  by_cases hz : 0 ≤ z
  · rw [Int.natAbs_of_nonneg hz]
    omega
  · rw [Int.ofNat_natAbs_of_nonpos (le_of_not_ge hz)]
    omega

private def rootBound (alpha beta : Charge D) : ℕ :=
  (Int.natAbs (bilinear D beta alpha)) + Int.natAbs (chargeEnergy D beta) + 3

private theorem rootBound_energy_gt_one (alpha beta : Charge D)
    (hα : 0 < chargeEnergy D alpha) :
    1 < chargeEnergy D (beta + (rootBound D alpha beta : ℤ) • alpha) := by
  let s : ℤ := Int.natAbs (bilinear D beta alpha)
  let t : ℤ := Int.natAbs (chargeEnergy D beta)
  let n : ℤ := rootBound D alpha beta
  have hn : n = s + t + 3 := by
    simp [n, s, t, rootBound]
  have hs : -(s) ≤ bilinear D beta alpha := by
    exact neg_natAbs_le _
  have ht : -t ≤ chargeEnergy D beta := by
    exact neg_natAbs_le _
  have hs0 : 0 ≤ s := Int.natCast_nonneg _
  have ht0 : 0 ≤ t := Int.natCast_nonneg _
  have hn0 : 0 ≤ n := by omega
  have hnsub : n - s = t + 3 := by omega
  have hα1 : 1 ≤ chargeEnergy D alpha := by omega
  have hcross : -n * s ≤ n * bilinear D beta alpha := by
    simpa only [mul_neg, neg_mul] using (mul_le_mul_of_nonneg_left hs hn0)
  have hsq : 0 ≤ n ^ 2 := sq_nonneg n
  have hquad :
      chargeEnergy D (beta + n • alpha) =
        chargeEnergy D beta + n * bilinear D beta alpha + n ^ 2 * chargeEnergy D alpha :=
    chargeEnergy_add_zsmul D beta alpha n
  change 1 < chargeEnergy D (beta + n • alpha)
  rw [hquad]
  have henergy :
      n ^ 2 * 1 ≤ n ^ 2 * chargeEnergy D alpha :=
    mul_le_mul_of_nonneg_left hα1 hsq
  have hn3 : 3 ≤ n := by omega
  have hnt : t ≤ n * t := by
    have h := mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ n by omega) ht0
    simpa using h
  have hbase : 1 < -t - n * s + n ^ 2 := by
    have hprod : n * (n - s) = n * (t + 3) := by rw [hnsub]
    nlinarith only [hprod, hnt, hn3]
  nlinarith only [hbase, ht, hcross, henergy]

private theorem fixed_physical_class_mem_fiber (p : Charge D)
    (u : physicalStates D H) (hu : (u : State D) ∈ fixedMomentum D p) :
    physicalClass D H h26 hHG hGH u ∈ Fib p := by
  refine ⟨⟨u, rfl⟩, ?_⟩
  let s : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorCycles
      D H p := ⟨⟨(u : State D), hu⟩, by
        apply Subtype.ext
        exact u.property.1⟩
  refine ⟨sectorClassOf D H h26 hHG hGH p s, ?_⟩
  rw [inclusion_sectorClassOf]
  rfl

private theorem bracket_mem_fiber (alpha beta : Charge D)
    (x z : Phys) (hx : (x : C) ∈ Fib alpha) (hz : (z : C) ∈ Fib beta) :
    ((⁅x, z⁆ : Phys) : C) ∈ Fib (alpha + beta) := by
  -- Fib is literally physicalImage ⊓ range inclusion, not a fixed-point premise.
  obtain ⟨ux, hux, hcx⟩ := physical_charge_representative D H h26 hHG hGH
    alpha (x : C) hx.1 hx.2
  obtain ⟨uz, huz, hcz⟩ := physical_charge_representative D H h26 hHG hGH
    beta (z : C) hz.1 hz.2
  let w : physicalStates D H :=
    ⟨descentCurrent D ux uz, physicalStates_current D H hHG hGH ux uz⟩
  have hw : (w : State D) ∈ fixedMomentum D (alpha + beta) :=
    current_charge D alpha beta (ux : State D) (uz : State D) hux huz
  have hclass : physicalClass D H h26 hHG hGH w = ((⁅x, z⁆ : Phys) : C) := by
    change physicalClass D H h26 hHG hGH w =
      cohomologyCurrent D H h26 hHG hGH (x : C) (z : C)
    rw [← hcx, ← hcz]
    exact (current_classOf D H h26 hHG hGH
      ⟨(ux : State D), ux.property.1⟩
      ⟨(uz : State D), uz.property.1⟩).symm
  rw [← hclass]
  exact fixed_physical_class_mem_fiber D H h26 hHG hGH (alpha + beta) w hw

private theorem iterate_mem_fiber (alpha beta : Charge D)
    (x : Phys) (hx : (x : C) ∈ Fib alpha) (n : ℕ)
    (z : Phys) (hz : (z : C) ∈ Fib beta) :
    (((fun v : Phys => ⁅x, v⁆)^[n]) z : C) ∈
      Fib (beta + (n : ℤ) • alpha) := by
  induction n with
  | zero =>
      simpa only [Function.iterate_zero_apply, Nat.cast_zero, zero_smul, add_zero] using hz
  | succ n ih =>
      have hnext := bracket_mem_fiber D H h26 hHG hGH
        alpha (beta + (n : ℤ) • alpha) x
        (((fun v : Phys => ⁅x, v⁆)^[n]) z) hx ih
      simpa only [Function.iterate_succ_apply', Nat.cast_succ, add_zsmul,
        one_zsmul, add_assoc, add_left_comm, add_comm] using hnext

private theorem iterate_component_zero (alpha : Charge D) (hα : 0 < chargeEnergy D alpha)
    (beta : Charge D) (x : Phys) (hx : (x : C) ∈ Fib alpha)
    (z : Phys) (hz : (z : C) ∈ Fib beta) :
    ((fun v : Phys => ⁅x, v⁆)^[rootBound D alpha beta]) z = 0 := by
  have hq : 1 < chargeEnergy D
      (beta + (rootBound D alpha beta : ℤ) • alpha) :=
    rootBound_energy_gt_one D alpha beta hα
  have hq0 : beta + (rootBound D alpha beta : ℤ) • alpha ≠ 0 := by
    intro hzero
    rw [hzero, LatticePositiveEnergy.chargeEnergy_zero] at hq
    omega
  have hmem := iterate_mem_fiber D H h26 hHG hGH alpha beta x hx
    (rootBound D alpha beta) z hz
  have hlevel : 1 - chargeEnergy D
      (beta + (rootBound D alpha beta : ℤ) • alpha) < 0 := by omega
  have hbot := physicalChargeFiber_eq_bot_of_level_neg D H h26 hHG hGH
    (beta + (rootBound D alpha beta : ℤ) • alpha) hq0 hlevel
  rw [hbot] at hmem
  have hzero : (((fun v : Phys => ⁅x, v⁆)^[rootBound D alpha beta]) z : C) = 0 := by
    exact (Submodule.mem_bot ℂ (M := C)).mp hmem
  apply Subtype.ext
  exact hzero

private def physicalComponent (y : physicalStates D H) (p : Charge D) : Phys :=
  let yp : physicalStates D H :=
    ⟨chargeProject p (y : State D), project_physical D H hHG hGH p y⟩
  ⟨physicalClass D H h26 hHG hGH yp, ⟨yp, rfl⟩⟩

private theorem physicalComponent_mem_fiber (y : physicalStates D H) (p : Charge D) :
    (physicalComponent D H h26 hHG hGH y p : C) ∈ Fib p := by
  unfold physicalComponent
  let yp : physicalStates D H :=
    ⟨chargeProject p (y : State D), project_physical D H hHG hGH p y⟩
  change physicalClass D H h26 hHG hGH yp ∈ Fib p
  exact fixed_physical_class_mem_fiber D H h26 hHG hGH p yp
    (chargeProject_mem D p (y : State D))

private theorem physical_sum_components (y : physicalStates D H) :
    (⟨physicalClass D H h26 hHG hGH y, ⟨y, rfl⟩⟩ : Phys) =
      ∑ p ∈ chargeSupport D (y : State D),
        physicalComponent D H h26 hHG hGH y p := by
  classical
  let yp : Charge D → physicalStates D H := fun p =>
    ⟨chargeProject p (y : State D), project_physical D H hHG hGH p y⟩
  -- Reconstruct y IN the physical subtype, using its actual linear inclusion.
  have hsum : (∑ p ∈ chargeSupport D (y : State D), yp p) = y := by
    apply Subtype.ext
    change (physicalStates D H).subtype
      (∑ p ∈ chargeSupport D (y : State D), yp p) = (y : State D)
    rw [map_sum]
    exact sum_chargeProject D (y : State D)
  apply Subtype.ext
  change physicalClass D H h26 hHG hGH y =
    (physicalImage D H h26 hHG hGH).subtype
      (∑ p ∈ chargeSupport D (y : State D),
        physicalComponent D H h26 hHG hGH y p)
  rw [map_sum]
  change physicalClass D H h26 hHG hGH y =
    ∑ p ∈ chargeSupport D (y : State D), physicalClass D H h26 hHG hGH (yp p)
  rw [← map_sum, hsum]

private theorem iterate_sum {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (x : L) (n : ℕ) (s : Finset (Charge D)) (g : Charge D → L) :
    ((fun w : L => ⁅x, w⁆)^[n]) (∑ p ∈ s, g p) =
      ∑ p ∈ s, ((fun w : L => ⁅x, w⁆)^[n]) (g p) := by
  classical
  have hA : (LieModule.toEnd ℂ L L x : L → L) = (fun w : L => ⁅x, w⁆) := by
    funext w
    exact LieModule.toEnd_apply_apply ℂ L L x w
  simpa only [Module.End.pow_apply, hA] using
    (map_sum ((LieModule.toEnd ℂ L L x) ^ n) g s)

-- Checking this proof unfolds the original global BRST quotient through its actual adjoint.
set_option maxHeartbeats 8000000 in
set_option diagnostics true in
theorem positive_root_adjoint_locally_nilpotent
    (alpha : Charge D) (hα : 0 < chargeEnergy D alpha)
    (x : Phys) (hx : (x : C) ∈ Fib alpha) (y : Phys) :
    ∃ N : ℕ, ((fun z : Phys => ⁅x, z⁆)^[N]) y = 0 := by
  classical
  obtain ⟨ys, hys⟩ := y.property
  let S : Finset (Charge D) := chargeSupport D (ys : State D)
  let N : ℕ := S.sup (fun p => rootBound D alpha p)
  have hdecomp : y = ∑ p ∈ S, physicalComponent D H h26 hHG hGH ys p := by
    calc
      y = (⟨physicalClass D H h26 hHG hGH ys, ⟨ys, rfl⟩⟩ : Phys) := by
        apply Subtype.ext
        exact hys.symm
      _ = _ := physical_sum_components D H h26 hHG hGH ys
  refine ⟨N, ?_⟩
  rw [hdecomp, iterate_sum D x N S
    (physicalComponent D H h26 hHG hGH ys)]
  apply Finset.sum_eq_zero
  intro p hp
  have hk := iterate_component_zero D H h26 hHG hGH alpha hα p
    x hx (physicalComponent D H h26 hHG hGH ys p)
    (physicalComponent_mem_fiber D H h26 hHG hGH ys p)
  have hle : rootBound D alpha p ≤ N :=
    Finset.le_sup (f := fun q => rootBound D alpha q) hp
  -- Pad the actual linear adjoint power using the existing endomorphism law.
  let A : Module.End ℂ Phys := LieModule.toEnd ℂ Phys Phys x
  have hA : (A : Phys → Phys) = (fun w : Phys => ⁅x, w⁆) := by
    funext w
    exact LieModule.toEnd_apply_apply ℂ Phys Phys x w
  have hkA : (A ^ rootBound D alpha p)
      (physicalComponent D H h26 hHG hGH ys p) = 0 := by
    rw [Module.End.pow_apply, hA]
    exact hk
  have hN := Module.End.pow_map_zero_of_le hle hkA
  rw [Module.End.pow_apply, hA] at hN
  exact hN

end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPositiveRootIntegrability
