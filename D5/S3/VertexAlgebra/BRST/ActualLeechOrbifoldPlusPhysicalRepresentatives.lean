/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldPlusPhysicalRepresentatives
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldPlusPhysicalRepresentatives
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual corrected BRST representative has pure c1 and plus-null primary matter. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldPlusOscillators
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCohomology
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldPureC1Primary

/-! Support of the literal perturbation representative on the relative shell. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST

open ActualLeechOrbifoldMatter (Orbifold)
open ActualLeechOrbifoldCriticalMatter (Matter hyperbolicPlane matter)
open LatticeGeneratingFieldLocality (Carrier Charge)
open LatticeLightConeCoordinates (NullFrame)
open LatticeQuartetContraction (State d0 h)
open PlusOscillators
open D5.S3.Quantum.Fermionic.CountableOccupationFock (Fock)
open D5.S3.Quantum.Fermionic.BcGhostFock (c)
open D5.S3.Quantum.Fermionic.BcGhostQuartetCount (c1vac)
open D5.S3.HomologicalAlgebra

open private rightLift_tmul from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightCone
open private groundIndex groundShell cutoff assocQ_reassoc
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCohomology

namespace RelativeCohomology

variable (F : NullFrame hyperbolicPlane) (B : Module.Basis (Fin 0) ℂ F.K)
variable (p : Charge hyperbolicPlane)

private local instance : AddCommGroup ComplexState := TensorProduct.addCommGroup

private local instance (p : Charge hyperbolicPlane) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup (relativeShell p)

private def attachGhost (w : Fock) : Matter →ₗ[ℂ] AssocState :=
  reassoc.toLinearMap.comp ((TensorProduct.mk ℂ Matter Fock).flip w)

private theorem attachGhost_apply (w : Fock) (φ : Matter) :
    attachGhost w φ = reassoc (φ ⊗ₜ[ℂ] w) := rfl

private theorem attachGhost_tmul (w : Fock) (v : Orbifold) (u : Carrier hyperbolicPlane) :
    attachGhost w (v ⊗ₜ[ℂ] u) = v ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] w) := rfl

private def pureAssoc : Submodule ℂ AssocState :=
  (plusMatter F B p).map (attachGhost c1vac)

private def extraAssoc : Submodule ℂ AssocState :=
  Submodule.span ℂ {x | ∃ (v : Orbifold) (y : State hyperbolicPlane),
    y ∈ extraCSector F B p ∧ x = v ⊗ₜ[ℂ] y}

/-- The actual shell submodule with only c1vac and plus-null matter oscillators. -/
def plusC1Shell : Submodule ℂ (relativeShell p) :=
  (pureAssoc F B p).comap (relativeShell p).subtype

theorem mem_plusC1Shell_iff (x : relativeShell p) :
    x ∈ plusC1Shell F B p ↔ ∃ φ ∈ plusMatter F B p,
      reassoc (φ ⊗ₜ[ℂ] c1vac) = x.val := by
  change x.val ∈ (plusMatter F B p).map (attachGhost c1vac) ↔ _
  simp only [Submodule.mem_map, attachGhost_apply]

private theorem extra_tmul_mem (v : Orbifold) {y : State hyperbolicPlane}
    (hy : y ∈ extraCSector F B p) : v ⊗ₜ[ℂ] y ∈ extraAssoc F B p :=
  Submodule.subset_span ⟨v, y, hy, rfl⟩

private theorem attach_extra_mem (n : ℕ) {φ : Matter} (hφ : φ ∈ plusMatter F B p) :
    attachGhost (c (-(n : ℤ)) c1vac) φ ∈ extraAssoc F B p := by
  have hle : plusMatter F B p ≤
      (extraAssoc F B p).comap (attachGhost (c (-(n : ℤ)) c1vac)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, P, rfl⟩
    change attachGhost _ (v ⊗ₜ[ℂ] planeInsert F B p P) ∈ extraAssoc F B p
    rw [attachGhost_tmul]
    apply extra_tmul_mem F B p
    apply le_iSup (fun m : ℕ => plusSector F B p (c (-(m : ℤ)) c1vac)) n
    exact (mem_plusSector_iff F B p _ _).mpr ⟨P, rfl⟩
  exact hle hφ

private theorem assocQ_mem_extra (φ : Matter) (hφ : φ ∈ plusMatter F B p) :
    assocQ (attachGhost c1vac φ) ∈ extraAssoc F B p := by
  obtain ⟨N, _, hQ⟩ := Q_tmul_c1vac φ
  change assocQ (reassoc (φ ⊗ₜ[ℂ] c1vac)) ∈ extraAssoc F B p
  rw [assocQ_reassoc (φ ⊗ₜ[ℂ] c1vac), hQ]
  let T : ComplexState →ₗ[ℂ] AssocState := reassoc.toLinearMap
  change T (((matter.mode 0 φ - φ) ⊗ₜ[ℂ] c 0 c1vac) +
    ∑ n ∈ Finset.Icc 1 N, matter.mode n φ ⊗ₜ[ℂ] c (-n) c1vac) ∈ extraAssoc F B p
  rw [T.map_add, map_sum T]
  apply (extraAssoc F B p).add_mem
  · exact attach_extra_mem F B p 0
      ((plusMatter F B p).sub_mem (matter_mode_mem F B p 0 le_rfl hφ) hφ)
  · apply (extraAssoc F B p).sum_mem
    intro n hn
    have hn0 : 0 ≤ n := by
      have hlow := (Finset.mem_Icc.mp hn).1
      omega
    have hmem := attach_extra_mem F B p n.toNat (matter_mode_mem F B p n hn0 hφ)
    rw [attachGhost_apply, Int.toNat_of_nonneg hn0] at hmem
    exact hmem

private theorem lifted_d0_mem_extra (φ : Matter) (hφ : φ ∈ plusMatter F B p) :
    rightLift (d0 F p) (attachGhost c1vac φ) ∈ extraAssoc F B p := by
  have hle : plusMatter F B p ≤
      (extraAssoc F B p).comap ((rightLift (d0 F p)).comp (attachGhost c1vac)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, P, rfl⟩
    change rightLift (d0 F p) (attachGhost c1vac (v ⊗ₜ[ℂ] planeInsert F B p P)) ∈
      extraAssoc F B p
    rw [attachGhost_tmul, rightLift_tmul]
    apply extra_tmul_mem F B p
    exact d0_mem_extraCSector F B p
      ((mem_plusSector_iff F B p _ _).mpr ⟨P, rfl⟩)
  exact hle hφ

private theorem lifted_h_mem_pure {x : AssocState} (hx : x ∈ extraAssoc F B p) :
    rightLift (h F B p) x ∈ pureAssoc F B p := by
  have hle : extraAssoc F B p ≤ (pureAssoc F B p).comap (rightLift (h F B p)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, y, hy, rfl⟩
    change rightLift (h F B p) (v ⊗ₜ[ℂ] y) ∈ pureAssoc F B p
    rw [rightLift_tmul]
    obtain ⟨P, hP⟩ := (mem_plusSector_iff F B p _ _).mp (h_mem_plusSector F B p hy)
    rw [← hP]
    exact Submodule.mem_map.mpr
      ⟨v ⊗ₜ[ℂ] planeInsert F B p P, tmul_mem_plusMatter F B p v P,
        attachGhost_tmul _ _ _⟩
  exact hle hx

/-- The actual relative homotopy times the actual relative remainder
preserves the plus-null pure-c1 submodule. -/
theorem relativeH_mul_relativeDelta_mem_plusC1Shell {x : relativeShell p}
    (hx : x ∈ plusC1Shell F B p) :
    (relativeH F B p * relativeDelta F B p) x ∈ plusC1Shell F B p := by
  obtain ⟨φ, hφ, heq⟩ := (mem_plusC1Shell_iff F B p x).mp hx
  change attachGhost c1vac φ = x.val at heq
  change rightLift (h F B p) (assocQ x.val - rightLift (d0 F p) x.val) ∈ pureAssoc F B p
  rw [← heq]
  exact lifted_h_mem_pure F B p
    ((extraAssoc F B p).sub_mem (assocQ_mem_extra F B p φ hφ)
      (lifted_d0_mem_extra F B p φ hφ))

private theorem ground_mem_plusC1Shell (v : OrbifoldWeight p) :
    groundShell F B p v ∈ plusC1Shell F B p := by
  apply (mem_plusC1Shell_iff F B p _).mpr
  refine ⟨v.val ⊗ₜ[ℂ] planeInsert F B p 1, tmul_mem_plusMatter F B p v.val 1, ?_⟩
  change v.val ⊗ₜ[ℂ] (planeInsert F B p 1 ⊗ₜ[ℂ] c1vac) =
    v.val ⊗ₜ[ℂ] LatticeQuartetContraction.actualBasis F B (groundIndex p)
  rw [planeInsert_one, groundBasis_eq]

variable (hp : F.pPlus p ≠ 0)

/-- The actual finite inverse polynomial gives a representative supported on
plus-null plane oscillators with the original c1vac ghost factor. -/
theorem representative_mem_plusC1Shell (v : OrbifoldWeight p) :
    representative F B p hp v ∈ plusC1Shell F B p := by
  rw [representative_polynomial]
  let A := relativeH F B p * relativeDelta F B p
  have hpow (j : ℕ) : ((-A) ^ j) (groundShell F B p v) ∈ plusC1Shell F B p := by
    induction j with
    | zero =>
      rw [pow_zero, Module.End.one_apply]
      exact ground_mem_plusC1Shell F B p v
    | succ j hj =>
      rw [pow_succ', Module.End.mul_apply, LinearMap.neg_apply]
      exact (plusC1Shell F B p).neg_mem (relativeH_mul_relativeDelta_mem_plusC1Shell F B p hj)
  change FinitePerturbation.inversePolynomial A (cutoff p) (groundShell F B p v) ∈
    plusC1Shell F B p
  simp only [FinitePerturbation.inversePolynomial, LinearMap.sum_apply]
  exact (plusC1Shell F B p).sum_mem fun j _ => hpow j

/-- The actual BRST representative is a weight-one primary in the plus-null
matter submodule tensored with the native c1vac. The hypothesis pPlus ≠ 0
implies nonzero momentum. This applies to both of the hyperbolic plane frames. -/
theorem representative_eq_plus_primary_tmul (v : OrbifoldWeight p) :
    ∃ φ ∈ plusMatter F B p,
      (representative F B p hp v).val = reassoc (φ ⊗ₜ[ℂ] c1vac) ∧
      matter.mode 0 φ = φ ∧ ∀ n : ℤ, 0 < n → matter.mode n φ = 0 := by
  obtain ⟨φ, hφ, heq⟩ := (mem_plusC1Shell_iff F B p _).mp
    (representative_mem_plusC1Shell F B p hp v)
  refine ⟨φ, hφ, heq.symm, (Q_tmul_c1vac_eq_zero_iff φ).mp ?_⟩
  have hclosed := congrArg (fun z : relativeShell p => z.val)
    (representative_closed F B p hp v)
  change assocQ (representative F B p hp v).val = 0 at hclosed
  rw [← heq, assocQ_reassoc] at hclosed
  exact reassoc.injective (hclosed.trans (reassoc.map_zero).symm)

end RelativeCohomology
end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST
