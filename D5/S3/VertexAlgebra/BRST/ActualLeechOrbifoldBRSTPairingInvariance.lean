/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldBRSTPairingInvariance
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldBRSTPairingInvariance
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: Invariance of the actual ghost-one relative BRST pairing. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldTensorBPZ
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldPlusPhysicalRepresentatives
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldNativeBPZRadical
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeBracketIdentities

/-! The native relative pairing is invariant under the original BRST bracket. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.NativeBPZ

open ActualLeechOrbifoldCriticalMatter (Matter matter hyperbolicPlane)
open LatticeGeneratingFieldLocality (Charge)
open LatticeLightConeCoordinates (NullFrame)
open RelativeBracket (Degree bracket bracket_mk current current_tmul_c1vac cycleCurrent nativeValue)
open RelativeCohomology (GhostSpace GradedCycles GradedBoundaries GradedCohomology
  NativeShell nativeQ coefficient primitive representative representative_closed
  representative_degree primitive_degree cycle_boundary_witness representative_eq_plus_primary_tmul)
open D5.S3.Quantum.Fermionic.BcGhostQuartetCount (c1vac c1vac_eq)
open D5.S3.Quantum.Fermionic.BcGhostBilinear (Bg_c0_ket_one)

open private nativeShellEquiv assocQ_reassoc gradedBoundaryMap from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCohomology
open private native_mem native_degree native_closed native_add native_smul native_boundary
  native_cycleCurrent degree_shell boundary_of_native from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeBracket
open private representative_one orbVac planeCurrent from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeZeroMomentum

local notation "Cycles" => GradedCycles planeFrame planeBasis
local notation "Coh" => GradedCohomology planeFrame planeBasis
local notation "Boundaries" => GradedBoundaries planeFrame planeBasis

local instance : AddCommGroup ComplexState := TensorProduct.addCommGroup
local instance (p : Charge hyperbolicPlane) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup _
local instance (p : Charge hyperbolicPlane) : AddCommGroup (NativeShell p) :=
  Submodule.addCommGroup _
local instance (p : Charge hyperbolicPlane) : AddCommGroup (Cycles p 1) :=
  Submodule.addCommGroup _

private theorem pair_boundary {p q : Charge hyperbolicPlane} (a : NativeShell p)
    (y : Cycles q 1) : relativePairing (Q a.val) (nativeValue y) = 0 := by
  let z := (nativeShellEquiv q).symm y.val
  have hz : nativeQ q z = 0 := Subtype.ext (native_closed y)
  exact relativePairing_boundary_cycle a z hz

private def valueMap (p : Charge hyperbolicPlane) : Cycles p 1 →ₗ[ℂ] ComplexState where
  toFun := nativeValue
  map_add' := native_add
  map_smul' := native_smul

private theorem pair_boundary_map {p q : Charge hyperbolicPlane}
    (a : GhostSpace p ((1 : ℤ) - 1)) (y : Cycles q 1) :
    relativePairing (nativeValue (gradedBoundaryMap planeFrame planeBasis p 1 a))
      (nativeValue y) = 0 := by
  rw [native_boundary]
  exact pair_boundary ((nativeShellEquiv p).symm a.val) y

/-- The signed native BPZ form on the actual ghost-one kernel/image quotients. -/
def gradedRelativePairing (p q : Charge hyperbolicPlane) : Coh p 1 →ₗ[ℂ] Coh q 1 →ₗ[ℂ] ℂ :=
  LinearMap.liftQ₂ (R := ℂ) (R₂ := ℂ) (S := ℂ) (S₂ := ℂ)
    (M := Cycles p 1) (N := Cycles q 1) (P := ℂ)
    (ρ := RingHom.id ℂ) (σ := RingHom.id ℂ) (Boundaries p 1) (Boundaries q 1)
    ((-relativePairing).compl₁₂ (valueMap p) (valueMap q))
    (by
      rintro x ⟨a, rfl⟩
      apply LinearMap.mem_ker.mpr
      ext y
      change -relativePairing (nativeValue (gradedBoundaryMap planeFrame planeBasis p 1 a))
        (nativeValue y) = 0
      rw [pair_boundary_map, neg_zero])
    (by
      rintro y ⟨a, rfl⟩
      apply LinearMap.mem_ker.mpr
      ext x
      change -relativePairing (nativeValue x)
        (nativeValue (gradedBoundaryMap planeFrame planeBasis q 1 a)) = 0
      rw [relativePairing_symmetric (nativeValue x), pair_boundary_map, neg_zero])

@[simp] theorem gradedRelativePairing_mk {p q : Charge hyperbolicPlane}
    (x : Cycles p 1) (y : Cycles q 1) :
    gradedRelativePairing p q (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      -relativePairing (nativeValue x) (nativeValue y) := rfl

set_option maxHeartbeats 2500000 in
-- The two shell associations are compared through the actual restricted charge.
private theorem frame_representative {p : Charge hyperbolicPlane} (x : Cycles p 1)
    (F : NullFrame hyperbolicPlane) (B : Module.Basis (Fin 0) ℂ F.K) (hp : F.pPlus p ≠ 0) :
    ∃ y : Cycles p 1, (Submodule.Quotient.mk y : Coh p 1) = Submodule.Quotient.mk x ∧
      ∃ φ : Matter, nativeValue y = φ ⊗ₜ[ℂ] c1vac := by
  let z := x.val
  let v := coefficient F B p hp z
  let t := representative F B p hp v
  let y : Cycles p 1 :=
    ⟨t, representative_degree F B p hp v, representative_closed F B p hp v⟩
  let a := primitive F B p hp z
  have hQ : relativeQ F B p z = 0 := x.property.2
  have he := cycle_boundary_witness F B p hp z hQ
  have hnative : Q (reassoc.symm a.val) = nativeValue (x - y) := by
    apply reassoc.injective
    change reassoc (Q (reassoc.symm a.val)) = reassoc (reassoc.symm (x - y).val.val)
    rw [← assocQ_reassoc, reassoc.apply_symm_apply]
    exact (congrArg (fun w : relativeShell p => w.val) he).trans
      (reassoc.apply_symm_apply (x - y).val.val).symm
  have hmem : reassoc (reassoc.symm a.val) ∈ relativeShell p := by
    rw [reassoc.apply_symm_apply]
    exact a.property
  have hd : Degree 0 (reassoc.symm a.val) := by
    simpa only [sub_self] using (degree_shell p (1 - 1) a).mp
      (primitive_degree F B p hp 1 z x.property.1)
  have hb := boundary_of_native (x - y) _ hmem hd hnative
  have hmk : (Boundaries p 1).mkQ (x - y) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hb
  obtain ⟨φ, _, hφ, _, _⟩ := representative_eq_plus_primary_tmul F B p hp v
  refine ⟨y, (sub_eq_zero.mp ?_).symm, φ, ?_⟩
  · change (Boundaries p 1).mkQ x - (Boundaries p 1).mkQ y = 0
    rw [← (Boundaries p 1).mkQ.map_sub]
    exact hmk
  · change reassoc.symm t.val = _
    rw [hφ, reassoc.symm_apply_apply]

set_option maxHeartbeats 2500000 in
-- Zero and nonzero momentum use different existing shell equivalences.
private theorem pure_representative {p : Charge hyperbolicPlane} (x : Cycles p 1) :
    ∃ y : Cycles p 1, (Submodule.Quotient.mk y : Coh p 1) = Submodule.Quotient.mk x ∧
      ∃ φ : Matter, nativeValue y = φ ⊗ₜ[ℂ] c1vac := by
  by_cases hp : p = 0
  · subst p
    let d : GhostSpace 0 1 := ⟨x.val, x.property.1⟩
    let f := RelativeZeroMomentum.degreeOneEquiv d
    have he : RelativeZeroMomentum.representative (0, (f, 0)) = nativeValue x :=
      congrArg (fun w : GhostSpace 0 1 => reassoc.symm w.val.val)
        (RelativeZeroMomentum.degreeOneEquiv.symm_apply_apply d)
    refine ⟨x, rfl, orbVac ⊗ₜ[ℂ] (∑ i : Fin 2, f i • planeCurrent i), ?_⟩
    rw [← he, representative_one, c1vac_eq]
  · rcases planeFrame_covers_nonzero p hp with h | h
    · exact frame_representative x planeFrame planeBasis h
    · exact frame_representative x swappedPlaneFrame swappedPlaneBasis h

private theorem current_pairing_pure (φ ψ χ : Matter)
    (h₀ : matter.mode 0 φ = φ) (h₁ : matter.mode 1 φ = 0) :
    relativePairing (current (φ ⊗ₜ[ℂ] c1vac) (ψ ⊗ₜ[ℂ] c1vac)) (χ ⊗ₜ[ℂ] c1vac) =
      -relativePairing (ψ ⊗ₜ[ℂ] c1vac) (current (φ ⊗ₜ[ℂ] c1vac) (χ ⊗ₜ[ℂ] c1vac)) := by
  rw [current_tmul_c1vac, current_tmul_c1vac]
  simp only [relativePairing_tmul, c1vac_eq, Bg_c0_ket_one, one_mul]
  exact matterPairing_matterZeroMode_skew φ ψ χ h₀ h₁

set_option maxHeartbeats 2500000 in
-- Quotient representatives reduce through the shell coercions and the literal field.
private theorem bracket_pairing_skew {p q r : Charge hyperbolicPlane}
    (x : Coh p 1) (y : Coh q 1) (z : Coh r 1) :
    gradedRelativePairing (p + q) r (bracket p q x y) z =
      -gradedRelativePairing q (p + r) y (bracket p r x z) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (Boundaries p 1) x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (Boundaries q 1) y
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (Boundaries r 1) z
  obtain ⟨x', hx, φ, hφ⟩ := pure_representative x
  obtain ⟨y', hy, ψ, hψ⟩ := pure_representative y
  obtain ⟨z', hz, χ, hχ⟩ := pure_representative z
  have hQ : Q (φ ⊗ₜ[ℂ] c1vac) = 0 := hφ ▸ native_closed x'
  obtain ⟨h₀, hp⟩ := (Q_tmul_c1vac_eq_zero_iff φ).mp hQ
  rw [← hx, ← hy, ← hz, bracket_mk, bracket_mk, gradedRelativePairing_mk,
    gradedRelativePairing_mk, native_cycleCurrent, native_cycleCurrent, hφ, hψ, hχ]
  exact congrArg Neg.neg (current_pairing_pure φ ψ χ h₀ (hp 1 (by decide)))

set_option maxHeartbeats 2500000 in
-- The cyclic identity compares native cycles after three quotient projections.
/-- The actual relative BRST bracket preserves its signed BPZ pairing in every
triple of momentum sectors. -/
theorem gradedRelativePairing_bracket_invariant {p q r : Charge hyperbolicPlane}
    (x : Coh p 1) (y : Coh q 1) (z : Coh r 1) :
    gradedRelativePairing (p + q) r (bracket p q x y) z =
      gradedRelativePairing p (q + r) x (bracket q r y z) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (Boundaries p 1) x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective (Boundaries q 1) y
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective (Boundaries r 1) z
  have hs := bracket_pairing_skew (p := q) (q := p) (r := r) (Submodule.Quotient.mk b)
    (Submodule.Quotient.mk a) (Submodule.Quotient.mk c)
  rw [bracket_mk, bracket_mk, gradedRelativePairing_mk, gradedRelativePairing_mk,
    native_cycleCurrent, native_cycleCurrent] at hs
  rw [bracket_mk, bracket_mk, gradedRelativePairing_mk, gradedRelativePairing_mk,
    native_cycleCurrent, native_cycleCurrent]
  obtain ⟨hm, _, hQ⟩ := RelativeBracket.skew_boundary RelativeBracket.odd_product_skew
    (native_mem a) (native_mem b) (native_degree a) (native_degree b)
    (native_closed a) (native_closed b)
  let s : NativeShell (p + q) := ⟨_, hm⟩
  have h := pair_boundary s c
  change relativePairing (Q (RelativeBracket.skewPrimitive (nativeValue a) (nativeValue b)))
    (nativeValue c) = 0 at h
  rw [hQ, map_add, LinearMap.add_apply] at h
  linear_combination -h - hs

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.NativeBPZ
