/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeC0
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeC0
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: The native c0 Ward identity and pairing descent on the actual relative BRST quotient. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCohomology
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
The Ward remainder is a literal ghost operator on the original string states.
The form is a parameter on those same states. Its adjoint equalities use the
ordinary unsigned convention. The formal parameter for the first scalar
action permits both complex-bilinear and conjugate-linear first arguments.

The ghost adjoints are available as BcGhostHermitian.Hg_b and Hg_c and
BcGhostBRST.Hg_Qg. LatticeMatterGhostHermitian supplies the analogous
absolute adjoints for lattice matter. The input needed here is the form
and its adjoints on the combined fixed and negative twisted Leech sectors
tensored with the hyperbolic lattice and the ghosts. The construction
applies at each pair of momenta (p, q), including q = -p.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeC0

open ActualLeechOrbifoldCriticalMatter (Matter matter hyperbolicPlane)
open LatticeGeneratingFieldLocality (Carrier Charge)
open LatticeQuartetContraction (chargeProject tp)
open RelativeCohomology (NativeShell nativeQ NativeCohomology)
open D5.S3.HomologicalAlgebra
open D5.S3.Quantum.Fermionic
open D5.S3.Quantum.Fermionic.BcGhostFock (b c ghost_mixed_car)
open D5.S3.Quantum.Fermionic.CountableOccupationFock (Fock)

open private Q_commutes_energy from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldBRST
open private nativeQ_sq from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCohomology
open private ghost_number_c from D5.S3.Quantum.Fermionic.BcGhostCharge

local instance : AddCommGroup ComplexState := TensorProduct.addCommGroup

local instance (p : Charge hyperbolicPlane) : AddCommGroup (NativeShell p) :=
  Submodule.addCommGroup _

/-- The original c ghost at mode zero, lifted through the identity on matter. -/
abbrev c0 : Module.End ℂ ComplexState := VirasoroBRST.ghostC matter 0

/-- The original c Ward remainder at mode zero. -/
abbrev R0 : Module.End ℂ ComplexState := VirasoroBRST.ghostR matter 0

private abbrev ghostLift : Module.End ℂ Fock →ₐ[ℂ] Module.End ℂ ComplexState :=
  Module.End.lTensorAlgHom ℂ Fock Matter

theorem Q_c0_ward : Q * c0 + c0 * Q = R0 :=
  VirasoroBRST.Q_ward_c matter 0

private theorem b0_c0_car : b0 * c0 + c0 * b0 = 1 := by
  have h : b 0 * c 0 + c 0 * b 0 = (1 : Module.End ℂ Fock) := by
    simpa using ghost_mixed_car 0 0
  change ghostLift (b 0) * ghostLift (c 0) + ghostLift (c 0) * ghostLift (b 0) = 1
  simpa only [map_add, map_mul, map_one] using congrArg ghostLift h

private theorem E_c0_comm : E * c0 = c0 * E := by
  have hL : BcGhostVirasoro.L 0 * c 0 = c 0 * BcGhostVirasoro.L 0 := by
    apply sub_eq_zero.mp
    simpa only [mul_zero, sub_zero, Int.cast_zero, zero_smul] using
      BcGhostVirasoro.ward_c 0 0
  have hGhost : VirasoroBRST.ghostVirasoro matter 0 * c0 =
      c0 * VirasoroBRST.ghostVirasoro matter 0 := by
    change ghostLift (BcGhostVirasoro.L 0) * ghostLift (c 0) =
      ghostLift (c 0) * ghostLift (BcGhostVirasoro.L 0)
    simpa only [map_mul] using congrArg ghostLift hL
  have hMatter : VirasoroBRST.matterMode matter 0 * c0 =
      c0 * VirasoroBRST.matterMode matter 0 := by
    change TensorProduct.map (matter.mode 0) (1 : Module.End ℂ Fock) *
        TensorProduct.map (1 : Module.End ℂ Matter) (c 0) =
      TensorProduct.map (1 : Module.End ℂ Matter) (c 0) *
        TensorProduct.map (matter.mode 0) (1 : Module.End ℂ Fock)
    simp only [← TensorProduct.map_mul, mul_one, one_mul]
  change (VirasoroBRST.matterMode matter 0 + VirasoroBRST.ghostVirasoro matter 0) * c0 =
    c0 * (VirasoroBRST.matterMode matter 0 + VirasoroBRST.ghostVirasoro matter 0)
  rw [add_mul, mul_add, hMatter, hGhost]

private theorem b0_R0_comm : b0 * R0 = R0 * b0 := by
  have hWard : Q * b0 + b0 * Q = E := VirasoroBRST.Q_ward_b matter 0
  apply sub_eq_zero.mp
  calc
    b0 * R0 - R0 * b0 =
        (Q * b0 + b0 * Q) * c0 - c0 * (Q * b0 + b0 * Q) +
          (b0 * c0 + c0 * b0) * Q - Q * (b0 * c0 + c0 * b0) := by
      rw [← Q_c0_ward]
      noncomm_ring
    _ = 0 := by
      rw [hWard, b0_c0_car, E_c0_comm, one_mul, mul_one, sub_self, zero_add, sub_self]

private theorem E_R0_comm : E * R0 = R0 * E := by
  calc
    E * R0 = (E * Q) * c0 + (E * c0) * Q := by
      rw [← Q_c0_ward, mul_add, ← mul_assoc, ← mul_assoc]
    _ = (Q * E) * c0 + (c0 * E) * Q := by rw [Q_commutes_energy, E_c0_comm]
    _ = Q * (c0 * E) + c0 * (Q * E) := by
      rw [mul_assoc, mul_assoc, E_c0_comm, ← Q_commutes_energy]
    _ = R0 * E := by
      calc
        Q * (c0 * E) + c0 * (Q * E) = (Q * c0 + c0 * Q) * E := by
          simp only [add_mul, mul_assoc]
        _ = R0 * E := congrArg (· * E) Q_c0_ward

/-- The even Ward remainder preserves both defining zero-mode kernels. -/
theorem R0_preserves_relative_kernels {x : ComplexState}
    (hb : b0 x = 0) (he : E x = 0) : b0 (R0 x) = 0 ∧ E (R0 x) = 0 := by
  constructor
  · simpa only [Module.End.mul_apply, hb, map_zero] using
      LinearMap.congr_fun b0_R0_comm x
  · simpa only [Module.End.mul_apply, he, map_zero] using
      LinearMap.congr_fun E_R0_comm x

private theorem reassoc_R0 (x : ComplexState) :
    reassoc (R0 x) =
      rightLift (tp (1 : Module.End ℂ (Carrier hyperbolicPlane)) (BcGhostBRST.R 0))
        (reassoc x) := by
  let A := rightLift (tp (1 : Module.End ℂ (Carrier hyperbolicPlane)) (BcGhostBRST.R 0))
  have h : (reassoc.conjAlgEquiv ℂ) R0 = A := by
    apply TensorProduct.ext'
    intro v y
    induction y using TensorProduct.inductionOn with
    | tmul u w => rfl
    | add y z hy hz =>
      rw [TensorProduct.tmul_add, map_add ((reassoc.conjAlgEquiv ℂ) R0), map_add A, hy, hz]
  change reassoc (R0 x) = A (reassoc x)
  rw [← h, LinearEquiv.conjAlgEquiv_apply (R := ℂ) reassoc R0]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

/-- The Ward remainder preserves the actual plane momentum, before imposing either kernel. -/
theorem R0_preserves_momentum (p : Charge hyperbolicPlane) {x : ComplexState}
    (hx : rightLift (chargeProject p) (reassoc x) = reassoc x) :
    rightLift (chargeProject p) (reassoc (R0 x)) = reassoc (R0 x) := by
  let A := tp (1 : Module.End ℂ (Carrier hyperbolicPlane)) (BcGhostBRST.R 0)
  have h : chargeProject p * A = A * chargeProject p := by
    simp only [A, chargeProject, tp, ← TensorProduct.map_mul, mul_one, one_mul]
  have hc : rightLift (chargeProject p) * rightLift A =
      rightLift A * rightLift (chargeProject p) := by
    simpa only [map_mul] using congrArg rightLift h
  rw [reassoc_R0]
  change rightLift (chargeProject p) (rightLift A (reassoc x)) = rightLift A (reassoc x)
  have hh := LinearMap.congr_fun hc (reassoc x)
  simpa only [Module.End.mul_apply, hx] using hh

private theorem mem_nativeShell_iff (p : Charge hyperbolicPlane) (x : ComplexState) :
    x ∈ NativeShell p ↔
      rightLift (chargeProject p) (reassoc x) = reassoc x ∧ b0 x = 0 ∧ E x = 0 := by
  change reassoc x ∈ relativeShell p ↔ _
  rw [mem_relativeShell_iff]
  have transport (A : Module.End ℂ ComplexState) :
      ((reassoc.conjAlgEquiv ℂ) A) (reassoc x) = reassoc (A x) := by
    rw [LinearEquiv.conjAlgEquiv_apply (R := ℂ) reassoc A]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  have hb : assocB0 (reassoc x) = reassoc (b0 x) := transport b0
  have he : assocE (reassoc x) = reassoc (E x) := transport E
  have hzero (z : ComplexState) : reassoc z = 0 ↔ z = 0 := by
    rw [← reassoc.map_zero, reassoc.injective.eq_iff]
  simp only [hb, he, hzero]

/-- The literal Ward remainder lands in the same native relative shell. -/
theorem R0_mem_nativeShell (p : Charge hyperbolicPlane) {x : ComplexState}
    (hx : x ∈ NativeShell p) : R0 x ∈ NativeShell p := by
  obtain ⟨hp, hb, he⟩ := (mem_nativeShell_iff p x).mp hx
  exact (mem_nativeShell_iff p (R0 x)).mpr
    ⟨R0_preserves_momentum p hp, R0_preserves_relative_kernels hb he⟩

private theorem N_c0 : VirasoroBRST.N matter * c0 - c0 * VirasoroBRST.N matter = c0 := by
  change ghostLift BcGhostCharge.ghostNumber * ghostLift (c 0) -
    ghostLift (c 0) * ghostLift BcGhostCharge.ghostNumber = ghostLift (c 0)
  simpa only [map_sub, map_mul] using congrArg ghostLift (ghost_number_c 0)

private theorem N_R0 :
    VirasoroBRST.N matter * R0 - R0 * VirasoroBRST.N matter = (2 : ℂ) • R0 := by
  let N := VirasoroBRST.N matter
  have hQ : N * Q - Q * N = Q := VirasoroBRST.N_Q matter
  have hC : N * c0 - c0 * N = c0 := N_c0
  change N * R0 - R0 * N = (2 : ℂ) • R0
  calc
    N * R0 - R0 * N =
        (N * Q - Q * N) * c0 + Q * (N * c0 - c0 * N) +
        ((N * c0 - c0 * N) * Q + c0 * (N * Q - Q * N)) := by
      rw [← Q_c0_ward]
      noncomm_ring
    _ = (2 : ℂ) • R0 := by rw [hQ, hC, two_smul, ← Q_c0_ward]; abel

/-- The native Ward remainder stays at the same momentum and raises ghost number by two. -/
theorem R0_mem_graded_nativeShell (p : Charge hyperbolicPlane) (g : ℤ) {x : ComplexState}
    (hx : x ∈ NativeShell p) (hg : VirasoroBRST.N matter x = (g : ℂ) • x) :
    R0 x ∈ NativeShell p ∧ VirasoroBRST.N matter (R0 x) = ((g + 2 : ℤ) : ℂ) • R0 x := by
  refine ⟨R0_mem_nativeShell p hx, ?_⟩
  have h := LinearMap.congr_fun N_R0 x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hg, map_smul] at h
  rw [Int.cast_add, Int.cast_ofNat, add_smul]
  exact sub_eq_iff_eq_add'.mp h

private theorem b0_c0_apply_of_b0_eq_zero {z : ComplexState} (hz : b0 z = 0) :
    b0 (c0 z) = z := by
  simpa only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply,
    hz, map_zero, add_zero] using LinearMap.congr_fun b0_c0_car z

/-- Cycles of the original differential restricted to the actual shell at p. -/
abbrev NativeCycles (p : Charge hyperbolicPlane) := LinearMap.ker (nativeQ p)

local instance (p : Charge hyperbolicPlane) : AddCommGroup (NativeCycles p) :=
  Submodule.addCommGroup _

section Pairing

variable {σ : ℂ →+* ℂ}
variable (H : ComplexState →ₛₗ[σ] ComplexState →ₗ[ℂ] ℂ)
variable (hB : ∀ x y, H (b0 x) y = H x (b0 y))
variable (hQ : ∀ x y, H (Q x) y = H x (Q y))

include hB in
/-- The absolute form vanishes on two vectors in the b0 kernel. -/
theorem b0_kernel_isotropic {x z : ComplexState} (hx : b0 x = 0) (hz : b0 z = 0) :
    H x z = 0 := by
  calc
    H x z = H x (b0 (c0 z)) := congrArg (H x) (b0_c0_apply_of_b0_eq_zero hz).symm
    _ = H (b0 x) (c0 z) := (hB x (c0 z)).symm
    _ = 0 := by rw [hx, map_zero, LinearMap.zero_apply]

include hB hQ in
/-- The unsigned absolute Q adjoint becomes skew on the native c0-inserted form. -/
theorem c0_inserted_Q_skew {p q : Charge hyperbolicPlane}
    (x : NativeShell p) (y : NativeShell q) :
    H (nativeQ p x).val (c0 y.val) = -H x.val (c0 (nativeQ q y).val) := by
  change H (Q x.val) (c0 y.val) = -H x.val (c0 (Q y.val))
  have hx := ((mem_nativeShell_iff p x.val).mp x.property).2.1
  have hy := R0_mem_nativeShell q y.property
  have hz := ((mem_nativeShell_iff q (R0 y.val)).mp hy).2.1
  have hWard : Q (c0 y.val) + c0 (Q y.val) = R0 y.val :=
    LinearMap.congr_fun Q_c0_ward y.val
  apply eq_neg_iff_add_eq_zero.mpr
  rw [hQ x.val (c0 y.val), ← map_add (H x.val), hWard]
  exact b0_kernel_isotropic H hB hx hz

include hB hQ in
/-- A native relative boundary pairs to zero with every native cycle. -/
theorem c0_left_boundary {p q : Charge hyperbolicPlane}
    (x : NativeShell p) (y : NativeCycles q) :
    H (nativeQ p x).val (c0 y.val.val) = 0 := by
  have hy : nativeQ q y.val = 0 := LinearMap.mem_ker.mp y.property
  simpa only [hy, Submodule.coe_zero, map_zero, neg_zero] using
    c0_inserted_Q_skew H hB hQ x y.val

include hB hQ in
/-- A native relative cycle pairs to zero with every native boundary. -/
theorem c0_right_boundary {p q : Charge hyperbolicPlane}
    (x : NativeCycles p) (y : NativeShell q) :
    H x.val.val (c0 (nativeQ q y).val) = 0 := by
  have hx : nativeQ p x.val = 0 := LinearMap.mem_ker.mp x.property
  have h : 0 = -H x.val.val (c0 (nativeQ q y).val) := by
    simpa only [hx, Submodule.coe_zero, map_zero, LinearMap.zero_apply] using
      c0_inserted_Q_skew H hB hQ x.val y
  exact neg_eq_zero.mp h.symm

private def c0CyclePairing (p q : Charge hyperbolicPlane) :
    NativeCycles p →ₛₗ[σ] NativeCycles q →ₗ[ℂ] ℂ :=
  (H.comp ((NativeShell p).subtype.comp (NativeCycles p).subtype)).compl₂
    (c0.comp ((NativeShell q).subtype.comp (NativeCycles q).subtype))

include hB hQ in
/-- The c0 insertion descends through both literal kernel/image quotients.
In particular q may be the opposite plane momentum -p. -/
def c0QuotientPairing (p q : Charge hyperbolicPlane) :
    NativeCohomology p →ₛₗ[σ] NativeCohomology q →ₗ[ℂ] ℂ :=
  LinearMap.liftQ₂ (R := ℂ) (R₂ := ℂ) (S := ℂ) (S₂ := ℂ)
    (ρ := σ) (σ := RingHom.id ℂ)
    (FinitePerturbation.Boundaries (nativeQ p) (nativeQ_sq p))
    (FinitePerturbation.Boundaries (nativeQ q) (nativeQ_sq q))
    (c0CyclePairing H p q)
    (by
      intro x hx
      obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hx
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro y
      exact c0_left_boundary H hB hQ a y)
    (by
      intro y hy
      obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hy
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro x
      exact c0_right_boundary H hB hQ x a)

@[simp]
theorem c0QuotientPairing_mk {p q : Charge hyperbolicPlane}
    (x : NativeCycles p) (y : NativeCycles q) :
    c0QuotientPairing H hB hQ p q (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      H x.val.val (c0 y.val.val) := rfl

/-- The literal unsigned c0 adjoint permits insertion in the first slot as well. -/
theorem c0QuotientPairing_mk_left
    (hC : ∀ x y, H (c0 x) y = H x (c0 y)) {p q : Charge hyperbolicPlane}
    (x : NativeCycles p) (y : NativeCycles q) :
    c0QuotientPairing H hB hQ p q (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      H (c0 x.val.val) y.val.val :=
  (c0QuotientPairing_mk H hB hQ x y).trans (hC x.val.val y.val.val).symm

end Pairing

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeC0
