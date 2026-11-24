import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedRelativeZeroMomentum
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedSemirelativeZeroEnergyCone
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! The connecting operator on the native double-zero-momentum relative shell. -/

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.ClosedSemirelative

open ActualLeechOrbifoldCriticalMatter (Matter matter hyperbolicPlane)
open ActualLeechOrbifoldMatter (Orbifold)
open LatticeGeneratingFieldLocality (Carrier)
open LatticeQuartetContraction (State)
open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock ket phase lowerCount create_ket annihilate_ket)
open BcGhostFock (c)
open BcGhostBRST (rTerm)
open RelativeZeroMomentum (v u w)
open ClosedRelative (TotalGhostSpace)
open ClosedRelative.ZeroMomentum
  (ChiralIndex chiralBasis chiralBasis_native tensorBasis chiralDegree DegreeIndex
    totalGhostSpace_eq_span)
open Module (Basis)

local instance : AddCommGroup Matter :=
  TensorProduct.addCommGroup (R := ℂ) (M := Orbifold) (N := Carrier hyperbolicPlane)

local instance : AddCommGroup ComplexState :=
  TensorProduct.addCommGroup (R := ℂ) (M := Matter) (N := Fock)

local instance : AddCommGroup AssocState :=
  TensorProduct.addCommGroup (R := ℂ) (M := Orbifold) (N := State hyperbolicPlane)

local instance : AddCommGroup ClosedState :=
  TensorProduct.addCommGroup (R := ℂ) (M := ComplexState) (N := ComplexState)

local instance : AddCommGroup (relativeShell 0) := Submodule.addCommGroup (relativeShell 0)

local instance : AddCommGroup (ClosedRelative.Shell 0 0) :=
  TensorProduct.addCommGroup (R := ℂ) (M := relativeShell 0) (N := relativeShell 0)

local instance : AddCommGroup (EnergySpace 0) := Submodule.addCommGroup (EnergySpace 0)

open private mem_ghostSpace from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCohomology
open private gamma_c0 from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedSemirelativeZeroEnergyCone
open private tensor_neg_left from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedRelativeBRST

abbrev R0 : Module.End ℂ ComplexState := VirasoroBRST.ghostR matter 0

theorem M_eq_tensor_R0 :
    M = (1 / 2 : ℂ) • (TensorProduct.map R0 1 + TensorProduct.map 1 R0) := by
  have tensor_anticommutator (q : Module.End ℂ ComplexState)
      (hq : Γ * q = -(q * Γ)) :
      (TensorProduct.map q 1 + TensorProduct.map Γ q) *
          (TensorProduct.map c0 1 + TensorProduct.map Γ c0) +
        (TensorProduct.map c0 1 + TensorProduct.map Γ c0) *
          (TensorProduct.map q 1 + TensorProduct.map Γ q) =
        TensorProduct.map (q * c0 + c0 * q) 1 +
          TensorProduct.map 1 (q * c0 + c0 * q) := by
    simp only [mul_add, add_mul, ← TensorProduct.map_mul, one_mul, mul_one,
      hq, gamma_c0, gamma_square, tensor_neg_left, TensorProduct.map_add_left,
      TensorProduct.map_add_right]
    abel
  rw [M, C_plus, mul_smul_comm, smul_mul_assoc, ← smul_add, D,
    tensor_anticommutator Q gamma_Q, VirasoroBRST.Q_ward_c matter 0]

/-- At mode zero the actual Ward summand has coefficient p. -/
theorem rTerm_zero (p : ℤ) :
    rTerm 0 p = (p : ℂ) • (c p * c (-p)) := by
  have h : (1 / 2 : ℂ) * ((2 * p - 0 : ℤ) : ℂ) = (p : ℂ) := by
    push_cast
    ring
  rw [rTerm, h, zero_sub]

private theorem c_kills_no_even (S : Finset ℕ) (hS : ∀ k : ℕ, 2 * k ∉ S)
    (n : ℤ) (hn : 2 ≤ n) : c n (ket S) = 0 := by
  rw [BcGhostFock.c, ite_eq_right (by omega), annihilate_ket, ite_eq_right (hS _)]

private theorem rTerm_zero_off_pair (S : Finset ℕ) (hS : ∀ k : ℕ, 2 * k ∉ S)
    {p : ℤ} (hp : p ≠ 1) (hm : p ≠ -1) : rTerm 0 p (ket S) = 0 := by
  rw [rTerm_zero]
  rcases lt_trichotomy p 0 with h | rfl | h
  · rw [LinearMap.smul_apply, Module.End.mul_apply,
      c_kills_no_even S hS (-p) (by omega), map_zero, smul_zero]
  · simp
  · have hc := LinearMap.congr_fun (BcGhostFock.ghost_c_car p (-p)) (ket S)
    change c p (c (-p) (ket S)) + c (-p) (c p (ket S)) = 0 at hc
    rw [c_kills_no_even S hS p (by omega), map_zero, add_zero] at hc
    rw [LinearMap.smul_apply, Module.End.mul_apply, hc, smul_zero]

private theorem ghostR_zero_capture (S : Finset ℕ) (hS : ∀ k : ℕ, 2 * k ∉ S) :
    BcGhostBRST.R 0 (ket S) = rTerm 0 1 (ket S) + rTerm 0 (-1) (ket S) := by
  change (∑ᶠ p : ℤ, rTerm 0 p (ket S)) = _
  have h : Function.support (fun p : ℤ => rTerm 0 p (ket S)) ⊆
      (({1, -1} : Finset ℤ) : Set ℤ) := by
    intro p hp
    by_contra hn
    have hne : p ≠ 1 ∧ p ≠ -1 := by simpa using hn
    exact hp (rTerm_zero_off_pair S hS hne.1 hne.2)
  rw [finsum_eq_sum_of_support_subset _ h, Finset.sum_pair (by decide)]

private theorem c_neg_one : c (-1) = CountableOccupationFock.create 5 := by
  norm_num [BcGhostFock.c]

/-- The two surviving vacuum terms have equal positive coefficients. -/
theorem rTerm_zero_vacuum_pair :
    rTerm 0 1 (ket ∅) = ket {1, 5} ∧ rTerm 0 (-1) (ket ∅) = ket {1, 5} := by
  have h15 : lowerCount 1 {5} = 0 := by decide
  have h51 : lowerCount 5 {1} = 1 := by decide
  have hset : ({5, 1} : Finset ℕ) = {1, 5} := by decide
  constructor <;> rw [rTerm_zero] <;>
    simp [c_neg_one, phase, h15, h51, hset, show lowerCount 5 ∅ = 0 by decide,
      show lowerCount 1 ∅ = 0 by decide]

private theorem ghostR_zero_vacuum : BcGhostBRST.R 0 (ket ∅) = (2 : ℂ) • ket {1, 5} := by
  rw [ghostR_zero_capture ∅ (by simp), rTerm_zero_vacuum_pair.1,
    rTerm_zero_vacuum_pair.2, two_smul]

private theorem ghostR_zero_current : BcGhostBRST.R 0 (ket {1}) = 0 := by
  rw [ghostR_zero_capture {1} (by intro k; simp), rTerm_zero, rTerm_zero]
  simp [c_neg_one, create_ket]

private theorem ghostR_zero_top : BcGhostBRST.R 0 (ket {1, 5}) = 0 := by
  rw [ghostR_zero_capture {1, 5} (by intro k; simp; omega), rTerm_zero, rTerm_zero]
  simp [c_neg_one, create_ket]

theorem R0_v : R0 v = (2 : ℂ) • w := by
  simp only [v, R0, VirasoroBRST.ghostR, TensorProduct.map_tmul, LinearMap.id_apply,
    ghostR_zero_vacuum, w, TensorProduct.tmul_smul]

theorem R0_u (i : Fin 2) : R0 (u i) = 0 := by
  simp only [u, R0, VirasoroBRST.ghostR, TensorProduct.map_tmul, LinearMap.id_apply,
    ghostR_zero_current, TensorProduct.tmul_zero]

theorem R0_w : R0 w = 0 := by
  simp only [w, R0, VirasoroBRST.ghostR, TensorProduct.map_tmul, LinearMap.id_apply,
    ghostR_zero_top, TensorProduct.tmul_zero]

private abbrev chiralInclusion : relativeShell 0 →ₗ[ℂ] ComplexState :=
  reassoc.symm.toLinearMap.comp (relativeShell 0).subtype

/-- The native inclusion on the two momentum-zero relative factors. -/
def doubleZeroInclusion : ClosedRelative.Shell 0 0 →ₗ[ℂ] ClosedState :=
  TensorProduct.map chiralInclusion chiralInclusion

theorem doubleZeroInclusion_injective : Function.Injective doubleZeroInclusion := by
  have h : Function.Injective chiralInclusion :=
    reassoc.symm.injective.comp Subtype.val_injective
  exact TensorProduct.map_injective_of_flat_flat chiralInclusion chiralInclusion h h

theorem doubleZeroInclusion_tmul (x y : relativeShell 0) :
    doubleZeroInclusion (x ⊗ₜ[ℂ] y) = reassoc.symm x.val ⊗ₜ[ℂ] reassoc.symm y.val :=
  TensorProduct.map_tmul _ _ _ _

private theorem chiralInclusion_constraints (x : relativeShell 0) :
    b0 (chiralInclusion x) = 0 ∧ E (chiralInclusion x) = 0 := by
  obtain ⟨_, hb, he⟩ := (mem_relativeShell_iff 0 x.val).mp x.property
  change reassoc (b0 (chiralInclusion x)) = 0 at hb
  change reassoc (E (chiralInclusion x)) = 0 at he
  exact ⟨reassoc.map_eq_zero_iff.mp hb, reassoc.map_eq_zero_iff.mp he⟩

theorem doubleZeroInclusion_mem_R (x : ClosedRelative.Shell 0 0) :
    doubleZeroInclusion x ∈ R := by
  induction x using TensorProduct.inductionOn with
  | tmul x y =>
    obtain ⟨hbx, hex⟩ := chiralInclusion_constraints x
    obtain ⟨hby, hey⟩ := chiralInclusion_constraints y
    apply (mem_R_iff _).mpr
    simp only [doubleZeroInclusion, TensorProduct.map_tmul, hbx, hby, hex, hey,
      TensorProduct.zero_tmul, TensorProduct.tmul_zero, and_self]
  | add x y hx hy => rw [map_add]; exact R.add_mem hx hy

/-- The native tensor inclusion with its zero-energy double-relative codomain. -/
def doubleZeroToR : ClosedRelative.Shell 0 0 →ₗ[ℂ] R :=
  doubleZeroInclusion.codRestrict R doubleZeroInclusion_mem_R

private abbrev vacuumIndex : ChiralIndex := .inl ()
private abbrev topIndex : ChiralIndex := .inr (.inr ())

/-- Half of the actual chiral Ward map on the relative momentum-zero shell. -/
def chiralHalfR : Module.End ℂ (relativeShell 0) :=
  chiralBasis.constr ℂ (Sum.elim (fun _ => chiralBasis topIndex) (fun _ => 0))

theorem chiralHalfR_basis (i : ChiralIndex) :
    chiralHalfR (chiralBasis i) =
      Sum.elim (fun _ => chiralBasis topIndex) (fun _ => 0) i := by
  simp [chiralHalfR]

private theorem R0_inclusion_basis (i : ChiralIndex) :
    R0 (chiralInclusion (chiralBasis i)) =
      (2 : ℂ) • chiralInclusion (chiralHalfR (chiralBasis i)) := by
  rw [chiralHalfR_basis]
  change R0 (reassoc.symm (chiralBasis i).val) = _
  rw [chiralBasis_native]
  rcases i with i | (i | i)
  · change R0 v = (2 : ℂ) • chiralInclusion (chiralBasis topIndex)
    rw [R0_v]
    congr 1
    exact (chiralBasis_native topIndex).symm
  · simpa only [Sum.elim_inr, Sum.elim_inl, map_zero, smul_zero] using R0_u i
  · simpa only [Sum.elim_inr, map_zero, smul_zero] using R0_w

theorem R0_chiralInclusion (x : relativeShell 0) :
    R0 (chiralInclusion x) = (2 : ℂ) • chiralInclusion (chiralHalfR x) := by
  have h : R0.comp chiralInclusion = (2 : ℂ) • (chiralInclusion.comp chiralHalfR) :=
    chiralBasis.ext fun i => R0_inclusion_basis i
  exact LinearMap.congr_fun h x

/-- The actual connecting operator written on the two relative momentum-zero factors. -/
def doubleZeroM : Module.End ℂ (ClosedRelative.Shell 0 0) :=
  TensorProduct.map chiralHalfR 1 + TensorProduct.map 1 chiralHalfR

theorem doubleZeroM_basis (i j : ChiralIndex) :
    doubleZeroM (tensorBasis (i, j)) =
      (Sum.elim (fun _ => tensorBasis (topIndex, j)) (fun _ => 0) i) +
      (Sum.elim (fun _ => tensorBasis (i, topIndex)) (fun _ => 0) j) := by
  simp only [doubleZeroM, tensorBasis, Basis.tensorProduct_apply', LinearMap.add_apply,
    TensorProduct.map_tmul, Module.End.one_apply, chiralHalfR_basis]
  congr 1
  · cases i <;> simp
  · cases j <;> simp

theorem M_doubleZeroInclusion (x : ClosedRelative.Shell 0 0) :
    M (doubleZeroInclusion x) = doubleZeroInclusion (doubleZeroM x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    simp only [M_eq_tensor_R0, doubleZeroInclusion, doubleZeroM, LinearMap.smul_apply,
      LinearMap.add_apply, map_add, TensorProduct.map_tmul, Module.End.one_apply,
      R0_chiralInclusion, TensorProduct.smul_tmul, ← TensorProduct.tmul_smul,
      smul_add, smul_smul]
    norm_num

theorem doubleZeroInclusion_tensorBasis (i j : ChiralIndex) :
    doubleZeroInclusion (tensorBasis (i, j)) =
      (Sum.elim (fun _ => v) (Sum.elim u (fun _ => w)) i) ⊗ₜ[ℂ]
      (Sum.elim (fun _ => v) (Sum.elim u (fun _ => w)) j) := by
  rw [tensorBasis, Basis.tensorProduct_apply', doubleZeroInclusion_tmul,
    chiralBasis_native, chiralBasis_native]

theorem M_R_doubleZeroToR (x : ClosedRelative.Shell 0 0) :
    M_R (doubleZeroToR x) = doubleZeroToR (doubleZeroM x) :=
  Subtype.ext (M_doubleZeroInclusion x)

private theorem Q_chiralInclusion (x : relativeShell 0) : Q (chiralInclusion x) = 0 := by
  have h := LinearMap.congr_fun RelativeZeroMomentum.relativeQ_eq_zero x
  have h' : assocQ x.val = 0 := congrArg Subtype.val h
  change reassoc (Q (chiralInclusion x)) = 0 at h'
  exact reassoc.map_eq_zero_iff.mp h'

theorem D_R_doubleZeroToR (x : ClosedRelative.Shell 0 0) : D_R (doubleZeroToR x) = 0 := by
  apply Subtype.ext
  change D (doubleZeroInclusion x) = 0
  induction x using TensorProduct.inductionOn with
  | tmul x y =>
    change Q (chiralInclusion x) ⊗ₜ[ℂ] chiralInclusion y +
      Γ (chiralInclusion x) ⊗ₜ[ℂ] Q (chiralInclusion y) = 0
    rw [Q_chiralInclusion, Q_chiralInclusion, TensorProduct.zero_tmul,
      TensorProduct.tmul_zero, add_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/-- Inclusion into the native semirelative complex with the supplier's literal splitting. -/
def doubleZeroConeInclusion :
    ClosedRelative.Shell 0 0 × ClosedRelative.Shell 0 0 →ₗ[ℂ] EnergySpace 0 :=
  zeroEnergySplit.symm.toLinearMap.comp (doubleZeroToR.prodMap doubleZeroToR)

theorem doubleZeroConeInclusion_val (x y : ClosedRelative.Shell 0 0) :
    (doubleZeroConeInclusion (x, y)).val =
      doubleZeroInclusion x + C_plus (doubleZeroInclusion y) :=
  zeroEnergySplit_symm_apply _

theorem doubleZeroConeInclusion_injective : Function.Injective doubleZeroConeInclusion := by
  have h : Function.Injective doubleZeroToR := fun _ _ h =>
    doubleZeroInclusion_injective (congrArg Subtype.val h)
  exact zeroEnergySplit.symm.injective.comp fun _ _ eq =>
    Prod.ext (h (congrArg Prod.fst eq)) (h (congrArg Prod.snd eq))

theorem differential_doubleZeroConeInclusion (x y : ClosedRelative.Shell 0 0) :
    differential 0 (doubleZeroConeInclusion (x, y)) = doubleZeroConeInclusion (doubleZeroM y, 0) := by
  apply zeroEnergySplit.injective
  rw [zeroEnergySplit_differential]
  have split (z t : ClosedRelative.Shell 0 0) :
      zeroEnergySplit (doubleZeroConeInclusion (z, t)) = (doubleZeroToR z, doubleZeroToR t) :=
    zeroEnergySplit.apply_symm_apply _
  rw [split, split, coneDifferential_apply, D_R_doubleZeroToR, D_R_doubleZeroToR,
    M_R_doubleZeroToR, zero_add, neg_zero, map_zero]

/-- The actual plane momentum-zero projector in the original matter and ghost association. -/
def momentumZero : Module.End ℂ ComplexState :=
  TensorProduct.map (TensorProduct.map LinearMap.id (LatticeQuartetContraction.chargeMatter
    (D := hyperbolicPlane) 0)) LinearMap.id

/-- The two native plane momentum projections act separately on the closed tensor. -/
def DoubleZeroMomentum : Submodule ℂ ClosedState :=
  (TensorProduct.map momentumZero (1 : Module.End ℂ ComplexState) - 1).ker ⊓
    (TensorProduct.map (1 : Module.End ℂ ComplexState) momentumZero - 1).ker

private theorem mem_doubleZeroMomentum_iff (x : ClosedState) :
    x ∈ DoubleZeroMomentum ↔
      TensorProduct.map momentumZero (1 : Module.End ℂ ComplexState) x = x ∧
      TensorProduct.map (1 : Module.End ℂ ComplexState) momentumZero x = x := by
  simp only [DoubleZeroMomentum, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
    Module.End.one_apply, sub_eq_zero]

private theorem reassoc_momentumZero (x : ComplexState) :
    reassoc (momentumZero x) =
      rightLift (LatticeQuartetContraction.chargeProject (D := hyperbolicPlane) 0) (reassoc x) := by
  have h : reassoc.toLinearMap.comp momentumZero = (rightLift
      (LatticeQuartetContraction.chargeProject (D := hyperbolicPlane) 0)).comp reassoc.toLinearMap := by
    apply TensorProduct.ext'
    intro a s
    induction a using TensorProduct.inductionOn with
    | tmul v u => rfl
    | add a d ha hd =>
      simp only [LinearMap.comp_apply, TensorProduct.add_tmul, map_add] at ha hd ⊢
      rw [ha, hd]
  exact LinearMap.congr_fun h x

private abbrev ChiralConstraints := ComplexState × (ComplexState × ComplexState)

private def chiralConstraints : ComplexState →ₗ[ℂ] ChiralConstraints :=
  (momentumZero - 1).prod (b0.prod E)

private theorem chiralConstraints_exact : Function.Exact chiralInclusion chiralConstraints := by
  intro x
  change (momentumZero x - x, (b0 x, E x)) = (0, (0, 0)) ↔ _
  have h : reassoc x ∈ relativeShell 0 ↔
      momentumZero x = x ∧ b0 x = 0 ∧ E x = 0 := by
    have transport (A : Module.End ℂ ComplexState) :
        ((reassoc.conjAlgEquiv ℂ) A) (reassoc x) = reassoc (A x) := by
      rw [LinearEquiv.conjAlgEquiv_apply (R := ℂ) reassoc A]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [mem_relativeShell_iff, ← reassoc_momentumZero,
      show assocB0 (reassoc x) = reassoc (b0 x) from transport b0,
      show assocE (reassoc x) = reassoc (E x) from transport E]
    simp only [reassoc.injective.eq_iff, reassoc.map_eq_zero_iff]
  simp only [Prod.mk.injEq, sub_eq_zero, Set.mem_range]
  rw [← h]
  constructor
  · intro hx
    exact ⟨⟨reassoc x, hx⟩, reassoc.symm_apply_apply x⟩
  · rintro ⟨y, rfl⟩
    change reassoc (reassoc.symm y.val) ∈ relativeShell 0
    rw [reassoc.apply_symm_apply]
    exact y.property

private theorem tensor_prod_zero_iff {U V W X : Type*}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W] [AddCommGroup X]
    [Module ℂ U] [Module ℂ V] [Module ℂ W] [Module ℂ X]
    (f : U →ₗ[ℂ] V) (g : U →ₗ[ℂ] W) (z : U ⊗[ℂ] X) :
    (f.prod g).rTensor X z = 0 ↔ f.rTensor X z = 0 ∧ g.rTensor X z = 0 := by
  let e := TensorProduct.prodLeft ℂ ℂ V W X
  have h : e.toLinearMap.comp ((f.prod g).rTensor X) =
      (f.rTensor X).prod (g.rTensor X) := TensorProduct.ext' fun _ _ => rfl
  rw [← e.map_eq_zero_iff]
  change e (((f.prod g).rTensor X) z) = 0 ↔ _
  rw [show e (((f.prod g).rTensor X) z) = (f.rTensor X z, g.rTensor X z) from LinearMap.congr_fun h z]
  exact Prod.ext_iff

private theorem prod_tensor_zero_iff {U V W X : Type*}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W] [AddCommGroup X]
    [Module ℂ U] [Module ℂ V] [Module ℂ W] [Module ℂ X]
    (f : U →ₗ[ℂ] V) (g : U →ₗ[ℂ] W) (z : X ⊗[ℂ] U) :
    (f.prod g).lTensor X z = 0 ↔ f.lTensor X z = 0 ∧ g.lTensor X z = 0 := by
  let e := TensorProduct.prodRight ℂ ℂ X V W
  have h : e.toLinearMap.comp ((f.prod g).lTensor X) =
      (f.lTensor X).prod (g.lTensor X) := TensorProduct.ext' fun _ _ => rfl
  rw [← e.map_eq_zero_iff]
  change e (((f.prod g).lTensor X) z) = 0 ↔ _
  rw [show e (((f.prod g).lTensor X) z) = (f.lTensor X z, g.lTensor X z) from LinearMap.congr_fun h z]
  exact Prod.ext_iff

open private tensor_sub_left tensor_sub_right from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedRelativeBRST

/-- The embedded tensor shell is exactly the common native momentum-zero and double-relative shell. -/
theorem mem_doubleZeroInclusion_range_iff (z : ClosedState) :
    z ∈ doubleZeroInclusion.range ↔ z ∈ R ∧ z ∈ DoubleZeroMomentum := by
  have hleft (z : ClosedState) : chiralConstraints.rTensor ComplexState z = 0 ↔
      TensorProduct.map momentumZero (1 : Module.End ℂ ComplexState) z = z ∧
      TensorProduct.map b0 (1 : Module.End ℂ ComplexState) z = 0 ∧
      TensorProduct.map E (1 : Module.End ℂ ComplexState) z = 0 := by
    rw [chiralConstraints, tensor_prod_zero_iff, tensor_prod_zero_iff]
    change TensorProduct.map (momentumZero - 1) 1 z = 0 ∧ _ ↔ _
    simp only [tensor_sub_left, TensorProduct.map_one, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero]
    rfl
  have hright (z : ClosedState) : chiralConstraints.lTensor ComplexState z = 0 ↔
      TensorProduct.map (1 : Module.End ℂ ComplexState) momentumZero z = z ∧
      TensorProduct.map (1 : Module.End ℂ ComplexState) b0 z = 0 ∧
      TensorProduct.map (1 : Module.End ℂ ComplexState) E z = 0 := by
    rw [chiralConstraints, prod_tensor_zero_iff, prod_tensor_zero_iff]
    change TensorProduct.map 1 (momentumZero - 1) z = 0 ∧ _ ↔ _
    simp only [tensor_sub_right, TensorProduct.map_one, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero]
    rfl
  have hl := Module.Flat.rTensor_exact ComplexState chiralConstraints_exact z
  have hr := Module.Flat.lTensor_exact (relativeShell 0) chiralConstraints_exact
  have hcomp : (chiralConstraints.lTensor ComplexState).comp (chiralInclusion.rTensor ComplexState) =
      (chiralInclusion.rTensor ChiralConstraints).comp
        (chiralConstraints.lTensor (relativeShell 0)) :=
    TensorProduct.ext' fun _ _ => rfl
  have hinj : Function.Injective (chiralInclusion.rTensor ChiralConstraints) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (reassoc.symm.injective.comp Subtype.val_injective)
  have hmap : doubleZeroInclusion =
      (chiralInclusion.rTensor ComplexState).comp (chiralInclusion.lTensor (relativeShell 0)) :=
    TensorProduct.ext' fun _ _ => rfl
  rw [mem_R_iff, mem_doubleZeroMomentum_iff]
  constructor
  · rintro ⟨x, rfl⟩
    have hn : ∀ x : ClosedRelative.Shell 0 0,
        chiralConstraints.rTensor ComplexState (doubleZeroInclusion x) = 0 ∧
        chiralConstraints.lTensor ComplexState (doubleZeroInclusion x) = 0 := by
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul x y =>
        have hx := (chiralConstraints_exact (chiralInclusion x)).mpr ⟨x, rfl⟩
        have hy := (chiralConstraints_exact (chiralInclusion y)).mpr ⟨y, rfl⟩
        change chiralConstraints (chiralInclusion x) ⊗ₜ[ℂ] chiralInclusion y = 0 ∧
          chiralInclusion x ⊗ₜ[ℂ] chiralConstraints (chiralInclusion y) = 0
        simp only [hx, hy, TensorProduct.zero_tmul, TensorProduct.tmul_zero, and_self]
      | add x y hx hy =>
        simp only [map_add, hx.1, hx.2, hy.1, hy.2, add_zero, and_self]
    obtain ⟨hL, hR⟩ := hn x
    have left := (hleft _).mp hL
    have right := (hright _).mp hR
    exact ⟨⟨left.2.1, right.2.1, left.2.2, right.2.2⟩, left.1, right.1⟩
  · rintro ⟨⟨hbL, hbR, heL, heR⟩, hpL, hpR⟩
    have hzR := (hright z).mpr ⟨hpR, hbR, heR⟩
    obtain ⟨y, hy⟩ := hl.mp ((hleft z).mpr ⟨hpL, hbL, heL⟩)
    have hyR : chiralConstraints.lTensor (relativeShell 0) y = 0 := by
      apply (chiralInclusion.rTensor ChiralConstraints).map_eq_zero_iff hinj |>.mp
      change ((chiralInclusion.rTensor ChiralConstraints).comp
        (chiralConstraints.lTensor (relativeShell 0))) y = 0
      rw [← hcomp, LinearMap.comp_apply, hy]
      exact hzR
    obtain ⟨x, hx⟩ := (hr y).mp hyR
    exact ⟨x, by rw [hmap, LinearMap.comp_apply, hx, hy]⟩

private theorem momentumZero_ghost_comm (A : Module.End ℂ Fock) :
    momentumZero * TensorProduct.map (1 : Module.End ℂ Matter) A =
      TensorProduct.map 1 A * momentumZero := by
  simp only [momentumZero, ← TensorProduct.map_mul, one_mul, mul_one]
  rfl

private theorem momentum_signed_comm (a : Module.End ℂ ComplexState)
    (ha : momentumZero * a = a * momentumZero) :
    let T := TensorProduct.map a (1 : Module.End ℂ ComplexState) + TensorProduct.map Γ a
    TensorProduct.map momentumZero 1 * T = T * TensorProduct.map momentumZero 1 ∧
      TensorProduct.map 1 momentumZero * T = T * TensorProduct.map 1 momentumZero := by
  have hΓ : momentumZero * Γ = Γ * momentumZero := momentumZero_ghost_comm CountableOccupationFock.parity
  dsimp only
  constructor <;>
    simp only [mul_add, add_mul, ← TensorProduct.map_mul, one_mul, mul_one, ha, hΓ]

private theorem momentum_fixed_preserved (a : Module.End ℂ ClosedState)
    (hl : TensorProduct.map momentumZero (1 : Module.End ℂ ComplexState) * a =
      a * TensorProduct.map momentumZero 1)
    (hr : TensorProduct.map (1 : Module.End ℂ ComplexState) momentumZero * a =
      a * TensorProduct.map 1 momentumZero)
    {x : ClosedState} (hx : x ∈ DoubleZeroMomentum) : a x ∈ DoubleZeroMomentum := by
  obtain ⟨hxL, hxR⟩ := (mem_doubleZeroMomentum_iff x).mp hx
  exact (mem_doubleZeroMomentum_iff _).mpr
    ⟨by simpa only [Module.End.mul_apply, hxL] using LinearMap.congr_fun hl x,
      by simpa only [Module.End.mul_apply, hxR] using LinearMap.congr_fun hr x⟩

private theorem B_plus_mem_doubleZeroMomentum {x : ClosedState} (hx : x ∈ DoubleZeroMomentum) :
    B_plus x ∈ DoubleZeroMomentum := by
  obtain ⟨hl, hr⟩ := momentum_signed_comm b0 (momentumZero_ghost_comm (BcGhostFock.b 0))
  exact momentum_fixed_preserved B_plus hl hr hx

private theorem C_plus_mem_doubleZeroMomentum {x : ClosedState} (hx : x ∈ DoubleZeroMomentum) :
    C_plus x ∈ DoubleZeroMomentum := by
  obtain ⟨hl, hr⟩ := momentum_signed_comm c0 (momentumZero_ghost_comm (c 0))
  apply momentum_fixed_preserved C_plus _ _ hx
  · rw [C_plus, mul_smul_comm, smul_mul_assoc, hl]
  · rw [C_plus, mul_smul_comm, smul_mul_assoc, hr]

/-- The literal cone inclusion exhausts the native semirelative energy-zero sector
with both plane momenta set to zero. -/
theorem mem_doubleZeroConeInclusion_range_iff (x : EnergySpace 0) :
    x ∈ doubleZeroConeInclusion.range ↔ x.val ∈ DoubleZeroMomentum := by
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    have ha := ((mem_doubleZeroInclusion_range_iff _).mp ⟨a, rfl⟩).2
    have hb := ((mem_doubleZeroInclusion_range_iff _).mp ⟨b, rfl⟩).2
    rw [doubleZeroConeInclusion_val]
    exact DoubleZeroMomentum.add_mem ha (C_plus_mem_doubleZeroMomentum hb)
  · intro hx
    have hs := zeroEnergySplit_apply x
    have hB := B_plus_mem_doubleZeroMomentum hx
    have ha : (zeroEnergySplit x).1.val ∈ DoubleZeroMomentum := by
      rw [hs.1]
      exact DoubleZeroMomentum.sub_mem hx (C_plus_mem_doubleZeroMomentum hB)
    have hb : (zeroEnergySplit x).2.val ∈ DoubleZeroMomentum := by rwa [hs.2]
    obtain ⟨a, ha'⟩ := (mem_doubleZeroInclusion_range_iff _).mpr ⟨(zeroEnergySplit x).1.property, ha⟩
    obtain ⟨b, hb'⟩ := (mem_doubleZeroInclusion_range_iff _).mpr ⟨(zeroEnergySplit x).2.property, hb⟩
    refine ⟨(a, b), zeroEnergySplit.injective ?_⟩
    have he : zeroEnergySplit (doubleZeroConeInclusion (a, b)) =
        (doubleZeroToR a, doubleZeroToR b) := zeroEnergySplit.apply_symm_apply _
    rw [he]
    exact Prod.ext (Subtype.ext ha') (Subtype.ext hb')

private def tensorDegree (ij : ChiralIndex × ChiralIndex) : ℤ :=
  chiralDegree ij.1 + chiralDegree ij.2

private def tensorNumber : Module.End ℂ (ClosedRelative.Shell 0 0) :=
  tensorBasis.constr ℂ fun ij => (tensorDegree ij : ℂ) • tensorBasis ij

private theorem N_chiralBasis (i : ChiralIndex) :
    N (chiralInclusion (chiralBasis i)) = (chiralDegree i : ℂ) • chiralInclusion (chiralBasis i) := by
  have h := (mem_ghostSpace 0 (chiralDegree i) (chiralBasis i)).mp
    (ClosedRelative.ZeroMomentum.chiralBasis_mem i)
  apply reassoc.injective
  change RelativeCohomology.assocN (chiralBasis i).val =
    reassoc ((chiralDegree i : ℂ) • chiralInclusion (chiralBasis i))
  rw [map_smul]
  exact h.trans (congrArg (fun z : AssocState => (chiralDegree i : ℂ) • z)
    (reassoc.apply_symm_apply (chiralBasis i).val).symm)

private theorem tensorNumber_intertwines (x : ClosedRelative.Shell 0 0) :
    N_total (doubleZeroInclusion x) = doubleZeroInclusion (tensorNumber x) := by
  have h : N_total.comp doubleZeroInclusion = doubleZeroInclusion.comp tensorNumber := by
    apply tensorBasis.ext
    rintro ⟨i, j⟩
    simp only [LinearMap.comp_apply]
    rw [show tensorNumber (tensorBasis (i, j)) =
      (tensorDegree (i, j) : ℂ) • tensorBasis (i, j) from tensorBasis.constr_basis ℂ _ _, map_smul]
    rw [tensorBasis, Basis.tensorProduct_apply']
    change N (chiralInclusion (chiralBasis i)) ⊗ₜ[ℂ] chiralInclusion (chiralBasis j) +
      chiralInclusion (chiralBasis i) ⊗ₜ[ℂ] N (chiralInclusion (chiralBasis j)) =
        (tensorDegree (i, j) : ℂ) •
          (chiralInclusion (chiralBasis i) ⊗ₜ[ℂ] chiralInclusion (chiralBasis j))
    rw [N_chiralBasis, N_chiralBasis, TensorProduct.smul_tmul, ← TensorProduct.tmul_smul,
      ← TensorProduct.tmul_add, tensorDegree, Int.cast_add, add_smul]
  exact LinearMap.congr_fun h x

private theorem tensorNumber_repr (x : ClosedRelative.Shell 0 0) (ij : ChiralIndex × ChiralIndex) :
    tensorBasis.repr (tensorNumber x) ij = (tensorDegree ij : ℂ) * tensorBasis.repr x ij := by
  have h : tensorBasis.coord ij ∘ₗ tensorNumber =
      (tensorDegree ij : ℂ) • tensorBasis.coord ij := by
    apply tensorBasis.ext
    intro k
    simp only [LinearMap.comp_apply, tensorNumber, Basis.constr_basis, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    by_cases hk : k = ij
    · subst k; rfl
    · have hz : tensorBasis.coord ij (tensorBasis k) = 0 := by
        simp [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_of_ne, Ne.symm hk]
      rw [hz, mul_zero, mul_zero]
  exact LinearMap.congr_fun h x

theorem doubleZeroInclusion_degree_iff (g : ℤ) (x : ClosedRelative.Shell 0 0) :
    doubleZeroInclusion x ∈ GhostSpace g ↔ x ∈ TotalGhostSpace 0 0 g := by
  have hspan : Set.range (fun ij : DegreeIndex g => tensorBasis ij.val) =
      tensorBasis '' {ij | tensorDegree ij = g} := by
    ext z
    constructor
    · rintro ⟨ij, rfl⟩
      exact ⟨ij.val, ij.property, rfl⟩
    · rintro ⟨ij, h, rfl⟩
      exact ⟨⟨ij, h⟩, rfl⟩
  rw [Module.End.mem_eigenspace_iff, tensorNumber_intertwines, ← map_smul,
    doubleZeroInclusion_injective.eq_iff, totalGhostSpace_eq_span, hspan, Basis.mem_span_image]
  constructor
  · intro h ij hij
    have hc := congrArg (fun z => tensorBasis.repr z ij) h
    rw [tensorNumber_repr, map_smul, Finsupp.smul_apply, smul_eq_mul] at hc
    exact Int.cast_injective (mul_right_cancel₀ (Finsupp.mem_support_iff.mp hij) hc)
  · intro h
    apply tensorBasis.repr.injective
    ext ij
    rw [tensorNumber_repr, map_smul, Finsupp.smul_apply, smul_eq_mul]
    by_cases hi : ij ∈ (tensorBasis.repr x).support
    · rw [show tensorDegree ij = g from h hi]
    · rw [Finsupp.notMem_support_iff.mp hi, mul_zero, mul_zero]

theorem doubleZeroConeInclusion_degree_iff (g : ℤ) (x y : ClosedRelative.Shell 0 0) :
    (doubleZeroConeInclusion (x, y)).val ∈ GhostSpace g ↔
      x ∈ TotalGhostSpace 0 0 g ∧ y ∈ TotalGhostSpace 0 0 (g - 1) := by
  rw [zeroEnergySplit_degree_iff]
  have h : zeroEnergySplit (doubleZeroConeInclusion (x, y)) = (doubleZeroToR x, doubleZeroToR y) :=
    zeroEnergySplit.apply_symm_apply _
  rw [h]
  exact and_congr (doubleZeroInclusion_degree_iff g x) (doubleZeroInclusion_degree_iff (g - 1) y)

private abbrev currentIndex (i : Fin 2) : ChiralIndex := .inr (.inl i)

private def degreeOneImagePair : Fin 2 ⊕ Fin 2 → ChiralIndex × ChiralIndex
  | .inl i => (topIndex, currentIndex i)
  | .inr i => (currentIndex i, topIndex)

private theorem degreeOneImagePair_injective : Function.Injective degreeOneImagePair := by
  rintro (i | i) (j | j) h <;> simp [degreeOneImagePair] at h ⊢ <;> exact h

/-- The ranked image is the image of the actual ambient connecting operator in that degree. -/
theorem finrank_native_M_image (g : ℤ) :
    Module.finrank ℂ (((TotalGhostSpace 0 0 g).map doubleZeroInclusion).map M) =
      Module.finrank ℂ ((TotalGhostSpace 0 0 g).map doubleZeroM) := by
  have h : M.comp doubleZeroInclusion = doubleZeroInclusion.comp doubleZeroM :=
    LinearMap.ext M_doubleZeroInclusion
  rw [← Submodule.map_comp, h, Submodule.map_comp]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective doubleZeroInclusion
    doubleZeroInclusion_injective ((TotalGhostSpace 0 0 g).map doubleZeroM))).symm

private theorem range_M_degree (g : ℤ) :
    (TotalGhostSpace 0 0 g).map doubleZeroM =
      Submodule.span ℂ (Set.range fun ij : DegreeIndex g => doubleZeroM (tensorBasis ij.val)) := by
  rw [totalGhostSpace_eq_span, Submodule.map_span, ← Set.range_comp]
  rfl

private theorem range_M_degree_zero :
    (TotalGhostSpace 0 0 0).map doubleZeroM =
      ℂ ∙ (tensorBasis (topIndex, vacuumIndex) + tensorBasis (vacuumIndex, topIndex)) := by
  rw [range_M_degree]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨⟨i, j⟩, h⟩, rfl⟩
    change chiralDegree i + chiralDegree j = 0 at h
    rcases i with ⟨⟩ | (i | ⟨⟩) <;> rcases j with ⟨⟩ | (j | ⟨⟩) <;>
      norm_num [chiralDegree] at h
    exact Set.mem_singleton_iff.mpr (doubleZeroM_basis _ _)
  · rintro rfl
    exact ⟨⟨(vacuumIndex, vacuumIndex), rfl⟩, doubleZeroM_basis _ _⟩

private theorem range_M_degree_one :
    (TotalGhostSpace 0 0 1).map doubleZeroM =
      Submodule.span ℂ (Set.range (tensorBasis ∘ degreeOneImagePair)) := by
  rw [range_M_degree]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨⟨i, j⟩, h⟩, rfl⟩
    change chiralDegree i + chiralDegree j = 1 at h
    rcases i with ⟨⟩ | (i | ⟨⟩) <;> rcases j with ⟨⟩ | (j | ⟨⟩) <;>
      norm_num [chiralDegree] at h
    · exact ⟨.inl j, by simp [degreeOneImagePair, doubleZeroM_basis]⟩
    · exact ⟨.inr i, by simp [degreeOneImagePair, doubleZeroM_basis]⟩
  · rintro ⟨i | i, rfl⟩
    · exact ⟨⟨(vacuumIndex, currentIndex i), rfl⟩, by
        simp [degreeOneImagePair, doubleZeroM_basis]⟩
    · exact ⟨⟨(currentIndex i, vacuumIndex), rfl⟩, by
        simp [degreeOneImagePair, doubleZeroM_basis]⟩

private theorem range_M_degree_two :
    (TotalGhostSpace 0 0 2).map doubleZeroM = ℂ ∙ tensorBasis (topIndex, topIndex) := by
  rw [range_M_degree]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨⟨i, j⟩, h⟩, rfl⟩
    change chiralDegree i + chiralDegree j = 2 at h
    rcases i with ⟨⟩ | (i | ⟨⟩) <;> rcases j with ⟨⟩ | (j | ⟨⟩) <;>
      norm_num [chiralDegree] at h
    all_goals simp [doubleZeroM_basis, Submodule.mem_span_singleton_self]
  · apply Submodule.span_le.mpr
    rintro _ rfl
    apply Submodule.subset_span
    exact ⟨⟨(vacuumIndex, topIndex), rfl⟩, by simp [doubleZeroM_basis]⟩

theorem doubleZeroM_rank_zero : Module.finrank ℂ ((TotalGhostSpace 0 0 0).map doubleZeroM) = 1 := by
  rw [range_M_degree_zero]
  have hne : (topIndex, vacuumIndex) ≠ (vacuumIndex, topIndex) := by decide
  have hn : tensorBasis (topIndex, vacuumIndex) + tensorBasis (vacuumIndex, topIndex) ≠ 0 := by
    intro h
    let f : ClosedRelative.Shell 0 0 →ₗ[ℂ] ℂ := tensorBasis.coord (topIndex, vacuumIndex)
    have hz := congrArg f h
    rw [map_add, map_zero] at hz
    change tensorBasis.repr (tensorBasis (topIndex, vacuumIndex)) (topIndex, vacuumIndex) +
      tensorBasis.repr (tensorBasis (vacuumIndex, topIndex)) (topIndex, vacuumIndex) = 0 at hz
    rw [tensorBasis.repr_self, tensorBasis.repr_self, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne hne, add_zero] at hz
    exact one_ne_zero hz
  exact finrank_span_singleton (K := ℂ) hn

theorem doubleZeroM_rank_one : Module.finrank ℂ ((TotalGhostSpace 0 0 1).map doubleZeroM) = 4 := by
  rw [range_M_degree_one, finrank_span_eq_card
    (tensorBasis.linearIndependent.comp degreeOneImagePair degreeOneImagePair_injective)]
  decide

theorem doubleZeroM_rank_two : Module.finrank ℂ ((TotalGhostSpace 0 0 2).map doubleZeroM) = 1 := by
  rw [range_M_degree_two]
  exact finrank_span_singleton (K := ℂ) (tensorBasis.ne_zero (topIndex, topIndex))

theorem doubleZeroM_range_eq_bot {g : ℤ} (hg : g < 0 ∨ 2 < g) :
    (TotalGhostSpace 0 0 g).map doubleZeroM = ⊥ := by
  rw [range_M_degree, eq_bot_iff]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨⟨i, j⟩, h⟩, rfl⟩
  change chiralDegree i + chiralDegree j = g at h
  rcases i with ⟨⟩ | (i | ⟨⟩) <;> rcases j with ⟨⟩ | (j | ⟨⟩) <;>
    norm_num [chiralDegree] at h
  all_goals first | omega | simp [doubleZeroM_basis]

private abbrev RelativeDegree (g : ℤ) := TotalGhostSpace 0 0 g

/-- The degree-`g` native semirelative cochains from the two zero-momentum factors. -/
def DoubleZeroGhostSpace (g : ℤ) : Submodule ℂ (EnergySpace 0) :=
  ((RelativeDegree g).prod (RelativeDegree (g - 1))).map doubleZeroConeInclusion

local instance (g : ℤ) : AddCommGroup (DoubleZeroGhostSpace g) :=
  Submodule.addCommGroup (DoubleZeroGhostSpace g)

theorem mem_doubleZeroGhostSpace_iff (g : ℤ) (x : EnergySpace 0) :
    x ∈ DoubleZeroGhostSpace g ↔
      x ∈ doubleZeroConeInclusion.range ∧ x.val ∈ GhostSpace g := by
  constructor
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    exact ⟨⟨(a, b), rfl⟩, (doubleZeroConeInclusion_degree_iff g a b).mpr hab⟩
  · rintro ⟨⟨⟨a, b⟩, rfl⟩, h⟩
    exact ⟨(a, b), (doubleZeroConeInclusion_degree_iff g a b).mp h, rfl⟩

theorem mem_doubleZeroGhostSpace_fixed_iff (g : ℤ) (x : EnergySpace 0) :
    x ∈ DoubleZeroGhostSpace g ↔ x.val ∈ DoubleZeroMomentum ∧ x.val ∈ GhostSpace g := by
  rw [mem_doubleZeroGhostSpace_iff, mem_doubleZeroConeInclusion_range_iff]

private theorem D_mem_doubleZeroGhostSpace (g : ℤ) {x : EnergySpace 0}
    (hx : x ∈ DoubleZeroGhostSpace g) : differential 0 x ∈ DoubleZeroGhostSpace (g + 1) := by
  obtain ⟨⟨⟨a, b⟩, rfl⟩, hg⟩ := (mem_doubleZeroGhostSpace_iff g x).mp hx
  apply (mem_doubleZeroGhostSpace_iff _ _).mpr
  exact ⟨⟨(doubleZeroM b, 0), (differential_doubleZeroConeInclusion a b).symm⟩, D_degree hg⟩

/-- Restriction of the actual level-matched BRST differential to this graded sector. -/
def doubleZeroDifferential (g : ℤ) :
    DoubleZeroGhostSpace g →ₗ[ℂ] DoubleZeroGhostSpace (g + 1) :=
  (differential 0).restrict fun _ => D_mem_doubleZeroGhostSpace g

abbrev DoubleZeroCycles (g : ℤ) := (doubleZeroDifferential g).ker

local instance (g : ℤ) : AddCommGroup (DoubleZeroCycles g) :=
  Submodule.addCommGroup (DoubleZeroCycles g)

private def doubleZeroBoundary (g : ℤ) :
    DoubleZeroGhostSpace (g - 1) →ₗ[ℂ] DoubleZeroCycles g where
  toFun x :=
    ⟨⟨differential 0 x.val, by
      simpa only [sub_add_cancel] using D_mem_doubleZeroGhostSpace (g - 1) x.property⟩,
      Subtype.ext (LinearMap.congr_fun (differential_square 0) x.val)⟩
  map_add' x y := Subtype.ext (Subtype.ext (map_add (differential 0) x.val y.val))
  map_smul' a x := Subtype.ext (Subtype.ext (map_smul (differential 0) a x.val))

abbrev DoubleZeroBoundaries (g : ℤ) := (doubleZeroBoundary g).range

/-- Cohomology of the native differential on the graded double-zero-momentum image. -/
abbrev DoubleZeroCohomology (g : ℤ) := DoubleZeroCycles g ⧸ DoubleZeroBoundaries g

private def doubleZeroGhostEquiv (g : ℤ) :
    (RelativeDegree g × RelativeDegree (g - 1)) ≃ₗ[ℂ] DoubleZeroGhostSpace g :=
  ((RelativeDegree g).prodEquiv (RelativeDegree (g - 1))).symm.trans
    (Submodule.equivMapOfInjective doubleZeroConeInclusion doubleZeroConeInclusion_injective _)

private instance (g : ℤ) : Module.Free ℂ (RelativeDegree g) :=
  Module.Free.of_basis (ClosedRelative.ZeroMomentum.totalGhostBasis g)

private instance (g : ℤ) : Module.Finite ℂ (RelativeDegree g) :=
  Module.Finite.of_basis (ClosedRelative.ZeroMomentum.totalGhostBasis g)

private instance (g : ℤ) : Module.Finite ℂ (DoubleZeroGhostSpace g) :=
  Module.Finite.of_surjective (doubleZeroGhostEquiv g).toLinearMap (doubleZeroGhostEquiv g).surjective

private theorem finrank_G (g : ℤ) :
    Module.finrank ℂ (RelativeDegree g) = ClosedRelative.ZeroMomentum.multiplicity g := by
  rw [← LinearEquiv.finrank_eq (ClosedRelative.ZeroMomentum.cohomologyGhostEquiv g)]
  exact ClosedRelative.ZeroMomentum.finrank_cohomology g

private theorem finrank_DoubleZeroGhostSpace (g : ℤ) :
    Module.finrank ℂ (DoubleZeroGhostSpace g) =
      ClosedRelative.ZeroMomentum.multiplicity g + ClosedRelative.ZeroMomentum.multiplicity (g - 1) := by
  rw [← LinearEquiv.finrank_eq (doubleZeroGhostEquiv g), Module.finrank_prod, finrank_G, finrank_G]

private theorem finrank_doubleZeroDifferential (g : ℤ) :
    Module.finrank ℂ (doubleZeroDifferential g).range =
      Module.finrank ℂ ((RelativeDegree (g - 1)).map doubleZeroM) := by
  let S := ClosedRelative.Shell 0 0
  let incl : S →ₗ[ℂ] EnergySpace 0 := doubleZeroConeInclusion.comp (LinearMap.inl ℂ S S)
  have hincl : Function.Injective incl := fun _ _ h =>
    congrArg Prod.fst (doubleZeroConeInclusion_injective h)
  have h : ((doubleZeroDifferential g).range).map (DoubleZeroGhostSpace (g + 1)).subtype =
      ((RelativeDegree (g - 1)).map doubleZeroM).map incl := by
    ext z
    constructor
    · rintro ⟨_, ⟨⟨_, ⟨⟨a, b⟩, hab, rfl⟩⟩, rfl⟩, rfl⟩
      exact ⟨_, ⟨b, hab.2, rfl⟩, (differential_doubleZeroConeInclusion a b).symm⟩
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      let x : DoubleZeroGhostSpace g := ⟨doubleZeroConeInclusion (0, b),
        ⟨(0, b), ⟨(RelativeDegree g).zero_mem, hb⟩, rfl⟩⟩
      exact ⟨doubleZeroDifferential g x, ⟨x, rfl⟩, differential_doubleZeroConeInclusion 0 b⟩
  rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (DoubleZeroGhostSpace (g + 1)).subtype
    Subtype.val_injective (doubleZeroDifferential g).range), h,
    ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective incl hincl _)]

private theorem finrank_doubleZeroBoundaries (g : ℤ) :
    Module.finrank ℂ (DoubleZeroBoundaries g) =
      Module.finrank ℂ ((RelativeDegree (g - 1 - 1)).map doubleZeroM) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, g = n + 1 := ⟨g - 1, by omega⟩
  have hn : n + 1 - 1 = n := by omega
  let sub := (DoubleZeroCycles (n + 1)).subtype
  have h : sub.comp (doubleZeroBoundary (n + 1)) =
      (doubleZeroDifferential n).comp
        (LinearEquiv.ofEq _ _ (congrArg DoubleZeroGhostSpace hn)).toLinearMap := by
    apply LinearMap.ext
    intro x
    rfl
  have hr : ((DoubleZeroBoundaries (n + 1)).map sub) = (doubleZeroDifferential n).range := by
    change ((doubleZeroBoundary (n + 1)).range).map sub = _
    rw [← LinearMap.range_comp, h, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective sub Subtype.val_injective _), hr,
    finrank_doubleZeroDifferential, hn]

private def connectingRank : ℤ → ℕ
  | 0 => 1
  | 1 => 4
  | 2 => 1
  | _ => 0

private theorem finrank_gradedM (g : ℤ) :
    Module.finrank ℂ ((RelativeDegree g).map doubleZeroM) = connectingRank g := by
  by_cases h : g < 0 ∨ 2 < g
  · rw [doubleZeroM_range_eq_bot h, finrank_bot]
    unfold connectingRank
    split <;> omega
  · have hh : g = 0 ∨ g = 1 ∨ g = 2 := by omega
    rcases hh with rfl | rfl | rfl
    · exact doubleZeroM_rank_zero
    · exact doubleZeroM_rank_one
    · exact doubleZeroM_rank_two

def doubleZeroMultiplicity : ℤ → ℕ
  | 0 => 1
  | 1 => 4
  | 2 => 5
  | 3 => 5
  | 4 => 4
  | 5 => 1
  | _ => 0

theorem finrank_doubleZeroCohomology (g : ℤ) :
    Module.finrank ℂ (DoubleZeroCohomology g) = doubleZeroMultiplicity g := by
  have h := LinearMap.finrank_range_add_finrank_ker (doubleZeroDifferential g)
  rw [finrank_doubleZeroDifferential, finrank_gradedM, finrank_DoubleZeroGhostSpace] at h
  have hquot : Module.finrank ℂ (DoubleZeroCohomology g) +
      Module.finrank ℂ (DoubleZeroBoundaries g) = Module.finrank ℂ (DoubleZeroCycles g) :=
    Submodule.finrank_quotient_add_finrank (DoubleZeroBoundaries g)
  have hb : Module.finrank ℂ (DoubleZeroBoundaries g) = connectingRank (g - 1 - 1) :=
    (finrank_doubleZeroBoundaries g).trans (finrank_gradedM (g - 1 - 1))
  have hq : Module.finrank ℂ (DoubleZeroCohomology g) + connectingRank (g - 1 - 1) =
      Module.finrank ℂ (DoubleZeroCycles g) :=
    (congrArg (fun n : ℕ => Module.finrank ℂ (DoubleZeroCohomology g) + n) hb).symm.trans hquot
  change connectingRank (g - 1) + Module.finrank ℂ (DoubleZeroCycles g) =
    ClosedRelative.ZeroMomentum.multiplicity g + ClosedRelative.ZeroMomentum.multiplicity (g - 1) at h
  suffices hd : connectingRank (g - 1) + connectingRank (g - 1 - 1) + doubleZeroMultiplicity g =
      ClosedRelative.ZeroMomentum.multiplicity g + ClosedRelative.ZeroMomentum.multiplicity (g - 1) by
    omega
  by_cases hg : g < 0 ∨ 5 < g
  · have a (n : ℤ) (hn : 0 ≤ n ∧ n ≤ 5) : g ≠ n := by omega
    have b (n : ℤ) (hn : 0 ≤ n ∧ n ≤ 4) : g - 1 ≠ n := by omega
    have c (n : ℤ) (hn : 0 ≤ n ∧ n ≤ 2) : g - 1 - 1 ≠ n := by omega
    simp [ClosedRelative.ZeroMomentum.multiplicity, connectingRank, doubleZeroMultiplicity,
      a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide),
      a 5 (by decide), b 0 (by decide), b 1 (by decide), b 2 (by decide), b 3 (by decide),
      b 4 (by decide), c 0 (by decide), c 1 (by decide), c 2 (by decide)]
  · have hh : g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 4 ∨ g = 5 := by omega
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.ClosedSemirelative
