/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldLightCone
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldLightCone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite decomposition and relative light-cone filtration of the actual orbifold BRST. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldBRST
import D5.S3.VertexAlgebra.Lattice.LatticeRelativeBRSTGround
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! The right slices take values in the actual orbifold. The filtration uses
the standalone plane's oscillator basis and the original ghost occupations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST

open ActualLeechOrbifoldMatter (Orbifold mode)
open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane matter hyperbolicMatter)
open LatticeGeneratingFieldLocality (Carrier Charge)
open LatticeSugawaraCurrents (gramComplex)
open LatticeLightConeCoordinates (NullFrame g chargeVector)
open LatticeQuartetContraction
open LatticeBRSTModeFiltration (degree c_shift h_shift sector_coefficient)
open LatticeBRSTFullOriginalRaising
  (HasCharge original_operators_preserve_charge full_remainder_fixed_charge_basis_raises)
open D5.S3.Quantum.Fermionic.CountableOccupationFock (Fock ket)
open D5.S3.Quantum.Fermionic.BcGhostFock (c)
open D5.S3.Quantum.Fermionic.BcGhostCharge (charge)
open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
  (ac diagonal_coefficient)

open private plane_inverse tensorMode
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldCriticalMatter
open private Q_commutes_energy from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldBRST
open private originalEnergy originalEnergy_d0 originalEnergy_R originalEnergy_invM chargeProject_h
  from D5.S3.VertexAlgebra.Lattice.LatticeRelativeBRSTGround

private abbrev Plane := Carrier hyperbolicPlane
private abbrev H := gramComplex hyperbolicPlane

abbrev AssocState := Orbifold ⊗[ℂ] State hyperbolicPlane

def reassoc : ComplexState ≃ₗ[ℂ] AssocState :=
  TensorProduct.assoc ℂ Orbifold Plane Fock

abbrev assocQ : Module.End ℂ AssocState := (reassoc.conjAlgEquiv ℂ) Q
abbrev assocE : Module.End ℂ AssocState := (reassoc.conjAlgEquiv ℂ) E
abbrev assocB0 : Module.End ℂ AssocState := (reassoc.conjAlgEquiv ℂ) b0

abbrev rightLift : Module.End ℂ (State hyperbolicPlane) →ₐ[ℂ] Module.End ℂ AssocState :=
  Module.End.lTensorAlgHom ℂ (State hyperbolicPlane) Orbifold

private theorem rightLift_tmul (A : Module.End ℂ (State hyperbolicPlane))
    (v : Orbifold) (y : State hyperbolicPlane) :
    rightLift A (v ⊗ₜ[ℂ] y) = v ⊗ₜ[ℂ] A y := rfl

/-- One orbifold Virasoro mode tensored with the matching ghost mode. -/
def orbifoldSummand (n : ℤ) : Module.End ℂ AssocState :=
  TensorProduct.map (mode n) (tp (1 : Module.End ℂ Plane) (c (-n)))

/-- The difference of the literal critical charge and the lifted
standalone plane charge, including cancellation of the common ghost cubic. -/
def orbifoldCoupling : Module.End ℂ AssocState :=
  assocQ - rightLift (LatticeBRST.totalCharge hyperbolicPlane H)

private theorem matter_mode_tmul (n : ℤ) (v : Orbifold) (u : Plane) :
    matter.mode n (v ⊗ₜ[ℂ] u) =
      mode n v ⊗ₜ[ℂ] u + v ⊗ₜ[ℂ] hyperbolicMatter.mode n u := by
  change tensorMode ActualLeechOrbifoldMatter.matter hyperbolicMatter n
    (v ⊗ₜ[ℂ] u) = _
  simp only [tensorMode, LinearMap.add_apply, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul]
  rfl

private theorem summand_reassoc (n : ℤ) (v : Orbifold) (u : Plane) (w : Fock) :
    reassoc (VirasoroBRST.summand matter n ((v ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] w)) =
      orbifoldSummand n (v ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] w)) +
        rightLift (LatticeMatterGhostCoupling.summand hyperbolicPlane H n)
          (v ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] w)) := by
  simp only [VirasoroBRST.summand, orbifoldSummand, LatticeMatterGhostCoupling.summand,
    rightLift_tmul, TensorProduct.map_tmul, tp_tmul, Module.End.one_apply,
    matter_mode_tmul, TensorProduct.add_tmul, map_add, reassoc, TensorProduct.assoc_tmul]
  rfl

set_option maxHeartbeats 800000 in
/-- A common finite capture computes the literal charge on each triple tensor.
The same cubic appears in the critical charge and the plane charge. -/
theorem assocQ_tmul_finite_capture (v : Orbifold) (u : Plane) (w : Fock) :
    ∃ s : Finset ℤ,
      Function.support (fun n => orbifoldSummand n (v ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] w))) ⊆
        (s : Set ℤ) ∧
      assocQ (v ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] w)) =
        rightLift (LatticeBRST.totalCharge hyperbolicPlane H)
          (v ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] w)) +
          ∑ n ∈ s, mode n v ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] c (-n) w) := by
  classical
  let y : State hyperbolicPlane := u ⊗ₜ[ℂ] w
  let z : ComplexState := (v ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] w
  let s₁ := (VirasoroBRST.summand_finite matter z).toFinset
  let s₂ := (LatticeMatterGhostCoupling.summand_finite hyperbolicPlane H y).toFinset
  let s := s₁ ∪ s₂
  have hs₁ : Function.support (fun n => VirasoroBRST.summand matter n z) ⊆
      (s : Set ℤ) := by
    intro n hn
    exact Finset.mem_union_left _ (by simpa [s₁] using hn)
  have hs₂ :
      Function.support (fun n => LatticeMatterGhostCoupling.summand hyperbolicPlane H n y)
        ⊆ (s : Set ℤ) := by
    intro n hn
    exact Finset.mem_union_right _ (by simpa [s₂] using hn)
  have hs := VirasoroBRST.finite_capture matter z s hs₁
  have hp := LatticeMatterGhostCoupling.finite_capture hyperbolicPlane H y s hs₂
  have hc : reassoc (VirasoroBRST.ghostCharge matter z) =
      v ⊗ₜ[ℂ] LatticeBRST.ghostCharge hyperbolicPlane y := rfl
  have hsum :
      reassoc (VirasoroBRST.T matter z) =
        (∑ n ∈ s, orbifoldSummand n (v ⊗ₜ[ℂ] y)) +
          v ⊗ₜ[ℂ] LatticeMatterGhostCoupling.T hyperbolicPlane H y := by
    rw [hs]
    change reassoc.toLinearMap.toAddMonoidHom (∑ n ∈ s, VirasoroBRST.summand matter n z) = _
    rw [map_sum reassoc.toLinearMap.toAddMonoidHom (fun n => VirasoroBRST.summand matter n z) s]
    change (∑ n ∈ s, reassoc (VirasoroBRST.summand matter n z)) = _
    simp only [z, summand_reassoc, rightLift_tmul]
    rw [Finset.sum_add_distrib, ← TensorProduct.tmul_sum, ← hp]
  refine ⟨s, ?_, ?_⟩
  · intro n hn
    by_contra hns
    have h₁ : VirasoroBRST.summand matter n z = 0 := by
      by_contra hz
      exact hns (hs₁ hz)
    have h₂ : LatticeMatterGhostCoupling.summand hyperbolicPlane H n y = 0 := by
      by_contra hz
      exact hns (hs₂ hz)
    have h := summand_reassoc n v u w
    change reassoc (VirasoroBRST.summand matter n z) =
      orbifoldSummand n (v ⊗ₜ[ℂ] y) +
        rightLift (LatticeMatterGhostCoupling.summand hyperbolicPlane H n) (v ⊗ₜ[ℂ] y) at h
    have hz : reassoc (0 : ComplexState) = 0 := reassoc.toLinearMap.toAddMonoidHom.map_zero
    rw [h₁, hz, rightLift_tmul, h₂, TensorProduct.tmul_zero, add_zero] at h
    exact hn h.symm
  · change reassoc (VirasoroBRST.T matter z + VirasoroBRST.ghostCharge matter z) = _
    rw [reassoc.map_add, hsum, hc, rightLift_tmul]
    simp only [LatticeBRST.totalCharge, LinearMap.add_apply, TensorProduct.tmul_add,
      orbifoldSummand, y, TensorProduct.map_tmul, tp_tmul, Module.End.one_apply]
    abel

private theorem orbifoldCoupling_finsum (x : AssocState) :
    Function.HasFiniteSupport (fun n => orbifoldSummand n x) ∧
      orbifoldCoupling x = ∑ᶠ n : ℤ, orbifoldSummand n x := by
  classical
  let Captured (y : AssocState) : Prop :=
    Function.HasFiniteSupport (fun n => orbifoldSummand n y) ∧
      orbifoldCoupling y = ∑ᶠ n : ℤ, orbifoldSummand n y
  have hadd (y z : AssocState) (hy : Captured y) (hz : Captured z) : Captured (y + z) := by
    refine ⟨?_, ?_⟩
    · apply (hy.1.union hz.1).subset
      intro n hn
      by_contra h
      have hy₀ : orbifoldSummand n y = 0 := by
        by_contra hne
        exact h (Or.inl hne)
      have hz₀ : orbifoldSummand n z = 0 := by
        by_contra hne
        exact h (Or.inr hne)
      exact hn (by simp only [map_add, hy₀, hz₀, add_zero])
    · simp only [map_add, hy.2, hz.2]
      exact (finsum_add_distrib hy.1 hz.1).symm
  change Captured x
  induction x using TensorProduct.inductionOn with
  | tmul v y =>
    induction y using TensorProduct.inductionOn with
    | tmul u w =>
      obtain ⟨s, hsupport, hc⟩ := assocQ_tmul_finite_capture v u w
      refine ⟨s.finite_toSet.subset hsupport, ?_⟩
      rw [finsum_eq_sum_of_support_subset _ hsupport,
        orbifoldCoupling, LinearMap.sub_apply, hc]
      simp only [orbifoldSummand, TensorProduct.map_tmul, tp_tmul, Module.End.one_apply]
      abel
    | add y z hy hz =>
      rw [TensorProduct.tmul_add]
      exact hadd _ _ hy hz
  | add y z hy hz => exact hadd y z hy hz

/-- On every algebraic state, the difference between the critical and plane
charges is captured by finitely many actual orbifold/ghost modes. -/
theorem orbifoldCoupling_finite_capture (x : AssocState) :
    ∃ s : Finset ℤ,
      Function.support (fun n => orbifoldSummand n x) ⊆ (s : Set ℤ) ∧
      orbifoldCoupling x = ∑ n ∈ s, orbifoldSummand n x := by
  classical
  obtain ⟨hfinite, hx⟩ := orbifoldCoupling_finsum x
  have hsupport : Function.support (fun n => orbifoldSummand n x) ⊆
      (hfinite.toFinset : Set ℤ) := by
    intro n hn
    simpa using hn
  exact ⟨hfinite.toFinset, hsupport, hx.trans (finsum_eq_sum_of_support_subset _ hsupport)⟩

/-- On every reassociated state, the literal critical Q is the lifted full
plane charge plus a finite sum of actual orbifold/ghost modes. -/
theorem assocQ_finite_capture (x : AssocState) :
    ∃ s : Finset ℤ,
      Function.support (fun n => orbifoldSummand n x) ⊆ (s : Set ℤ) ∧
      assocQ x = rightLift (LatticeBRST.totalCharge hyperbolicPlane H) x +
        ∑ n ∈ s, orbifoldSummand n x := by
  obtain ⟨s, hsupport, hc⟩ := orbifoldCoupling_finite_capture x
  refine ⟨s, hsupport, ?_⟩
  rw [← hc, orbifoldCoupling, LinearMap.sub_apply]
  abel

/-- The differential remainder on the reassociated state space. -/
def remainder (F : NullFrame hyperbolicPlane) (p : Charge hyperbolicPlane) :
    Module.End ℂ AssocState :=
  assocQ - rightLift (d0 F p)

theorem remainder_decomposition (F : NullFrame hyperbolicPlane) (p : Charge hyperbolicPlane) :
    remainder F p =
      rightLift (LatticeBRST.totalCharge hyperbolicPlane H - d0 F p) + orbifoldCoupling := by
  rw [remainder, orbifoldCoupling, map_sub]
  abel

section Slices

variable (F : NullFrame hyperbolicPlane) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)

def rightSlices : AssocState ≃ₗ[ℂ] (StateIndex hyperbolicPlane t →₀ Orbifold) := by
  classical
  exact TensorProduct.equivFinsuppOfBasisRight (actualBasis F B)

def rightSlice (i : StateIndex hyperbolicPlane t) : AssocState →ₗ[ℂ] Orbifold :=
  (Finsupp.lapply i).comp (rightSlices F B).toLinearMap

private theorem rightSlice_tmul (v : Orbifold) (y : State hyperbolicPlane)
    (i : StateIndex hyperbolicPlane t) :
    rightSlice F B i (v ⊗ₜ[ℂ] y) = (actualBasis F B).repr y i • v := by
  classical
  exact TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply (actualBasis F B) v y i

private theorem rightSlices_expand (x : AssocState) :
    x = ∑ i ∈ (rightSlices F B x).support,
      rightSlice F B i x ⊗ₜ[ℂ] actualBasis F B i := by
  classical
  simpa only [rightSlice, LinearMap.comp_apply, Finsupp.lapply_apply, LinearEquiv.coe_coe,
    rightSlices, TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum] using
    ((rightSlices F B).symm_apply_apply x).symm

private def supportedOn (keep : StateIndex hyperbolicPlane t → Prop) :
    Submodule ℂ AssocState where
  carrier := {x | ∀ i, ¬ keep i → rightSlice F B i x = 0}
  zero_mem' := by
    intro i hi
    exact map_zero _
  add_mem' := by
    intro x y hx hy i hi
    change rightSlice F B i (x + y) = 0
    rw [map_add, hx i hi, hy i hi, add_zero]
  smul_mem' := by
    intro a x hx i hi
    change rightSlice F B i (a • x) = 0
    rw [map_smul, hx i hi, smul_zero]

/-- Fixed right momentum and a lower bound for exponent degree plus ghost charge minus one. -/
def momentumFiltration (p : Charge hyperbolicPlane) (a : ℤ) : Submodule ℂ AssocState :=
  supportedOn F B (fun i => i.1.1 = p ∧ a ≤ degree i)

theorem mem_momentumFiltration_iff (p : Charge hyperbolicPlane) (a : ℤ) (x : AssocState) :
    x ∈ momentumFiltration F B p a ↔
      ∀ i, rightSlice F B i x ≠ 0 → i.1.1 = p ∧ a ≤ degree i := by
  classical
  change (∀ i, ¬ (i.1.1 = p ∧ a ≤ degree i) → rightSlice F B i x = 0) ↔ _
  constructor
  · intro hx i hi
    exact by_contra (fun hn => hi (hx i hn))
  · intro hx i hi
    exact by_contra (fun hn => hi (hx i hn))

private theorem map_supportedOn
    (A : Module.End ℂ AssocState) {keep target : StateIndex hyperbolicPlane t → Prop}
    (hA : ∀ i, keep i → ∀ v : Orbifold,
      A (v ⊗ₜ[ℂ] actualBasis F B i) ∈ supportedOn F B target)
    {x : AssocState} (hx : x ∈ supportedOn F B keep) :
    A x ∈ supportedOn F B target := by
  classical
  have hsum := congrArg (fun z : AssocState => A z) (rightSlices_expand F B x)
  change A x = A (∑ i ∈ (rightSlices F B x).support,
    rightSlice F B i x ⊗ₜ[ℂ] actualBasis F B i) at hsum
  rw [hsum, map_sum]
  apply Submodule.sum_mem
  intro i hi
  apply hA i
  exact Classical.byContradiction (fun hn => (Finsupp.mem_support_iff.mp hi) (hx i hn))

private theorem rightLift_supportedOn (A : Module.End ℂ (State hyperbolicPlane))
    {keep target : StateIndex hyperbolicPlane t → Prop}
    (hA : ∀ i j, keep i → (actualBasis F B).repr (A (actualBasis F B i)) j ≠ 0 → target j)
    {x : AssocState} (hx : x ∈ supportedOn F B keep) :
    rightLift A x ∈ supportedOn F B target := by
  classical
  apply map_supportedOn F B (rightLift A) (keep := keep) (target := target) _ hx
  intro i hi v j hj
  rw [rightLift_tmul, rightSlice_tmul]
  have hz : (actualBasis F B).repr (A (actualBasis F B i)) j = 0 :=
    by_contra (fun hn => hj (hA i j hi hn))
  rw [hz, zero_smul]

private theorem basis_hasCharge (i : StateIndex hyperbolicPlane t) :
    HasCharge F B i.1.1 (actualBasis F B i) := by
  classical
  intro j hj
  by_cases hij : i = j
  · exact congrArg (fun k : StateIndex hyperbolicPlane t => k.1.1) hij.symm
  · exact False.elim (hj (by rw [Module.Basis.repr_self_apply, ite_eq_right hij]))

private theorem orbifoldSummand_basis_slices (n : ℤ) (v : Orbifold)
    (i j : StateIndex hyperbolicPlane t)
    (hj : rightSlice F B j (orbifoldSummand n (v ⊗ₜ[ℂ] actualBasis F B i)) ≠ 0) :
    j.1.1 = i.1.1 ∧ j.1.2 = i.1.2 ∧ charge j.2 = charge i.2 + 1 := by
  classical
  simp only [orbifoldSummand, TensorProduct.map_tmul, rightSlice_tmul] at hj
  have hc : (actualBasis F B).repr
      (tp (1 : Module.End ℂ Plane) (c (-n)) (actualBasis F B i)) j ≠ 0 := by
    intro hz
    exact hj (by rw [hz, zero_smul])
  rcases i with ⟨⟨p, m⟩, S⟩
  rw [actualBasis_apply, ghost_sector, sector_coefficient] at hc
  have hp : p = j.1.1 := by
    by_contra hn
    exact hc (ite_eq_right hn)
  rw [ite_eq_left hp] at hc
  have hm : m = j.1.2 := by
    by_contra hn
    exact hc (by simp [MvPolynomial.coeff_monomial, hn])
  have hg : (c (-n) (ket S)) j.2 ≠ 0 := by
    intro hz
    exact hc (by simp [hz])
  exact ⟨hp.symm, hm.symm, c_shift (-n) S j.2 hg⟩

/-- Each nonzero right slice of the orbifold coupling at a basis input retains
the plane momentum and exponent and increases the ghost charge by one. -/
theorem orbifoldCoupling_basis_slices (v : Orbifold) (i j : StateIndex hyperbolicPlane t)
    (hj : rightSlice F B j (orbifoldCoupling (v ⊗ₜ[ℂ] actualBasis F B i)) ≠ 0) :
    j.1.1 = i.1.1 ∧ j.1.2 = i.1.2 ∧ charge j.2 = charge i.2 + 1 := by
  classical
  obtain ⟨s, _, hs⟩ := orbifoldCoupling_finite_capture (v ⊗ₜ[ℂ] actualBasis F B i)
  rw [hs, map_sum] at hj
  by_contra hstep
  apply hj
  apply Finset.sum_eq_zero
  intro n hn
  by_contra hc
  exact hstep (orbifoldSummand_basis_slices F B n v i j hc)

private theorem orbifoldCoupling_supportedOn
    {keep target : StateIndex hyperbolicPlane t → Prop}
    (hstep : ∀ i j, keep i → j.1.1 = i.1.1 → degree j = degree i + 1 → target j)
    {x : AssocState} (hx : x ∈ supportedOn F B keep) :
    orbifoldCoupling x ∈ supportedOn F B target := by
  classical
  apply map_supportedOn F B orbifoldCoupling (keep := keep) (target := target) _ hx
  intro i hi v j hj
  by_contra hc
  obtain ⟨hp, hm, hg⟩ := orbifoldCoupling_basis_slices F B v i j hc
  have hd : degree j = degree i + 1 := by
    simp only [degree, hm, hg]
    omega
  exact hj (hstep i j hi hp hd)

/-- The actual reassociated Q minus the lifted d0 raises the lower bound
at fixed momentum, on all algebraic tensors. -/
theorem remainder_raises (p : Charge hyperbolicPlane) (a : ℤ) {x : AssocState}
    (hx : x ∈ momentumFiltration F B p a) :
    remainder F p x ∈ momentumFiltration F B p (a + 1) := by
  classical
  have hplane : rightLift (LatticeBRST.totalCharge hyperbolicPlane H - d0 F p) x ∈
      momentumFiltration F B p (a + 1) := by
    change _ ∈ supportedOn F B (fun j => j.1.1 = p ∧ a + 1 ≤ degree j)
    refine rightLift_supportedOn F B _ (keep := fun i => i.1.1 = p ∧ a ≤ degree i) ?_ hx
    intro i j hi hj
    have hq : HasCharge F B p (actualBasis F B i) := hi.1 ▸ basis_hasCharge F B i
    have hp := original_operators_preserve_charge F B H p (actualBasis F B i) hq
    refine ⟨?_, (add_le_add_left hi.2 1).trans
      (full_remainder_fixed_charge_basis_raises F B H plane_inverse plane_inverse p i j hi.1 hj)⟩
    by_contra hn
    have hQ : (actualBasis F B).repr
        (LatticeBRST.totalCharge hyperbolicPlane H (actualBasis F B i)) j = 0 :=
      by_contra (fun h => hn (hp.1 j h))
    have hd : (actualBasis F B).repr (d0 F p (actualBasis F B i)) j = 0 :=
      by_contra (fun h => hn (hp.2.1 j h))
    apply hj
    let coeff : State hyperbolicPlane →ₗ[ℂ] ℂ :=
      (Finsupp.lapply j).comp (actualBasis F B).repr.toLinearMap
    change coeff ((LatticeBRST.totalCharge hyperbolicPlane H - d0 F p) (actualBasis F B i)) = 0
    change coeff (LatticeBRST.totalCharge hyperbolicPlane H (actualBasis F B i)) = 0 at hQ
    change coeff (d0 F p (actualBasis F B i)) = 0 at hd
    rw [LinearMap.sub_apply, coeff.map_sub, hQ, hd, sub_self]
  have horb : orbifoldCoupling x ∈ momentumFiltration F B p (a + 1) := by
    change _ ∈ supportedOn F B (fun j => j.1.1 = p ∧ a + 1 ≤ degree j)
    refine orbifoldCoupling_supportedOn F B (keep := fun i => i.1.1 = p ∧ a ≤ degree i) ?_ hx
    intro i j hi hp hd
    refine ⟨hp.trans hi.1, ?_⟩
    rw [hd]
    exact add_le_add_left hi.2 1
  rw [remainder_decomposition, LinearMap.add_apply]
  exact (momentumFiltration F B p (a + 1)).add_mem hplane horb

/-- Composing the actual remainder with the lifted inverse-count homotopy
still raises the fixed-momentum filtration by one. -/
theorem h_remainder_raises (p : Charge hyperbolicPlane) (a : ℤ) {x : AssocState}
    (hx : x ∈ momentumFiltration F B p a) :
    rightLift (h F B p) (remainder F p x) ∈ momentumFiltration F B p (a + 1) := by
  change _ ∈ supportedOn F B (fun i => i.1.1 = p ∧ a + 1 ≤ degree i)
  refine rightLift_supportedOn F B (h F B p)
    (keep := fun i => i.1.1 = p ∧ a + 1 ≤ degree i) ?_ (remainder_raises F B p a hx)
  intro i j hi hj
  have hq : HasCharge F B p (actualBasis F B i) := hi.1 ▸ basis_hasCharge F B i
  have hs := h_shift F B p i j hj
  exact ⟨(original_operators_preserve_charge F B H p _ hq).2.2 j hj,
    (by simpa only [hs, add_zero] using hi.2)⟩

private theorem rightSlice_chargeProject (p : Charge hyperbolicPlane)
    (j : StateIndex hyperbolicPlane t) (x : AssocState) :
    rightSlice F B j (rightLift (chargeProject p) x) =
      if j.1.1 = p then rightSlice F B j x else 0 := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul v y =>
    rw [rightLift_tmul, rightSlice_tmul, rightSlice_tmul, chargeProject_diagonal F B p,
      diagonal_coefficient]
    by_cases hj : j.1.1 = p <;> simp [hj]
  | add x y hx hy =>
    rw [map_add (rightLift (chargeProject p)), map_add (rightSlice F B j), hx, hy]
    by_cases hj : j.1.1 = p <;> simp [hj]

private theorem fixedMomentum_iff_slices (p : Charge hyperbolicPlane) (x : AssocState) :
    rightLift (chargeProject p) x = x ↔ x ∈ supportedOn F B (fun i => i.1.1 = p) := by
  classical
  constructor
  · intro hx j hj
    have h := congrArg (fun z => rightSlice F B j z) hx
    rw [rightSlice_chargeProject F B, ite_eq_right hj] at h
    exact h.symm
  · intro hx
    apply (rightSlices F B).injective
    apply Finsupp.ext
    intro j
    change rightSlice F B j (rightLift (chargeProject p) x) = rightSlice F B j x
    rw [rightSlice_chargeProject F B]
    by_cases hj : j.1.1 = p
    · rw [ite_eq_left hj]
    · rw [ite_eq_right hj, hx j hj]

include F B in
private theorem assocQ_preserves_momentum (p : Charge hyperbolicPlane) {x : AssocState}
    (hx : rightLift (chargeProject p) x = x) :
    rightLift (chargeProject p) (assocQ x) = assocQ x := by
  let fixed := supportedOn F B (fun i => i.1.1 = p)
  have hx' : x ∈ fixed := (fixedMomentum_iff_slices F B p x).mp hx
  have hplane : rightLift (LatticeBRST.totalCharge hyperbolicPlane H) x ∈ fixed := by
    refine rightLift_supportedOn F B _ (keep := fun i => i.1.1 = p)
      (target := fun i => i.1.1 = p) ?_ hx'
    intro i j hi hj
    have hq : HasCharge F B p (actualBasis F B i) := hi ▸ basis_hasCharge F B i
    exact (original_operators_preserve_charge F B H p _ hq).1 j hj
  have horb : orbifoldCoupling x ∈ fixed := by
    refine orbifoldCoupling_supportedOn F B (keep := fun i => i.1.1 = p)
      (target := fun i => i.1.1 = p) ?_ hx'
    intro i j hi hp _
    exact hp.trans hi
  apply (fixedMomentum_iff_slices F B p (assocQ x)).mpr
  have hsplit : assocQ x =
      rightLift (LatticeBRST.totalCharge hyperbolicPlane H) x + orbifoldCoupling x := by
    rw [orbifoldCoupling, LinearMap.sub_apply]
    abel
  rw [hsplit]
  exact fixed.add_mem hplane horb

end Slices

private theorem assocB0_eq : assocB0 = rightLift (ghostB0 (D := hyperbolicPlane)) := by
  apply TensorProduct.ext'
  intro v y
  induction y using TensorProduct.inductionOn with
  | tmul u w => rfl
  | add y z hy hz =>
    rw [TensorProduct.tmul_add, map_add assocB0, map_add (rightLift _), hy, hz]

private theorem assocE_decomposition :
    assocE = (mode 0).rTensor (State hyperbolicPlane) +
      rightLift (originalEnergy hyperbolicPlane H) := by
  apply TensorProduct.ext'
  intro v y
  induction y using TensorProduct.inductionOn with
  | tmul u w =>
    change reassoc (E ((v ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] w)) = _
    simp only [E, VirasoroBRST.Ltotal, VirasoroBRST.matterMode,
      VirasoroBRST.ghostVirasoro, originalEnergy, LatticeMatterGhostCoupling.matterMode,
      LatticeMatterGhostCoupling.ghostVirasoro, LinearMap.add_apply, rightLift_tmul,
      LinearMap.rTensor_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
      matter_mode_tmul, TensorProduct.add_tmul, map_add,
      reassoc, TensorProduct.assoc_tmul]
    rw [add_assoc]
    rfl
  | add y z hy hz =>
    rw [TensorProduct.tmul_add, map_add assocE, map_add (_ + rightLift _), hy, hz]

/-- The literal reassociated relative shell at fixed plane momentum. -/
def relativeShell (p : Charge hyperbolicPlane) : Submodule ℂ AssocState :=
  (rightLift (chargeProject p) - 1).ker ⊓ (assocB0.ker ⊓ assocE.ker)

theorem mem_relativeShell_iff (p : Charge hyperbolicPlane) (x : AssocState) :
    x ∈ relativeShell p ↔
      rightLift (chargeProject p) x = x ∧ assocB0 x = 0 ∧ assocE x = 0 := by
  simp only [relativeShell, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
    Module.End.one_apply, sub_eq_zero]

private theorem rightLift_mem_relativeShell (p : Charge hyperbolicPlane)
    (A : Module.End ℂ (State hyperbolicPlane))
    (hP : chargeProject p * A = A * chargeProject p)
    (hB : ac (ghostB0 (D := hyperbolicPlane)) A = 0)
    (hE : originalEnergy hyperbolicPlane H * A = A * originalEnergy hyperbolicPlane H)
    {x : AssocState} (hx : x ∈ relativeShell p) :
    rightLift A x ∈ relativeShell p := by
  obtain ⟨hp, hb, he⟩ := (mem_relativeShell_iff p x).mp hx
  apply (mem_relativeShell_iff p _).mpr
  have hP' : rightLift (chargeProject p) * rightLift A =
      rightLift A * rightLift (chargeProject p) := by
    simpa only [map_mul] using congrArg rightLift hP
  have hB' : assocB0 * rightLift A + rightLift A * assocB0 = 0 := by
    rw [assocB0_eq]
    simpa only [ac, map_add, map_mul, map_zero] using congrArg rightLift hB
  have hCross : (mode 0).rTensor (State hyperbolicPlane) * rightLift A =
      rightLift A * (mode 0).rTensor (State hyperbolicPlane) := by
    change ((mode 0).rTensor (State hyperbolicPlane)).comp (A.lTensor Orbifold) =
      (A.lTensor Orbifold).comp ((mode 0).rTensor (State hyperbolicPlane))
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have hRight : rightLift (originalEnergy hyperbolicPlane H) * rightLift A =
      rightLift A * rightLift (originalEnergy hyperbolicPlane H) := by
    simpa only [map_mul] using congrArg rightLift hE
  have hE' : assocE * rightLift A = rightLift A * assocE := by
    rw [assocE_decomposition, add_mul, mul_add, hCross, hRight]
  refine ⟨?_, ?_, ?_⟩
  · have h := LinearMap.congr_fun hP' x
    simpa only [Module.End.mul_apply, hp] using h
  · have h := LinearMap.congr_fun hB' x
    simpa only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply,
      hb, map_zero, add_zero] using h
  · have h := LinearMap.congr_fun hE' x
    simpa only [Module.End.mul_apply, he, map_zero] using h

section Relative

variable (F : NullFrame hyperbolicPlane) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)

include F B in
theorem assocQ_mem_relativeShell (p : Charge hyperbolicPlane)
    {x : AssocState} (hx : x ∈ relativeShell p) : assocQ x ∈ relativeShell p := by
  obtain ⟨hp, hb, he⟩ := (mem_relativeShell_iff p x).mp hx
  apply (mem_relativeShell_iff p _).mpr
  have hWard : assocQ * assocB0 + assocB0 * assocQ = assocE := by
    simpa only [map_add, map_mul] using
      congrArg (reassoc.conjAlgEquiv ℂ) (VirasoroBRST.Q_ward_b matter 0)
  have hComm : assocQ * assocE = assocE * assocQ := by
    simpa only [map_mul] using congrArg (reassoc.conjAlgEquiv ℂ) Q_commutes_energy
  refine ⟨assocQ_preserves_momentum F B p hp, ?_, ?_⟩
  · have h := LinearMap.congr_fun hWard x
    simpa only [Module.End.mul_apply, LinearMap.add_apply, hb, he, map_zero, zero_add] using h
  · have h := LinearMap.congr_fun hComm.symm x
    simpa only [Module.End.mul_apply, he, map_zero] using h

/-- The actual Q on the literal relative shell. -/
def relativeQ (p : Charge hyperbolicPlane) : Module.End ℂ (relativeShell p) :=
  assocQ.restrict (fun _ hx => assocQ_mem_relativeShell F B p hx)

/-- The quartet differential on the same shell. -/
def relativeD0 (_B : Module.Basis (Fin t) ℂ F.K) (p : Charge hyperbolicPlane) :
    Module.End ℂ (relativeShell p) :=
  (rightLift (d0 F p)).restrict (fun _ hx =>
    rightLift_mem_relativeShell p (d0 F p) (chargeProject_d0 F p p) (b0_d0 F p)
      (originalEnergy_d0 F H plane_inverse plane_inverse p) hx)

/-- The inverse-count quartet homotopy on the same shell. -/
def relativeH (p : Charge hyperbolicPlane) : Module.End ℂ (relativeShell p) :=
  (rightLift (h F B p)).restrict (by
    intro x hx
    refine rightLift_mem_relativeShell p _ (chargeProject_h F B p p) (b0_h F B p) ?_ hx
    change originalEnergy hyperbolicPlane H * (R F p * invM F B) =
      (R F p * invM F B) * originalEnergy hyperbolicPlane H
    rw [← mul_assoc, originalEnergy_R F H plane_inverse plane_inverse p, mul_assoc,
      ← originalEnergy_invM F B H plane_inverse plane_inverse, ← mul_assoc])

theorem relativeQ_squared (p : Charge hyperbolicPlane) : relativeQ F B p ^ 2 = 0 := by
  have hs : assocQ ^ 2 = 0 := by
    simpa only [map_pow, map_zero] using congrArg (reassoc.conjAlgEquiv ℂ) Q_squared
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change assocQ (assocQ x.val) = 0
  simpa only [pow_two, Module.End.mul_apply, LinearMap.zero_apply] using
    LinearMap.congr_fun hs x.val

/-- The difference between the actual relative charge and the quartet differential. -/
def relativeDelta (p : Charge hyperbolicPlane) : Module.End ℂ (relativeShell p) :=
  (remainder F p).restrict (fun x hx => by
    change assocQ x - rightLift (d0 F p) x ∈ relativeShell p
    exact (relativeShell p).sub_mem (assocQ_mem_relativeShell F B p hx)
      (relativeD0 F B p ⟨x, hx⟩).property)

/-- The induced remainder and its composition with the homotopy raise the
same filtration on the actual relative shell. -/
theorem relative_remainder_raises (p : Charge hyperbolicPlane) (a : ℤ) (x : relativeShell p)
    (hx : x.val ∈ momentumFiltration F B p a) :
    (relativeDelta F B p x).val ∈ momentumFiltration F B p (a + 1) ∧
      (relativeH F B p (relativeDelta F B p x)).val ∈
        momentumFiltration F B p (a + 1) := by
  change remainder F p x.val ∈ momentumFiltration F B p (a + 1) ∧
    rightLift (h F B p) (remainder F p x.val) ∈ momentumFiltration F B p (a + 1)
  exact ⟨remainder_raises F B p a hx, h_remainder_raises F B p a hx⟩

end Relative

private theorem plane_pairing (u v : Fin 2 → ℂ) :
    g hyperbolicPlane u v = u 0 * v 1 + u 1 * v 0 := by
  change (∑ i : Fin 2, ∑ j : Fin 2, u i * (OrderedHyperbolicExtension.U i j : ℂ) * v j) = _
  simp [Fin.sum_univ_two]

private theorem plane_pairing_zero (v : Fin 2 → ℂ) :
    g hyperbolicPlane (Pi.single (0 : Fin 2) 1) v = v 1 := by
  rw [plane_pairing]
  simp

private theorem plane_pairing_one (v : Fin 2 → ℂ) :
    g hyperbolicPlane (Pi.single (1 : Fin 2) 1) v = v 0 := by
  rw [plane_pairing]
  simp

/-- The two coordinate null vectors in the standalone hyperbolic plane. -/
def planeFrame : NullFrame hyperbolicPlane where
  ePlus := Pi.single (0 : Fin 2) 1
  eMinus := Pi.single (1 : Fin 2) 1
  plus_null := by simp [plane_pairing_zero]
  minus_null := by simp [plane_pairing_one]
  plus_minus := by simp [plane_pairing_zero]

/-- The second polarization exchanges the two coordinate null vectors. -/
def swappedPlaneFrame : NullFrame hyperbolicPlane where
  ePlus := planeFrame.eMinus
  eMinus := planeFrame.ePlus
  plus_null := planeFrame.minus_null
  minus_null := planeFrame.plus_null
  plus_minus := planeFrame.minus_plus

@[simp] theorem planeFrame_pPlus (p : Charge hyperbolicPlane) :
    planeFrame.pPlus p = (p (1 : Fin 2) : ℂ) :=
  plane_pairing_zero (chargeVector p)

@[simp] theorem swappedPlaneFrame_pPlus (p : Charge hyperbolicPlane) :
    swappedPlaneFrame.pPlus p = (p (0 : Fin 2) : ℂ) :=
  plane_pairing_one (chargeVector p)

private def planeEmptyBasis (F : NullFrame hyperbolicPlane)
    (hK : ∀ k : F.K, (show Fin 2 → ℂ from k.val) 0 = 0 ∧ (show Fin 2 → ℂ from k.val) 1 = 0) :
    Module.Basis (Fin 0) ℂ F.K := by
  have hz (k : F.K) : k = 0 := by
    apply Subtype.ext
    funext i
    change (show Fin 2 → ℂ from k.val) i = 0
    fin_cases i
    · exact (hK k).1
    · exact (hK k).2
  letI : Subsingleton F.K := ⟨fun x y => (hz x).trans (hz y).symm⟩
  exact Module.Basis.empty F.K

def planeBasis : Module.Basis (Fin 0) ℂ planeFrame.K :=
  planeEmptyBasis planeFrame (fun k =>
    ⟨(plane_pairing_one k.val).symm.trans (planeFrame.minus_K k),
      (plane_pairing_zero k.val).symm.trans (planeFrame.plus_K k)⟩)

def swappedPlaneBasis : Module.Basis (Fin 0) ℂ swappedPlaneFrame.K :=
  planeEmptyBasis swappedPlaneFrame (fun k =>
    ⟨(plane_pairing_one k.val).symm.trans (swappedPlaneFrame.plus_K k),
      (plane_pairing_zero k.val).symm.trans (swappedPlaneFrame.minus_K k)⟩)

/-- Every nonzero plane momentum has nonzero plus component in one of the two frames. -/
theorem planeFrame_covers_nonzero (p : Charge hyperbolicPlane) (hp : p ≠ 0) :
    planeFrame.pPlus p ≠ 0 ∨ swappedPlaneFrame.pPlus p ≠ 0 := by
  by_cases h₁ : p (1 : Fin 2) = 0
  · right
    rw [swappedPlaneFrame_pPlus]
    have h₀ : p (0 : Fin 2) ≠ 0 := by
      intro h₀
      apply hp
      funext i
      change p i = 0
      fin_cases i
      · exact h₀
      · exact h₁
    exact_mod_cast h₀
  · left
    rw [planeFrame_pPlus]
    exact_mod_cast h₁

theorem plane_chargeEnergy (p : Charge hyperbolicPlane) :
    LatticePositiveEnergy.chargeEnergy hyperbolicPlane p = p (0 : Fin 2) * p (1 : Fin 2) := by
  have h := LatticePositiveEnergy.two_chargeEnergy hyperbolicPlane p
  change 2 * LatticePositiveEnergy.chargeEnergy hyperbolicPlane p =
    ∑ i : Fin 2, ∑ j : Fin 2, p i * OrderedHyperbolicExtension.U i j * p j at h
  simp only [Fin.sum_univ_two, OrderedHyperbolicExtension.U_zero_zero,
    OrderedHyperbolicExtension.U_zero_one, OrderedHyperbolicExtension.U_one_zero,
    OrderedHyperbolicExtension.U_one_one, mul_zero, zero_mul, mul_one, add_zero, zero_add] at h
  rw [mul_comm (p (1 : Fin 2)) (p (0 : Fin 2))] at h
  omega

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST
