/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTAbsoluteQuartetGround
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTAbsoluteQuartetGround
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Unique actual absolute quartet ground coordinates and compressed energy. -/

import D5.S3.VertexAlgebra.Lattice.LatticeRelativeBRSTGround
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration

/-!
The original integral-charge matter/occupation-ghost tensor carrier is retained.
The absolute zero-count sector has TWO independent transverse polynomials.
In particular, the second coordinate uses the actual ghostC D 0, whose action
on ket {1} is minus ket {1,3}. There is no b0 or mass-shell restriction here.

Source attribution: the transverse support/comapDomain argument below adapts
the private transverse_monomial_preimage argument in LatticeQuartetContraction.
The actual energy proof adapts the private energyOperator and
totalL0_groundMap proofs in LatticeRelativeBRSTGround, using their public
frequency_grading and sugawaraMode_weighted_homogeneous suppliers. The c0
commutator proof adapts the private totalL0_c_zero argument in
LatticeBRSTRelativeZeroMode, independently from the public ghost Ward law.
No private declaration is opened, and no original-Q compression is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000

noncomputable section
open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteQuartetGround

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeSugawaraConformal LatticePositiveEnergy
open LatticeLightConeCoordinates LatticeQuartetContraction
open LatticeMatterGhostCoupling (ghostB ghostC matterMode ghostVirasoro)
open LatticeRelativeMassShell (totalL0)
open LatticeRelativeBRSTCohomology.Ground (weight energyTarget groundMap_injective)
open LatticeBRSTRelativeZeroMode (ghost_zero_mixed ghost_c_zero_square)
open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
open D5.S3.Quantum.Fermionic
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open MvPolynomial

abbrev Poly (t : ℕ) := MvPolynomial (Fin t × ℕ) ℂ
abbrev Exponent (t : ℕ) := (Fin t × ℕ) →₀ ℕ

variable {D : LatticeData} (F : NullFrame D) {t : ℕ}
variable (B : Module.Basis (Fin t) ℂ F.K)

/-- The literal two-polynomial map, using the original ghost zero mode. -/
def G (p : Charge D) : (Poly t × Poly t) →ₗ[ℂ] State D where
  toFun fg := groundMap F B p fg.1 + ghostC D 0 (groundMap F B p fg.2)
  map_add' x y := by
    change groundMap F B p (x.1 + y.1) +
      ghostC D 0 (groundMap F B p (x.2 + y.2)) = _
    simp only [map_add]
    abel
  map_smul' z x := by
    change groundMap F B p (z • x.1) +
      ghostC D 0 (groundMap F B p (z • x.2)) = _
    simp [map_smul, smul_add]

/-- The actual fixed-charge zero-count submodule, with no energy condition. -/
def absoluteGround (p : Charge D) : Submodule ℂ (State D) where
  carrier := {v | P0 F B v = v ∧ chargeProject p v = v}
  zero_mem' := by simp
  add_mem' := by
    rintro v w ⟨hv0, hvp⟩ ⟨hw0, hwp⟩
    constructor
    · simp only [map_add, hv0, hw0]
    · simp only [map_add, hvp, hwp]
  smul_mem' := by
    rintro z v ⟨hv0, hvp⟩
    constructor
    · rw [map_smul, hv0]
    · rw [map_smul, hvp]

/- The sign is computed from the actual occupation convention, not chosen
   when defining the second coordinate. It is used in BOTH image inclusions. -/
private theorem c0_basis (p : Charge D) (m : Exponents t) :
    ghostC D 0 (actualBasis F B (⟨p,m⟩,{1})) =
      -actualBasis F B (⟨p,m⟩,{1,3}) := by
  have hc : c 0 (ket {1}) = -ket {1,3} := by
    have hs : ({3, 1} : Finset ℕ) = {1, 3} := by
      ext j
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    norm_num [c, phase, lowerCount, Finset.filter_singleton, hs]
  simp only [actualBasis_apply]
  change tp (1 : Module.End ℂ (Carrier D)) (c 0)
    (sector F B p (monomial m 1) (ket {1})) = _
  rw [ghost_sector, hc]
  simpa only [neg_one_smul] using
    sector_smul_right F B p (-1 : ℂ) (monomial m 1) (ket {1,3})

/- Construct the exponent preimage; no spanning or independence is assumed. -/
private theorem transverse_exponent_lift (m : Exponents t) (hm : NoLongitudinal m) :
    ∃ nu : Exponent t, nu.mapDomain transverseVariable = m := by
  have hs : (m.support : Set (Variables t)) ⊆ Set.range transverseVariable := by
    intro x hx
    rcases x with ⟨l,r⟩
    rcases l with u | (u | j)
    · cases u
      exact False.elim ((Finsupp.mem_support_iff.mp hx) (hm r).1)
    · cases u
      exact False.elim ((Finsupp.mem_support_iff.mp hx) (hm r).2)
    · exact ⟨(j,r),rfl⟩
  refine ⟨m.comapDomain transverseVariable transverseVariable_injective.injOn, ?_⟩
  exact Finsupp.mapDomain_comapDomain transverseVariable
    transverseVariable_injective m hs

private theorem G_mem (p : Charge D) (fg : Poly t × Poly t) :
    G F B p fg ∈ absoluteGround F B p := by
  classical
  have hmono (nu : Exponent t) :
      groundMap F B p (monomial nu 1) ∈ absoluteGround F B p ∧
      ghostC D 0 (groundMap F B p (monomial nu 1)) ∈ absoluteGround F B p := by
    have hn : NoLongitudinal (nu.mapDomain transverseVariable) := by
      intro r
      constructor
      · apply Finsupp.mapDomain_of_notMem_range
        rintro ⟨⟨j,s⟩,h⟩
        simp [transverseVariable, NullFrame.transverse, NullFrame.plus] at h
      · apply Finsupp.mapDomain_of_notMem_range
        rintro ⟨⟨j,s⟩,h⟩
        simp [transverseVariable, NullFrame.transverse, NullFrame.minus] at h
    have hb (S : Finset ℕ) (hS : S = {1} ∨ S = {1,3}) :
        actualBasis F B (⟨p,nu.mapDomain transverseVariable⟩,S) ∈
          absoluteGround F B p := by
      change P0 F B _ = _ ∧ chargeProject p _ = _
      constructor
      · rw [P0_basis, if_pos ((totalCount_zero_iff _).mpr ⟨hn,hS⟩), one_smul]
      · rw [chargeProject_diagonal F B, diagonal_basis]
        simp
    constructor
    · rw [groundMap_monomial]
      exact hb {1} (Or.inl rfl)
    · rw [groundMap_monomial, c0_basis]
      exact (absoluteGround F B p).neg_mem (hb {1,3} (Or.inr rfl))
  have hpoly (A : Poly t →ₗ[ℂ] State D)
      (hA : ∀ nu, A (monomial nu 1) ∈ absoluteGround F B p) (f : Poly t) :
      A f ∈ absoluteGround F B p := by
    rw [← LatticeBRSTModeFiltration.basis_expand
      (MvPolynomial.basisMonomials (Fin t × ℕ) ℂ) f]
    simp only [map_sum, LinearMap.map_smul, MvPolynomial.coe_basisMonomials]
    apply Submodule.sum_mem
    intro nu hnu
    exact (absoluteGround F B p).smul_mem _ (hA nu)
  exact (absoluteGround F B p).add_mem
    (hpoly (groundMap F B p) (fun nu => (hmono nu).1) fg.1)
    (hpoly ((ghostC D 0).comp (groundMap F B p)) (fun nu => (hmono nu).2) fg.2)

set_option backward.isDefEq.respectTransparency true in
private theorem basis_in_range (p : Charge D) (i : StateIndex D t)
    (hz : totalCount i = 0) (hp : i.1.1 = p) :
    actualBasis F B i ∈ LinearMap.range (G F B p) := by
  have hi := (totalCount_zero_iff i).mp hz
  obtain ⟨nu,hnu⟩ := transverse_exponent_lift i.1.2 hi.1
  rcases i with ⟨⟨q,m⟩,S⟩
  change q = p at hp
  change NoLongitudinal m ∧ (S = {1} ∨ S = {1,3}) at hi
  change nu.mapDomain transverseVariable = m at hnu
  subst q
  rcases hi.2 with hS | hS
  · subst S
    refine ⟨(monomial nu 1,0), ?_⟩
    change groundMap F B p (monomial nu 1) + ghostC D 0 (groundMap F B p 0) = _
    simp only [map_zero, add_zero, groundMap_monomial, hnu]
  · subst S
    refine ⟨(0,-monomial nu 1), ?_⟩
    change groundMap F B p 0 + ghostC D 0 (groundMap F B p (-monomial nu 1)) = _
    rw [(groundMap F B p).map_zero, zero_add, (groundMap F B p).map_neg,
      (ghostC D 0).map_neg, groundMap_monomial F B p nu,
      c0_basis F B p (nu.mapDomain transverseVariable), hnu]
    exact neg_neg (actualBasis F B (⟨p,m⟩,{1,3}))

/- Every nonzero coefficient of a fixed state has zero count and charge p.
   Expanding its finite actual-basis support constructs the full preimage. -/
private theorem range_of_fixed (p : Charge D) (v : State D)
    (hv : P0 F B v = v ∧ chargeProject p v = v) :
    v ∈ LinearMap.range (G F B p) := by
  classical
  rw [← LatticeBRSTModeFiltration.basis_expand (actualBasis F B) v]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  have hne := Finsupp.mem_support_iff.mp hi
  have hz : totalCount i = 0 := by
    by_contra hz
    have hc := congrArg (fun w => (actualBasis F B).repr w i) hv.1
    change (actualBasis F B).repr
      (diagonal (actualBasis F B) (fun j => if totalCount j = 0 then 1 else 0) v) i =
      (actualBasis F B).repr v i at hc
    rw [diagonal_coefficient, if_neg hz, zero_mul] at hc
    exact hne hc.symm
  have hp : i.1.1 = p := by
    by_contra hp
    have hc := congrArg (fun w => (actualBasis F B).repr w i) hv.2
    rw [chargeProject_diagonal F B, diagonal_coefficient, if_neg hp, zero_mul] at hc
    exact hne hc.symm
  exact basis_in_range F B p i hz hp

private theorem b0_G (p : Charge D) (fg : Poly t × Poly t) :
    ghostB D 0 (G F B p fg) = groundMap F B p fg.2 := by
  have hb (f : Poly t) : ghostB D 0 (groundMap F B p f) = 0 :=
    LinearMap.congr_fun (groundMap_identities F B p).2.1 f
  have hc := LinearMap.congr_fun (ghost_zero_mixed D) (groundMap F B p fg.2)
  simp only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply,
    hb, map_zero, add_zero] at hc
  change ghostB D 0 (groundMap F B p fg.1 +
    ghostC D 0 (groundMap F B p fg.2)) = _
  rw [map_add, hb, zero_add, hc]

private theorem G_injective (p : Charge D) : Function.Injective (G F B p) := by
  intro fg uv he
  have hg : fg.2 = uv.2 := by
    apply groundMap_injective F B p
    have hb := congrArg (ghostB D 0) he
    simpa only [b0_G] using hb
  change groundMap F B p fg.1 + ghostC D 0 (groundMap F B p fg.2) =
    groundMap F B p uv.1 + ghostC D 0 (groundMap F B p uv.2) at he
  rw [hg] at he
  exact Prod.ext (groundMap_injective F B p (add_right_cancel he)) hg

/-- Exact unrestricted absolute ground coordinates on every original state.
The two fixed-point conditions alone are equivalent to one UNIQUE pair. -/
theorem absolute_ground_coordinates (p : Charge D) (v : State D) :
    (P0 F B v = v ∧ chargeProject p v = v) ↔
      ∃! fg : Poly t × Poly t, v = G F B p fg := by
  constructor
  · intro hv
    obtain ⟨fg,hfg⟩ := range_of_fixed F B p v hv
    refine ⟨fg,hfg.symm,?_⟩
    intro uv huv
    exact G_injective F B p (huv.symm.trans hfg.symm)
  · rintro ⟨fg,hfg,_⟩
    rw [hfg]
    exact G_mem F B p fg

/-- Actual transverse monomial energy, including the ghost ground shift -1. -/
def E (p : Charge D) : Module.End ℂ (Poly t) :=
  diagonal (MvPolynomial.basisMonomials (Fin t × ℕ) ℂ)
    (fun nu => (((weight nu : ℤ) + chargeEnergy D p - 1 : ℤ) : ℂ))

theorem E_monomial (p : Charge D) (nu : Exponent t) :
    E (t := t) p (monomial nu 1) =
      (((weight nu : ℤ) + chargeEnergy D p - 1 : ℤ) : ℂ) • monomial nu 1 := by
  exact diagonal_basis (MvPolynomial.basisMonomials (Fin t × ℕ) ℂ) _ nu

/- Frequency is unchanged by the actual transverse variable injection. -/
private theorem frequencyWeight_mapDomain (nu : Exponent t) :
    Finsupp.weight frequencyWeight (nu.mapDomain transverseVariable) = weight nu := by
  simp only [Finsupp.weight_apply, weight, smul_eq_mul]
  exact Finsupp.sum_mapDomain_index (fun _ => zero_mul _)
    (fun _ _ _ => add_mul _ _ _)

/- Adapted from the pinned PRIVATE ground energy proof, not an application
   of an inaccessible name. Both inverse-Gram laws enter the actual Sugawara
   formula. The ghost contribution is computed on the original ket {1}. -/
private theorem totalL0_groundMap
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) :
    (totalL0 D H).comp (groundMap F B p) =
      (groundMap F B p).comp (E p) := by
  apply (MvPolynomial.basisMonomials (Fin t × ℕ) ℂ).ext
  intro nu
  change totalL0 D H (groundMap F B p (monomial nu 1)) =
    groundMap F B p (E p (monomial nu 1))
  rw [E_monomial, map_smul]
  let Q : PolynomialCoordinates (NullFrame.Label t) :=
    monomial (nu.mapDomain transverseVariable) 1
  have hQ : IsWeightedHomogeneous frequencyWeight Q (weight nu) := by
    apply isWeightedHomogeneous_monomial
    exact frequencyWeight_mapDomain nu
  have hP : IsWeightedHomogeneous (oscillatorWeight D)
      ((F.coordinateEquiv B).symm Q) (weight nu) :=
    (F.frequency_grading B _ _).mp
      (by simpa only [AlgEquiv.apply_symm_apply] using hQ)
  have hL := sugawaraMode_weighted_homogeneous D H hHG hGH p
    ((F.coordinateEquiv B).symm Q) (weight nu) hP
  simp only [groundMap_sector, rename_monomial]
  change (sugawaraMode D H 0 (Finsupp.single p ((F.coordinateEquiv B).symm Q))
      ⊗ₜ[ℂ] ket {1}) +
    (Finsupp.single p ((F.coordinateEquiv B).symm Q) ⊗ₜ[ℂ]
      BcGhostVirasoro.L 0 (ket {1})) = _
  have hg : BcGhostRelativeEnergy.energy ({1} : Finset ℕ) = -1 := by
    simp [BcGhostRelativeEnergy.energy, BcGhostRelativeEnergy.siteEnergy_one]
  rw [hL, BcGhostRelativeEnergy.L_zero_ket, hg, TensorProduct.tmul_smul]
  simp only [TensorProduct.smul_tmul', Int.cast_neg, Int.cast_one]
  change ((weight nu : ℂ) + (bilinear D p p : ℂ) / 2) •
      sector F B p Q (ket {1}) + (-1 : ℂ) • sector F B p Q (ket {1}) =
    (((weight nu : ℤ) + chargeEnergy D p - 1 : ℤ) : ℂ) •
      sector F B p Q (ket {1})
  rw [← add_smul]
  congr 1
  rw [← chargeEnergy_complex_half D p]
  push_cast
  ring

/- Independently evaluate the literal zero ghost Ward commutator. This
   needs no inverse-Gram premise, nilpotence of Q, or original-Q compression. -/
private theorem totalL0_c0_commutes
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    totalL0 D H * ghostC D 0 = ghostC D 0 * totalL0 D H := by
  apply sub_eq_zero.mp
  have hm : matterMode D H 0 * ghostC D 0 - ghostC D 0 * matterMode D H 0 = 0 := by
    apply TensorProduct.ext'
    intro v w
    simp only [matterMode, ghostC, LinearMap.sub_apply, Module.End.mul_apply,
      TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.zero_apply, sub_self]
  have hg : ghostVirasoro D 0 * ghostC D 0 - ghostC D 0 * ghostVirasoro D 0 = 0 := by
    apply TensorProduct.ext'
    intro v w
    have hw := LinearMap.congr_fun (BcGhostVirasoro.ward_c 0 0) w
    have hw' : BcGhostVirasoro.L 0 (c 0 w) - c 0 (BcGhostVirasoro.L 0 w) = 0 := by
      simpa using hw
    simp only [ghostVirasoro, ghostC, LinearMap.sub_apply, Module.End.mul_apply,
      TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.zero_apply]
    rw [← TensorProduct.tmul_sub, hw', TensorProduct.tmul_zero]
  change (matterMode D H 0 + ghostVirasoro D 0) * ghostC D 0 -
    ghostC D 0 * (matterMode D H 0 + ghostVirasoro D 0) = 0
  calc
    _ = (matterMode D H 0 * ghostC D 0 - ghostC D 0 * matterMode D H 0) +
        (ghostVirasoro D 0 * ghostC D 0 - ghostC D 0 * ghostVirasoro D 0) := by
      noncomm_ring
    _ = 0 := by rw [hm, hg, add_zero]

/-- The effective absolute ground complex BEFORE restricting to the mass shell.
This is a calculation of the literal ambient P0*c0*(matterL0+ghostL0)*P0,
on every polynomial pair, with only the two inverse-Gram laws as premises. -/
theorem compressed_energy
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (fg : Poly t × Poly t) :
    (P0 F B * ghostC D 0 * totalL0 D H * P0 F B) (G F B p fg) =
      G F B p (0,E p fg.1) := by
  have hL (f : Poly t) :
      totalL0 D H (groundMap F B p f) = groundMap F B p (E p f) :=
    LinearMap.congr_fun (totalL0_groundMap F B H hHG hGH p) f
  have hc (v : State D) : totalL0 D H (ghostC D 0 v) =
      ghostC D 0 (totalL0 D H v) :=
    LinearMap.congr_fun (totalL0_c0_commutes H) v
  have hcc (v : State D) : ghostC D 0 (ghostC D 0 v) = 0 :=
    LinearMap.congr_fun (ghost_c_zero_square D) v
  change P0 F B (ghostC D 0 (totalL0 D H (P0 F B (G F B p fg)))) = _
  rw [(G_mem F B p fg).1]
  change P0 F B (ghostC D 0 (totalL0 D H
    (groundMap F B p fg.1 + ghostC D 0 (groundMap F B p fg.2)))) = _
  rw [LinearMap.map_add, hL, hc, hL, LinearMap.map_add, hcc, add_zero]
  have hz : G F B p (0,E p fg.1) =
      ghostC D 0 (groundMap F B p (E p fg.1)) := by
    change groundMap F B p 0 + ghostC D 0 (groundMap F B p (E p fg.1)) = _
    rw [LinearMap.map_zero, zero_add]
  rw [← hz]
  exact (G_mem F B p (0,E p fg.1)).1

private theorem E_coefficient (p : Charge D) (f : Poly t) (nu : Exponent t) :
    (E p f).coeff nu =
      (((weight nu : ℤ) + chargeEnergy D p - 1 : ℤ) : ℂ) * f.coeff nu := by
  change (MvPolynomial.basisMonomials (Fin t × ℕ) ℂ).repr (E p f) nu = _
  exact diagonal_coefficient (MvPolynomial.basisMonomials (Fin t × ℕ) ℂ) _ f nu

/- Same coefficient calculation as the pinned private energyOperator_zero_iff;
   the public, independently coefficient-defined energyTarget is reused. -/
private theorem E_zero_iff (p : Charge D) (f : Poly t) :
    E p f = 0 ↔ f ∈ energyTarget D t p := by
  constructor
  · intro he nu hnu
    have hz : (((weight nu : ℤ) + chargeEnergy D p - 1 : ℤ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (weight nu : ℤ) + chargeEnergy D p - 1 ≠ 0 by omega)
    have hc := congrArg (fun g : Poly t => g.coeff nu) he
    rw [E_coefficient] at hc
    exact (mul_eq_zero.mp hc).resolve_left hz
  · intro hf
    ext nu
    change (E p f).coeff nu = 0
    rw [E_coefficient]
    by_cases he : (weight nu : ℤ) + chargeEnergy D p = 1
    · have hz : (weight nu : ℤ) + chargeEnergy D p - 1 = 0 := by omega
      simp [hz]
    · rw [hf nu he, mul_zero]

/- A diagonal inverse on the complement of energy 1 preserves finite support.
   Thus this is a polynomial preimage, not a formal power series. -/
private theorem E_range_iff (p : Charge D) (g : Poly t) :
    (∃ f : Poly t, E p f = g) ↔
      ∀ nu, (weight nu : ℤ) + chargeEnergy D p = 1 → g.coeff nu = 0 := by
  classical
  constructor
  · rintro ⟨f,rfl⟩ nu hnu
    rw [E_coefficient]
    have hz : (weight nu : ℤ) + chargeEnergy D p - 1 = 0 := by omega
    simp [hz]
  · intro hg
    let f : Poly t :=
      diagonal (MvPolynomial.basisMonomials (Fin t × ℕ) ℂ)
        (fun nu => if (weight nu : ℤ) + chargeEnergy D p - 1 = 0 then 0
          else ((((weight nu : ℤ) + chargeEnergy D p - 1 : ℤ) : ℂ))⁻¹) g
    refine ⟨f,?_⟩
    ext nu
    change (E p f).coeff nu = g.coeff nu
    rw [E_coefficient]
    have hf : f.coeff nu =
        (if (weight nu : ℤ) + chargeEnergy D p - 1 = 0 then 0
          else ((((weight nu : ℤ) + chargeEnergy D p - 1 : ℤ) : ℂ))⁻¹) *
            g.coeff nu := by
      exact diagonal_coefficient (MvPolynomial.basisMonomials (Fin t × ℕ) ℂ) _ g nu
    rw [hf]
    by_cases he : (weight nu : ℤ) + chargeEnergy D p - 1 = 0
    · have hs : (weight nu : ℤ) + chargeEnergy D p = 1 := by omega
      rw [if_pos he, hg nu hs]
      simp
    · have hz : (((weight nu : ℤ) + chargeEnergy D p - 1 : ℤ) : ℂ) ≠ 0 := by
        exact_mod_cast he
      rw [if_neg he, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]

/-- Concrete cycles: the first polynomial has only energy-one monomials;
the second polynomial is unrestricted. -/
theorem compressed_energy_cycle_iff
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (fg : Poly t × Poly t) :
    (P0 F B * ghostC D 0 * totalL0 D H * P0 F B) (G F B p fg) = 0 ↔
      fg.1 ∈ energyTarget D t p := by
  rw [compressed_energy F B H hHG hGH p fg]
  constructor
  · intro h
    have he : (0,E p fg.1) = (0 : Poly t × Poly t) :=
      G_injective F B p (h.trans (map_zero (G F B p)).symm)
    exact (E_zero_iff p fg.1).mp (congrArg Prod.snd he)
  · intro hf
    rw [(E_zero_iff p fg.1).mpr hf]
    exact map_zero (G F B p)

/-- Concrete boundaries: the first coordinate vanishes, and the second
has zero coefficient at EVERY energy-one transverse monomial. -/
theorem compressed_energy_boundary_iff
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (fg : Poly t × Poly t) :
    (∃ uv : Poly t × Poly t,
      (P0 F B * ghostC D 0 * totalL0 D H * P0 F B) (G F B p uv) = G F B p fg) ↔
      fg.1 = 0 ∧
        ∀ nu, (weight nu : ℤ) + chargeEnergy D p = 1 → fg.2.coeff nu = 0 := by
  constructor
  · rintro ⟨uv,huv⟩
    rw [compressed_energy F B H hHG hGH p uv] at huv
    have he := G_injective F B p huv
    exact ⟨(congrArg Prod.fst he).symm,
      (E_range_iff p fg.2).mp ⟨uv.1,congrArg Prod.snd he⟩⟩
  · rintro ⟨hf,hg⟩
    obtain ⟨f,he⟩ := (E_range_iff p fg.2).mpr hg
    refine ⟨(f,0),?_⟩
    rw [compressed_energy F B H hHG hGH p (f,0)]
    apply congrArg (G F B p)
    exact Prod.ext hf.symm he

end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteQuartetGround
