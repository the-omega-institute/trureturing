/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTNeutralPhysicalCartan
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTNeutralPhysicalCartan
   mirror-E: none(waiver:original-Q-neutral-physical-Cartan)
   anchors: []
   utility: none
   digest: Neutral original-Q physical classes and their original current action. -/

/- SOURCE ONLY UNCOMPILED.
Authored by the assigned native Codex CLI worker from the immutable 150-source
package at actual accepted head 1cf73dcc3c3f4495c5612013b6e9de86a0320314.
No independent Pro or other live worker output was read. The new scripts have
not been elaborated, compiled, kernel checked, or accepted.

The occupation arguments below use the ORIGINAL tensor basis. In particular,
the absolute primitive argument has no b_0 hypothesis. Its projections act on
ALL State D. Nonzero-charge contractions are never used at zero charge.
The construction and action retain the source's X(i,0), ket{1}, original
Gram coefficients, field modes, and bc signs.

proof_shape: low_energy_ghost_support, neutral_number_zero_shell,
  neutral_number_one_shell, basis_current_Q, cartan_current,
  cartan_no_global_primitive, neutralCartanEquiv, cartan_adjoint: content
Other private lemmas organize these live proofs and are consumed below.
admission_basis: escape-witness
escape_witness: Classification of the literal low-energy occupations excludes
every global Q primitive of a nonzero neutral candidate, and identifies the
whole neutral component of the existing physical image. The actual original
current is then evaluated on arbitrary fixed-charge original states.
Utility none: general occupation and operator proofs, not a numerical instance,
bounded enumeration, checker, or numerical reduction.
-/

import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLieSectors
import D5.S3.VertexAlgebra.LatticeActualConformalState

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTNeutralPhysicalCartan

open LatticeGeneratingFieldLocality
open LatticePositiveEnergy (Exponent oscillatorEnergy chargeEnergy)
open LatticeFiniteNegativeGeneration (neutralMode neutralPolynomialMode)
open LatticeSugawaraCurrents (gramComplex sugawaraMode)
open LatticeActualConformalState (currentState)
open LatticeMatterGhostCoupling (State ghostB)
open LatticeMatterGhostDegree (tensorNumber)
open LatticeRelativeMassShell (TensorLabel tensorBasis tensorCoeffEquiv coeff
  fixedMomentum mem_fixedMomentum_iff)
open LatticeBRSTCohomologyField (cycles Cohomology classOf originalMode)
open LatticeBRSTCohomologyBVSecondOrder (descentCurrent cohomologyCurrent)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie (physicalStates physicalClass physicalImage)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology (inclusion projection)
open LatticeQuartetContraction (chargeProject)
open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock ket)
open BcGhostCharge (charge)

open private siteEnergy_le_relativeEnergy from
  D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy
open private number_basis number_coefficient project_coefficient
  project_number project_charge from
  D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyGhostGrading
open private energyWeight_coeff from
  D5.S3.VertexAlgebra.Lattice.LatticeBRSTZeroEnergyReduction
open private charge_vacuum from
  D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyLaws
open private chargeProject_mem chargeProject_tmul from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology
open private right_vacuum_modes from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateField
open private cycleCurrent current_classOf from
  D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyBVSecondOrder

noncomputable section

variable (D : LatticeData)

private def cartanLabel (i : Fin D.rank) : TensorLabel D :=
  ((0, Finsupp.single (i, 0) 1), {1})

private theorem cartanLabel_injective : Function.Injective (cartanLabel D) := by
  intro i j h
  have hd := congrArg (fun l : TensorLabel D => l.1.2) h
  have hi := Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0) hd
  exact congrArg Prod.fst hi

/-- The literal original neutral creation state with the original c_1 vacuum.
The basis definition expands to X(i,0) tensor ket{1}, with coefficient one. -/
def cartanState : (Fin D.rank → ℂ) →ₗ[ℂ] State D where
  toFun e := ∑ i, e i • tensorBasis D (cartanLabel D i)
  map_add' e f := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' t e := by simp [smul_smul, Finset.smul_sum]

private theorem cartan_basis_tensor (i : Fin D.rank) :
    tensorBasis D (cartanLabel D i) =
      currentState D i ⊗ₜ[ℂ] ket {1} := by
  simp [cartanLabel, LatticeRelativeMassShell.tensorBasis_apply,
    currentState, MvPolynomial.X]

private theorem cartanState_coeff (e : Fin D.rank → ℂ) (l : TensorLabel D) :
    coeff D (cartanState D e) l =
      ∑ i, if cartanLabel D i = l then e i else 0 := by
  classical
  change (tensorBasis D).repr (∑ i, e i • tensorBasis D (cartanLabel D i)) l = _
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]

private theorem cartanState_coordinate (e : Fin D.rank → ℂ) (i : Fin D.rank) :
    coeff D (cartanState D e) (cartanLabel D i) = e i := by
  classical
  rw [cartanState_coeff]
  simp only [(cartanLabel_injective D).eq_iff]
  simp

private theorem cartanState_injective : Function.Injective (cartanState D) := by
  intro e f h
  funext i
  have hi := congrArg (fun x => coeff D x (cartanLabel D i)) h
  simpa only [cartanState_coordinate] using hi

private theorem low_energy_ghost_support (S : Finset ℕ)
    (hE : BcGhostRelativeEnergy.energy S ≤ 0) : S ⊆ {1, 3, 5} := by
  intro j hj
  by_contra hbad
  have h1 : j ≠ 1 := by intro h; apply hbad; simp [h]
  have h3 : j ≠ 3 := by intro h; apply hbad; simp [h]
  have h5 : j ≠ 5 := by intro h; apply hbad; simp [h]
  have htwo : 2 ≤ BcGhostRelativeEnergy.siteEnergy j := by
    by_cases he : j % 2 = 0
    · have hj' : j = 2 * (j / 2) := by omega
      rw [hj', BcGhostRelativeEnergy.siteEnergy_even]
      omega
    · have hj' : j = 2 * (j / 2) + 1 := by omega
      rw [hj', BcGhostRelativeEnergy.siteEnergy_odd]
      have hk : 3 ≤ j / 2 := by omega
      omega
  have hle := siteEnergy_le_relativeEnergy S j hj
  unfold BcGhostRelativeEnergy.relativeEnergy at hle
  omega

private theorem low_energy_ghost_charge (S : Finset ℕ)
    (hE : BcGhostRelativeEnergy.energy S ≤ 0) : charge S = (S.card : ℤ) := by
  classical
  have hs := low_energy_ghost_support S hE
  have odd : S.filter (fun j => j % 2 = 1) = S := by
    apply Finset.filter_eq_self.mpr
    intro j hj
    have hj' := hs hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj'
    rcases hj' with rfl | rfl | rfl <;> norm_num
  have even : S.filter (fun j => j % 2 = 0) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    obtain ⟨hj,he⟩ := Finset.mem_filter.mp hj
    have hj' := hs hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj'
    rcases hj' with rfl | rfl | rfl <;> norm_num at he
  simp [charge, odd, even]

private theorem low_energy_ghost_number_zero (S : Finset ℕ)
    (hE : BcGhostRelativeEnergy.energy S ≤ 0) (hN : charge S = 0) : S = ∅ := by
  have hc := low_energy_ghost_charge S hE
  have hn : S.card = 0 := by omega
  exact Finset.card_eq_zero.mp hn

private theorem low_energy_relative_number_one (S : Finset ℕ)
    (hE : BcGhostRelativeEnergy.energy S ≤ 0)
    (hN : charge S = 1) (hb : 3 ∉ S) : S = {1} := by
  have hc := low_energy_ghost_charge S hE
  have hn : S.card = 1 := by omega
  obtain ⟨j,rfl⟩ := Finset.card_eq_one.mp hn
  have hj := low_energy_ghost_support {j} hE (Finset.mem_singleton_self j)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl
  · rfl
  · simp at hb
  · norm_num [BcGhostRelativeEnergy.energy,
      BcGhostRelativeEnergy.siteEnergy, BcGhostCharge.siteMode,
      BcGhostCharge.siteSign] at hE

private theorem oscillator_energy_one (d : Exponent D) (hd : oscillatorEnergy d = 1) :
    ∃ i : Fin D.rank, d = Finsupp.single (i, 0) 1 := by
  classical
  have hn : d ≠ 0 := by
    intro hz
    simp [hz, oscillatorEnergy] at hd
  obtain ⟨x,hx⟩ := Finsupp.support_nonempty_iff.mpr hn
  have hx0 : d x ≠ 0 := Finsupp.mem_support_iff.mp hx
  have hw := Finsupp.weight_sub_single_add
    (w := fun y : Index D => y.2 + 1) hx0
  change oscillatorEnergy (d - Finsupp.single x 1) + (x.2 + 1) =
    oscillatorEnergy d at hw
  have hx2 : x.2 = 0 := by omega
  have hr : oscillatorEnergy (d - Finsupp.single x 1) = 0 := by omega
  have hz := (LatticePositiveEnergy.oscillatorEnergy_eq_zero_iff D _).mp hr
  refine ⟨x.1, ?_⟩
  have hsum := Finsupp.sub_add_single_one_cancel hx0
  rw [hz, zero_add] at hsum
  exact hsum.symm.trans (congrArg (fun y : Index D => Finsupp.single y (1 : ℕ))
    (Prod.ext rfl hx2))

private theorem number_of_nonzero_coefficient
    (x : State D) (g : ℤ) (hN : tensorNumber D x = (g : ℂ) • x)
    (l : TensorLabel D) (hl : coeff D x l ≠ 0) : charge l.2 = g := by
  have hn := congrArg (fun y : State D => coeff D y l) hN
  change (LatticeBRSTZeroEnergyReduction.fullBasis D).repr (tensorNumber D x) l =
    (LatticeBRSTZeroEnergyReduction.fullBasis D).repr ((g : ℂ) • x) l at hn
  rw [number_coefficient, map_smul, Finsupp.smul_apply, smul_eq_mul] at hn
  have hc : ((charge l.2 : ℂ) - (g : ℂ)) * coeff D x l = 0 := by
    change ((charge l.2 : ℂ) - (g : ℂ)) *
      (LatticeBRSTZeroEnergyReduction.fullBasis D).repr x l = 0
    linear_combination hn
  have he := (mul_eq_zero.mp hc).resolve_right hl
  exact_mod_cast sub_eq_zero.mp he

/- This is a statement about arbitrary actual states, not merely cycles or
relative primitives. No b_0 condition occurs in its telescope. -/
private theorem neutral_number_zero_shell
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x : State D) (hx : x ∈ fixedMomentum D 0)
    (hN : tensorNumber D x = 0)
    (hL : LatticeBRSTZeroEnergyReduction.totalL0 D H x = 0) :
    x = coeff D x ((0,0),∅) • LatticeMatterGhostStateField.vacuum D := by
  classical
  have support (l : TensorLabel D) (hl : coeff D x l ≠ 0) : l = ((0,0),∅) := by
    have hq : l.1.1 = 0 := by
      by_contra h
      exact hl ((mem_fixedMomentum_iff D 0 x).mp hx l h)
    have he := (LatticeRelativeMassShell.totalL0_zero_iff D H hHG hGH x).mp hL l hl
    have he' : (oscillatorEnergy l.1.2 : ℤ) +
        BcGhostRelativeEnergy.energy l.2 = 0 := by
      simpa only [LatticeRelativeMassShell.totalEnergy, LatticePositiveEnergy.energy,
        hq, LatticePositiveEnergy.chargeEnergy_zero, zero_add] using he
    have hg : BcGhostRelativeEnergy.energy l.2 ≤ 0 := by omega
    have hn := number_of_nonzero_coefficient D x 0 (by simpa using hN) l hl
    have hs := low_energy_ghost_number_zero l.2 hg hn
    have he0 : oscillatorEnergy l.1.2 = 0 := by
      simp only [hs, BcGhostRelativeEnergy.energy, Finset.sum_empty, add_zero] at he'
      exact_mod_cast he'
    have hd := (LatticePositiveEnergy.oscillatorEnergy_eq_zero_iff D _).mp he0
    exact Prod.ext (Prod.ext hq hd) hs
  have hv : LatticeMatterGhostStateField.vacuum D = tensorBasis D ((0,0),∅) := by
    simp [LatticeMatterGhostStateField.vacuum, LatticeAllStateField.vacuum,
      CountableOccupationFock.vacuum, LatticeRelativeMassShell.tensorBasis_apply]
  rw [hv]
  apply (tensorCoeffEquiv D).injective
  ext l
  change coeff D x l = (tensorBasis D).repr
    (coeff D x ((0,0),∅) • tensorBasis D ((0,0),∅)) l
  rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self]
  by_cases hl : l = ((0,0),∅)
  · subst l
    simp [coeff, tensorCoeffEquiv]
  · have hz : coeff D x l = 0 := by
      by_contra hn
      exact hl (support l hn)
    simp [hz, Ne.symm hl]

private theorem neutral_number_one_shell
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x : State D) (hx : x ∈ fixedMomentum D 0)
    (hb : ghostB D 0 x = 0) (hN : tensorNumber D x = x)
    (hL : LatticeBRSTZeroEnergyReduction.totalL0 D H x = 0) :
    ∃! e : Fin D.rank → ℂ, cartanState D e = x := by
  classical
  have support (l : TensorLabel D) (hl : coeff D x l ≠ 0) :
      ∃ i, l = cartanLabel D i := by
    have hq : l.1.1 = 0 := by
      by_contra h
      exact hl ((mem_fixedMomentum_iff D 0 x).mp hx l h)
    have he := (LatticeRelativeMassShell.totalL0_zero_iff D H hHG hGH x).mp hL l hl
    have he' : (oscillatorEnergy l.1.2 : ℤ) +
        BcGhostRelativeEnergy.energy l.2 = 0 := by
      simpa only [LatticeRelativeMassShell.totalEnergy, LatticePositiveEnergy.energy,
        hq, LatticePositiveEnergy.chargeEnergy_zero, zero_add] using he
    have hg : BcGhostRelativeEnergy.energy l.2 ≤ 0 := by omega
    have hn := number_of_nonzero_coefficient D x 1 (by simpa using hN) l hl
    have hb' : 3 ∉ l.2 := by
      intro h3
      exact hl ((LatticeRelativeMassShell.ghostB_zero_iff D x).mp hb l h3)
    have hs := low_energy_relative_number_one l.2 hg hn hb'
    have he1 : oscillatorEnergy l.1.2 = 1 := by
      norm_num [hs, BcGhostRelativeEnergy.energy, BcGhostRelativeEnergy.siteEnergy,
        BcGhostCharge.siteMode, BcGhostCharge.siteSign] at he'
      omega
    obtain ⟨i,hi⟩ := oscillator_energy_one D l.1.2 he1
    exact ⟨i,Prod.ext (Prod.ext hq hi) hs⟩
  let e : Fin D.rank → ℂ := fun i => coeff D x (cartanLabel D i)
  have he : cartanState D e = x := by
    apply (tensorCoeffEquiv D).injective
    ext l
    change coeff D (cartanState D e) l = coeff D x l
    by_cases hl : ∃ i, l = cartanLabel D i
    · obtain ⟨i,rfl⟩ := hl
      exact cartanState_coordinate D e i
    · rw [cartanState_coeff]
      have hz : coeff D x l = 0 := by
        by_contra hn
        exact hl (support l hn)
      rw [hz]
      apply Finset.sum_eq_zero
      intro i hi
      exact if_neg (fun h => hl ⟨i,h.symm⟩)
  refine ⟨e,he,?_⟩
  intro f hf
  exact cartanState_injective D (hf.trans he.symm)

private theorem c_high_down (r : ℤ) (hr : 2 ≤ r) :
    BcGhostFock.c r (ket {1}) = 0 := by
  have h := LinearMap.congr_fun (BcGhostFock.ghost_c_car r 1)
    CountableOccupationFock.vacuum
  simpa only [LinearMap.add_apply, Module.End.mul_apply,
    BcGhostFock.ghost_vacuum.2.2.1,
    BcGhostFock.ghost_vacuum.2.1 r hr, map_zero, add_zero,
    LinearMap.zero_apply] using h

private theorem c_one_down : BcGhostFock.c 1 (ket {1}) = 0 := by
  norm_num [BcGhostFock.c, CountableOccupationFock.create_ket]

/- The sign is derived from the original cubic Ward law. Keeping c_0 ket{1}
symbolic avoids importing a different ghost inner product or normalization. -/
private theorem Qg_down : BcGhostBRST.Qg (ket {1}) =
    -BcGhostFock.c 0 (ket {1}) := by
  classical
  have tail (p : ℤ) (hp : p ≠ 0) (hp1 : p ≠ 1) :
      BcGhostBRST.rTerm 1 p CountableOccupationFock.vacuum = 0 := by
    by_cases hlow : p < 0
    · have hright := BcGhostFock.ghost_vacuum.2.1 (1-p) (by omega)
      simp [BcGhostBRST.rTerm, Module.End.mul_apply, hright]
    · have hhigh : 2 ≤ p := by omega
      have h := LinearMap.congr_fun (BcGhostFock.ghost_c_car p (1-p))
        CountableOccupationFock.vacuum
      have hz : BcGhostFock.c p
          (BcGhostFock.c (1-p) CountableOccupationFock.vacuum) = 0 := by
        simpa only [LinearMap.add_apply, Module.End.mul_apply,
          BcGhostFock.ghost_vacuum.2.1 p hhigh, map_zero, add_zero,
          LinearMap.zero_apply] using h
      simp [BcGhostBRST.rTerm, Module.End.mul_apply, hz]
  have capture : BcGhostBRST.R 1 CountableOccupationFock.vacuum =
      ∑ p ∈ ({0,1} : Finset ℤ),
        BcGhostBRST.rTerm 1 p CountableOccupationFock.vacuum := by
    change (∑ᶠ p : ℤ, BcGhostBRST.rTerm 1 p CountableOccupationFock.vacuum) = _
    apply finsum_eq_sum_of_support_subset
    intro p hp
    by_contra hbad
    have hp0 : p ≠ 0 := by intro h; subst p; simp at hbad
    have hp1 : p ≠ 1 := by intro h; subst p; simp at hbad
    exact hp (tail p hp0 hp1)
  have anti : BcGhostFock.c 1
      (BcGhostFock.c 0 CountableOccupationFock.vacuum) =
        -BcGhostFock.c 0 (BcGhostFock.c 1 CountableOccupationFock.vacuum) := by
    have h := LinearMap.congr_fun (BcGhostFock.ghost_c_car 1 0)
      CountableOccupationFock.vacuum
    have h' : BcGhostFock.c 1 (BcGhostFock.c 0 CountableOccupationFock.vacuum) +
        BcGhostFock.c 0 (BcGhostFock.c 1 CountableOccupationFock.vacuum) = 0 := by
      simpa only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] using h
    exact eq_neg_of_add_eq_zero_left h'
  have hR : BcGhostBRST.R 1 CountableOccupationFock.vacuum =
      -BcGhostFock.c 0 (ket {1}) := by
    rw [capture]
    norm_num only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one,
      not_false_eq_true, Finset.sum_singleton, BcGhostBRST.rTerm,
      LinearMap.smul_apply, Module.End.mul_apply, Int.cast_ofNat,
      Int.cast_sub, Int.cast_mul, Int.cast_zero, Int.cast_one,
      mul_zero, mul_one, sub_zero, zero_sub, neg_zero]
    rw [anti, BcGhostFock.ghost_vacuum.2.2.1]
    module
  have h := LinearMap.congr_fun (BcGhostBRST.ward_c 1)
    CountableOccupationFock.vacuum
  simpa only [LinearMap.add_apply, Module.End.mul_apply,
    BcGhostFock.ghost_vacuum.2.2.1, BcGhostBRST.Qg_vacuum,
    map_zero, add_zero, hR] using h

private theorem current_creation (i : Fin D.rank) :
    neutralMode D i (-1) (Finsupp.single 0 (1 : Oscillator D)) = currentState D i := by
  have h := LatticeActualConformalState.current_state_creation D i
  simpa only [LatticeSugawaraCurrents.neutralField_ncoeff,
    LatticeAllStateField.vacuum] using h

private theorem neutral_ground_nonnegative (i : Fin D.rank) (m : ℤ) (hm : 0 ≤ m) :
    neutralMode D i m (Finsupp.single 0 (1 : Oscillator D)) = 0 := by
  classical
  by_cases hm0 : m = 0
  · simp [neutralMode, neutralPolynomialMode, not_lt.mpr hm, hm0, bilinear]
  · simp [neutralMode, neutralPolynomialMode, not_lt.mpr hm, hm0, bilinear,
      LinearMap.smul_apply, LinearMap.sum_apply]

private theorem current_nonnegative_sugawara
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (i : Fin D.rank) (m : ℤ) (hm : 0 ≤ m) :
    sugawaraMode D H m (currentState D i) =
      if m = 0 then currentState D i else 0 := by
  classical
  have hg : sugawaraMode D H m (Finsupp.single 0 (1 : Oscillator D)) = 0 := by
    by_cases hm0 : m = 0
    · subst m
      rw [LatticeSugawaraVirasoro.sugawaraMode_ground_zero]
      simp [LatticeSugawaraVirasoro.chargeQuadratic,
        LatticeSugawaraVirasoro.chargeScalar, bilinear]
    · exact LatticeSugawaraVirasoro.sugawaraMode_ground_positive D H 0 m (by omega)
  have h := LinearMap.congr_fun
    (LatticeSugawaraCurrents.sugawaraMode_current_commutator D H hHG hGH i m (-1))
      (Finsupp.single 0 (1 : Oscillator D))
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hg, map_zero, sub_zero,
    current_creation, Int.cast_neg, Int.cast_one, neg_neg,
    LinearMap.smul_apply, one_smul] at h
  by_cases hm0 : m = 0
  · simpa only [hm0, zero_add, ite_true, current_creation] using h
  · rw [if_neg hm0]
    rw [h]
    exact neutral_ground_nonnegative D i (m + -1) (by omega)

private theorem basis_current_Q
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (i : Fin D.rank) :
    LatticeBRST.totalCharge D H (tensorBasis D (cartanLabel D i)) = 0 := by
  classical
  have Tvalue : LatticeMatterGhostCoupling.T D H
      (currentState D i ⊗ₜ[ℂ] ket {1}) =
        currentState D i ⊗ₜ[ℂ] BcGhostFock.c 0 (ket {1}) := by
    change (∑ᶠ m : ℤ, LatticeMatterGhostCoupling.summand D H m
      (currentState D i ⊗ₜ[ℂ] ket {1})) = _
    rw [finsum_eq_single _ 0]
    · simp only [LatticeMatterGhostCoupling.summand, TensorProduct.map_tmul,
        current_nonnegative_sugawara D H hHG hGH i 0 (by omega),
        ite_true, neg_zero]
    · intro m hm
      simp only [LatticeMatterGhostCoupling.summand, TensorProduct.map_tmul]
      by_cases hneg : m < 0
      · by_cases hm1 : m = -1
        · subst m
          simp [c_one_down]
        · rw [c_high_down (-m) (by omega), TensorProduct.tmul_zero]
      · rw [current_nonnegative_sugawara D H hHG hGH i m (by omega),
          if_neg hm, TensorProduct.zero_tmul]
  rw [cartan_basis_tensor, LatticeBRST.totalCharge, LinearMap.add_apply, Tvalue]
  simp only [LatticeBRST.ghostCharge, TensorProduct.map_tmul, LinearMap.id_apply,
    Qg_down, TensorProduct.tmul_neg, add_neg_cancel]

private theorem basis_current_fixed (i : Fin D.rank) :
    tensorBasis D (cartanLabel D i) ∈ fixedMomentum D 0 := by
  classical
  apply (mem_fixedMomentum_iff D 0 _).mpr
  intro l hl
  change (tensorBasis D).repr (tensorBasis D (cartanLabel D i)) l = 0
  rw [Module.Basis.repr_self]
  have hne : cartanLabel D i ≠ l := by
    intro he
    exact hl (congrArg (fun k : TensorLabel D => k.1.1) he).symm
  simp only [Finsupp.single_apply, if_neg hne]

private theorem cartanState_fixed (e : Fin D.rank → ℂ) :
    cartanState D e ∈ fixedMomentum D 0 := by
  change (∑ i, e i • tensorBasis D (cartanLabel D i)) ∈ fixedMomentum D 0
  apply (fixedMomentum D 0).sum_mem
  intro i hi
  exact (fixedMomentum D 0).smul_mem _ (basis_current_fixed D i)

/-- All four original physical equations hold for the actual neutral candidate. -/
theorem cartan_physical
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (e : Fin D.rank → ℂ) : cartanState D e ∈ physicalStates D H := by
  classical
  have physical (i : Fin D.rank) :
      tensorBasis D (cartanLabel D i) ∈ physicalStates D H := by
    refine ⟨basis_current_Q D H hHG hGH i, ?_, ?_, ?_⟩
    · rw [cartan_basis_tensor]
      simp only [ghostB, TensorProduct.map_tmul, LinearMap.id_apply,
        BcGhostRelativeEnergy.b_zero_down, TensorProduct.tmul_zero]
    · change tensorNumber D (LatticeBRSTZeroEnergyReduction.fullBasis D
        (cartanLabel D i)) = _
      rw [number_basis]
      have hc : charge ({1} : Finset ℕ) = 1 := by
        norm_num [charge, Finset.filter_singleton]
      simp only [cartanLabel, hc, Int.cast_one, one_smul]
      rfl
    · change LatticeRelativeMassShell.totalL0 D H
        (tensorBasis D (cartanLabel D i)) = 0
      rw [LatticeRelativeMassShell.totalL0_basis D H hHG hGH]
      norm_num [LatticeRelativeMassShell.totalEnergy, cartanLabel,
        LatticePositiveEnergy.energy, oscillatorEnergy,
        Finsupp.weight_single,
        BcGhostRelativeEnergy.energy, BcGhostRelativeEnergy.siteEnergy,
        BcGhostCharge.siteMode, BcGhostCharge.siteSign]
  change (∑ i, e i • tensorBasis D (cartanLabel D i)) ∈ physicalStates D H
  apply (physicalStates D H).sum_mem
  intro i hi
  exact (physicalStates D H).smul_mem _ (physical i)

/-- The exact original Gram/coordinate factor, without H or a frame. -/
def gamma (e : Fin D.rank → ℂ) (a : Charge D) : ℂ :=
  ∑ i, e i * (bilinear D (unitCharge D i) a : ℂ)

private theorem basis_current_action (i : Fin D.rank) (a : Charge D)
    (x : State D) (hx : x ∈ fixedMomentum D a) :
    descentCurrent D (tensorBasis D (cartanLabel D i)) x =
      (bilinear D (unitCharge D i) a : ℂ) • x := by
  classical
  have hb : ghostB D (-1) (tensorBasis D (cartanLabel D i)) =
      currentState D i ⊗ₜ[ℂ] CountableOccupationFock.vacuum := by
    rw [cartan_basis_tensor]
    norm_num [ghostB, TensorProduct.map_tmul, BcGhostFock.b,
      CountableOccupationFock.annihilate_ket, CountableOccupationFock.phase,
      CountableOccupationFock.lowerCount, CountableOccupationFock.vacuum,
      Finset.filter_singleton]
  have op : descentCurrent D (tensorBasis D (cartanLabel D i)) =
      TensorProduct.map (neutralMode D i 0) (LinearMap.id : Fock →ₗ[ℂ] Fock) := by
    change originalMode D 0 (ghostB D (-1) (tensorBasis D (cartanLabel D i))) = _
    rw [hb]
    change ((LatticeMatterGhostStateField.Y D
      (currentState D i ⊗ₜ[ℂ] CountableOccupationFock.vacuum))[[0]]) = _
    rw [right_vacuum_modes, LatticeActualConformalState.current_state_field,
      LatticeSugawaraCurrents.neutralField_ncoeff]
  rw [op]
  rw [LatticeRelativeMassShell.fixedMomentum_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨l,hl,rfl⟩ := hy
      change l.1.1 = a at hl
      simp only [LatticeRelativeMassShell.tensorBasis_apply, TensorProduct.map_tmul,
        LinearMap.id_apply, LatticeSugawaraVirasoro.neutralMode_zero_single,
        TensorProduct.smul_tmul, TensorProduct.tmul_smul, hl,
        LatticeSugawaraVirasoro.chargeScalar]
  | zero => simp
  | add y z hy hz iy iz => simp only [map_add, iy, iz, smul_add]
  | smul t y hy iy => simp only [map_smul, iy, smul_comm t]

/-- Actual descentCurrent on every original fixed-charge state. No oscillator,
ghost-occupation, physicality, nonzero-charge, or nonzero-vector restriction. -/
theorem cartan_current (e : Fin D.rank → ℂ) (a : Charge D)
    (x : State D) (hx : x ∈ fixedMomentum D a) :
    descentCurrent D (cartanState D e) x = gamma D e a • x := by
  classical
  change descentCurrent D (∑ i, e i • tensorBasis D (cartanLabel D i)) x = _
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  simp_rw [basis_current_action D _ a x hx, smul_smul]
  rw [← Finset.sum_smul]
  rfl

private theorem numberProject_fixed (g : ℤ) (x : State D)
    (hx : tensorNumber D x = (g : ℂ) • x) :
    LatticeBRSTCohomologyGhostGrading.project D g x = x := by
  classical
  apply (LatticeBRSTZeroEnergyReduction.fullBasis D).repr.injective
  ext l
  rw [project_coefficient]
  by_cases hl : charge l.2 = g
  · simp only [if_pos hl]
  · rw [if_neg hl]
    change 0 = coeff D x l
    by_contra hn
    exact hl (number_of_nonzero_coefficient D x g hx l (Ne.symm hn))

/-- A primitive is initially an arbitrary all-charge, all-energy, all-number
original state. Three literal spectral projections reduce it to the original
neutral degree-zero energy-zero vacuum line; Q of that line is zero. -/
theorem cartan_no_global_primitive
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (e : Fin D.rank → ℂ) (z : State D)
    (hz : LatticeBRST.totalCharge D H z = cartanState D e) : e = 0 := by
  classical
  let zq : State D := chargeProject 0 z
  let zE : State D := LatticeBRSTZeroEnergyReduction.P0 D zq
  let zN : State D := LatticeBRSTCohomologyGhostGrading.project D 0 zE
  have pe := cartan_physical D H hHG hGH e
  have hQq : LatticeBRST.totalCharge D H zq = cartanState D e := by
    change LatticeBRST.totalCharge D H (chargeProject 0 z) = _
    rw [← D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.chargeProject_commutes D H, hz,
      D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.chargeProject_fixed D 0 _ (cartanState_fixed D e)]
  have hQE : LatticeBRST.totalCharge D H zE = cartanState D e := by
    calc
      _ = LatticeBRSTZeroEnergyReduction.P0 D (LatticeBRST.totalCharge D H zq) :=
        (LinearMap.congr_fun
          (LatticeBRSTZeroEnergyReduction.P0_commutes D H h26 hHG hGH) zq).symm
      _ = LatticeBRSTZeroEnergyReduction.P0 D (cartanState D e) := by rw [hQq]
      _ = cartanState D e :=
        (LatticeBRSTZeroEnergyReduction.P0_fixed_iff D H hHG hGH _).mpr pe.2.2.2
  have hQN : LatticeBRST.totalCharge D H zN = cartanState D e := by
    have h := project_charge D H 1 zE
    have hf := numberProject_fixed D 1 (cartanState D e) (by simpa using pe.2.2.1)
    simpa only [show (1-1 : ℤ) = 0 by omega, hQE, hf] using h.symm
  have hfixed : zN ∈ fixedMomentum D 0 := by
    apply (mem_fixedMomentum_iff D 0 zN).mpr
    intro l hl
    change (LatticeBRSTZeroEnergyReduction.fullBasis D).repr
      (LatticeBRSTCohomologyGhostGrading.project D 0 zE) l = 0
    rw [project_coefficient]
    have hE : (LatticeBRSTZeroEnergyReduction.fullBasis D).repr zE l = 0 := by
      change (LatticeBRSTZeroEnergyReduction.fullBasis D).repr
        (LatticeBRSTZeroEnergyReduction.energyWeight D
          (fun k => if k = 0 then 1 else 0) zq) l = 0
      rw [energyWeight_coeff]
      change _ * coeff D (chargeProject 0 z) l = 0
      rw [D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.chargeProject_coeff, if_neg hl, mul_zero]
    split_ifs <;> simp only [hE]
  have hnumber : tensorNumber D zN = 0 := by
    simpa only [Int.cast_zero, zero_smul] using project_number D 0 zE
  have henergy : LatticeBRSTZeroEnergyReduction.totalL0 D H zN = 0 := by
    apply (LatticeRelativeMassShell.totalL0_zero_iff D H hHG hGH zN).mpr
    intro l hl
    have hE : coeff D zE l ≠ 0 := by
      intro hzE
      apply hl
      change (LatticeBRSTZeroEnergyReduction.fullBasis D).repr
        (LatticeBRSTCohomologyGhostGrading.project D 0 zE) l = 0
      rw [project_coefficient]
      change (if charge l.2 = 0 then coeff D zE l else 0) = 0
      simp only [hzE, ite_self]
    exact (LatticeRelativeMassShell.totalL0_zero_iff D H hHG hGH zE).mp
      (LatticeBRSTZeroEnergyReduction.totalL0_P0 D H hHG hGH zq) l hE
  have vacuumLine := neutral_number_zero_shell D H hHG hGH zN hfixed hnumber henergy
  have hzN0 : LatticeBRST.totalCharge D H zN = 0 := by
    rw [vacuumLine, map_smul, charge_vacuum D H, smul_zero]
  apply cartanState_injective D
  simpa only [map_zero] using hQN.symm.trans hzN0

def cartanRepresentative
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    (Fin D.rank → ℂ) →ₗ[ℂ] physicalStates D H :=
  (cartanState D).codRestrict (physicalStates D H) (cartan_physical D H hHG hGH)

variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
  (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

local notation "C" => Cohomology D H h26 hHG hGH

/-- Class in the EXISTING global ker(original Q)/range(original Q). -/
def cartanClass : (Fin D.rank → ℂ) →ₗ[ℂ] C :=
  (physicalClass D H h26 hHG hGH).comp (cartanRepresentative D H hHG hGH)

include h26 hHG hGH in
private theorem cartanClass_injective :
    Function.Injective (cartanClass D H h26 hHG hGH) := by
  intro e f hef
  apply sub_eq_zero.mp
  have hc : cartanClass D H h26 hHG hGH (e-f) = 0 := by
    rw [map_sub, hef, sub_self]
  have hc' : classOf D H h26 hHG hGH
      ⟨cartanState D (e-f), (cartan_physical D H hHG hGH (e-f)).1⟩ = 0 := hc
  obtain ⟨z,hz⟩ := (LatticeBRSTCohomologyField.classOf_eq_zero
    D H h26 hHG hGH _).mp hc'
  exact cartan_no_global_primitive D H h26 hHG hGH (e-f) z hz

include hHG hGH in
private theorem project_physical (a : Charge D) (x : physicalStates D H) :
    chargeProject a (x : State D) ∈ physicalStates D H := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.chargeProject_commutes D H,
      x.property.1, map_zero]
  · apply (LatticeRelativeMassShell.ghostB_zero_iff D _).mpr
    intro l hl
    simp only [D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.chargeProject_coeff]
    have hz := (LatticeRelativeMassShell.ghostB_zero_iff D _).mp x.property.2.1 l hl
    simp only [hz, ite_self]
  · apply (LatticeBRSTZeroEnergyReduction.fullBasis D).repr.injective
    ext l
    rw [number_coefficient]
    change (charge l.2 : ℂ) * coeff D (chargeProject a (x : State D)) l =
      coeff D (chargeProject a (x : State D)) l
    simp only [D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.chargeProject_coeff]
    by_cases hl : l.1.1 = a
    · rw [if_pos hl]
      have h := congrArg (fun y : State D =>
        (LatticeBRSTZeroEnergyReduction.fullBasis D).repr y l) x.property.2.2.1
      rw [number_coefficient] at h
      change (charge l.2 : ℂ) *
        (LatticeBRSTZeroEnergyReduction.fullBasis D).repr (x : State D) l =
          (LatticeBRSTZeroEnergyReduction.fullBasis D).repr (x : State D) l
      exact h
    · simp only [if_neg hl, mul_zero]
  · apply (LatticeRelativeMassShell.totalL0_zero_iff D H hHG hGH _).mpr
    intro l hl
    have hx : coeff D (x : State D) l ≠ 0 := by
      intro hz
      apply hl
      rw [D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.chargeProject_coeff]
      simp only [hz, ite_self]
    exact (LatticeRelativeMassShell.totalL0_zero_iff D H hHG hGH _).mp
      x.property.2.2.2 l hx

/- The original quotient's charge component admits a physical representative
of that charge. The proof uses the existing inclusion/projection maps; it
does not define a replacement quotient or assume representative homogeneity. -/
include h26 hHG hGH in
private theorem physical_charge_representative (a : Charge D) (c : C)
    (hc : c ∈ physicalImage D H h26 hHG hGH)
    (ha : c ∈ LinearMap.range (inclusion D H h26 hHG hGH a)) :
    ∃ x : physicalStates D H, (x : State D) ∈ fixedMomentum D a ∧
      physicalClass D H h26 hHG hGH x = c := by
  obtain ⟨x,hx⟩ := hc
  let y : physicalStates D H :=
    ⟨chargeProject a (x : State D), project_physical D H hHG hGH a x⟩
  have pincl : inclusion D H h26 hHG hGH a
      (projection D H h26 hHG hGH a c) = c := by
    obtain ⟨s,hs⟩ := ha
    obtain ⟨u,hu⟩ := D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorClassOf_surjective
      D H h26 hHG hGH a s
    have huc : classOf D H h26 hHG hGH
        (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.cycleInclusion D H a u) = c := by
      rw [← D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.inclusion_sectorClassOf, hu]
      exact hs
    rw [← huc, D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.projection_classOf,
      D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.inclusion_sectorClassOf]
    apply congrArg (classOf D H h26 hHG hGH)
    apply Subtype.ext
    change chargeProject a (u.val.val : State D) = (u.val.val : State D)
    exact D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.chargeProject_fixed D a _ u.val.property
  refine ⟨y, chargeProject_mem D a (x : State D), ?_⟩
  calc
    physicalClass D H h26 hHG hGH y = inclusion D H h26 hHG hGH a
        (projection D H h26 hHG hGH a (physicalClass D H h26 hHG hGH x)) := rfl
    _ = inclusion D H h26 hHG hGH a (projection D H h26 hHG hGH a c) := by rw [hx]
    _ = c := pincl

/-- The entire neutral component of the EXISTING literal physical image. -/
def neutralPhysicalImage : Submodule ℂ C :=
  physicalImage D H h26 hHG hGH ⊓ LinearMap.range (inclusion D H h26 hHG hGH 0)

include h26 hHG hGH in
private theorem cartanClass_mem (e : Fin D.rank → ℂ) :
    cartanClass D H h26 hHG hGH e ∈ neutralPhysicalImage D H h26 hHG hGH := by
  refine ⟨⟨cartanRepresentative D H hHG hGH e,rfl⟩, ?_⟩
  let u : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorCycles D H 0 :=
    ⟨⟨cartanState D e, cartanState_fixed D e⟩, by
      apply Subtype.ext
      exact (cartan_physical D H hHG hGH e).1⟩
  refine ⟨D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorClassOf D H h26 hHG hGH 0 u, ?_⟩
  rfl

private def neutralCartanMap : (Fin D.rank → ℂ) →ₗ[ℂ]
    neutralPhysicalImage D H h26 hHG hGH :=
  (cartanClass D H h26 hHG hGH).codRestrict
    (neutralPhysicalImage D H h26 hHG hGH) (cartanClass_mem D H h26 hHG hGH)

include h26 hHG hGH in
private theorem neutralCartanMap_bijective :
    Function.Bijective (neutralCartanMap D H h26 hHG hGH) := by
  constructor
  · intro e f hef
    exact cartanClass_injective D H h26 hHG hGH (congrArg Subtype.val hef)
  · intro c
    obtain ⟨x,hx,hc⟩ := physical_charge_representative D H h26 hHG hGH 0 c
      c.property.1 c.property.2
    obtain ⟨e,he,_⟩ := neutral_number_one_shell D H hHG hGH x hx
      x.property.2.1 x.property.2.2.1 x.property.2.2.2
    refine ⟨e,Subtype.ext ?_⟩
    change cartanClass D H h26 hHG hGH e = (c : C)
    have hx' : cartanRepresentative D H hHG hGH e = x := Subtype.ext he
    change physicalClass D H h26 hHG hGH (cartanRepresentative D H hHG hGH e) = _
    rw [hx', hc]

/-- Full construction, classification, and uniqueness in the original global
quotient. Its domain has rank D.rank, hence 26 under the stated rank binder. -/
def neutralCartanEquiv : (Fin D.rank → ℂ) ≃ₗ[ℂ]
    neutralPhysicalImage D H h26 hHG hGH :=
  LinearEquiv.ofBijective (neutralCartanMap D H h26 hHG hGH)
    (neutralCartanMap_bijective D H h26 hHG hGH)

include h26 hHG hGH in
/-- The induced original current on every actual charge-a physical-image
component is the exact gamma scalar times identity, including a=0. -/
theorem cartan_current_class (e : Fin D.rank → ℂ) (a : Charge D) (c : C)
    (hc : c ∈ physicalImage D H h26 hHG hGH)
    (ha : c ∈ LinearMap.range (inclusion D H h26 hHG hGH a)) :
    cohomologyCurrent D H h26 hHG hGH (cartanClass D H h26 hHG hGH e) c =
      gamma D e a • c := by
  obtain ⟨x,hx,rfl⟩ := physical_charge_representative D H h26 hHG hGH a c hc ha
  let u : cycles D H := ⟨cartanState D e, (cartan_physical D H hHG hGH e).1⟩
  let v : cycles D H := ⟨(x : State D), x.property.1⟩
  change cohomologyCurrent D H h26 hHG hGH (classOf D H h26 hHG hGH u)
    (classOf D H h26 hHG hGH v) = _
  rw [current_classOf]
  change classOf D H h26 hHG hGH (cycleCurrent D H hHG hGH u v) =
    gamma D e a • classOf D H h26 hHG hGH v
  rw [← map_smul]
  apply congrArg (classOf D H h26 hHG hGH)
  apply Subtype.ext
  exact cartan_current D e a x hx

/-- The Cartan element is regarded as an element of the actual physical Lie
image, so the final action below is its existing LieRing bracket. -/
def cartanPhysicalImage : (Fin D.rank → ℂ) →ₗ[ℂ]
    physicalImage D H h26 hHG hGH :=
  (cartanClass D H h26 hHG hGH).codRestrict (physicalImage D H h26 hHG hGH)
    (fun e => (cartanClass_mem D H h26 hHG hGH e).1)

include h26 hHG hGH in
theorem cartan_adjoint (e : Fin D.rank → ℂ) (a : Charge D)
    (c : physicalImage D H h26 hHG hGH)
    (ha : (c : C) ∈ LinearMap.range (inclusion D H h26 hHG hGH a)) :
    ⁅cartanPhysicalImage D H h26 hHG hGH e, c⁆ = gamma D e a • c := by
  apply Subtype.ext
  exact cartan_current_class D H h26 hHG hGH e a c c.property ha

end
end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTNeutralPhysicalCartan


