/- GID: D5/S3/VertexAlgebra/Lattice/LatticeBRSTFullOriginalRaising
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeBRSTFullOriginalRaising
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Statewise finite assembly and fixed-integral-charge raising for original Q-d0. -/

import D5.S3.VertexAlgebra.Lattice.LatticeSugawaraNullFrameEndpoints
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard

/-! Native construction for the original full BRST remainder.

The original 412-line source was an uncompiled proposal. Kernel status is given
by the actual current build and scoped report. Independent source-fidelity
review, escape audits and canonical admission are separate pending obligations.

Q means the literal LatticeBRST.totalCharge = T + id tensor original Qg. No
relative Qhat, intercept, vacuum, ghost cutoff, shell or uniform mode bound is
substituted. The finite set below is reconstructed separately for each input.
Its zero endpoint is inserted once; the native asymmetric Sugawara capture is
left untouched. Both inverse-Gram equations are required for raising, though
finite assembly itself is algebraic and needs neither equation.

The finite assembly, basis consequences and charge helpers are consumed below
by actual vector-level inference. None is retained solely as an endpoint alias.
No shell bounds, preservation of the relative shell, nilpotence, HPL, Q^2=0,
cohomology, no-ghost or physical realization is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.LatticeBRSTFullOriginalRaising

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeSugawaraVirasoro
open LatticeLightConeCoordinates LatticeLightConeCoordinates.NullFrame
open LatticeQuartetContraction LatticeBRSTModeFiltration
open LatticeSugawaraNullFrameEndpoints
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
open private sector_current from D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction

variable {D : LatticeData} (F : NullFrame D)

/-- A finite union of ACTUAL state-action supports, with zero inserted once.
There is no finsum in an endomorphism space. -/
def commonModes (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (x : State D) : Finset ℤ :=
  insert 0 ((LatticeMatterGhostCoupling.summand_finite D H x).toFinset ∪
    (signed_support F x).1.toFinset)

private theorem commonModes_spec
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (x : State D) :
    0 ∈ commonModes F H x ∧
    Function.support (fun n : ℤ => LatticeMatterGhostCoupling.summand D H n x) ⊆
      (commonModes F H x : Set ℤ) ∧
    Function.support (fun n : ℤ => if n = 0 then 0 else dm F n x) ⊆
      (commonModes F H x : Set ℤ) := by
  classical
  refine ⟨by simp [commonModes], ?_, ?_⟩
  · intro n hn
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _
      ((LatticeMatterGhostCoupling.summand_finite D H x).mem_toFinset.mpr hn))
  · intro n hn
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _
      ((signed_support F x).1.mem_toFinset.mpr hn))

private theorem d0_common_capture
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (p : Charge D) (x : State D) :
    d0 F p x = ∑ n ∈ commonModes F H x,
      if n = 0 then 0 else F.pPlus p • dm F n x := by
  classical
  rw [d0_signed_formula F p x]
  change F.pPlus p • (∑ᶠ n : ℤ, if n = 0 then 0 else dm F n x) = _
  rw [finsum_eq_sum_of_support_subset _ (commonModes_spec F H x).2.2,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hz : n = 0 <;> simp [hz]

/-- Exact statewise identity for the ORIGINAL totalCharge-d0. The finite set
depends on x; no equality with a globally truncated operator is claimed.
In particular it applies to actualBasis F B i with the original integral charge
i.1.1=p. The algebraic identity itself is valid on every original state. -/
theorem totalCharge_sub_d0_finite_capture
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (p : Charge D) (x : State D) :
    (LatticeBRST.totalCharge D H - d0 F p) x =
      finiteRemainder F H p (commonModes F H x) x +
        (LatticePositiveEnergy.chargeEnergy D p : ℂ) •
          tp (1 : Module.End ℂ (Carrier D)) (c 0) x := by
  classical
  let s := commonModes F H x
  have hs0 : 0 ∈ s := (commonModes_spec F H x).1
  have hT : LatticeMatterGhostCoupling.T D H x =
      ∑ n ∈ s, LatticeMatterGhostCoupling.summand D H n x :=
    LatticeMatterGhostCoupling.finite_capture D H x s (commonModes_spec F H x).2.1
  have hd : d0 F p x =
      ∑ n ∈ s, if n = 0 then 0 else F.pPlus p • dm F n x :=
    d0_common_capture F H p x
  have hsubtract :
      (∑ n ∈ s, (if n = 0 then tp (endpoint p 0) (c 0)
        else F.pPlus p • tp (a F.eMinus n) (c (-n))) x) =
      tp (endpoint p 0) (c 0) x + d0 F p x := by
    have hterm (n : ℤ) :
        (if n = 0 then tp (endpoint p 0) (c 0)
          else F.pPlus p • tp (a F.eMinus n) (c (-n))) x =
        (if n = 0 then tp (endpoint p 0) (c 0) x else 0) +
          (if n = 0 then 0 else F.pPlus p • dm F n x) := by
      by_cases hz : n = 0 <;> simp [hz, dm]
    rw [Finset.sum_congr rfl (fun n _ => hterm n), Finset.sum_add_distrib, ← hd]
    congr 1
    simp [hs0]
  have hfinite : finiteRemainder F H p s x =
      LatticeMatterGhostCoupling.T D H x -
        (tp (endpoint p 0) (c 0) x + d0 F p x) + LatticeBRST.ghostCharge D x := by
    simp only [finiteRemainder, LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.sub_apply, Finset.sum_sub_distrib]
    change (∑ n ∈ s, LatticeMatterGhostCoupling.summand D H n x) -
      (∑ n ∈ s, (if n = 0 then tp (endpoint p 0) (c 0)
        else F.pPlus p • tp (a F.eMinus n) (c (-n))) x) +
      LatticeBRST.ghostCharge D x = _
    rw [← hT, hsubtract]
  have hzero : tp (endpoint p 0) (c 0) x =
      (LatticePositiveEnergy.chargeEnergy D p : ℂ) •
        tp (1 : Module.End ℂ (Carrier D)) (c 0) x := by
    change (TensorProduct.map
      ((LatticePositiveEnergy.chargeEnergy D p : ℂ) • (1 : Module.End ℂ (Carrier D)))
      (c 0)) x = _
    rw [TensorProduct.map_smul_left, LinearMap.smul_apply]
    rfl
  change LatticeBRST.totalCharge D H x - d0 F p x =
    finiteRemainder F H p s x + _
  rw [hfinite, hzero]
  change (LatticeMatterGhostCoupling.T D H x + LatticeBRST.ghostCharge D x) -
    d0 F p x = _
  abel

variable {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)

/-- Every original fixed-integral-charge basis input, with no pPlus nonzero or
energy hypothesis. The energy*c0 term has degree +1 even at arbitrary p. -/
theorem full_remainder_fixed_charge_basis_raises
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (i j : StateIndex D t) (hi : i.1.1 = p)
    (hc : (actualBasis F B).repr
      ((LatticeBRST.totalCharge D H - d0 F p) (actualBasis F B i)) j ≠ 0) :
    degree i + 1 ≤ degree j := by
  classical
  by_contra hw
  have hr : (actualBasis F B).repr
      (finiteRemainder F H p (commonModes F H (actualBasis F B i))
        (actualBasis F B i)) j = 0 := by
    by_contra hn
    exact hw (finiteRemainder_fixed_charge_raises F B H hHG hGH p
      (commonModes F H (actualBasis F B i)) i j hi hn)
  have hz : (actualBasis F B).repr
      ((LatticePositiveEnergy.chargeEnergy D p : ℂ) •
        tp (1 : Module.End ℂ (Carrier D)) (c 0) (actualBasis F B i)) j = 0 := by
    by_contra hn
    have hshift := shift_smul (actualBasis F B) degree
      (LatticePositiveEnergy.chargeEnergy D p : ℂ)
      (tensor_ghost_shift F B (c 0) 1 (c_shift 0))
    have he := hshift i j (by simpa only [LinearMap.smul_apply] using hn)
    exact hw (by omega)
  apply hc
  change (actualBasis F B).coord j
    ((LatticeBRST.totalCharge D H - d0 F p) (actualBasis F B i)) = 0
  rw [totalCharge_sub_d0_finite_capture F H p]
  simp only [map_add, Module.Basis.coord_apply, hr, hz, add_zero]

/-- This basis consequence is consumed by the vector inference below. It
reuses the native h*finiteRemainder theorem and degree zero of the genuine h. -/
theorem h_full_remainder_fixed_charge_basis_raises
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (i j : StateIndex D t) (hi : i.1.1 = p)
    (hc : (actualBasis F B).repr
      ((h F B p * (LatticeBRST.totalCharge D H - d0 F p))
        (actualBasis F B i)) j ≠ 0) : degree i + 1 ≤ degree j := by
  classical
  by_contra hw
  have hr : (actualBasis F B).repr
      (h F B p (finiteRemainder F H p (commonModes F H (actualBasis F B i))
        (actualBasis F B i))) j = 0 := by
    by_contra hn
    exact hw (h_finiteRemainder_fixed_charge_raises F B H hHG hGH p
      (commonModes F H (actualBasis F B i)) i j hi hn)
  have hz : (actualBasis F B).repr
      ((LatticePositiveEnergy.chargeEnergy D p : ℂ) •
        h F B p (tp (1 : Module.End ℂ (Carrier D)) (c 0) (actualBasis F B i))) j = 0 := by
    by_contra hn
    have hproduct : Shift (actualBasis F B) degree
        (h F B p * tp (1 : Module.End ℂ (Carrier D)) (c 0)) 1 := by
      simpa only [zero_add] using shift_mul (actualBasis F B) degree
        (h_shift F B p) (tensor_ghost_shift F B (c 0) 1 (c_shift 0))
    have hshift := shift_smul (actualBasis F B) degree
      (LatticePositiveEnergy.chargeEnergy D p : ℂ) hproduct
    have he := hshift i j (by
      simpa only [LinearMap.smul_apply, Module.End.mul_apply] using hn)
    exact hw (by omega)
  apply hc
  change (actualBasis F B).coord j
    (h F B p ((LatticeBRST.totalCharge D H - d0 F p) (actualBasis F B i))) = 0
  rw [totalCharge_sub_d0_finite_capture F H p, map_add, map_smul]
  simp only [map_add, Module.Basis.coord_apply, hr, hz, add_zero]

/- Charge preservation is derived separately from original operator formulas.
It is not inferred from a degree statement, a relative-shell claim or a proposed
global fixed-charge replacement for any of these operators. -/

private theorem current_off_charge (u : LatticeLightConeCoordinates.E D)
    (n : ℤ) (G : Module.End ℂ Fock) (i j : StateIndex D t)
    (hne : j.1.1 ≠ i.1.1) :
    (actualBasis F B).repr (tp (a u n) G (actualBasis F B i)) j = 0 := by
  classical
  rcases i with ⟨⟨p,m⟩,S⟩
  rw [actualBasis_apply, sector_current, sector_coefficient]
  exact ite_eq_right (Ne.symm hne)

private theorem ghost_off_charge (G : Module.End ℂ Fock) (i j : StateIndex D t)
    (hne : j.1.1 ≠ i.1.1) :
    (actualBasis F B).repr
      (tp (1 : Module.End ℂ (Carrier D)) G (actualBasis F B i)) j = 0 := by
  classical
  rcases i with ⟨⟨p,m⟩,S⟩
  rw [actualBasis_apply, ghost_sector, sector_coefficient]
  exact ite_eq_right (Ne.symm hne)

private theorem matter_off_charge
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (n : ℤ)
    (G : Module.End ℂ Fock) (i j : StateIndex D t) (hne : j.1.1 ≠ i.1.1) :
    (actualBasis F B).repr
      (tp (sugawaraMode D H n) G (actualBasis F B i)) j = 0 := by
  classical
  rcases i with ⟨⟨p,m⟩,S⟩
  have haction (Q : PolynomialCoordinates (Label t)) (w : Fock) :
      tp (sugawaraMode D H n) G (sector F B p Q w) =
        sector F B p
          (F.coordinateEquiv B (sectorSugawaraMode D H p n
            ((F.coordinateEquiv B).symm Q))) (G w) := by
    simp only [sector, tp_tmul, sugawaraMode_single_sector,
      AlgEquiv.symm_apply_apply]
  rw [actualBasis_apply, haction, sector_coefficient]
  exact ite_eq_right (Ne.symm hne)

private theorem totalCharge_off_charge
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (i j : StateIndex D t) (hne : j.1.1 ≠ i.1.1) :
    (actualBasis F B).repr (LatticeBRST.totalCharge D H (actualBasis F B i)) j = 0 := by
  classical
  have hT := LatticeMatterGhostCoupling.finite_capture D H (actualBasis F B i)
    (commonModes F H (actualBasis F B i))
    (commonModes_spec F H (actualBasis F B i)).2.1
  have hg : (actualBasis F B).repr
      (LatticeBRST.ghostCharge D (actualBasis F B i)) j = 0 :=
    ghost_off_charge F B D5.S3.Quantum.Fermionic.BcGhostBRST.Qg i j hne
  change (actualBasis F B).coord j
    (LatticeMatterGhostCoupling.T D H (actualBasis F B i) +
      LatticeBRST.ghostCharge D (actualBasis F B i)) = 0
  rw [hT, map_add, map_sum]
  simp only [Module.Basis.coord_apply, hg, add_zero]
  apply Finset.sum_eq_zero
  intro n hn
  exact matter_off_charge F B H n (c (-n)) i j hne

private theorem d0_off_charge (p : Charge D) (i j : StateIndex D t)
    (hne : j.1.1 ≠ i.1.1) :
    (actualBasis F B).repr (d0 F p (actualBasis F B i)) j = 0 := by
  classical
  have hcurrent (u : LatticeLightConeCoordinates.E D) (n : ℤ)
      (G : Module.End ℂ Fock) := current_off_charge F B u n G i j hne
  have hterm (r : ℕ) :
      (actualBasis F B).coord j (dTerm F r (actualBasis F B i)) = 0 := by
    simp only [dTerm, dm, LinearMap.add_apply, map_add,
      Module.Basis.coord_apply, hcurrent, add_zero]
  change (actualBasis F B).coord j (F.pPlus p • unscaledD F (actualBasis F B i)) = 0
  rw [unscaledD, (dFamily F).total_eq_sum (actualBasis F B i)
    (modeBound F (actualBasis F B i)) le_rfl]
  simp only [map_smul, map_sum]
  change F.pPlus p • (∑ r ∈ Finset.range (modeBound F (actualBasis F B i)),
    (actualBasis F B).coord j (dTerm F r (actualBasis F B i))) = 0
  simp only [hterm, Finset.sum_const_zero, smul_zero]

private theorem R_off_charge (p : Charge D) (i j : StateIndex D t)
    (hne : j.1.1 ≠ i.1.1) :
    (actualBasis F B).repr (R F p (actualBasis F B i)) j = 0 := by
  classical
  have hcurrent (u : LatticeLightConeCoordinates.E D) (n : ℤ)
      (G : Module.End ℂ Fock) := current_off_charge F B u n G i j hne
  have hterm (r : ℕ) :
      (actualBasis F B).coord j (rTerm F r (actualBasis F B i)) = 0 := by
    simp only [rTerm, rr, LinearMap.smul_apply, LinearMap.add_apply,
      map_smul, map_add, Module.Basis.coord_apply, hcurrent, add_zero, smul_zero]
  change (actualBasis F B).coord j
    ((F.pPlus p)⁻¹ • unscaledR F (actualBasis F B i)) = 0
  rw [unscaledR, (rFamily F).total_eq_sum (actualBasis F B i)
    (modeBound F (actualBasis F B i)) le_rfl]
  simp only [map_smul, map_sum]
  change (F.pPlus p)⁻¹ • (∑ r ∈ Finset.range (modeBound F (actualBasis F B i)),
    (actualBasis F B).coord j (rTerm F r (actualBasis F B i))) = 0
  simp only [hterm, Finset.sum_const_zero, smul_zero]

private theorem h_off_charge (p : Charge D) (i j : StateIndex D t)
    (hne : j.1.1 ≠ i.1.1) :
    (actualBasis F B).repr (h F B p (actualBasis F B i)) j = 0 := by
  classical
  have hinv : invM F B (actualBasis F B i) =
      (if totalCount i = 0 then (0 : ℂ) else (totalCount i : ℂ)⁻¹) •
        actualBasis F B i := by
    simp only [invM, inverseNumber, diagonal_basis]
  change (actualBasis F B).coord j (R F p (invM F B (actualBasis F B i))) = 0
  rw [hinv, map_smul, map_smul]
  change _ • (actualBasis F B).repr (R F p (actualBasis F B i)) j = 0
  rw [R_off_charge F B p i j hne, smul_zero]

/-- Exactly the original basis-representation charge condition on a vector.
This is a predicate on states, not a certificate replacing an operator. -/
def HasCharge (p : Charge D) (v : State D) : Prop :=
  ∀ i : StateIndex D t, (actualBasis F B).repr v i ≠ 0 → i.1.1 = p

/-- Original full Q, d0 and h preserve actual fixed integral charge on all
algebraic tensor states. No degree, inverse-Gram or shell assumption is used. -/
theorem original_operators_preserve_charge
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (p : Charge D) (v : State D)
    (hv : HasCharge F B p v) :
    HasCharge F B p (LatticeBRST.totalCharge D H v) ∧
      HasCharge F B p (d0 F p v) ∧ HasCharge F B p (h F B p v) := by
  classical
  have extend (A : Module.End ℂ (State D))
      (hA : ∀ i j : StateIndex D t, j.1.1 ≠ i.1.1 →
        (actualBasis F B).repr (A (actualBasis F B i)) j = 0) :
      HasCharge F B p (A v) := by
    intro j hj
    by_contra hq
    apply hj
    change (actualBasis F B).coord j (A v) = 0
    rw [← basis_expand (actualBasis F B) v]
    simp only [map_sum, map_smul, Module.Basis.coord_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hz : (actualBasis F B).repr v i = 0
    · simp [hz]
    · have hne : j.1.1 ≠ i.1.1 := by
        rw [hv i hz]
        exact hq
      rw [hA i j hne, mul_zero]
  exact ⟨extend _ (totalCharge_off_charge F B H),
    extend _ (d0_off_charge F B p), extend _ (h_off_charge F B p)⟩

/-- Actual all-vector inference, consuming finite assembly and the basis
raising statements. On any vector whose ORIGINAL basis support has charge p
and degrees at least a, BOTH original (Q-d0)v and h(Q-d0)v still have charge p
and have degrees at least a+1. The bound a is an explicit INPUT bound, not an
asserted global energy/shell bound. This theorem supplies one honest step for
later iteration; it makes no all-powers or nilpotence assertion. -/
theorem full_remainder_fixed_charge_vectors
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (v : State D) (hv : HasCharge F B p v)
    (a : ℤ) (ha : ∀ i : StateIndex D t,
      (actualBasis F B).repr v i ≠ 0 → a ≤ degree i) :
    (HasCharge F B p ((LatticeBRST.totalCharge D H - d0 F p) v) ∧
      ∀ j : StateIndex D t, (actualBasis F B).repr
        ((LatticeBRST.totalCharge D H - d0 F p) v) j ≠ 0 → a + 1 ≤ degree j) ∧
    (HasCharge F B p ((h F B p * (LatticeBRST.totalCharge D H - d0 F p)) v) ∧
      ∀ j : StateIndex D t, (actualBasis F B).repr
        ((h F B p * (LatticeBRST.totalCharge D H - d0 F p)) v) j ≠ 0 →
          a + 1 ≤ degree j) := by
  classical
  have hpres := original_operators_preserve_charge F B H p v hv
  have hdcharge : HasCharge F B p ((LatticeBRST.totalCharge D H - d0 F p) v) := by
    intro j hj
    by_cases hq : (actualBasis F B).repr (LatticeBRST.totalCharge D H v) j = 0
    · apply hpres.2.1 j
      intro hz
      exact hj (by simp [LinearMap.sub_apply, hq, hz])
    · exact hpres.1 j hq
  have hhcharge :
      HasCharge F B p ((h F B p * (LatticeBRST.totalCharge D H - d0 F p)) v) :=
    (original_operators_preserve_charge F B H p
      ((LatticeBRST.totalCharge D H - d0 F p) v) hdcharge).2.2
  have raise_vector (A : Module.End ℂ (State D))
      (hA : ∀ i j : StateIndex D t, i.1.1 = p →
        (actualBasis F B).repr (A (actualBasis F B i)) j ≠ 0 →
          degree i + 1 ≤ degree j) :
      ∀ j : StateIndex D t, (actualBasis F B).repr (A v) j ≠ 0 →
        a + 1 ≤ degree j := by
    intro j hj
    by_contra hw
    apply hj
    change (actualBasis F B).coord j (A v) = 0
    rw [← basis_expand (actualBasis F B) v]
    simp only [map_sum, map_smul, Module.Basis.coord_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hz : (actualBasis F B).repr v i = 0
    · simp [hz]
    · by_cases hAi : (actualBasis F B).repr (A (actualBasis F B i)) j = 0
      · simp [hAi]
      · have hstep := hA i j (hv i hz) hAi
        have hinput := ha i hz
        exact False.elim (hw (by omega))
  exact ⟨⟨hdcharge, raise_vector _
      (full_remainder_fixed_charge_basis_raises F B H hHG hGH p)⟩,
    ⟨hhcharge, raise_vector _
      (h_full_remainder_fixed_charge_basis_raises F B H hHG hGH p)⟩⟩

end D5.S3.VertexAlgebra.LatticeBRSTFullOriginalRaising
