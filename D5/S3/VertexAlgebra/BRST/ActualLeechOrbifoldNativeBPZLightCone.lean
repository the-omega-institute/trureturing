/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldNativeBPZLightCone
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldNativeBPZLightCone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Null-oscillator contractions and BPZ pairing of corrected relative representatives. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldNativeBPZ
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCohomology
import D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws

/-! The light-cone filtration preserves the native BPZ pairing on corrected representatives. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.NativeBPZ

open ActualLeechOrbifoldMatter (Orbifold)
open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open LatticeGeneratingFieldLocality (Charge Oscillator)
open LatticeLightConeCoordinates (NullFrame PolynomialCoordinates chargeVector g g_smul_right
  polynomialCurrent)
open LatticeLightConeCoordinates.NullFrame (Label plus minus)
open LatticeQuartetContraction (Variables Exponents StateIndex actualBasis actualBasis_apply sector)
open LatticeBRSTModeFiltration (degree exponentDegree variableWeight weight_plus weight_minus
  exponentDegree_add exponentDegree_single X_mul_monomial single_add_sub derivative_monomial
  derivative_coefficient derivative_support_degree)
open SourceBPZ.OriginalSourcePairing
open RelativeCohomology (OrbifoldWeight groundEquiv groundEquiv_symm_value input representative)
open D5.S3.Quantum.Fermionic
open CountableOccupationFock (ket)
open BcGhostFock (c)
open BcGhostCharge (charge)
open BcGhostBilinear
open BcGhostHermitian (partner mem_partner relativePartner charge_relativePartner
  c_zero create_coefficient)
open MvPolynomial (X monomial pderiv)
open D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation (K)

open private integerWick_neutral from D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws
open private rightSlices_expand from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightCone
open private ground_filtration nilpotent K_preserves_filtration from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCohomology
open private K_inverse from D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation
open private planeWick_one tensor_pairing_tmul from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldNativeBPZ

local instance : AddCommGroup ComplexState := TensorProduct.addCommGroup
local instance (p : Charge hyperbolicPlane) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup (relativeShell p)

variable (F : NullFrame hyperbolicPlane) (B : Module.Basis (Fin 0) ℂ F.K)

private def oppositeVariable : Variables 0 → Variables 0
  | (.inl _, r) => (minus 0, r)
  | (.inr (.inl _), r) => (plus 0, r)
  | (.inr (.inr j), _) => Fin.elim0 j

private theorem weight_opposite (x : Variables 0) :
    variableWeight (oppositeVariable x) = -variableWeight x := by
  rcases x with ⟨u | (u | j), r⟩
  · cases u
    change variableWeight (minus 0, r) = -variableWeight (plus 0, r)
    rw [weight_minus, weight_plus]
  · cases u
    change variableWeight (plus 0, r) = -variableWeight (minus 0, r)
    rw [weight_plus, weight_minus, neg_neg]
  · exact Fin.elim0 j

private abbrev PlanePolynomial := PolynomialCoordinates (Label 0)

private def frameWick : LinearMap.BilinForm ℂ PlanePolynomial :=
  (integerWick hyperbolicPlane).compl₁₂
    (F.coordinateEquiv B).symm.toLinearMap (F.coordinateEquiv B).symm.toLinearMap

private theorem frameWick_symmetric (P Q : PlanePolynomial) :
    frameWick F B P Q = frameWick F B Q P :=
  integerWick_symmetric hyperbolicPlane _ _

private theorem integerWick_current (u : LatticeLightConeCoordinates.E hyperbolicPlane) (n : ℤ)
    (P Q : Oscillator hyperbolicPlane) :
    integerWick hyperbolicPlane (polynomialCurrent u 0 n P) Q =
      -integerWick hyperbolicPlane P (polynomialCurrent u 0 (-n) Q) := by
  classical
  simp only [polynomialCurrent, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [integerWick_neutral hyperbolicPlane i 0 n, neg_zero, smul_neg]

set_option maxHeartbeats 600000 in
-- Both recurrences come from the same signed integer Wick transpose.
private theorem frameWick_creation (x : Variables 0) (P Q : PlanePolynomial) :
    frameWick F B (X x * P) Q =
      -frameWick F B P ((x.2 + 1 : ℂ) • pderiv (oppositeVariable x) Q) := by
  let e := F.coordinateEquiv B
  have transpose (u : LatticeLightConeCoordinates.E hyperbolicPlane)
      (hP : e (polynomialCurrent u 0 (-(x.2 : ℤ) - 1) (e.symm P)) = X x * P)
      (hQ : e (polynomialCurrent u 0 ((x.2 : ℤ) + 1) (e.symm Q)) =
        (x.2 + 1 : ℂ) • pderiv (oppositeVariable x) Q) :
      frameWick F B (X x * P) Q =
        -frameWick F B P ((x.2 + 1 : ℂ) • pderiv (oppositeVariable x) Q) := by
    change integerWick hyperbolicPlane (e.symm (X x * P)) (e.symm Q) =
      -integerWick hyperbolicPlane (e.symm P)
        (e.symm ((x.2 + 1 : ℂ) • pderiv (oppositeVariable x) Q))
    rw [← hP, ← hQ]
    simpa only [AlgEquiv.symm_apply_apply,
      show -(-(x.2 : ℤ) - 1) = (x.2 : ℤ) + 1 by omega] using
        integerWick_current u (-(x.2 : ℤ) - 1) (e.symm P) (e.symm Q)
  rcases x with ⟨u | (u | j), r⟩
  · cases u
    exact transpose F.ePlus
      (by simpa only [e, plus, AlgEquiv.apply_symm_apply] using F.creation_plus B 0 r (e.symm P))
      (by simpa only [e, oppositeVariable, AlgEquiv.apply_symm_apply] using
        F.annihilation_plus B 0 r (e.symm Q))
  · cases u
    exact transpose F.eMinus
      (by simpa only [e, minus, AlgEquiv.apply_symm_apply] using F.creation_minus B 0 r (e.symm P))
      (by simpa only [e, oppositeVariable, AlgEquiv.apply_symm_apply] using
        F.annihilation_minus B 0 r (e.symm Q))
  · exact Fin.elim0 j

private theorem frameWick_monomial_orthogonal (m n : Exponents 0)
    (h : exponentDegree m + exponentDegree n ≠ 0) :
    frameWick F B (monomial m 1) (monomial n 1) = 0 := by
  classical
  suffices aux : ∀ N : ℕ, ∀ m n : Exponents 0, m.degree = N →
      exponentDegree m + exponentDegree n ≠ 0 →
      frameWick F B (monomial m 1) (monomial n 1) = 0 from aux m.degree m n rfl h
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro m n hN hdeg
    by_cases hm : m = 0
    · subst m
      have hn : n ≠ 0 := by
        rintro rfl
        simp [exponentDegree] at hdeg
      obtain ⟨x, hx⟩ := Finsupp.support_nonempty_iff.mpr hn
      have hnX : X x * monomial (n - Finsupp.single x 1) (1 : ℂ) = monomial n 1 := by
        rw [X_mul_monomial, single_add_sub x n (Finsupp.mem_support_iff.mp hx)]
      rw [frameWick_symmetric F B, ← hnX, frameWick_creation,
        MvPolynomial.monomial_zero', MvPolynomial.C_1, MvPolynomial.pderiv_one,
        smul_zero, map_zero, neg_zero]
    · obtain ⟨x, hx⟩ := Finsupp.support_nonempty_iff.mpr hm
      let m' := m - Finsupp.single x 1
      let y := oppositeVariable x
      let n' := n - Finsupp.single y 1
      have hm' : Finsupp.single x 1 + m' = m :=
        single_add_sub x m (Finsupp.mem_support_iff.mp hx)
      have hmX : X x * monomial m' (1 : ℂ) = monomial m 1 := by
        rw [X_mul_monomial, hm']
      rw [← hmX, frameWick_creation, derivative_monomial]
      by_cases hy : n y = 0
      · change n (oppositeVariable x) = 0 at hy
        rw [hy, Nat.cast_zero, zero_smul, smul_zero, map_zero, neg_zero]
      · have hcoef : (pderiv y (monomial n (1 : ℂ))).coeff n' ≠ 0 := by
          change (pderiv y (monomial n (1 : ℂ))).coeff (n - Finsupp.single y 1) ≠ 0
          rw [derivative_coefficient, ite_eq_left rfl]
          exact_mod_cast hy
        have hnDegree := derivative_support_degree y n n' hcoef
        have hmDegree := congrArg exponentDegree hm'
        rw [exponentDegree_add, exponentDegree_single, Nat.cast_one, one_mul] at hmDegree
        have hyWeight : variableWeight y = -variableWeight x := weight_opposite x
        have htotal := congrArg Finsupp.degree hm'
        rw [map_add, Finsupp.degree_single, hN] at htotal
        have hsmaller : m'.degree < N := by omega
        have hrec : exponentDegree m' + exponentDegree n' ≠ 0 := by omega
        change -frameWick F B (monomial m' 1)
          ((x.2 + 1 : ℂ) • ((n y : ℂ) • monomial n' 1)) = 0
        rw [smul_smul, map_smul, ih _ hsmaller _ _ rfl hrec, smul_zero, neg_zero]

private theorem ghost_c0_ket_orthogonal (S T : Finset ℕ) (h : charge S + charge T ≠ 2) :
    Bg (ket S) (c 0 (ket T)) = 0 := by
  classical
  by_cases hS : 3 ∈ S
  · have hp : 3 ∉ partner S := by
      rw [mem_partner]
      simp [BcGhostHermitian.E, BcGhostHermitian.tau, hS]
    rw [Bg_ket_coefficient, c_zero, create_coefficient, ite_eq_right hp, mul_zero]
  · have hT : relativePartner S ≠ T := by
      intro he
      apply h
      rw [← he]
      exact charge_relativePartner S hS
    rw [Bg_c0_ket_coefficient S hS]
    simp [ket, Ne.symm hT]

/-- The relative form in the native light-cone tensor association. -/
def assocRelativePairing : LinearMap.BilinForm ℂ AssocState :=
  relativePairing.compl₁₂ reassoc.symm.toLinearMap reassoc.symm.toLinearMap

private theorem assocRelativePairing_tmul (v w : Orbifold) (p q : Charge hyperbolicPlane)
    (P Q : Oscillator hyperbolicPlane) (S T : Finset ℕ) :
    assocRelativePairing (v ⊗ₜ[ℂ] (Finsupp.single p P ⊗ₜ[ℂ] ket S))
      (w ⊗ₜ[ℂ] (Finsupp.single q Q ⊗ₜ[ℂ] ket T)) =
      Bg (ket S) (c 0 (ket T)) *
        (sourcePairing hyperbolicPlane (Finsupp.single p P) (Finsupp.single q Q) *
          orbifoldPairing v w) := by
  change relativePairing
    ((TensorProduct.assoc ℂ _ _ _).symm (v ⊗ₜ[ℂ] (Finsupp.single p P ⊗ₜ[ℂ] ket S)))
    ((TensorProduct.assoc ℂ _ _ _).symm (w ⊗ₜ[ℂ] (Finsupp.single q Q ⊗ₜ[ℂ] ket T))) = _
  rw [TensorProduct.assoc_symm_tmul, TensorProduct.assoc_symm_tmul, relativePairing_tmul]
  rw [matterPairing, tensor_pairing_tmul]

/-- Nonzero relative BPZ coefficients in a common null frame have opposite degrees. -/
theorem relativePairing_basis_orthogonal
    (v w : Orbifold) (i j : StateIndex hyperbolicPlane 0) (hij : degree i + degree j ≠ 0) :
    assocRelativePairing (v ⊗ₜ[ℂ] actualBasis F B i) (w ⊗ₜ[ℂ] actualBasis F B j) = 0 := by
  classical
  rcases i with ⟨⟨p, m⟩, S⟩
  rcases j with ⟨⟨q, n⟩, T⟩
  change (exponentDegree m + charge S - 1) + (exponentDegree n + charge T - 1) ≠ 0 at hij
  simp only [actualBasis_apply, sector, assocRelativePairing_tmul]
  by_cases hcharge : charge S + charge T = 2
  · have hmn : exponentDegree m + exponentDegree n ≠ 0 := by omega
    rw [sourcePairing_single_single]
    split_ifs
    · change Bg (ket S) (c 0 (ket T)) * (frameWick F B (monomial m 1) (monomial n 1) *
        orbifoldPairing v w) = 0
      rw [frameWick_monomial_orthogonal F B m n hmn, zero_mul, mul_zero]
    · rw [zero_mul, mul_zero]
  · rw [ghost_c0_ket_orthogonal S T hcharge, zero_mul]

set_option maxHeartbeats 600000 in
-- Expanding both sums elaborates the nested tensor-product and Finsupp linear maps.
/-- The native lower filtrations are orthogonal when their bounds sum to a positive number. -/
theorem relativePairing_momentumFiltration_orthogonal
    {p q : Charge hyperbolicPlane} {a d : ℤ} {x y : AssocState}
    (hx : x ∈ momentumFiltration F B p a) (hy : y ∈ momentumFiltration F B q d)
    (had : 0 < a + d) :
    assocRelativePairing x y = 0 := by
  classical
  calc
    assocRelativePairing x y = assocRelativePairing
        (∑ i ∈ (rightSlices F B x).support,
          rightSlice F B i x ⊗ₜ[ℂ] actualBasis F B i)
        (∑ j ∈ (rightSlices F B y).support,
          rightSlice F B j y ⊗ₜ[ℂ] actualBasis F B j) :=
      congrArg₂ (fun u v => assocRelativePairing u v)
        (rightSlices_expand F B x) (rightSlices_expand F B y)
    _ = 0 := by
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro j hj
      rw [map_sum, LinearMap.sum_apply]
      apply Finset.sum_eq_zero
      intro i hi
      have hdi := ((mem_momentumFiltration_iff F B p a x).mp hx i
        (Finsupp.mem_support_iff.mp hi)).2
      have hdj := ((mem_momentumFiltration_iff F B q d y).mp hy j
        (Finsupp.mem_support_iff.mp hj)).2
      exact relativePairing_basis_orthogonal F B _ _ i j (by omega)

private theorem representative_filtration (p : Charge hyperbolicPlane) (hp : F.pPlus p ≠ 0)
    (v : OrbifoldWeight p) :
    (representative F B p hp v).val ∈ momentumFiltration F B p 0 := by
  let u := (groundEquiv F B p hp).symm v
  change (K (input F B p hp) (nilpotent F B p hp) u.val).val ∈ momentumFiltration F B p 0
  exact K_preserves_filtration F B p hp 0 u.val (ground_filtration F B p hp u)

private theorem representative_sub_ground_filtration
    (p : Charge hyperbolicPlane) (hp : F.pPlus p ≠ 0) (v : OrbifoldWeight p) :
    (representative F B p hp v).val - ((groundEquiv F B p hp).symm v).val.val ∈
      momentumFiltration F B p 1 := by
  let u := (groundEquiv F B p hp).symm v
  let r := representative F B p hp v
  have hr : r + relativeH F B p (relativeDelta F B p r) = u.val := by
    have hrK : r = K (input F B p hp) (nilpotent F B p hp) u.val := rfl
    have hH : (input F B p hp).h = relativeH F B p := rfl
    have hδ : (input F B p hp).delta = relativeDelta F B p := rfl
    have he := DFunLike.congr_fun (K_inverse (input F B p hp) (nilpotent F B p hp)).2 u.val
    rw [hrK]
    simpa only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply, hH, hδ] using he
  have hsub : r - u.val = -relativeH F B p (relativeDelta F B p r) := by
    rw [← hr, sub_add_eq_sub_sub, sub_self, zero_sub]
  change (r - u.val).val ∈ momentumFiltration F B p 1
  rw [hsub]
  exact (momentumFiltration F B p 1).neg_mem
    (relative_remainder_raises F B p 0 r (representative_filtration F B p hp v)).2

private theorem opposite_plus_ne_zero (p : Charge hyperbolicPlane) (hp : F.pPlus p ≠ 0) :
    F.pPlus (-p) ≠ 0 := by
  have hvec : chargeVector (-p) = (-1 : ℂ) • chargeVector p := by
    funext i
    simp [chargeVector, Pi.neg_apply]
  change g hyperbolicPlane F.ePlus (chargeVector (-p)) ≠ 0
  rw [hvec, g_smul_right, neg_one_mul]
  exact neg_ne_zero.mpr hp

/-- The corrected native representatives in a common frame retain exactly the orbifold pairing. -/
theorem relativePairing_representative
    (p : Charge hyperbolicPlane) (hp : F.pPlus p ≠ 0)
    (v : OrbifoldWeight p) (w : OrbifoldWeight (-p)) :
    relativePairing (reassoc.symm (representative F B p hp v).val)
      (reassoc.symm (representative F B (-p) (opposite_plus_ne_zero F p hp) w).val) =
      orbifoldPairing v.val w.val := by
  let hq := opposite_plus_ne_zero F p hp
  let r := (representative F B p hp v).val
  let s := (representative F B (-p) hq w).val
  let u := (groundEquiv F B p hp).symm v
  let z := (groundEquiv F B (-p) hq).symm w
  have hrs : assocRelativePairing (r - u.val.val) s = 0 :=
    relativePairing_momentumFiltration_orthogonal F B
      (representative_sub_ground_filtration F B p hp v)
      (representative_filtration F B (-p) hq w) (by omega)
  have huz : assocRelativePairing u.val.val (s - z.val.val) = 0 :=
    relativePairing_momentumFiltration_orthogonal F B
      (ground_filtration F B p hp u)
      (representative_sub_ground_filtration F B (-p) hq w) (by omega)
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at hrs
  rw [map_sub, sub_eq_zero] at huz
  change assocRelativePairing r s = orbifoldPairing v.val w.val
  calc
    assocRelativePairing r s = assocRelativePairing u.val.val z.val.val := hrs.trans huz
    _ = orbifoldPairing v.val w.val := by
      dsimp only [u, z]
      rw [groundEquiv_symm_value, groundEquiv_symm_value,
        BcGhostQuartetCount.c1vac_eq, assocRelativePairing_tmul, Bg_c0_ket_one,
        sourcePairing_single_single, ite_eq_left rfl, planeWick_one, one_mul, one_mul]

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.NativeBPZ
