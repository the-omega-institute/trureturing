/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalPureDown
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalPureDown
   mirror-E: none(waiver:source-candidate-not-enrolled)
   anchors: []
   utility: none
   digest: Actual finite-HPL pure-down support and global primary representatives. -/

import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPureDownHomotopy
import D5.S3.VertexAlgebra.Lattice.LatticeNullFrameExistence
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTNeutralPhysicalCartan
import Batteries.Tactic.OpenPrivate

/-!
SOURCE ONLY, UNCOMPILED. No kernel, Reg, or publication claim.

The differential, h = R invM, finiteInput, K, physicalLift and global
physicalClass below are the original maps. The only support argument added
here is invariance of the actual plus/transverse polynomial space, followed
by the actual homotopy formulas on its finite monomial expansion. No
explicit U^r formula, positive metric, real frame, or integral inverse is
used. Signed input levels are never replaced by natural levels in a claim.

Attribution: the original lattice Sugawara/current and occupation-CAR
suppliers; BRST (Becchi--Rouet--Stora--Tyutin), Kato--Ogawa,
Lian--Zuckerman and finite HPL (Gugenheim--Lambe--Stasheff); Mathlib
polynomial, linear and finite-support algebra. The supplied Pro advisory
suggested the invariant-space route; the source maps are authoritative.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct

open private sector_add sector_smul from
  D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction
open private fixed_charge_transport lin_single polynomialEquiv_symm_X completeBasis_plus from
  D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates
open private sugawaraMode_a_commutator from
  D5.S3.VertexAlgebra.Lattice.LatticeRelativeBRSTGround
open private noMinus_derivative from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPureDownHomotopy
open private Qg_down c_one_down c_high_down project_physical
  neutral_number_one_shell cartan_basis_tensor cartanLabel from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTNeutralPhysicalCartan
open private b_nonnegative_down from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPureGhostPrimary
open private chargeProject_mem from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology
open private number_ket from D5.S3.Quantum.Fermionic.BcGhostCharge
open private d0_common_capture from
  D5.S3.VertexAlgebra.Lattice.LatticeBRSTFullOriginalRaising
open private inclusion_expansion from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalTransverseRealization

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPureDown

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeLightConeCoordinates
open LatticeLightConeCoordinates.NullFrame
open LatticeQuartetContraction hiding State
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPureDownHomotopy D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPureGhostPrimary
open LatticeBRSTModeFiltration (derivative_monomial X_mul_monomial cm cm_plus_positive)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPerturbationFiltration D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTFiniteTransfer
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalTransverseRealization LatticeBRSTFullOriginalRaising
open LatticeRelativeBRSTCohomology.Ground (energyTarget)
open LatticeMatterGhostCoupling LatticeMatterGhostDegree
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTNeutralPhysicalCartan
open D5.S3.Quantum.Fermionic CountableOccupationFock
open D5.S3.HomologicalAlgebra MvPolynomial

/-- Finite polynomials in the actual plus and transverse creators. -/
def noMinusPolynomials (t : ℕ) : Submodule ℂ (PolynomialCoordinates (Label t)) :=
  Submodule.span ℂ {P | ∃ e : Exponents t, NoMinus e ∧ P = monomial e 1}

/-- The plus-generated ideal inside the no-minus polynomial algebra, written
as its finite monomial span. Every generator visibly contains a plus creator. -/
def plusCorrections (t : ℕ) : Submodule ℂ (PolynomialCoordinates (Label t)) :=
  Submodule.span ℂ {P | ∃ (r : ℕ) (e : Exponents t),
    NoMinus e ∧ P = X (plus t,r) * monomial e 1}

private theorem one_noMinus (t : ℕ) : (1 : PolynomialCoordinates (Label t)) ∈
    noMinusPolynomials t := by
  apply Submodule.subset_span
  exact ⟨0, by intro r; rfl, by simp⟩

private theorem monomial_noMinus {t : ℕ} (e : Exponents t) (he : NoMinus e) :
    monomial e (1 : ℂ) ∈ noMinusPolynomials t :=
  Submodule.subset_span ⟨e,he,rfl⟩

private theorem mul_X_noMinus {t : ℕ} (x : Variables t) (hx : x.1 ≠ minus t)
    (P : PolynomialCoordinates (Label t)) (hP : P ∈ noMinusPolynomials t) :
    X x * P ∈ noMinusPolynomials t := by
  classical
  induction hP using Submodule.span_induction with
  | mem Q hQ =>
      obtain ⟨e,he,rfl⟩ := hQ
      rw [X_mul_monomial]
      apply monomial_noMinus
      intro r
      have hx' : x ≠ (minus t,r) := fun h => hx (congrArg Prod.fst h)
      simp [Finsupp.single_apply, hx', he r]
  | zero => simp
  | add Q R hQ hR iQ iR =>
      simpa only [mul_add] using (noMinusPolynomials t).add_mem iQ iR
  | smul a Q hQ iQ =>
      simpa only [mul_smul_comm] using (noMinusPolynomials t).smul_mem a iQ

private theorem plusCorrections_le (t : ℕ) :
    plusCorrections t ≤ noMinusPolynomials t := by
  apply Submodule.span_le.mpr
  rintro P ⟨r,e,he,rfl⟩
  exact mul_X_noMinus (plus t,r) (by simp [plus,minus]) _ (monomial_noMinus e he)

private theorem derivative_noMinus {t : ℕ} (x : Variables t)
    (P : PolynomialCoordinates (Label t)) (hP : P ∈ noMinusPolynomials t) :
    pderiv x P ∈ noMinusPolynomials t := by
  classical
  induction hP using Submodule.span_induction with
  | mem Q hQ =>
      obtain ⟨e,he,rfl⟩ := hQ
      rw [derivative_monomial]
      apply (noMinusPolynomials t).smul_mem
      apply monomial_noMinus
      intro r
      simp [Finsupp.tsub_apply, he r]
  | zero => simp
  | add Q R hQ hR iQ iR => simpa only [map_add] using
      (noMinusPolynomials t).add_mem iQ iR
  | smul a Q hQ iQ => simpa only [smul_eq_C_mul, pderiv_C_mul] using
      (noMinusPolynomials t).smul_mem a iQ

private theorem minus_derivative_zero {t : ℕ}
    (P : PolynomialCoordinates (Label t)) (hP : P ∈ noMinusPolynomials t) (r : ℕ) :
    pderiv (minus t,r) P = 0 := by
  induction hP using Submodule.span_induction with
  | mem Q hQ =>
      obtain ⟨e,he,rfl⟩ := hQ
      exact noMinus_derivative e he r
  | zero => simp
  | add Q R hQ hR iQ iR => simp only [map_add, iQ, iR, add_zero]
  | smul a Q hQ iQ => simp only [smul_eq_C_mul, pderiv_C_mul, iQ, mul_zero]

/- Restricted polynomial induction, derived from the actual finite exponent
induction. In particular, no inference about a summand is made from a
possibly cancelling sum of coefficients. -/
private theorem noMinus_induction {t : ℕ}
    {M : PolynomialCoordinates (Label t) → Prop}
    (hone : M 1)
    (hadd : ∀ P Q, M P → M Q → M (P+Q))
    (hsmul : ∀ (a : ℂ) P, M P → M (a • P))
    (hmul : ∀ (x : Variables t) P, x.1 ≠ minus t → M P → M (X x * P))
    (P : PolynomialCoordinates (Label t)) (hP : P ∈ noMinusPolynomials t) : M P := by
  have hmono (e : Exponents t) : NoMinus e → M (monomial e 1) := by
    apply @Finsupp.induction (Variables t) ℕ _ _ e
    · intro he
      simpa only [monomial_zero', C_1] using hone
    · intro x n e hxe hn ih he
      have he' : NoMinus e := by
        intro r
        have hz := he r
        simp only [Finsupp.add_apply] at hz
        omega
      have hx : x.1 ≠ minus t := by
        intro hxm
        have hz := he x.2
        have heq : x = (minus t,x.2) := Prod.ext hxm rfl
        have hs : (Finsupp.single x n) (minus t,x.2) = n := by
          rw [← heq, Finsupp.single_eq_same]
        simp only [Finsupp.add_apply, hs] at hz
        omega
      have hk (k : ℕ) : M (monomial e 1 * X x ^ k) := by
        induction k with
        | zero => simpa only [pow_zero, mul_one] using ih he'
        | succ k ik =>
            have heq : monomial e (1 : ℂ) * X x ^ (k+1) =
                X x * (monomial e 1 * X x ^ k) := by rw [pow_succ]; ring
            rw [heq]
            exact hmul x _ hx ik
      simpa only [add_comm (Finsupp.single x n) e, monomial_add_single] using hk n
  induction hP using Submodule.span_induction with
  | mem Q hQ =>
      obtain ⟨e,he,rfl⟩ := hQ
      exact hmono e he
  | zero => simpa only [zero_smul] using hsmul 0 1 hone
  | add Q R hQ hR iQ iR => exact hadd Q R iQ iR
  | smul a Q hQ iQ => exact hsmul a Q iQ

private theorem rename_noMinus {t : ℕ} (f : MvPolynomial (Fin t × ℕ) ℂ) :
    rename transverseVariable f ∈ noMinusPolynomials t := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa only [map_C, C_eq_smul_one] using
      (noMinusPolynomials t).smul_mem a (one_noMinus t)
  | add f g hf hg => simpa only [map_add] using (noMinusPolynomials t).add_mem hf hg
  | mul_X f x hf =>
      simpa only [map_mul, rename_X, mul_comm] using
        mul_X_noMinus (transverseVariable x) (by simp [transverseVariable,transverse,minus])
          _ hf

section ActualOperators

variable {D : LatticeData} (F : NullFrame D) {t : ℕ}
  (B : Module.Basis (Fin t) ℂ F.K)

private def matterMap (p : Charge D) : PolynomialCoordinates (Label t) →ₗ[ℂ] Carrier D :=
  (Finsupp.lsingle p).comp (F.coordinateEquiv B).symm.toLinearEquiv.toLinearMap

private def matterSpace (p : Charge D) : Submodule ℂ (Carrier D) :=
  (noMinusPolynomials t).map (matterMap F B p)

private def sectorMap (p : Charge D) (g : Fock) :
    PolynomialCoordinates (Label t) →ₗ[ℂ] State D :=
  ((TensorProduct.mk ℂ (Carrier D) Fock).flip g).comp (matterMap F B p)

private def downSpace (p : Charge D) : Submodule ℂ (State D) :=
  (noMinusPolynomials t).map (sectorMap F B p (ket {1}))

private def downCorrections (p : Charge D) : Submodule ℂ (State D) :=
  (plusCorrections t).map (sectorMap F B p (ket {1}))

private theorem downCorrections_le (p : Charge D) :
    downCorrections F B p ≤ downSpace F B p := by
  rintro x ⟨P,hP,rfl⟩
  exact ⟨P,plusCorrections_le t hP,rfl⟩

private theorem current_matterMap (u : E D) (p : Charge D) (n : ℤ)
    (P : PolynomialCoordinates (Label t)) :
    a u n (matterMap F B p P) = matterMap F B p (cm F B u p n P) := by
  change a u n (Finsupp.single p ((F.coordinateEquiv B).symm P)) =
    Finsupp.single p ((F.coordinateEquiv B).symm (cm F B u p n P))
  rw [a_single]
  congr 1
  apply (F.coordinateEquiv B).injective
  rw [fixed_charge_transport, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

private theorem current_nonnegative_noMinus (u : E D) (p : Charge D)
    (n : ℤ) (hn : 0 ≤ n) (P : PolynomialCoordinates (Label t))
    (hP : P ∈ noMinusPolynomials t) :
    cm F B u p n P ∈ noMinusPolynomials t := by
  classical
  by_cases hz : n = 0
  · subst n
    simpa [cm,coordinatePolynomialMode] using
      (noMinusPolynomials t).smul_mem (g D u (chargeVector p)) hP
  · change coordinatePolynomialMode (F.completeBasis B) u p n P ∈ noMinusPolynomials t
    rw [coordinatePolynomialMode, if_neg (by omega), if_neg hz]
    change (n : ℂ) • coordinateDerivative (F.completeBasis B) u (n-1).toNat P ∈ _
    apply (noMinusPolynomials t).smul_mem
    have hs : (∑ c : Label t, g D u (F.completeBasis B c) •
        pderiv (c,(n-1).toNat) P) ∈ noMinusPolynomials t := by
      apply (noMinusPolynomials t).sum_mem
      intro c hc
      exact (noMinusPolynomials t).smul_mem _ (derivative_noMinus _ P hP)
    simpa [coordinateDerivative] using hs

private theorem basis_current_noMinus (c : Label t) (hc : c ≠ minus t)
    (p : Charge D) (n : ℤ) (P : PolynomialCoordinates (Label t))
    (hP : P ∈ noMinusPolynomials t) :
    cm F B (F.completeBasis B c) p n P ∈ noMinusPolynomials t := by
  classical
  by_cases hn : n < 0
  · have he : (F.completeBasis B).equivFun (F.completeBasis B c) =
        Pi.single c (1 : ℂ) := by
      ext d
      simp [Module.Basis.equivFun_apply, Pi.single_apply, eq_comm]
    change coordinatePolynomialMode (F.completeBasis B) (F.completeBasis B c) p n P ∈
      noMinusPolynomials t
    rw [coordinatePolynomialMode, if_pos hn]
    change lin (-n-1).toNat ((F.completeBasis B).equivFun (F.completeBasis B c)) * P ∈ _
    rw [he,lin_single]
    exact mul_X_noMinus (c,(-n-1).toNat) hc P hP
  · by_cases hp : c = plus t ∧ 0 < n
    · obtain ⟨rfl,hpos⟩ := hp
      have he : n = (((n-1).toNat : ℕ) : ℤ)+1 := by omega
      rw [completeBasis_plus, he, cm_plus_positive,
        minus_derivative_zero P hP, smul_zero]
      exact (noMinusPolynomials t).zero_mem
    · exact current_nonnegative_noMinus F B _ p n (by omega) P hP

private theorem basis_current_matterSpace (c : Label t) (hc : c ≠ minus t)
    (p : Charge D) (n : ℤ) (v : Carrier D) (hv : v ∈ matterSpace F B p) :
    a (F.completeBasis B c) n v ∈ matterSpace F B p := by
  obtain ⟨P,hP,rfl⟩ := hv
  rw [current_matterMap]
  exact ⟨_,basis_current_noMinus F B c hc p n P hP,rfl⟩

private theorem nonnegative_current_matterSpace (u : E D) (p : Charge D)
    (n : ℤ) (hn : 0 ≤ n) (v : Carrier D) (hv : v ∈ matterSpace F B p) :
    a u n v ∈ matterSpace F B p := by
  obtain ⟨P,hP,rfl⟩ := hv
  rw [current_matterMap]
  exact ⟨_,current_nonnegative_noMinus F B u p n hn P hP,rfl⟩

private theorem creation_matterMap (x : Variables t) (p : Charge D)
    (P : PolynomialCoordinates (Label t)) :
    matterMap F B p (X x * P) =
      a (F.completeBasis B x.1) (-(x.2 : ℤ)-1) (matterMap F B p P) := by
  change Finsupp.single p ((F.coordinateEquiv B).symm (X x * P)) =
    a (F.completeBasis B x.1) (-(x.2 : ℤ)-1)
      (Finsupp.single p ((F.coordinateEquiv B).symm P))
  rw [a_single, polynomialCurrent_negative, map_mul, polynomialEquiv_symm_X]

/- The actual current commutator proves invariance, with no expansion of L
into an invented differential operator. The induction treats ALL modes of
the shifted current m-r, including zero and negative shifted modes. -/
private theorem sugawara_nonnegative_matterSpace
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (m : ℤ) (hm : 0 ≤ m)
    (v : Carrier D) (hv : v ∈ matterSpace F B p) :
    sugawaraMode D H m v ∈ matterSpace F B p := by
  obtain ⟨P,hP,rfl⟩ := hv
  suffices hh : P ∈ noMinusPolynomials t ∧
      sugawaraMode D H m (matterMap F B p P) ∈ matterSpace F B p from hh.2
  apply noMinus_induction
    (M := fun Q => Q ∈ noMinusPolynomials t ∧
      sugawaraMode D H m (matterMap F B p Q) ∈ matterSpace F B p)
    (P := P) (hP := hP)
  · refine ⟨one_noMinus t, ?_⟩
    have hg : Finsupp.single p (1 : Oscillator D) ∈ matterSpace F B p := by
      simpa [matterMap] using
        (show matterMap F B p 1 ∈ matterSpace F B p from ⟨1,one_noMinus t,rfl⟩)
    suffices hh : sugawaraMode D H m (Finsupp.single p 1) ∈ matterSpace F B p by
      simpa [matterMap] using hh
    by_cases hz : m = 0
    · subst m
      rw [LatticeSugawaraVirasoro.sugawaraMode_ground_zero]
      exact (matterSpace F B p).smul_mem _ hg
    · rw [LatticeSugawaraVirasoro.sugawaraMode_ground_positive D H p m (by omega)]
      exact (matterSpace F B p).zero_mem
  · intro Q R hQ hR
    refine ⟨(noMinusPolynomials t).add_mem hQ.1 hR.1, ?_⟩
    simpa only [map_add] using (matterSpace F B p).add_mem hQ.2 hR.2
  · intro a Q hQ
    refine ⟨(noMinusPolynomials t).smul_mem a hQ.1, ?_⟩
    simpa only [map_smul] using (matterSpace F B p).smul_mem a hQ.2
  · intro x Q hx hQ
    refine ⟨mul_X_noMinus x hx Q hQ.1, ?_⟩
    rw [creation_matterMap]
    have h := LinearMap.congr_fun
      (sugawaraMode_a_commutator D H hHG hGH (F.completeBasis B x.1)
        m (-(x.2 : ℤ)-1)) (matterMap F B p Q)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
    have he : sugawaraMode D H m
        (a (F.completeBasis B x.1) (-(x.2 : ℤ)-1) (matterMap F B p Q)) =
        a (F.completeBasis B x.1) (-(x.2 : ℤ)-1)
          (sugawaraMode D H m (matterMap F B p Q)) +
        (-(-(x.2 : ℤ)-1 : ℤ) : ℂ) •
          a (F.completeBasis B x.1) (m + (-(x.2 : ℤ)-1)) (matterMap F B p Q) := by
      have hh := sub_eq_iff_eq_add.mp h
      simpa only [Module.End.mul_apply, LinearMap.sub_apply,
        LinearMap.smul_apply, Int.cast_neg, add_comm] using hh
    rw [he]
    exact (matterSpace F B p).add_mem
      (basis_current_matterSpace F B x.1 hx p _ _ hQ.2)
      ((matterSpace F B p).smul_mem _
        (basis_current_matterSpace F B x.1 hx p _ _ ⟨Q,hQ.1,rfl⟩))

/- These two finite-sum extensions consume the sealed monomial formulas;
there is no replacement for invM or for R, and no division by a zero count. -/
private theorem h_excitation_polynomial (p : Charge D) (r : ℕ)
    (P : PolynomialCoordinates (Label t)) (hP : P ∈ noMinusPolynomials t) :
    h F B p (sector F B p P (BcGhostFock.c (-((r : ℤ)+1)) (ket {1}))) ∈
      downCorrections F B p := by
  induction hP using Submodule.span_induction with
  | mem Q hQ =>
      obtain ⟨e,he,rfl⟩ := hQ
      rw [h_excitation F B p e he r]
      apply (downCorrections F B p).smul_mem
      exact ⟨_,Submodule.subset_span ⟨r,e,he,rfl⟩,rfl⟩
  | zero => simp [sector]
  | add Q R hQ hR iQ iR =>
      simpa only [sector_add, map_add] using (downCorrections F B p).add_mem iQ iR
  | smul a Q hQ iQ =>
      simpa only [sector_smul, map_smul] using (downCorrections F B p).smul_mem a iQ

private theorem h_c0_polynomial (p : Charge D)
    (P : PolynomialCoordinates (Label t)) (hP : P ∈ noMinusPolynomials t) :
    h F B p (sector F B p P (BcGhostFock.c 0 (ket {1}))) = 0 := by
  induction hP using Submodule.span_induction with
  | mem Q hQ =>
      obtain ⟨e,he,rfl⟩ := hQ
      exact h_c0 F B p e he
  | zero => simp [sector]
  | add Q R hQ hR iQ iR => simp only [sector_add, map_add, iQ, iR, add_zero]
  | smul a Q hQ iQ => simp only [sector_smul, map_smul, iQ, smul_zero]

private theorem c_positive_down (m : ℤ) (hm : 0 < m) :
    BcGhostFock.c m (ket {1}) = 0 := by
  by_cases h1 : m = 1
  · simpa only [h1] using c_one_down
  · exact c_high_down m (by omega)

private theorem h_matter_c (p : Charge D) (v : Carrier D)
    (hv : v ∈ matterSpace F B p) (m : ℤ) (hm : 0 ≤ m) :
    h F B p (v ⊗ₜ[ℂ] BcGhostFock.c (-m) (ket {1})) ∈ downCorrections F B p := by
  obtain ⟨P,hP,rfl⟩ := hv
  by_cases hz : m = 0
  · subst m
    change h F B p (sector F B p P (BcGhostFock.c 0 (ket {1}))) ∈ _
    rw [h_c0_polynomial F B p P hP]
    exact (downCorrections F B p).zero_mem
  · have he : m = (((m-1).toNat : ℕ) : ℤ)+1 := by omega
    rw [he]
    exact h_excitation_polynomial F B p (m-1).toNat P hP

private theorem h_Q_down (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (P : PolynomialCoordinates (Label t))
    (hP : P ∈ noMinusPolynomials t) :
    h F B p (LatticeBRST.totalCharge D H (sector F B p P (ket {1}))) ∈
      downCorrections F B p := by
  classical
  let x := sector F B p P (ket {1})
  let s := (summand_finite D H x).toFinset
  have ht : T D H x = ∑ m ∈ s, summand D H m x :=
    finite_capture D H x s (by intro m hm; exact (summand_finite D H x).mem_toFinset.mpr hm)
  have terms (m : ℤ) : h F B p (summand D H m x) ∈ downCorrections F B p := by
    change h F B p (sugawaraMode D H m (matterMap F B p P) ⊗ₜ[ℂ]
      BcGhostFock.c (-m) (ket {1})) ∈ _
    by_cases hm : 0 ≤ m
    · exact h_matter_c F B p _
        (sugawara_nonnegative_matterSpace F B H hHG hGH p m hm _ ⟨P,hP,rfl⟩) m hm
    · rw [c_positive_down (-m) (by omega), TensorProduct.tmul_zero, map_zero]
      exact (downCorrections F B p).zero_mem
  have hg : h F B p (LatticeBRST.ghostCharge D x) = 0 := by
    change h F B p (matterMap F B p P ⊗ₜ[ℂ] BcGhostBRST.Qg (ket {1})) = 0
    rw [Qg_down, TensorProduct.tmul_neg, map_neg]
    exact neg_eq_zero.mpr (h_c0_polynomial F B p P hP)
  change h F B p (T D H x + LatticeBRST.ghostCharge D x) ∈ _
  rw [map_add, hg, add_zero, ht, map_sum]
  exact (downCorrections F B p).sum_mem (fun m hm => terms m)

private theorem h_d0_down (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (p : Charge D) (P : PolynomialCoordinates (Label t))
    (hP : P ∈ noMinusPolynomials t) :
    h F B p (d0 F p (sector F B p P (ket {1}))) ∈ downCorrections F B p := by
  classical
  let x := sector F B p P (ket {1})
  rw [d0_common_capture F H p x, map_sum]
  apply (downCorrections F B p).sum_mem
  intro n hn
  by_cases hz : n = 0
  · simp only [hz, if_pos rfl, map_zero, Submodule.zero_mem]
  · rw [if_neg hz, map_smul]
    apply (downCorrections F B p).smul_mem
    change h F B p (a F.eMinus n (matterMap F B p P) ⊗ₜ[ℂ]
      BcGhostFock.c (-n) (ket {1})) ∈ _
    by_cases hn : 0 ≤ n
    · exact h_matter_c F B p _
        (nonnegative_current_matterSpace F B F.eMinus p n hn _ ⟨P,hP,rfl⟩) n hn
    · rw [c_positive_down (-n) (by omega), TensorProduct.tmul_zero, map_zero]
      exact (downCorrections F B p).zero_mem

/-- The literal h(Q-d0) preserves pure-down/no-minus support and inserts a
plus creator. It applies to every finite polynomial, without a level or shell
hypothesis, and uses the actual c0 branch and d0 subtraction. -/
theorem actual_hdelta_support (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (P : PolynomialCoordinates (Label t))
    (hP : P ∈ noMinusPolynomials t) :
    ∃ C ∈ plusCorrections t,
      (h F B p * (LatticeBRST.totalCharge D H - d0 F p))
        (sector F B p P (ket {1})) = sector F B p C (ket {1}) := by
  have hs : (h F B p * (LatticeBRST.totalCharge D H - d0 F p))
      (sector F B p P (ket {1})) ∈ downCorrections F B p := by
    change h F B p (LatticeBRST.totalCharge D H (sector F B p P (ket {1})) -
      d0 F p (sector F B p P (ket {1}))) ∈ _
    rw [map_sub]
    exact (downCorrections F B p).sub_mem (h_Q_down F B H hHG hGH p P hP)
      (h_d0_down F B H p P hP)
  obtain ⟨C,hC,hEq⟩ := hs
  exact ⟨C,hC,hEq.symm⟩

private theorem correction_powers (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (x : State D) (hx : x ∈ downSpace F B p)
    (r : ℕ) (hr : 0 < r) :
    ((h F B p * (LatticeBRST.totalCharge D H - d0 F p)) ^ r) x ∈
      downCorrections F B p := by
  let A := h F B p * (LatticeBRST.totalCharge D H - d0 F p)
  have step (y : State D) (hy : y ∈ downSpace F B p) :
      A y ∈ downCorrections F B p := by
    obtain ⟨P,hP,rfl⟩ := hy
    obtain ⟨C,hC,hEq⟩ := actual_hdelta_support F B H hHG hGH p P hP
    exact ⟨C,hC,hEq.symm⟩
  have hpowers (k : ℕ) : (A ^ k) x ∈ downSpace F B p := by
    induction k with
    | zero => simpa only [pow_zero, Module.End.one_apply] using hx
    | succ k ih =>
        rw [pow_succ', Module.End.mul_apply]
        exact downCorrections_le F B p (step _ ih)
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  rw [pow_succ', Module.End.mul_apply]
  exact step _ (hpowers k)

variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
  (beta : Charge D) (level : ℤ) (hp : F.pPlus beta ≠ 0)
  (critical : D.rank = 26)
  (shell : groundEnergy beta + (level : ℂ) - 1 = 0)

/-- The EXISTING finite physicalLift is a literal primary tensor ket{1}.
Its difference from the literal transverse input is in the no-minus plus
ideal. Every positive power in its actual finite K is accounted for below. -/
theorem physicalLift_pure_down (f : energyTarget D t beta) :
    ∃ C ∈ plusCorrections t,
      rename transverseVariable f.val + C ∈ noMinusPolynomials t ∧
      (physicalLift F B H hHG hGH beta level hp critical shell f).val.val =
        sector F B beta (rename transverseVariable f.val + C) (ket {1}) ∧
      WeightOnePrimary H
        (Finsupp.single beta ((F.coordinateEquiv B).symm
          (rename transverseVariable f.val + C))) := by
  classical
  let u := transverseInput F B H hHG hGH beta level shell f
  let A := sectorH F B H hHG hGH beta level *
    (sectorQ F B H hHG hGH beta level - sectorD0 F B H hHG hGH beta level)
  have hin : u.val.val ∈ downSpace F B beta := by
    rw [transverseInput_state, groundMap_sector]
    exact ⟨_,rename_noMinus f.val,rfl⟩
  have hpower (r : ℕ) (hr : 0 < r) :
      (((-A) ^ r) u.val : State D) ∈ downCorrections F B beta := by
    have hsign : (-A) ^ r = ((-1 : ℂ) ^ r) • A ^ r := by
      simpa only [neg_one_smul] using smul_pow (-1 : ℂ) A r
    rw [hsign]
    change ((-1 : ℂ) ^ r) • ((A ^ r) u.val : State D) ∈ _
    rw [sector_correction_power_coe F B H hHG hGH beta level]
    exact (downCorrections F B beta).smul_mem _
      (correction_powers F B H hHG hGH beta _ hin r hr)
  have htail : (inclusionTail F B H hHG hGH beta level hp critical shell f).val ∈
      downCorrections F B beta := by
    change (↑(∑ r ∈ (Finset.range (2 * level.toNat + 2)).erase 0,
      ((-A) ^ r) u.val) : State D) ∈ _
    rw [Submodule.coe_sum]
    apply (downCorrections F B beta).sum_mem
    intro r hr
    exact hpower r (Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hr))
  obtain ⟨C,hC,hCe⟩ := htail
  have he : (physicalLift F B H hHG hGH beta level hp critical shell f).val.val =
      sector F B beta (rename transverseVariable f.val + C) (ket {1}) := by
    have hx := congrArg Subtype.val
      (inclusion_expansion F B H hHG hGH beta level hp critical shell f)
    change (physicalLift F B H hHG hGH beta level hp critical shell f).val.val =
      groundMap F B beta f.val +
        (inclusionTail F B H hHG hGH beta level hp critical shell f).val at hx
    rw [hx, groundMap_sector, ← hCe, sector_add]
    rfl
  refine ⟨C,hC,(noMinusPolynomials t).add_mem (rename_noMinus f.val)
    (plusCorrections_le t hC),he,?_⟩
  apply (closed_down_iff_primary H _).mp
  have hclosed := (physicalLift F B H hHG hGH beta level hp critical shell f).property.1
  rw [he] at hclosed
  exact hclosed

end ActualOperators

section GlobalRepresentatives

variable {D : LatticeData}

private theorem primary_physical
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (v : Carrier D) (hv : WeightOnePrimary H v) :
    v ⊗ₜ[ℂ] ket {1} ∈ D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie.physicalStates D H := by
  have hq := (closed_down_iff_primary H v).mpr hv
  have hb : ghostB D 0 (v ⊗ₜ[ℂ] ket {1}) = 0 := by
    change v ⊗ₜ[ℂ] BcGhostFock.b 0 (ket {1}) = 0
    rw [b_nonnegative_down 0 (by omega), TensorProduct.tmul_zero]
  refine ⟨hq,hb,?_,?_⟩
  · change v ⊗ₜ[ℂ] BcGhostCharge.ghostNumber (ket {1}) = v ⊗ₜ[ℂ] ket {1}
    rw [number_ket]
    norm_num [BcGhostCharge.charge, Finset.filter_singleton]
  · have hw := LinearMap.congr_fun (LatticeBRST.total_ward_b D H 0)
      (v ⊗ₜ[ℂ] ket {1})
    change LatticeBRST.totalCharge D H (ghostB D 0 (v ⊗ₜ[ℂ] ket {1})) +
      ghostB D 0 (LatticeBRST.totalCharge D H (v ⊗ₜ[ℂ] ket {1})) =
        LatticeBRSTZeroEnergyReduction.totalL0 D H (v ⊗ₜ[ℂ] ket {1}) at hw
    simpa only [hb,hq,map_zero,add_zero] using hw.symm

/- This helper concerns the actual state and an actual global Q primitive.
At charge zero the sealed neutral classification gives equality of states;
at nonzero charge the primitive is the existing finite-HPL homotopy. -/
private theorem fixed_charge_primary
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (x : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie.physicalStates D H)
    (hx : (x : State D) ∈ LatticeRelativeMassShell.fixedMomentum D p) :
    ∃ (v : Carrier D) (u : State D), WeightOnePrimary H v ∧
      LatticeBRST.totalCharge D H u = (x : State D) - v ⊗ₜ[ℂ] ket {1} := by
  classical
  by_cases hp : p = 0
  · subst p
    obtain ⟨e,he,heunique⟩ := neutral_number_one_shell D H hHG hGH x hx
      x.property.2.1 x.property.2.2.1 x.property.2.2.2
    let v : Carrier D := ∑ i, e i • LatticeActualConformalState.currentState D i
    have heq : (x : State D) = v ⊗ₜ[ℂ] ket {1} := by
      rw [← he]
      change (∑ i, e i • LatticeRelativeMassShell.tensorBasis D (cartanLabel D i)) = _
      simp only [cartan_basis_tensor, v, TensorProduct.sum_tmul,
        TensorProduct.smul_tmul']
    have hv : WeightOnePrimary H v := by
      apply (closed_down_iff_primary H v).mp
      rw [← heq]
      exact x.property.1
    exact ⟨v,0,hv,by rw [map_zero,heq,sub_self]⟩
  · obtain ⟨F,hF⟩ := LatticeNullFrameExistence.exists_nullFrame_pPlus_ne_zero
      D H hHG (by omega) p hp
    let B := F.transverseBasis
    let level : ℤ := 1 - LatticePositiveEnergy.chargeEnergy D p
    have hshell : groundEnergy p + (level : ℂ) - 1 = 0 := by
      have htwice : (2 : ℂ) * (LatticePositiveEnergy.chargeEnergy D p : ℂ) =
          (bilinear D p p : ℂ) := by
        exact_mod_cast LatticePositiveEnergy.two_chargeEnergy D p
      dsimp [groundEnergy,level]
      push_cast
      rw [← htwice]
      ring
    let a : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPairing.physicalCycles H p level :=
      ⟨⟨x, D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.chargeProject_fixed D p x hx, by
        change LatticeBRSTZeroEnergyReduction.totalL0 D H x =
          (groundEnergy p + (level : ℂ) - 1) • (x : State D)
        rw [hshell,zero_smul]
        exact x.property.2.2.2⟩,
        x.property.1,x.property.2.1,x.property.2.2.1⟩
    let f := physicalProjection F B H hHG hGH p level hF h26 hshell a
    obtain ⟨C,hC,hno,hlift,hprimary⟩ :=
      physicalLift_pure_down F B H hHG hGH p level hF h26 hshell f
    let v : Carrier D := Finsupp.single p ((F.coordinateEquiv B).symm
      (rename transverseVariable f.val + C))
    let u : State D :=
      (FinitePerturbation.Input.H (finiteInput F B H hHG hGH p level hF h26)
        (2 * level.toNat + 2) a.val).val
    refine ⟨v,u,hprimary,?_⟩
    have hr := actual_class_recovery F B H hHG hGH p level hF h26 hshell a
    change LatticeBRST.totalCharge D H u = (x : State D) -
      (physicalLift F B H hHG hGH p level hF h26 hshell f).val.val at hr
    rw [hlift] at hr
    exact hr

/- Finite splitting uses only the actual original tensor charge support.
There is no assertion that the union of all charge sectors at a fixed energy
is finite for an indefinite Gram matrix. -/
private theorem all_charge_primary
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie.physicalStates D H) :
    ∃ (v : Carrier D) (u : State D), WeightOnePrimary H v ∧
      LatticeBRST.totalCharge D H u = (x : State D) - v ⊗ₜ[ℂ] ket {1} := by
  classical
  let xp (p : Charge D) : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie.physicalStates D H :=
    ⟨chargeProject p (x : State D), project_physical D H hHG hGH p x⟩
  have reps (p : Charge D) : ∃ (v : Carrier D) (u : State D),
      WeightOnePrimary H v ∧ LatticeBRST.totalCharge D H u =
        (xp p : State D) - v ⊗ₜ[ℂ] ket {1} :=
    fixed_charge_primary H h26 hHG hGH p (xp p)
      (chargeProject_mem D p x)
  choose v u hv hu using reps
  let s := D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.chargeSupport D (x : State D)
  let V : Carrier D := ∑ p ∈ s, v p
  let U : State D := ∑ p ∈ s, u p
  have hV : WeightOnePrimary H V := by
    constructor
    · change sugawaraMode D H 0 (∑ p ∈ s, v p) = ∑ p ∈ s, v p
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro p hp
      exact (hv p).1
    · intro m hm
      change sugawaraMode D H m (∑ p ∈ s, v p) = 0
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro p hp
      exact (hv p).2 m hm
  refine ⟨V,U,hV,?_⟩
  change LatticeBRST.totalCharge D H (∑ p ∈ s, u p) = _
  rw [map_sum]
  simp_rw [hu]
  rw [Finset.sum_sub_distrib, ← TensorProduct.sum_tmul]
  change (∑ p ∈ s, chargeProject p (x : State D)) - V ⊗ₜ[ℂ] ket {1} = _
  rw [D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sum_chargeProject D (x : State D)]

/-- EVERY original global physicalClass admits a pure-down weight-one-primary
representative. The equality is in the original unrestricted global quotient;
the final witness is an actual original Q primitive of the difference. No
condition is imposed on incoming primitives in that quotient. -/
theorem physicalClass_pure_down
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie.physicalStates D H) :
    ∃ (y : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie.physicalStates D H) (v : Carrier D),
      (y : State D) = v ⊗ₜ[ℂ] ket {1} ∧ WeightOnePrimary H v ∧
      D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie.physicalClass D H h26 hHG hGH y =
        D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie.physicalClass D H h26 hHG hGH x ∧
      ∃ u : State D, LatticeBRST.totalCharge D H u = (x : State D) - (y : State D) := by
  obtain ⟨v,u,hv,hu⟩ := all_charge_primary H h26 hHG hGH x
  let y : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie.physicalStates D H :=
    ⟨v ⊗ₜ[ℂ] ket {1}, primary_physical H v hv⟩
  refine ⟨y,v,rfl,hv,?_,u,hu⟩
  change LatticeBRSTCohomologyField.classOf D H h26 hHG hGH ⟨(y : State D),y.property.1⟩ =
    LatticeBRSTCohomologyField.classOf D H h26 hHG hGH ⟨(x : State D),x.property.1⟩
  apply (Submodule.Quotient.eq
    (LatticeBRSTCohomologyField.boundaries D H h26 hHG hGH)).mpr
  apply (LatticeBRSTCohomologyField.mem_boundaries D H h26 hHG hGH _).mpr
  refine ⟨-u,?_⟩
  change LatticeBRST.totalCharge D H (-u) = (y : State D) - (x : State D)
  rw [map_neg,hu]
  change -((x : State D) - (y : State D)) = (y : State D) - (x : State D)
  abel

-- Exact full-scope applications are anonymous, not retained named wrappers.
example (D : LatticeData) (F : NullFrame D) (t : ℕ)
    (B : Module.Basis (Fin t) ℂ F.K)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (P : PolynomialCoordinates (Label t))
    (hP : P ∈ noMinusPolynomials t) :
    ∃ C ∈ plusCorrections t,
      (h F B p * (LatticeBRST.totalCharge D H - d0 F p))
        (sector F B p P (ket {1})) = sector F B p C (ket {1}) := by
  exact actual_hdelta_support F B H hHG hGH p P hP

example (D : LatticeData) (F : NullFrame D) (t : ℕ)
    (B : Module.Basis (Fin t) ℂ F.K)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (p : Charge D) (level : ℤ) (hp : F.pPlus p ≠ 0) (h26 : D.rank = 26)
    (shell : groundEnergy p + (level : ℂ) - 1 = 0)
    (f : energyTarget D t p) :
    ∃ C ∈ plusCorrections t,
      rename transverseVariable f.val + C ∈ noMinusPolynomials t ∧
      (physicalLift F B H hHG hGH p level hp h26 shell f).val.val =
        sector F B p (rename transverseVariable f.val + C) (ket {1}) ∧
      WeightOnePrimary H (Finsupp.single p ((F.coordinateEquiv B).symm
        (rename transverseVariable f.val + C))) := by
  exact physicalLift_pure_down F B H hHG hGH p level hp h26 shell f

example (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie.physicalStates D H) :
    ∃ (y : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie.physicalStates D H) (v : Carrier D),
      (y : State D) = v ⊗ₜ[ℂ] ket {1} ∧ WeightOnePrimary H v ∧
      D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie.physicalClass D H h26 hHG hGH y =
        D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie.physicalClass D H h26 hHG hGH x ∧
      ∃ u : State D, LatticeBRST.totalCharge D H u = (x : State D) - (y : State D) := by
  exact physicalClass_pure_down H h26 hHG hGH x

end GlobalRepresentatives
end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPureDown
