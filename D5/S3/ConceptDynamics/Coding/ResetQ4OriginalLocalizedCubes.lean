/- GID: D5/S3/ConceptDynamics/Coding/ResetQ4OriginalLocalizedCubes
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResetQ4OriginalLocalizedCubes
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Original reset automorphisms admit commuting dyadic matrix cube factorizations. -/
import D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm
import D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.ResetQ4OriginalLocalizedCubes

open Polynomial
open ResetNumberedHistories ResetSignIntegerCyclic ResetIntegralGluing
open ResetNativeIntegerChart ResetNativeIntegralDefect ResetHistoryKernel
open ResetStandardBeamGeometry ResetFullStandardBeamRepresentation
open ResetNativeUnitNormalForm ResetQ4UnitCubes
open scoped BigOperators

local instance nativeIntModule (q : ℕ) : Module ℤ (Native q) :=
  AddCommGroup.toIntModule _

/-- Exactly the coefficient ring Z[1/2], not Q or an abstract product of fields. -/
abbrev Dyadic := Localization.Away (2 : ℤ)
private def zD : ℤ →+* Dyadic := algebraMap ℤ Dyadic
private def half : Dyadic := IsLocalization.Away.invSelf (2 : ℤ)

private theorem two_half : (2 : Dyadic) * half = 1 := by
  simpa only [half, map_ofNat] using
    (IsLocalization.Away.mul_invSelf (S := Dyadic) (2 : ℤ))

private def fD : Dyadic[X] := (f 4).map zD
private def gD : Dyadic[X] := (g 4).map zD
private def P : Dyadic[X] := fD * gD
private abbrev O := AdjoinRoot P
private abbrev PlusD := AdjoinRoot fD
private abbrev MinusD := AdjoinRoot gD

private theorem map_F : (F 4).map zD = P := by
  simp only [F, fD, gD, P, f, g, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_X, show 2 * 4 = 4 * 2 from rfl, pow_mul]
  ring

/- The same integer certificate as the integral gluing owner, obtained from
its public geometric identity. This is not an assumption about CRT. -/
private theorem bezout_twice :
    (X : ℤ[X]) * f 4 + (2 - X) * g 4 = 2 := by
  simp only [f, g]
  linear_combination 2 * geometric 4

private theorem dyadic_bezout :
    (C half * X) * fD + (1 - C half * X) * gD = 1 := by
  have hb : (X : Dyadic[X]) * fD + (2 - X) * gD = 2 := by
    simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_ofNat, fD, gD] using
      congrArg (Polynomial.map zD) bezout_twice
  have hh : (2 : Dyadic[X]) * C half = 1 := by
    simpa only [map_mul, map_ofNat, map_one] using congrArg C two_half
  linear_combination C half * hb + (1 - gD) * hh

private theorem coprime : IsCoprime fD gD :=
  ⟨C half * X, 1 - C half * X, dyadic_bezout⟩

private theorem fD_monic : fD.Monic := by
  apply Polynomial.Monic.map
  have hf : f 4 = (X^4-X^3-X^2-X-1 : ℤ[X]) := by
    simp [f, S, Finset.sum_range_succ]; ring
  rw [hf]
  monicity!

private theorem gD_monic : gD.Monic := by
  apply Polynomial.Monic.map
  have hg : g 4 = (X^4+X^3+X^2+X+1 : ℤ[X]) := by
    simp [g, S, Finset.sum_range_succ]; ring
  rw [hg]
  monicity!

private def plusD : O →+* PlusD :=
  Ideal.Quotient.lift _ (AdjoinRoot.mk fD) (by
    intro p hp
    apply AdjoinRoot.mk_eq_zero.mpr
    exact dvd_trans (dvd_mul_right fD gD) (Ideal.mem_span_singleton.mp hp))

private def minusD : O →+* MinusD :=
  Ideal.Quotient.lift _ (AdjoinRoot.mk gD) (by
    intro p hp
    apply AdjoinRoot.mk_eq_zero.mpr
    exact dvd_trans (dvd_mul_left gD fD) (Ideal.mem_span_singleton.mp hp))

private def split : O →+* PlusD × MinusD := plusD.prod minusD

private theorem split_mk (p : Dyadic[X]) :
    split (AdjoinRoot.mk P p) = (AdjoinRoot.mk fD p, AdjoinRoot.mk gD p) := rfl

private theorem split_injective : Function.Injective split := by
  intro a b hab
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective b
  apply AdjoinRoot.mk_eq_mk.mpr
  exact coprime.mul_dvd
    (AdjoinRoot.mk_eq_mk.mp (congrArg Prod.fst hab))
    (AdjoinRoot.mk_eq_mk.mp (congrArg Prod.snd hab))

/- e+ = (1-X/2)g, e- = (X/2)f. Canonical representatives are
used only to define the inverse; there is no mod-two condition on a,b. -/
private def glue (a : PlusD) (b : MinusD) : O :=
  AdjoinRoot.mk P
    ((1 - C half * X) * gD * AdjoinRoot.modByMonicHom fD_monic a +
      C half * X * fD * AdjoinRoot.modByMonicHom gD_monic b)

private theorem split_glue (a : PlusD) (b : MinusD) : split (glue a b) = (a,b) := by
  have hp : AdjoinRoot.mk fD (1 - C half * X) * AdjoinRoot.mk fD gD = 1 := by
    have hb := congrArg (AdjoinRoot.mk fD) dyadic_bezout
    simpa only [map_add, map_mul, AdjoinRoot.mk_self, mul_zero,
      zero_add, map_one] using hb
  have hm : AdjoinRoot.mk gD (C half) * AdjoinRoot.mk gD X *
      AdjoinRoot.mk gD fD = 1 := by
    have hb := congrArg (AdjoinRoot.mk gD) dyadic_bezout
    simpa only [map_add, map_mul, AdjoinRoot.mk_self, mul_zero,
      add_zero, map_one] using hb
  apply Prod.ext
  · change AdjoinRoot.mk fD _ = a
    simp only [map_add, map_mul, AdjoinRoot.mk_self, mul_zero,
      zero_mul, add_zero, hp, one_mul]
    exact AdjoinRoot.mk_leftInverse fD_monic a
  · change AdjoinRoot.mk gD _ = b
    simp only [map_add, map_mul, AdjoinRoot.mk_self, mul_zero,
      zero_mul, zero_add, hm, one_mul]
    exact AdjoinRoot.mk_leftInverse gD_monic b

private def crt : O ≃+* PlusD × MinusD :=
  RingEquiv.ofBijective split ⟨split_injective, fun z => ⟨glue z.1 z.2, split_glue _ _⟩⟩

private theorem crt_inverse (a : PlusD) (b : MinusD) : crt.symm (a,b) = glue a b := by
  apply crt.injective
  rw [RingEquiv.apply_symm_apply]
  exact (split_glue a b).symm

/- Integral orders map to their coefficient extensions. -/
private def plusIntegral : Plus 4 →+* PlusD :=
  AdjoinRoot.map zD (f 4) fD dvd_rfl

private def minusIntegral : Minus 4 →+* MinusD :=
  AdjoinRoot.map zD (g 4) gD dvd_rfl

private def integral : QF 4 →+* O :=
  AdjoinRoot.map zD (F 4) P (by simpa only [map_F] using (dvd_rfl : P ∣ P))

private theorem map_mk {R S : Type*} [CommRing R] [CommRing S]
    (c : R →+* S) (p : R[X]) (q : S[X]) (hd : q ∣ p.map c) (a : R[X]) :
    AdjoinRoot.map c p q hd (AdjoinRoot.mk p a) = AdjoinRoot.mk q (a.map c) := by
  have he : (AdjoinRoot.map c p q hd).comp (AdjoinRoot.mk p) =
      (AdjoinRoot.mk q).comp (Polynomial.mapRingHom c) := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [AdjoinRoot.map, AdjoinRoot.mk_C]
    · simp [AdjoinRoot.map]
  exact RingHom.congr_fun he a

private theorem integral_components (a : QF 4) :
    split (integral a) = (plusIntegral (plus 4 a), minusIntegral (minus 4 a)) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  change split ((AdjoinRoot.map zD (F 4) P _)
      (AdjoinRoot.mk (F 4) p)) =
    ((AdjoinRoot.map zD (f 4) fD _) (AdjoinRoot.mk (f 4) p),
      (AdjoinRoot.map zD (g 4) gD _) (AdjoinRoot.mk (g 4) p))
  simp only [map_mk, split_mk]

private def pairUnit (a : PlusDˣ) (b : MinusDˣ) : (PlusD × MinusD)ˣ :=
  ⟨(a,b), (↑a⁻¹,↑b⁻¹), by ext <;> simp, by ext <;> simp⟩

private def joinUnit (a : PlusDˣ) (b : MinusDˣ) : Oˣ :=
  Units.map crt.symm.toMonoidHom (pairUnit a b)

private theorem split_joinUnit (a : PlusDˣ) (b : MinusDˣ) :
    split (joinUnit a b : O) = ((a : PlusD),(b : MinusD)) := by
  change split (crt.symm ((a,b) : PlusD × MinusD)) = _
  rw [crt_inverse]
  exact split_glue a b

private def plusUnits : (Plus 4)ˣ →* PlusDˣ := Units.map plusIntegral.toMonoidHom
private def minusUnits : (Minus 4)ˣ →* MinusDˣ := Units.map minusIntegral.toMonoidHom
private def integralUnits : (QF 4)ˣ →* Oˣ := Units.map integral.toMonoidHom
private def firstUnit : Oˣ →* PlusDˣ := Units.map plusD.toMonoidHom
private def secondUnit : Oˣ →* MinusDˣ := Units.map minusD.toMonoidHom

private theorem first_join (a : PlusDˣ) (b : MinusDˣ) :
    firstUnit (joinUnit a b) = a := Units.ext (congrArg Prod.fst (split_joinUnit a b))
private theorem second_join (a : PlusDˣ) (b : MinusDˣ) :
    secondUnit (joinUnit a b) = b := Units.ext (congrArg Prod.snd (split_joinUnit a b))

private theorem unit_components_ext {a b : Oˣ}
    (hp : firstUnit a = firstUnit b) (hm : secondUnit a = secondUnit b) : a = b := by
  apply Units.ext
  apply split_injective
  exact Prod.ext (congrArg Units.val hp) (congrArg Units.val hm)

private def timeUnit : Oˣ := joinUnit (plusUnits alpha) (minusUnits beta)
private def onePlusUnit : Oˣ := joinUnit (plusUnits Bplus) (minusUnits Bminus)

private theorem timeUnit_val : (timeUnit : O) = AdjoinRoot.mk P X := by
  apply split_injective
  rw [timeUnit, split_joinUnit, split_mk]
  apply Prod.ext
  · change (AdjoinRoot.map zD (f 4) fD _) (AdjoinRoot.mk (f 4) X) = _
    simp only [map_mk, Polynomial.map_X]
  · change (AdjoinRoot.map zD (g 4) gD _) (AdjoinRoot.mk (g 4) X) = _
    simp only [map_mk, Polynomial.map_X]

private theorem onePlusUnit_val : (onePlusUnit : O) = 1 + AdjoinRoot.mk P X := by
  apply split_injective
  rw [onePlusUnit, split_joinUnit, map_add, map_one, split_mk]
  apply Prod.ext
  · change (AdjoinRoot.map zD (f 4) fD _) (AdjoinRoot.mk (f 4) (1+X)) = _
    simp only [map_mk, Polynomial.map_X, map_add, map_one]
    rfl
  · change (AdjoinRoot.map zD (g 4) gD _) (AdjoinRoot.mk (g 4) (1+X)) = _
    simp only [map_mk, Polynomial.map_X, map_add, map_one]
    rfl

private theorem beta_fifth : beta ^ 5 = 1 := by
  apply Units.ext
  change (AdjoinRoot.mk (g 4) X) ^ 5 = 1
  apply sub_eq_zero.mp
  rw [← map_pow, ← map_one (AdjoinRoot.mk (g 4)), ← map_sub]
  apply AdjoinRoot.mk_eq_zero.mpr
  refine ⟨X-1, ?_⟩
  simp [g, S, Finset.sum_range_succ]; ring

private theorem beta_correction (i : ℕ) (w : (AdjoinRoot (g 4))ˣ) :
    beta^i * (beta^(3*i) * w)^3 = w^3 := by
  rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]
  have hi : i + 3*i*3 = 5*(2*i) := by omega
  rw [hi, pow_mul, beta_fifth, one_pow, one_mul]

/- This is the consumed localized cube statement for integral original-order
units. Integral compatibility is used only for j=k, not to glue cube roots. -/
private theorem localized_normal_form (u : (QF 4)ˣ) :
    ∃ i j : Fin 3, ∃ v : Oˣ,
      integralUnits u = timeUnit^i.val * onePlusUnit^j.val * v^3 ∧
      residueCharacter (Additive.ofMul (Units.map (rplus 4).toMonoidHom
        (Units.map (plus 4).toMonoidHom u))) = (j.val : ZMod 3) := by
  let up := Units.map (plus 4).toMonoidHom u
  let um := Units.map (minus 4).toMonoidHom u
  have hc : Units.map (rplus 4).toMonoidHom up =
      Units.map (rminus 4).toMonoidHom um := by
    apply Units.ext
    exact (toCompatible 4 (u : QF 4)).property
  obtain ⟨i,j,k,v,w,hp,hm,hjk⟩ := compatible_cube_normal_forms up um hc
  have he : j = k := by
    apply Fin.ext
    simpa only [ZMod.val_natCast_of_lt j.isLt, ZMod.val_natCast_of_lt k.isLt] using
      congrArg ZMod.val hjk
  subst k
  let root : Oˣ := joinUnit (plusUnits v) (minusUnits (beta^(3*i.val) * w))
  have hres : residueCharacter (Additive.ofMul
      (Units.map (rplus 4).toMonoidHom up)) = (j.val : ZMod 3) :=
    residueCharacter_plus_factorization up i j v hp
  refine ⟨i,j,root,?_,hres⟩
  apply unit_components_ext
  · have hcomp : firstUnit (integralUnits u) = plusUnits up := by
      apply Units.ext
      exact congrArg Prod.fst (integral_components (u : QF 4))
    rw [hcomp, hp]
    simp only [map_mul, map_pow, timeUnit, onePlusUnit, root, first_join]
  · have hcomp : secondUnit (integralUnits u) = minusUnits um := by
      apply Units.ext
      exact congrArg Prod.snd (integral_components (u : QF 4))
    rw [hcomp]
    have hd : um = beta^i.val * Bminus^j.val * (beta^(3*i.val) * w)^3 := by
      rw [hm]
      calc
        Bminus^j.val * w^3 = Bminus^j.val *
            (beta^i.val * (beta^(3*i.val) * w)^3) := by rw [beta_correction]
        _ = beta^i.val * Bminus^j.val * (beta^(3*i.val) * w)^3 := by ac_rfl
    simpa only [map_mul, map_pow, timeUnit, onePlusUnit, root, second_join] using
      congrArg minusUnits hd

/- All matrix indices are the ORIGINAL signed vertices. LinearMap.toMatrix
uses columns for composition; the underlying transition is the accepted
right-row transition, so this is its action matrix, never its inverse. -/
abbrev VertexIndex := Σ _ : Fin 4, Sign
abbrev IntegerMatrix := Matrix VertexIndex VertexIndex ℤ
abbrev DyadicMatrix := Matrix VertexIndex VertexIndex Dyadic
private abbrev Vertex := InertGroupBlockConjugacy.VertexModule Sign 4
private def vb : Module.Basis VertexIndex ℤ Vertex :=
  InertGroupBlockConjugacy.vertexBasis
private def coordinates : QF 4 ≃ₗ[ℤ] Vertex :=
  (nativeIntEquiv 4 (by decide)).trans (resetNativeEquiv 4 (by decide))
private def qb : Module.Basis VertexIndex ℤ (QF 4) := vb.map coordinates.symm
private def integralEvaluation : QF 4 →+* IntegerMatrix :=
  (Algebra.leftMulMatrix qb).toRingHom
private def matrixCast : IntegerMatrix →+* DyadicMatrix := zD.mapMatrix

/-- Matrix of the literal original forward transition in the original vertex basis. -/
def T : DyadicMatrix := matrixCast
  (LinearMap.toMatrix vb vb (InertGroupBlockConjugacy.transition (resetMatrix 4)))

/-- Scalar extension of the actual original beam-set-image action, at stage zero. -/
def rhoD (h : ResetFullAut 4) : DyadicMatrix := matrixCast
  (LinearMap.toMatrix vb vb
    (((resetNativeEquiv 4 (by decide)).symm.trans
      ((rho 4 (by decide) h).trans (resetNativeEquiv 4 (by decide)))).toLinearMap))

private theorem rhoD_unitShift :
    rhoD (StandardBeamHomeomorphisms.unitShift (ResetGraph 4)) = T := by
  apply congrArg matrixCast
  apply congrArg (LinearMap.toMatrix vb vb)
  apply LinearMap.ext
  intro v
  change resetNativeEquiv 4 (by decide)
    (rho 4 (by decide) (StandardBeamHomeomorphisms.unitShift (ResetGraph 4))
      ((resetNativeEquiv 4 (by decide)).symm v)) = _
  rw [show rho 4 (by decide) (StandardBeamHomeomorphisms.unitShift (ResetGraph 4))
      ((resetNativeEquiv 4 (by decide)).symm v) =
        resetTheta 4 ((resetNativeEquiv 4 (by decide)).symm v) from
      LinearMap.congr_fun (rho_unitShift 4 (by decide)) _,
    resetNativeEquiv_theta, LinearEquiv.apply_symm_apply]

private theorem rhoD_even : rhoD (evenAut 4 (by decide) (by decide)) = 1+T := by
  have hv : (((resetNativeEquiv 4 (by decide)).symm.trans
      ((rho 4 (by decide) (evenAut 4 (by decide) (by decide))).trans
        (resetNativeEquiv 4 (by decide)))).toLinearMap) =
      LinearMap.id + InertGroupBlockConjugacy.transition (resetMatrix 4) := by
    apply LinearMap.ext
    intro v
    change resetNativeEquiv 4 (by decide)
      ((rho 4 (by decide) (evenAut 4 (by decide) (by decide))).toLinearMap
        ((resetNativeEquiv 4 (by decide)).symm v)) = v + _
    rw [rho_even]
    simp only [LinearMap.add_apply, LinearMap.id_apply, map_add,
      resetNativeEquiv_theta, LinearEquiv.apply_symm_apply]
  change matrixCast (LinearMap.toMatrix vb vb _) = 1+T
  simp only [hv, map_add, LinearMap.toMatrix_id, map_one, T]

private theorem coordinates_X (b : QF 4) :
    coordinates (fp 4 X * b) =
      InertGroupBlockConjugacy.transition (resetMatrix 4) (coordinates b) := by
  change resetNativeEquiv 4 (by decide) (nativeIntEquiv 4 (by decide) (fp 4 X*b)) = _
  rw [(native_presentation 4 (by decide)).2.1, resetNativeEquiv_theta]
  rfl

private theorem integralEvaluation_X :
    integralEvaluation (fp 4 X) =
      LinearMap.toMatrix vb vb (InertGroupBlockConjugacy.transition (resetMatrix 4)) := by
  change (Algebra.leftMulMatrix qb) (fp 4 X) = _
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, LinearMap.toMatrix_apply]
  change vb.repr (coordinates (fp 4 X * coordinates.symm (vb j))) i = _
  rw [coordinates_X, LinearEquiv.apply_symm_apply]

private def originalScalar (h : ResetFullAut 4) : (QF 4)ˣ :=
  scalarUnit 4 (by decide) (rho 4 (by decide) h) (rho_time 4 (by decide) h)

private theorem originalScalar_action (h : ResetFullAut 4) (b : QF 4) :
    nativeIntEquiv 4 (by decide) ((originalScalar h : QF 4) * b) =
      rho 4 (by decide) h (nativeIntEquiv 4 (by decide) b) := by
  apply (nativeIntEquiv 4 (by decide)).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  have hs := centralizingMap_scalar 4 (by decide)
    (rho 4 (by decide) h).toLinearMap (rho_time 4 (by decide) h) b
  have happ : centralizingMap 4 (by decide) (rho 4 (by decide) h).toLinearMap
      (rho_time 4 (by decide) h) b = (nativeIntEquiv 4 (by decide)).symm
        (rho 4 (by decide) h (nativeIntEquiv 4 (by decide) b)) := by
    dsimp only [centralizingMap, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [(native_presentation 4 (by decide)).2.2.2.2.1]
    simp only [LinearMap.ofAEval, LinearMap.coe_mk,
      LinearMap.coe_toAddHom, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      Module.AEval'.of, LinearEquiv.symm_apply_apply]
  rw [happ] at hs
  rw [show (originalScalar h : QF 4) =
    centralizingMap 4 (by decide) (rho 4 (by decide) h).toLinearMap
      (rho_time 4 (by decide) h) 1 from rfl]
  exact (mul_comm _ _).trans hs.symm

private theorem originalScalar_matrix (h : ResetFullAut 4) :
    matrixCast (integralEvaluation (originalScalar h : QF 4)) = rhoD h := by
  apply congrArg matrixCast
  change (Algebra.leftMulMatrix qb) (originalScalar h : QF 4) = _
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, LinearMap.toMatrix_apply]
  change vb.repr (coordinates ((originalScalar h : QF 4) *
    coordinates.symm (vb j))) i = _
  change vb.repr (resetNativeEquiv 4 (by decide)
    (nativeIntEquiv 4 (by decide) ((originalScalar h : QF 4) *
      coordinates.symm (vb j)))) i = _
  rw [originalScalar_action]
  have hc : nativeIntEquiv 4 (by decide) (coordinates.symm (vb j)) =
      (resetNativeEquiv 4 (by decide)).symm (vb j) := by
    apply (resetNativeEquiv 4 (by decide)).injective
    change coordinates (coordinates.symm (vb j)) = _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rw [hc]
  rfl

private theorem integralPolynomial (p : ℤ[X]) :
    matrixCast (integralEvaluation (fp 4 p)) = (aeval T) p := by
  have he : matrixCast.comp (integralEvaluation.comp (fp 4)) =
      (aeval T : ℤ[X] →ₐ[ℤ] DyadicMatrix).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro z
      have hz : (C z : ℤ[X]) = (z : ℤ[X]) := map_intCast C z
      simp only [hz, map_intCast]
    · change matrixCast (integralEvaluation (fp 4 X)) = (aeval T) X
      rw [aeval_X]
      exact congrArg matrixCast integralEvaluation_X
  exact RingHom.congr_fun he p

private theorem evaluation_relation : (aeval T : Dyadic[X] →ₐ[Dyadic] DyadicMatrix) P = 0 := by
  have hzero : fp 4 (F 4) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hbase : (aeval T : ℤ[X] →ₐ[ℤ] DyadicMatrix) (F 4) = 0 := by
    rw [← integralPolynomial, hzero, map_zero, map_zero]
  have he := Polynomial.aeval_eq_aeval_map
    (R := ℤ) (S := DyadicMatrix) (T := Dyadic) (φ := zD)
    (by ext z; simp [zD]) (F 4) T
  rw [map_F] at he
  exact he.symm.trans hbase

/-- Evaluation of the localized original order on the literal original time matrix.
Ideal.Quotient.lift allows the noncommutative matrix codomain. -/
private def evaluation : O →+* DyadicMatrix :=
  Ideal.Quotient.lift _ (aeval T).toRingHom (by
    intro p hp
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    change (aeval T) (a * P) = 0
    rw [map_mul, evaluation_relation, mul_zero])

private theorem evaluation_mk (p : Dyadic[X]) :
    evaluation (AdjoinRoot.mk P p) = (aeval T) p := rfl

private theorem evaluation_integral (a : QF 4) :
    evaluation (integral a) = matrixCast (integralEvaluation a) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  change evaluation ((AdjoinRoot.map zD (F 4) P _)
    (AdjoinRoot.mk (F 4) p)) = matrixCast (integralEvaluation (fp 4 p))
  rw [map_mk, evaluation_mk, integralPolynomial]
  exact (Polynomial.aeval_eq_aeval_map
    (R := ℤ) (S := DyadicMatrix) (T := Dyadic) (φ := zD)
    (by ext z; simp [zD]) p T).symm

private def evaluationUnits : Oˣ →* DyadicMatrixˣ := Units.map evaluation.toMonoidHom
private def matrixTime : DyadicMatrixˣ := evaluationUnits timeUnit
private def matrixOnePlus : DyadicMatrixˣ := evaluationUnits onePlusUnit

private theorem matrixTime_val : (matrixTime : DyadicMatrix) = T := by
  change evaluation (timeUnit : O) = T
  rw [timeUnit_val, evaluation_mk, aeval_X]

private theorem matrixOnePlus_val : (matrixOnePlus : DyadicMatrix) = 1+T := by
  change evaluation (onePlusUnit : O) = 1+T
  rw [onePlusUnit_val, map_add, map_one, evaluation_mk, aeval_X]

/-- Genuine matrix units centralizing the literal original time matrix. -/
def Centralizer : Subgroup DyadicMatrixˣ := Subgroup.centralizer {matrixTime}

private def evaluateCentralizer : Oˣ →* Centralizer :=
  evaluationUnits.codRestrict Centralizer (by
    intro u
    apply Subgroup.mem_centralizer_iff.mpr
    intro v hv
    obtain rfl := Set.mem_singleton_iff.mp hv
    exact (evaluationUnits.map_mul timeUnit u).symm.trans
      ((congrArg evaluationUnits (mul_comm timeUnit u)).trans
        (evaluationUnits.map_mul u timeUnit)))

/-- Actual invertible matrix whose value is the exact forward time T. -/
def time : Centralizer := evaluateCentralizer timeUnit
/-- Actual invertible matrix whose value is literally I+T. -/
def onePlusTime : Centralizer := evaluateCentralizer onePlusUnit
/-- A unit over the original dyadic matrices; its value is proved equal to rhoD. -/
def originalImage (h : ResetFullAut 4) : Centralizer :=
  evaluateCentralizer (integralUnits (originalScalar h))

theorem time_val : ((time : DyadicMatrixˣ) : DyadicMatrix) = T :=
  matrixTime_val

theorem onePlusTime_val : ((onePlusTime : DyadicMatrixˣ) : DyadicMatrix) = 1+T :=
  matrixOnePlus_val

theorem originalImage_val (h : ResetFullAut 4) :
    ((originalImage h : DyadicMatrixˣ) : DyadicMatrix) = rhoD h := by
  change evaluation (integral (originalScalar h : QF 4)) = rhoD h
  rw [evaluation_integral, originalScalar_matrix]

private theorem originalImage_unitShift :
    originalImage (StandardBeamHomeomorphisms.unitShift (ResetGraph 4)) = time := by
  apply Subtype.ext
  apply Units.ext
  rw [originalImage_val, time_val, rhoD_unitShift]

private theorem originalImage_even :
    originalImage (evenAut 4 (by decide) (by decide)) = onePlusTime := by
  apply Subtype.ext
  apply Units.ext
  rw [originalImage_val, onePlusTime_val, rhoD_even]

private theorem centralizer_commutes (v : Centralizer) :
    Commute ((v : DyadicMatrixˣ) : DyadicMatrix) T := by
  have he := Subgroup.mem_centralizer_iff.mp v.property matrixTime (by simp)
  have hv := congrArg (fun u : DyadicMatrixˣ => (u : DyadicMatrix)) he.symm
  change ((v : DyadicMatrixˣ) : DyadicMatrix) * T =
    T * ((v : DyadicMatrixˣ) : DyadicMatrix)
  simpa only [Units.val_mul, matrixTime_val] using hv

private theorem original_unit_factorization (h : ResetFullAut 4) :
    ∃ i j : Fin 3, ∃ v : Centralizer,
      originalImage h =
        (originalImage (StandardBeamHomeomorphisms.unitShift (ResetGraph 4)))^i.val *
        (originalImage (evenAut 4 (by decide) (by decide)))^j.val * v^3 := by
  rw [originalImage_unitShift, originalImage_even]
  obtain ⟨i,j,v,hv,_⟩ := localized_normal_form (originalScalar h)
  refine ⟨i,j,evaluateCentralizer v,?_⟩
  simpa only [map_mul, map_pow, originalImage, time, onePlusTime] using
    congrArg evaluateCentralizer hv

/-- Every actual original-history automorphism, in the original vertex matrix
action, factors with bounded Fin 3 exponents and a real commuting dyadic unit.
This theorem neither constructs an SGCC character nor classifies the rho image. -/
theorem original_localized_cube_factorization (h : ResetFullAut 4) :
    ∃ i j : Fin 3, ∃ v : Centralizer,
      rhoD h = T^i.val * (1+T)^j.val *
        (((v : DyadicMatrixˣ) : DyadicMatrix)^3) ∧
      Commute ((v : DyadicMatrixˣ) : DyadicMatrix) T := by
  obtain ⟨i,j,v,hv⟩ := original_unit_factorization h
  refine ⟨i,j,v,?_,centralizer_commutes v⟩
  have he := congrArg (fun u : Centralizer => ((u : DyadicMatrixˣ) : DyadicMatrix)) hv
  simpa only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul,
    Units.val_pow_eq_pow_val, originalImage_val, rhoD_unitShift, rhoD_even] using he








end D5.S3.ConceptDynamics.Coding.ResetQ4OriginalLocalizedCubes
