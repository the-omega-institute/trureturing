/- GID: D5/S3/Factorization/Mordell/GoldenCubicBlockOrbitIndependence
   generality: G
   mirror-B: D5/B/S3/Factorization/Mordell/GoldenCubicBlockOrbitIndependence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Horizontal cubic traces and coordinate actions force independence modulo base-field points. -/

import D5.S3.Factorization.MordellTwoAdicNonTorsion
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Tactic
import D5.S3.Factorization.Mordell.SymmetricSquareAddition
import D5.S3.QuadraticForms.ParallelogramConstruction
import D5.S3.Factorization.Mordell.CanonicalPointHeight
import D5.S3.Factorization.Dedekind.GaloisScalarHeight
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.Group.Action.Hom
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Block
import D5.S3.Factorization.Galois.GoldenCubicCommonInertiaAndSignature
import D5.S3.Factorization.Mordell.PointVariableChange
import D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists
import D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower
import D5.S1.Scale.GoldenCubicBlockCongruences
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Range



set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S1.Scale
open D5.S3.Factorization.MordellTwoAdicNonTorsion
open D5.S3.Factorization.Galois.GoldenCubicBlockPositiveRootTower
open WeierstrassCurve
open Polynomial
open Height


namespace D5.S3.Factorization.Mordell.GoldenCubicBlockOrbitIndependence

theorem cubic_orbit_independent_mod_fixed
    {G : Type*} [AddCommGroup G] (J : ℕ)
    (P : Fin J → G) (T : G →+ G) (sigma : Fin J → (G →+ G))
    (base : AddSubgroup G)
    (hbase : ∀ j (q : G), q ∈ base → sigma j q = q)
    (hpoint : ∀ j i, sigma j (P i) = if i = j then T (P i) else P i)
    (hrotate : ∀ j i,
      sigma j (T (P i)) = if i = j then T (T (P i)) else T (P i))
    (htriple : ∀ i, P i + T (P i) + T (T (P i)) = 0)
    (hinfinite : ∀ i, ¬ IsOfFinAddOrder (P i))
    (a b : Fin J → ℤ)
    (hrel : (∑ i : Fin J, (a i • P i + b i • T (P i))) ∈ base) :
    ∀ i, a i = 0 ∧ b i = 0 := by
  classical
  let term : Fin J → G := fun i => a i • P i + b i • T (P i)
  let rotated : Fin J → G := fun i => a i • T (P i) + b i • T (T (P i))
  have hmapterm (j i : Fin J) :
      sigma j (term i) = if i = j then rotated i else term i := by
    dsimp [term, rotated]
    by_cases hij : i = j
    · simp [hij, hpoint, hrotate]
    · simp [hij, hpoint, hrotate]
  have hsumMap (j : Fin J) :
      sigma j (∑ i : Fin J, term i) =
        rotated j + ∑ i ∈ Finset.univ.erase j, term i := by
    rw [map_sum, ← Finset.add_sum_erase Finset.univ
      (fun i => sigma j (term i)) (Finset.mem_univ j)]
    rw [hmapterm j j, if_pos rfl]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    rw [hmapterm j i, if_neg hij]
  intro j
  have hsumFixed : sigma j (∑ i : Fin J, term i) =
      (∑ i : Fin J, term i) := hbase j _ hrel
  rw [hsumMap j,
    ← Finset.add_sum_erase Finset.univ term (Finset.mem_univ j)] at hsumFixed
  have hlocal : rotated j = term j := add_right_cancel hsumFixed
  have hfix :
      a j • (T (P j) - P j) +
        b j • (T (T (P j)) - T (P j)) = 0 := by
    dsimp [rotated, term] at hlocal
    linear_combination (norm := module) hlocal
  let x : ℤ := a j + b j
  let y : ℤ := 2 * b j - a j
  have hlinear : x • P j + y • T (P j) = 0 := by
    dsimp [x, y]
    linear_combination (norm := module) (b j) • (htriple j) - hfix
  have hlinearT : x • T (P j) + y • T (T (P j)) = 0 := by
    simpa only [map_add, map_zsmul, map_zero] using congrArg T hlinear
  have hsecond : (-y) • P j + (x - y) • T (P j) = 0 := by
    linear_combination (norm := module) hlinearT - y • (htriple j)
  let norm : ℤ := x * (x - y) + y * y
  have hnormP : norm • P j = 0 := by
    dsimp [norm]
    linear_combination (norm := module) (x - y) • hlinear - y • hsecond
  have hnorm0 : norm = 0 := by
    by_contra hn
    exact hinfinite j
      (isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨norm, hn, hnormP⟩)
  have hx0 : x = 0 := by
    by_contra hx
    have hxpos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    have hypos : 0 ≤ y ^ 2 := sq_nonneg y
    have hdpos : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
    dsimp [norm] at hnorm0
    nlinarith
  have hy0 : y = 0 := by
    by_contra hy
    have hypos : 0 < y ^ 2 := sq_pos_of_ne_zero hy
    have hxpos : 0 ≤ x ^ 2 := sq_nonneg x
    have hdpos : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
    dsimp [norm] at hnorm0
    nlinarith
  dsimp [x] at hx0
  dsimp [y] at hy0
  constructor <;> omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Factorization.MordellTwoAdicNonTorsion

set_option autoImplicit false
set_option relaxedAutoImplicit false



theorem cubic_mordell_family_independent_mod_base
    {K L : Type*} [Field K] [Field L]
    [Algebra ℚ K] [Algebra ℚ L] [Algebra K L] [IsScalarTower ℚ K L]
    [CharZero L] [DecidableEq K] [DecidableEq L]
    (J : ℕ) (c d : ℤ) (hd : d ≠ 0)
    (hell : (mordellCurve c).IsElliptic)
    (zeta : L) (hzeta : IsPrimitiveRoot zeta 3)
    (beta : Fin J → L) (hbeta0 : ∀ i, beta i ≠ 0)
    (sigma : Fin J → (L ≃ₐ[K] L))
    (hsigmaZeta : ∀ j, sigma j zeta = zeta)
    (hsigmaBeta : ∀ j i,
      sigma j (beta i) = if i = j then zeta * beta i else beta i)
    (y : Fin J → ℤ)
    (hns : ∀ i, ((mordellCurve c).baseChange L).Nonsingular
      ((d : L) * beta i) (y i : L))
    (hinfinite : ∀ i, ¬ IsOfFinAddOrder
      (.some ((d : L) * beta i) (y i : L) (hns i) :
        ((mordellCurve c).baseChange L).Point)) :
    ∃ T : ((mordellCurve c).baseChange L).Point ≃+
        ((mordellCurve c).baseChange L).Point,
      (∀ (x y : L) (h : ((mordellCurve c).baseChange L).Nonsingular x y),
        ∃ hrot : ((mordellCurve c).baseChange L).Nonsingular (zeta * x) y,
          T (.some x y h) = .some (zeta * x) y hrot) ∧
      ∀ a b : Fin J → ℤ,
        (∑ i : Fin J,
          (a i • (.some ((d : L) * beta i) (y i : L) (hns i) :
            ((mordellCurve c).baseChange L).Point) +
          b i • T (.some ((d : L) * beta i) (y i : L) (hns i)))) ∈
          (WeierstrassCurve.Affine.Point.map
            (W' := mordellCurve c) (Algebra.ofId K L)).range →
        ∀ i, a i = 0 ∧ b i = 0 := by
  classical
  have mordell_cm_point_rotation :
      let W := (mordellCurve c).baseChange L
      ∃ T : W.toAffine.Point ≃+ W.toAffine.Point,
        ∀ (x y : L) (h : W.toAffine.Nonsingular x y),
          ∃ hrot : W.toAffine.Nonsingular (zeta * x) y,
            T (.some x y h) = .some (zeta * x) y hrot := by
    let F := L
    classical
    let W : WeierstrassCurve F := (mordellCurve c).baseChange F
    letI : (mordellCurve c).IsElliptic := hell
    letI : W.IsElliptic := by
      dsimp [W, WeierstrassCurve.Affine.baseChange,
        WeierstrassCurve.baseChange]
      infer_instance
    have hzeta0 : zeta ≠ 0 := hzeta.ne_zero (by decide)
    have hpow4 : (zeta ^ 2) ^ 2 = zeta := by
      calc
        (zeta ^ 2) ^ 2 = zeta ^ 3 * zeta := by ring
        _ = zeta := by rw [hzeta.pow_eq_one, one_mul]
    have hpow6 : (zeta ^ 2) ^ 3 = 1 := by
      calc
        (zeta ^ 2) ^ 3 = (zeta ^ 3) ^ 2 := by ring
        _ = 1 := by rw [hzeta.pow_eq_one, one_pow]
    have hpow12 : (zeta ^ 2) ^ 6 = 1 := by
      calc
        (zeta ^ 2) ^ 6 = ((zeta ^ 2) ^ 3) ^ 2 := by ring
        _ = 1 := by rw [hpow6, one_pow]
    let C : VariableChange F :=
      ⟨Units.mk0 (zeta ^ 2) (pow_ne_zero _ hzeta0), 0, 0, 0⟩
    have hchange : C • W = W := by
      ext <;> simp [C, W, mordellCurve, variableChange_def,
        WeierstrassCurve.baseChange, WeierstrassCurve.map]
      rw [hpow12]
      simp
    let T : W.toAffine.Point ≃+ W.toAffine.Point :=
      (AddEquiv.cast (M := fun V : WeierstrassCurve F => V.toAffine.Point)
        hchange.symm).trans (Affine.Point.equivVariableChange W C)
    refine ⟨T, ?_⟩
    intro x y h
    have heq : W.toAffine.Equation x y :=
      W.toAffine.equation_iff_nonsingular.mpr h
    have hxy : y ^ 2 = x ^ 3 + (c : F) := by
      have hcurve := (W.toAffine.equation_iff x y).mp heq
      simpa [W, mordellCurve, WeierstrassCurve.baseChange,
        WeierstrassCurve.map] using hcurve
    have hxyRot : y ^ 2 = (zeta * x) ^ 3 + (c : F) := by
      rw [mul_pow, hzeta.pow_eq_one, one_mul]
      exact hxy
    have hrot : W.toAffine.Nonsingular (zeta * x) y := by
      apply W.toAffine.equation_iff_nonsingular.mp
      apply (W.toAffine.equation_iff (zeta * x) y).mpr
      simpa [W, mordellCurve, WeierstrassCurve.baseChange,
        WeierstrassCurve.map] using hxyRot
    have htarget : W.toAffine.Nonsingular
        ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) := by
      simpa [C, hpow4, hpow6] using hrot
    refine ⟨hrot, ?_⟩
    dsimp [T]
    have cast_some {V U : WeierstrassCurve F} (heq : V = U)
        {a b : F} (hab : V.toAffine.Nonsingular a b) :
        AddEquiv.cast (M := fun Z : WeierstrassCurve F => Z.toAffine.Point) heq
            (.some a b hab) = .some a b (heq ▸ hab) := by
      subst heq
      rfl
    have hcast :
        (AddEquiv.cast
          (M := fun V : WeierstrassCurve F => V.toAffine.Point)
          hchange.symm) (.some x y h) =
        (.some x y (hchange.symm ▸ h) : (C • W).toAffine.Point) :=
      cast_some hchange.symm h
    rw [hcast]
    change Affine.Point.some
      ((C.u : F) ^ 2 * x + C.r)
      ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      htarget = .some (zeta * x) y hrot
    simp [C, hpow4, hpow6]
  have galois_point_action_fixed_base
      (W : WeierstrassCurve ℚ) [W.IsElliptic]
      (sigma : L ≃ₐ[K] L) (P : (W.baseChange K).toAffine.Point) :
      (WeierstrassCurve.Affine.Point.map (sigma.restrictScalars ℚ).toAlgHom)
          (WeierstrassCurve.Affine.Point.map (Algebra.ofId K L) P) =
        WeierstrassCurve.Affine.Point.map (Algebra.ofId K L) P := by
    rcases P with _ | ⟨x, y, h⟩
    · rfl
    · change WeierstrassCurve.Affine.Point.map
          (sigma.restrictScalars ℚ).toAlgHom
          (WeierstrassCurve.Affine.Point.map (Algebra.ofId K L) (.some x y h)) =
        WeierstrassCurve.Affine.Point.map (Algebra.ofId K L) (.some x y h)
      simp only [WeierstrassCurve.Affine.Point.map_some]
      congr 1 <;> exact sigma.commutes _


  have cubic_point_action_commutes_rotation
      (W : WeierstrassCurve ℚ) [W.IsElliptic]
      (zeta : L) (sigma : L ≃ₐ[K] L) (hzeta : sigma zeta = zeta)
      (T : (W.baseChange L).toAffine.Point ≃+ (W.baseChange L).toAffine.Point)
      (hT : ∀ (x y : L) (h : (W.baseChange L).toAffine.Nonsingular x y),
        ∃ hrot : (W.baseChange L).toAffine.Nonsingular (zeta * x) y,
          T (.some x y h) = .some (zeta * x) y hrot)
      (P : (W.baseChange L).toAffine.Point) :
      (WeierstrassCurve.Affine.Point.map (sigma.restrictScalars ℚ).toAlgHom) (T P) =
        T ((WeierstrassCurve.Affine.Point.map (sigma.restrictScalars ℚ).toAlgHom) P) := by
    classical
    cases P with
    | zero =>
        change (WeierstrassCurve.Affine.Point.map
            (sigma.restrictScalars ℚ).toAlgHom)
            (T (0 : (W.baseChange L).toAffine.Point)) =
          T ((WeierstrassCurve.Affine.Point.map
            (sigma.restrictScalars ℚ).toAlgHom)
            (0 : (W.baseChange L).toAffine.Point))
        simp
    | some x y h =>
        obtain ⟨hrot, hTP⟩ := hT x y h
        let hs : (W.baseChange L).toAffine.Nonsingular (sigma x) (sigma y) :=
          (W.toAffine.baseChange_nonsingular
            (f := (sigma.restrictScalars ℚ).toAlgHom)
            (sigma.restrictScalars ℚ).injective x y).mpr h
        obtain ⟨hrotS, hTS⟩ := hT (sigma x) (sigma y) hs
        change WeierstrassCurve.Affine.Point.map
            (sigma.restrictScalars ℚ).toAlgHom (T (.some x y h)) =
          T (WeierstrassCurve.Affine.Point.map
            (sigma.restrictScalars ℚ).toAlgHom (.some x y h))
        rw [hTP]
        simp only [WeierstrassCurve.Affine.Point.map_some]
        have hrotMap : (W.baseChange L).toAffine.Nonsingular
            (sigma (zeta * x)) (sigma y) :=
          (W.toAffine.baseChange_nonsingular
            (f := (sigma.restrictScalars ℚ).toAlgHom)
            (sigma.restrictScalars ℚ).injective (zeta * x) y).mpr hrot
        change (.some (sigma (zeta * x)) (sigma y) hrotMap :
          (W.baseChange L).toAffine.Point) =
            T (.some (sigma x) (sigma y) hs)
        rw [hTS]
        congr 1
        simp [map_mul, hzeta]

  have cubic_point_action_on_coordinates
      (W : WeierstrassCurve ℚ) [W.IsElliptic]
      (zeta : L) (sigma : L ≃ₐ[K] L)
      (T : (W.baseChange L).toAffine.Point ≃+ (W.baseChange L).toAffine.Point)
      (hT : ∀ (x y : L) (h : (W.baseChange L).toAffine.Nonsingular x y),
        ∃ hrot : (W.baseChange L).toAffine.Nonsingular (zeta * x) y,
          T (.some x y h) = .some (zeta * x) y hrot)
      (x y : L) (h : (W.baseChange L).toAffine.Nonsingular x y)
      (hx : sigma x = zeta * x) (hy : sigma y = y) :
      (WeierstrassCurve.Affine.Point.map (sigma.restrictScalars ℚ).toAlgHom)
          (.some x y h) = T (.some x y h) := by
    classical
    obtain ⟨hrot, hTP⟩ := hT x y h
    change WeierstrassCurve.Affine.Point.map
        (sigma.restrictScalars ℚ).toAlgHom (.some x y h) = T (.some x y h)
    rw [hTP]
    simp only [WeierstrassCurve.Affine.Point.map_some]
    congr 1 <;> assumption

  have cubic_point_action_fixed_coordinates
      (W : WeierstrassCurve ℚ) [W.IsElliptic]
      (sigma : L ≃ₐ[K] L)
      (x y : L) (h : (W.baseChange L).toAffine.Nonsingular x y)
      (hx : sigma x = x) (hy : sigma y = y) :
      (WeierstrassCurve.Affine.Point.map (sigma.restrictScalars ℚ).toAlgHom)
          (.some x y h) = .some x y h := by
    classical
    change WeierstrassCurve.Affine.Point.map
        (sigma.restrictScalars ℚ).toAlgHom (.some x y h) = .some x y h
    simp only [WeierstrassCurve.Affine.Point.map_some]
    congr 1 <;> assumption

  have mordell_point_rotation_trace
      (c : ℤ) (zeta : L) (hzeta : IsPrimitiveRoot zeta 3)
      (T : ((mordellCurve c).baseChange L).Point ≃+
        ((mordellCurve c).baseChange L).Point)
      (hT : ∀ (x y : L) (h : ((mordellCurve c).baseChange L).Nonsingular x y),
        ∃ hrot : ((mordellCurve c).baseChange L).Nonsingular (zeta * x) y,
          T (.some x y h) = .some (zeta * x) y hrot)
      (x y : L) (hx : x ≠ 0)
      (h : ((mordellCurve c).baseChange L).Nonsingular x y) :
      (.some x y h : ((mordellCurve c).baseChange L).Point) +
        T (.some x y h) + T (T (.some x y h)) = 0 := by
    obtain ⟨h1, hT1⟩ := hT x y h
    obtain ⟨h2, hT2⟩ := hT (zeta * x) y h1
    have hT2' : T (T (.some x y h)) =
        (.some (zeta ^ 2 * x) y
          (by simpa only [pow_two, mul_assoc] using h2) :
            ((mordellCurve c).baseChange L).Point) := by
      rw [hT1, hT2]
      congr 1
      ring
    rw [hT2', hT1]
    have h2' : ((mordellCurve c).baseChange L).Nonsingular (zeta ^ 2 * x) y := by
      simpa only [pow_two, mul_assoc] using h2
    let W := (mordellCurve c).baseChange L
    change (.some x y h : W.Point) +
      (.some (zeta * x) y h1 : W.Point) +
      (.some (zeta ^ 2 * x) y h2' : W.Point) = 0
    have hzeta1 : zeta ≠ 1 := hzeta.ne_one (by decide)
    have hfac : (zeta - 1) * (zeta ^ 2 + zeta + 1) = 0 := by
      calc
        (zeta - 1) * (zeta ^ 2 + zeta + 1) = zeta ^ 3 - 1 := by ring
        _ = 0 := sub_eq_zero.mpr hzeta.pow_eq_one
    have hsum : zeta ^ 2 + zeta + 1 = 0 :=
      (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hzeta1)
    have hxne : x ≠ zeta * x := by
      intro heq
      have hmul : (1 - zeta) * x = 0 := by
        calc
          (1 - zeta) * x = x - zeta * x := by ring
          _ = 0 := sub_eq_zero.mpr heq
      have hone : 1 - zeta = 0 := (mul_eq_zero.mp hmul).resolve_right hx
      exact hzeta1 (by linear_combination -hone)
    have hthird : -(x + zeta * x) = zeta ^ 2 * x := by
      calc
        -(x + zeta * x) = -(1 + zeta) * x := by ring
        _ = zeta ^ 2 * x := by
          congr 1
          linear_combination -hsum
    have hslope : W.slope x (zeta * x) y y = 0 := by
      rw [W.slope_of_X_ne hxne]
      simp
    have hX : W.addX x (zeta * x) (W.slope x (zeta * x) y y) =
        zeta ^ 2 * x := by
      rw [hslope]
      have htarget : -x - zeta * x = zeta ^ 2 * x := by
        calc
          -x - zeta * x = -(x + zeta * x) := by ring
          _ = zeta ^ 2 * x := hthird
      simpa [W, mordellCurve, WeierstrassCurve.Affine.addX,
        WeierstrassCurve.baseChange, WeierstrassCurve.map] using htarget
    have hY : W.negAddY x (zeta * x) y
        (W.slope x (zeta * x) y y) = y := by
      rw [hslope]
      simp [WeierstrassCurve.Affine.negAddY]
    have hadd :
        (.some x y h : W.Point) + (.some (zeta * x) y h1 : W.Point) =
          -(.some (zeta ^ 2 * x) y h2' : W.Point) := by
      rw [WeierstrassCurve.Affine.Point.add_of_X_ne' hxne]
      simp only [hX, hY]
    calc
      (.some x y h : W.Point) + (.some (zeta * x) y h1 : W.Point) +
          (.some (zeta ^ 2 * x) y h2' : W.Point) =
          -(.some (zeta ^ 2 * x) y h2' : W.Point) +
            (.some (zeta ^ 2 * x) y h2' : W.Point) := by rw [hadd]
      _ = 0 := neg_add_cancel _
  let W : WeierstrassCurve ℚ := mordellCurve c
  letI : W.IsElliptic := hell
  let P : Fin J → ((mordellCurve c).baseChange L).Point :=
    fun i => .some ((d : L) * beta i) (y i : L) (hns i)
  let act (j : Fin J) :
      ((mordellCurve c).baseChange L).Point →+
        ((mordellCurve c).baseChange L).Point :=
    WeierstrassCurve.Affine.Point.map ((sigma j).restrictScalars ℚ).toAlgHom
  let f : ((mordellCurve c).baseChange K).Point →+
      ((mordellCurve c).baseChange L).Point :=
    WeierstrassCurve.Affine.Point.map (Algebra.ofId K L)
  let base : AddSubgroup ((mordellCurve c).baseChange L).Point := f.range
  obtain ⟨T, hT⟩ := mordell_cm_point_rotation
  have hbase (j : Fin J) (q : ((mordellCurve c).baseChange L).Point)
      (hq : q ∈ base) : act j q = q := by
    rcases hq with ⟨q0, rfl⟩
    exact galois_point_action_fixed_base W (sigma j) q0
  have hfixY (j i : Fin J) : sigma j (y i : L) = (y i : L) := by
    simp
  have hfixD (j : Fin J) : sigma j (d : L) = (d : L) := by
    simp
  have hpoint (j i : Fin J) :
      act j (P i) = if i = j then T (P i) else P i := by
    have hx : sigma j ((d : L) * beta i) =
        if i = j then zeta * ((d : L) * beta i) else (d : L) * beta i := by
      rw [map_mul, hfixD, hsigmaBeta]
      by_cases hij : i = j
      · simp only [hij, ↓reduceIte]
        ring
      · simp only [hij, ↓reduceIte]
    by_cases hij : i = j
    · have heq := cubic_point_action_on_coordinates W zeta (sigma j)
        T hT ((d : L) * beta i) (y i : L) (hns i)
        (by simpa only [hij, ↓reduceIte] using hx) (hfixY j i)
      simpa only [act, P, hij, ↓reduceIte] using heq
    · have hfixX : sigma j ((d : L) * beta i) = (d : L) * beta i := by
        simpa only [hij, ↓reduceIte] using hx
      have heq := cubic_point_action_fixed_coordinates W (sigma j)
        ((d : L) * beta i) (y i : L) (hns i) hfixX (hfixY j i)
      simpa only [act, P, hij, ↓reduceIte] using heq
  have hcommute (j : Fin J)
      (q : ((mordellCurve c).baseChange L).Point) :
      act j (T q) = T (act j q) :=
    cubic_point_action_commutes_rotation W zeta (sigma j)
      (hsigmaZeta j) T hT q
  have hrotate (j i : Fin J) :
      act j (T (P i)) = if i = j then T (T (P i)) else T (P i) := by
    rw [hcommute j, hpoint j i]
    split_ifs <;> rfl
  have htriple (i : Fin J) :
      P i + T (P i) + T (T (P i)) = 0 := by
    have hx0 : (d : L) * beta i ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hd) (hbeta0 i)
    exact mordell_point_rotation_trace c zeta hzeta T hT
      ((d : L) * beta i) (y i : L) hx0 (hns i)
  refine ⟨T, hT, ?_⟩
  intro a b hrel
  exact cubic_orbit_independent_mod_fixed J P T.toAddMonoidHom
      act base hbase hpoint hrotate
      htriple hinfinite a b hrel

end D5.S3.Factorization.Mordell.GoldenCubicBlockOrbitIndependence
