/- GID: D5/S3/Factorization/Mordell/CubicOrbitCanonicalHeightGram
   generality: G
   mirror-B: D5/B/S3/Factorization/Mordell/CubicOrbitCanonicalHeightGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cubic elliptic orbits have positive canonical heights and orthogonal Gram blocks of determinant three quarters of the squared height. -/

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


namespace D5.S3.Factorization.Mordell.CubicOrbitCanonicalHeightGram




theorem mordell_family_canonical_height_gram
    {K L : Type*} [Field K] [Field L]
    [Algebra ℚ K] [Algebra ℚ L] [Algebra K L] [IsScalarTower ℚ K L]
    [NumberField L] [DecidableEq L]
    (J : ℕ) (c : ℤ) [(mordellCurve c).IsElliptic]
    [((mordellCurve c).baseChange L).IsElliptic]
    (zeta : L) (hzeta : IsPrimitiveRoot zeta 3)
    (P : Fin J → ((mordellCurve c).baseChange L).Point)
    (T : ((mordellCurve c).baseChange L).Point ≃+
      ((mordellCurve c).baseChange L).Point)
    (hT : ∀ (x y : L) (h : ((mordellCurve c).baseChange L).Nonsingular x y),
      ∃ hrot : ((mordellCurve c).baseChange L).Nonsingular (zeta * x) y,
        T (.some x y h) = .some (zeta * x) y hrot)
    (sigma : Fin J → (L ≃ₐ[K] L))
    (hpoint : ∀ j i,
      (WeierstrassCurve.Affine.Point.map
        ((sigma j).restrictScalars ℚ).toAlgHom) (P i) =
        if i = j then T (P i) else P i)
    (hrotate : ∀ j i,
      (WeierstrassCurve.Affine.Point.map
        ((sigma j).restrictScalars ℚ).toAlgHom) (T (P i)) =
        if i = j then T (T (P i)) else T (P i))
    (htriple : ∀ i, P i + T (P i) + T (T (P i)) = 0)
    (hinfinite : ∀ i, ¬ IsOfFinAddOrder (P i)) :
    let W := (mordellCurve c).baseChange L
    let Q := TauCeti.QuadraticMap.ofParallelogram
      (f := WeierstrassCurve.Affine.Point.canonicalHeight (W := W))
      (smul_right_injective ℝ two_ne_zero) (by
        intro A B
        rw [two_smul, two_smul]
        linarith [(WeierstrassCurve.Affine.Point.canonicalHeight_properties
          (W := W)).2.2 A B])
    letI : Invertible (2 : Module.End ℤ ℝ) :=
      (Invertible.map (MonoidHom.smulOneHom (M := ℝ)
        (N := Module.End ℤ ℝ)) 2).copy 2 (by
          ext x
          simp [← ofNat_smul_eq_nsmul ℝ])
    let B := QuadraticMap.associated' Q
    let H : Fin J → ℝ := fun j => Q (P j)
    let orbit : Fin 2 × Fin J → W.Point :=
      fun ej => if ej.1 = 0 then P ej.2 else T (P ej.2)
    let gram : Matrix (Fin 2 × Fin J) (Fin 2 × Fin J) ℝ :=
      fun ej fk => B (orbit ej) (orbit fk)
    let realGram : Matrix (Fin J) (Fin J) ℝ :=
      fun i j => B (P i) (P j)
    let block : Fin J → Matrix (Fin 2) (Fin 2) ℝ :=
      fun j e f => if e = f then H j else -(H j) / 2
    gram = Matrix.blockDiagonal block ∧
      realGram = Matrix.diagonal H ∧
      gram.det = (3 / 4 : ℝ) ^ J * ∏ j : Fin J, (H j) ^ 2 ∧
      (∀ j, 0 < H j) ∧
      0 < gram.det := by
  classical
  letI : Invertible (2 : Module.End ℤ ℝ) :=
    (Invertible.map (MonoidHom.smulOneHom (M := ℝ)
      (N := Module.End ℤ ℝ)) 2).copy 2 (by
        ext x
        simp [← ofNat_smul_eq_nsmul ℝ])
  let W := (mordellCurve c).baseChange L
  have hfinite_x (x : L) : {q : W.Point | q.xRep 0 = x}.Finite := by
    have hfinite_rep (x : L) : {q : W.Point | q.xRep = ![x, 1]}.Finite := by
      rcases Set.eq_empty_or_nonempty {q : W.Point | q.xRep = ![x, 1]} with h | h
      · exact h ▸ Set.finite_empty
      choose q hq using h
      simp only [Set.mem_ofPred_eq] at hq
      rw [show {p : W.Point | p.xRep = ![x, 1]} = {q, -q} by
        ext p : 1
        simp [← hq, WeierstrassCurve.Affine.Point.xRep_eq_xRep_iff]]
      simp
    have hsubset : {q : W.Point | q.xRep 0 = x} ⊆
        {q | q.xRep = ![x, 1]} ∪ {0} := by
      intro q hq
      match q with
      | 0 => simp
      | .some x' y h => simp_all [WeierstrassCurve.Affine.Point.xRep_some]
    exact ((hfinite_rep x).union (Set.finite_singleton 0)).subset hsubset
  letI : Northcott (WeierstrassCurve.Affine.Point.naiveHeight (W := W)) := by
    eta_expand
    have hheight (q : W.Point) :
        q.naiveHeight = logHeight₁ (q.xRep 0) := by
      match q with
      | 0 => simp [WeierstrassCurve.Affine.Point.naiveHeight,
          WeierstrassCurve.Affine.Point.xRep]
      | .some .. => simpa [WeierstrassCurve.Affine.Point.naiveHeight] using
          (logHeight₁_eq_logHeight _).symm
    simp only [hheight]
    rw [← Function.comp_def]
    have : Filter.TendstoCofinite (fun q : W.Point ↦ q.xRep 0) :=
      (Filter.tendstoCofinite_iff_finite_preimage_singleton _).mpr hfinite_x
    exact Northcott.comp_of_finite_fibers ..
  letI : Northcott (WeierstrassCurve.Affine.Point.canonicalHeight (W := W)) := by
    obtain ⟨D, hD⟩ :=
      (WeierstrassCurve.Affine.Point.canonicalHeight_properties (W := W)).2.1
    refine ⟨fun B ↦ (Northcott.finite_le
      (h := WeierstrassCurve.Affine.Point.naiveHeight (W := W)) (2 * (B + D))).subset ?_⟩
    intro q hq
    simp only [Set.mem_ofPred_eq] at hq ⊢
    linarith [(abs_le.1 (hD q)).1]
  let Q : QuadraticMap ℤ W.Point ℝ :=
    TauCeti.QuadraticMap.ofParallelogram
      (f := WeierstrassCurve.Affine.Point.canonicalHeight (W := W))
      (smul_right_injective ℝ two_ne_zero) (by
        intro A B
        rw [two_smul, two_smul]
        linarith [(WeierstrassCurve.Affine.Point.canonicalHeight_properties
          (W := W)).2.2 A B])
  let act (j : Fin J) : W.Point →+ W.Point :=
    WeierstrassCurve.Affine.Point.map ((sigma j).restrictScalars ℚ).toAlgHom
  have hQsigma (j : Fin J) (q : W.Point) : Q (act j q) = Q q := by
    let s : L ≃ₐ[ℚ] L := (sigma j).restrictScalars ℚ
    have hnaive (r : W.Point) :
        (act j r).naiveHeight = r.naiveHeight := by
      change (WeierstrassCurve.Affine.Point.map s.toAlgHom r).naiveHeight =
        r.naiveHeight
      cases r with
      | zero =>
          simp [WeierstrassCurve.Affine.Point.naiveHeight,
            WeierstrassCurve.Affine.Point.map,
            WeierstrassCurve.Affine.Point.xRep]
      | some x y h =>
          change logHeight ![(sigma j) x, 1] = logHeight ![x, 1]
          letI : Algebra ℚ L := DivisionRing.toRatAlgebra
          have hg : logHeight₁ (sigma j x) = logHeight₁ x := by
            change Real.log (mulHeight₁ (sigma j x)) = Real.log (mulHeight₁ x)
            exact congrArg Real.log (NumberField.scalar_mul_height_galois
              ((sigma j).toRingEquiv.toRatAlgEquiv) x)
          simpa only [logHeight₁_eq_logHeight] using hg
    change (act j q).canonicalHeight = q.canonicalHeight
    unfold WeierstrassCurve.Affine.Point.canonicalHeight
    congr 1
    funext n
    rw [← map_nsmul]
    exact congrArg (fun h : ℝ => h / (2 * 4 ^ n)) (hnaive _)
  have hQT (q : W.Point) : Q (T q) = Q q := by
    have hmulHeight (x : L) : logHeight₁ (zeta * x) = logHeight₁ x := by
      have hzeta0 : zeta ≠ 0 := hzeta.ne_zero (by decide)
      have hroot : logHeight₁ zeta = 0 := by
        have h := logHeight₁_pow zeta 3
        rw [hzeta.pow_eq_one, logHeight₁_one] at h
        norm_num at h
        linarith
      have hrootInv : logHeight₁ zeta⁻¹ = 0 := by
        rw [logHeight₁_inv, hroot]
      have hforward := logHeight₁_mul_le zeta x
      have hbackward := logHeight₁_mul_le zeta⁻¹ (zeta * x)
      have hcancel : zeta⁻¹ * (zeta * x) = x := by
        simp [hzeta0, mul_assoc]
      rw [hroot] at hforward
      rw [hrootInv, hcancel] at hbackward
      linarith
    have hnaive (r : W.Point) : (T r).naiveHeight = r.naiveHeight := by
      cases r with
      | zero =>
        change (T (0 : W.Point)).naiveHeight = (0 : W.Point).naiveHeight
        rw [map_zero]
      | some x y h =>
        obtain ⟨hrot, hTrot⟩ := hT x y h
        rw [hTrot]
        change logHeight ![zeta * x, 1] = logHeight ![x, 1]
        simpa only [logHeight₁_eq_logHeight] using hmulHeight x
    change (T q).canonicalHeight = q.canonicalHeight
    unfold WeierstrassCurve.Affine.Point.canonicalHeight
    congr 1
    funext n
    rw [← map_nsmul]
    exact congrArg (fun h : ℝ => h / (2 * 4 ^ n)) (hnaive _)
  have hpositive (i : Fin J) : 0 < Q (P i) := by
    change 0 < (P i).canonicalHeight
    have hne : (P i).canonicalHeight ≠ 0 := by
      intro h
      have hQ : Q (P i) = 0 := by
        change (P i).canonicalHeight = 0
        exact h
      have hfinite : (Set.range (fun n : ℕ ↦ n • P i)).Finite := by
        refine (Northcott.finite_le
          (h := WeierstrassCurve.Affine.Point.canonicalHeight (W := W)) 0).subset ?_
        rintro q ⟨n, rfl⟩
        have hscale := Q.map_smul (n : ℤ) (P i)
        rw [hQ, smul_zero] at hscale
        have hvanish : Q (n • P i) = 0 := by
          simpa only [Nat.cast_smul_eq_nsmul ℤ] using hscale
        change Q (n • P i) ≤ 0
        exact le_of_eq hvanish
      have hnot : ¬ Function.Injective (fun n : ℕ ↦ n • P i) := by
        intro hinj
        exact (Set.infinite_range_of_injective hinj) hfinite
      obtain ⟨m, n, heq, hmn⟩ := Function.not_injective_iff.mp hnot
      have hcollision {a b : ℕ} (hab : a < b) (heq : a • P i = b • P i) :
          IsOfFinAddOrder (P i) := by
        apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
        refine ⟨b - a, Nat.sub_pos_of_lt hab, ?_⟩
        have hadd : (b - a) • P i + a • P i = b • P i := by
          rw [← add_nsmul, Nat.sub_add_cancel hab.le]
        apply add_right_cancel (b := a • P i)
        simpa only [hadd, zero_add] using heq.symm
      apply hinfinite i
      rcases lt_or_gt_of_ne hmn with hlt | hgt
      · exact hcollision hlt heq
      · exact hcollision hgt heq.symm
    have hnonneg : 0 ≤ (P i).canonicalHeight :=
      ge_of_tendsto'
        ((WeierstrassCurve.Affine.Point.canonicalHeight_properties (W := W)).1 (P i)) fun n ↦
        div_nonneg (by change 0 ≤ logHeight (((2 ^ n) • P i).xRep); positivity)
          (by positivity)
    exact lt_of_le_of_ne
      hnonneg hne.symm
  let G := W.Point
  let sigma := act
  let B := QuadraticMap.associated' Q
  let H : Fin J → ℝ := fun j => Q (P j)
  let orbit : Fin 2 × Fin J → G :=
    fun ej => if ej.1 = 0 then P ej.2 else T (P ej.2)
  let gram : Matrix (Fin 2 × Fin J) (Fin 2 × Fin J) ℝ :=
    fun ej fk => B (orbit ej) (orbit fk)
  let realGram : Matrix (Fin J) (Fin J) ℝ :=
    fun i j => B (P i) (P j)
  let block : Fin J → Matrix (Fin 2) (Fin 2) ℝ :=
    fun j e f => if e = f then H j else -(H j) / 2
  have hpairInvariant (j : Fin J) (x y : G) :
      B (sigma j x) (sigma j y) = B x y := by
    dsimp [B]
    rw [QuadraticMap.associated_apply, QuadraticMap.associated_apply,
      ← map_add, hQsigma j (x + y), hQsigma j x, hQsigma j y]
  have hpairZero (j : Fin J) (x : G) (hfix : sigma j x = x) :
      B x (P j) = 0 ∧ B x (T (P j)) = 0 := by
    have hfirst : B x (P j) = B x (T (P j)) := by
      have h := hpairInvariant j x (P j)
      rw [hfix, hpoint j j, if_pos rfl] at h
      exact h.symm
    have hsecond : B x (T (P j)) = B x (T (T (P j))) := by
      have h := hpairInvariant j x (T (P j))
      rw [hfix, hrotate j j, if_pos rfl] at h
      exact h.symm
    have hsum : B x (P j) + B x (T (P j)) + B x (T (T (P j))) = 0 := by
      have h := congrArg (B x) (htriple j)
      simpa only [map_add, map_zero] using h
    constructor <;> linarith
  have hcross (i j : Fin J) (hij : i ≠ j) (e f : Fin 2) :
      B (orbit (e, i)) (orbit (f, j)) = 0 := by
    have hfix : sigma j (orbit (e, i)) = orbit (e, i) := by
      fin_cases e
      · change sigma j (P i) = P i
        simpa only [sigma, act] using (hpoint j i).trans (if_neg hij)
      · change sigma j (T (P i)) = T (P i)
        simpa only [sigma, act] using (hrotate j i).trans (if_neg hij)
    have hz := hpairZero j (orbit (e, i)) hfix
    fin_cases f
    · simpa [orbit] using hz.1
    · simpa [orbit] using hz.2
  have hdiag (j : Fin J) : B (P j) (P j) = H j := by
    exact QuadraticMap.associated_eq_self_apply ℤ Q (P j)
  have hdiagT (j : Fin J) : B (T (P j)) (T (P j)) = H j := by
    rw [QuadraticMap.associated_eq_self_apply ℤ Q, hQT]
  have hoff (j : Fin J) : B (P j) (T (P j)) = -(H j) / 2 := by
    have hsum : P j + T (P j) = -T (T (P j)) := by
      linear_combination (norm := abel) (htriple j)
    have hsumQ : Q (P j + T (P j)) = H j := by
      rw [hsum, Q.map_neg, hQT (T (P j)), hQT (P j)]
    have hsumB : B (P j + T (P j)) (P j + T (P j)) = H j := by
      rw [QuadraticMap.associated_eq_self_apply ℤ Q]
      exact hsumQ
    have hexpand : B (P j + T (P j)) (P j + T (P j)) =
        B (P j) (P j) + B (P j) (T (P j)) +
        B (T (P j)) (P j) + B (T (P j)) (T (P j)) := by
      simp only [LinearMap.map_add₂, map_add, LinearMap.add_apply]
      ring
    have hsym : B (T (P j)) (P j) = B (P j) (T (P j)) :=
      QuadraticMap.associated_isSymm ℤ Q _ _
    linarith [hdiag j, hdiagT j]
  have hgram : gram = Matrix.blockDiagonal block := by
    ext ⟨e, i⟩ ⟨f, j⟩
    by_cases hij : i = j
    · subst j
      rw [Matrix.blockDiagonal_apply_eq]
      fin_cases e <;> fin_cases f
      · simpa [gram, orbit, block] using hdiag i
      · simpa [gram, orbit, block] using hoff i
      · have hsym : B (T (P i)) (P i) = B (P i) (T (P i)) :=
          QuadraticMap.associated_isSymm ℤ Q _ _
        simpa [gram, orbit, block] using hsym.trans (hoff i)
      · simpa [gram, orbit, block] using hdiagT i
    · rw [Matrix.blockDiagonal_apply_ne block e f hij]
      exact hcross i j hij e f
  have hreal : realGram = Matrix.diagonal H := by
    ext i j
    by_cases hij : i = j
    · subst j
      simpa [realGram, Matrix.diagonal_apply] using hdiag i
    · have hfix : sigma j (P i) = P i := by
        simpa [sigma, act, hij] using hpoint j i
      have hz := (hpairZero j (P i) hfix).1
      simpa [realGram, Matrix.diagonal_apply, hij] using hz
  have hblockdet (j : Fin J) : (block j).det = (3 / 4 : ℝ) * H j ^ 2 := by
    rw [Matrix.det_fin_two]
    simp [block]
    ring
  have hdet : gram.det = (3 / 4 : ℝ) ^ J * ∏ j : Fin J, H j ^ 2 := by
    rw [hgram, Matrix.det_blockDiagonal]
    simp_rw [hblockdet]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hdetpos : 0 < gram.det := by
    rw [hdet]
    apply mul_pos (by positivity)
    apply Finset.prod_pos
    intro j _
    exact pow_pos (hpositive j) 2
  exact ⟨hgram, hreal, hdet, hpositive, hdetpos⟩



end D5.S3.Factorization.Mordell.CubicOrbitCanonicalHeightGram
