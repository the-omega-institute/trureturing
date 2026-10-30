/- GID: D5/S3/Quantum/Matrix/AlternativeMeanLinearization
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/AlternativeMeanLinearization
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Characterization of linearizable alternative means over complex positive matrices. -/

/-
admission_basis: open-problem-resolution (#15957; Proved)
escape_witness: the characterization combines the spectral entrywise relation
  (f_i f_j - a - b t_i t_j) C_ij = 0, the factorization
  -(u-v)(yu-xv)/(x+y), and the three necessity constructions.
  The factorization itself is normalization, not independent new content.
Direct frozen dependencies: none (pinned Mathlib only).
Definitions and live consumers:
  gmInv: definition; consumers=altMean, Rigid, riccati, riccati_unique, commute_gm
  altMean: definition; consumers=Linearizable, necessary_spectrum_and_commute,
    linearizable_of_commute_card, necessity constructions
  Linearizable: definition; consumers=Rigid, necessary_spectrum_and_commute,
    linearizable_of_commute_card, necessity constructions
  Rigid: definition; consumers=sufficient_rigid, necessity constructions, result
  diagHom: definition; consumer=cfc_diag
Per-declaration proof_shape and live consumers:
  half_eq_sqrt: bind-only; consumers=riccati, riccati_unique
  half_inverse: bind-only; consumers=riccati, riccati_unique
  neg_half_pos: bind-only; consumer=riccati
  riccati: bind-only; consumers=necessary_spectrum_and_commute, linearizable_of_commute_card,
    Hiai.SpectralNonconcavity.native_riccati, native_reverse, unitary_native
  riccati_unique: bind-only; consumers=rigid_injective, rigid_quotient_injective, rigid_no_collinear,
    Hiai.SpectralNonconcavity.native_reverse, unitary_native, diagonal_mean_formula
  spectral_pos: bind-only; consumer=necessary_spectrum_and_commute
  spectral_entries: bind-only; consumer=necessary_spectrum_and_commute
  affine_three: bind-only; consumer=necessary_spectrum_and_commute
  off_diagonal_factor: bind-only; consumer=necessary_spectrum_and_commute
  necessary_spectrum_and_commute: bind-only; consumer=sufficient_rigid
  commute_gm: bind-only; consumer=linearizable_of_commute_card
  interpolate_two: bind-only; consumer=linearizable_of_commute_card
  linearizable_of_commute_card: bind-only; consumer=sufficient_rigid
  sufficient_rigid: bind-only; consumer=result
  diagonal_real_spectrum: bind-only; consumers=rigid_injective, rigid_quotient_injective,
    rigid_no_collinear
  witness_pos: bind-only; consumers=rigid_injective, rigid_quotient_injective
  witness_commute: bind-only; consumers=rigid_injective, rigid_quotient_injective
  rigid_injective: bind-only; consumer=result
  rigid_quotient_injective: bind-only; consumer=result
  cfc_diag: bind-only; consumer=rigid_no_collinear
  rigid_no_collinear: bind-only; consumer=result
  strictConvex_or_strictConcave_of_no_collinear: bind-only; consumer=result
  result: bind-only; designated open-problem-resolution conclusion
-/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

noncomputable section
open Matrix Unitary
open scoped ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Matrix.AlternativeMeanLinearization

/-- A⁻¹ ♯ B = A⁻¹ᐟ² (A¹ᐟ² B A¹ᐟ²)¹ᐟ² A⁻¹ᐟ². -/
noncomputable def gmInv {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  cfc (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A *
    cfc (fun x : ℝ => x ^ (1 / 2 : ℝ))
      (cfc (fun x : ℝ => x ^ (1 / 2 : ℝ)) A * B *
        cfc (fun x : ℝ => x ^ (1 / 2 : ℝ)) A) *
    cfc (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A

/-- Definition 2.3: the alternative mean. -/
noncomputable def altMean {n : ℕ} (f : ℝ → ℝ)
    (A B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  cfc f (gmInv A B) * A * cfc f (gmInv A B)

/-- Remark 2.2: linearizability. -/
def Linearizable {n : ℕ} (f : ℝ → ℝ)
    (A B : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ a b : ℝ, altMean f A B = a • A + b • B

/-- The property asked for in the source question. -/
def Rigid (f : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ), A.PosDef → B.PosDef →
    (Linearizable f A B ↔
      (A * B = B * A ∧ (spectrum ℝ (gmInv A B)).ncard ≤ 2))

lemma half_eq_sqrt {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) : cfc (fun x : ℝ => x ^ (1 / 2 : ℝ)) A = CFC.sqrt A := by
  rw [CFC.sqrt_eq_rpow, CFC.rpow_eq_cfc_real hA.posSemidef.nonneg]

lemma half_inverse {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) :
    cfc (fun x : ℝ => x ^ (1 / 2 : ℝ)) A *
      cfc (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A = 1 ∧
    cfc (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A *
      cfc (fun x : ℝ => x ^ (1 / 2 : ℝ)) A = 1 := by
  rw [← CFC.rpow_eq_cfc_real hA.posSemidef.nonneg,
    ← CFC.rpow_eq_cfc_real hA.posSemidef.nonneg]
  exact ⟨CFC.rpow_mul_rpow_neg _ hA.isStrictlyPositive,
    CFC.rpow_neg_mul_rpow _ hA.isStrictlyPositive⟩

private lemma neg_half_pos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) : (cfc (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A).PosDef := by
  rw [← CFC.rpow_eq_cfc_real hA.posSemidef.nonneg]
  exact (hA.isStrictlyPositive.rpow A (-(1 / 2 : ℝ))).posDef

lemma riccati {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    (gmInv A B).PosDef ∧ gmInv A B * A * gmInv A B = B := by
  let S := CFC.sqrt A
  let T := cfc (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A
  have hS : S.PosDef := hA.isStrictlyPositive.sqrt.posDef
  have hT : T.PosDef := neg_half_pos hA
  have hST : S * T = 1 := by simpa only [half_eq_sqrt hA] using (half_inverse hA).1
  have hTS : T * S = 1 := by simpa only [half_eq_sqrt hA] using (half_inverse hA).2
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self _ hA.posSemidef.nonneg
  have hM : (S * B * S).PosDef := by
    simpa only [star_eq_conjTranspose, hS.isHermitian.eq] using
      hS.isUnit.posDef_star_right_conjugate_iff.mpr hB
  have hR : (CFC.sqrt (S * B * S)).PosDef := hM.isStrictlyPositive.sqrt.posDef
  have hgm : gmInv A B = T * CFC.sqrt (S * B * S) * T := by
    simp only [gmInv, half_eq_sqrt hA, half_eq_sqrt hM, S, T]
  refine ⟨?_, ?_⟩
  · rw [hgm]
    simpa only [star_eq_conjTranspose, hT.isHermitian.eq] using
      hT.isUnit.posDef_star_right_conjugate_iff.mpr hR
  · rw [hgm, ← hSS]
    calc
      T * CFC.sqrt (S * B * S) * T * (S * S) *
          (T * CFC.sqrt (S * B * S) * T) =
          T * (CFC.sqrt (S * B * S) * CFC.sqrt (S * B * S)) * T := by
            simp only [mul_assoc, ← mul_assoc T S, ← mul_assoc S T, hTS, one_mul, hST]
      _ = T * (S * B * S) * T := by rw [CFC.sqrt_mul_sqrt_self _ hM.posSemidef.nonneg]
      _ = B := by simp only [mul_assoc, ← mul_assoc T S, hTS, one_mul, hST, mul_one]

lemma riccati_unique {n : ℕ} {A B Y : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) (hY : Y.PosDef) (h : Y * A * Y = B) : gmInv A B = Y := by
  let S := CFC.sqrt A
  let T := cfc (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A
  have hS : S.PosDef := hA.isStrictlyPositive.sqrt.posDef
  have hST : S * T = 1 := by simpa only [half_eq_sqrt hA] using (half_inverse hA).1
  have hTS : T * S = 1 := by simpa only [half_eq_sqrt hA] using (half_inverse hA).2
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self _ hA.posSemidef.nonneg
  have hSYS : (S * Y * S).PosDef := by
    simpa only [star_eq_conjTranspose, hS.isHermitian.eq] using
      hS.isUnit.posDef_star_right_conjugate_iff.mpr hY
  have hM : (S * B * S).PosDef := by
    rw [← h]
    have hB : (Y * A * Y).PosDef := by
      simpa only [star_eq_conjTranspose, hY.isHermitian.eq] using
        hY.isUnit.posDef_star_right_conjugate_iff.mpr hA
    simpa only [star_eq_conjTranspose, hS.isHermitian.eq] using
      hS.isUnit.posDef_star_right_conjugate_iff.mpr hB
  have hr : CFC.sqrt (S * B * S) = S * Y * S := by
    apply CFC.sqrt_unique _ hSYS.posSemidef.nonneg
    calc
      S * Y * S * (S * Y * S) = S * (Y * (S * S) * Y) * S := by simp only [mul_assoc]
      _ = S * B * S := by rw [hSS, h]
  rw [gmInv, half_eq_sqrt hA]
  change T * cfc (fun x : ℝ => x ^ (1 / 2 : ℝ)) (S * B * S) * T = Y
  rw [half_eq_sqrt hM, hr]
  simp only [mul_assoc, ← mul_assoc T S, hTS, one_mul, hST, mul_one]

private lemma spectral_pos {n : ℕ} {A Y : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) (hY : Y.IsHermitian) :
    ((conjStarAlgAut ℂ _ hY.eigenvectorUnitary).symm A).PosDef := by
  have hu : IsUnit (star hY.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := isUnit_coe.star
  have h := hu.posDef_star_right_conjugate_iff.mpr hA
  simpa only [conjStarAlgAut_symm_apply, coe_star, star_star] using h

private lemma spectral_entries {n : ℕ} {A Y : Matrix (Fin n) (Fin n) ℂ}
    (hY : Y.IsHermitian) (f : ℝ → ℝ) (a b : ℝ)
    (h : cfc f Y * A * cfc f Y = a • A + b • (Y * A * Y)) :
    ∀ i j, ((f (hY.eigenvalues i) * f (hY.eigenvalues j) - a -
      b * hY.eigenvalues i * hY.eigenvalues j : ℝ) : ℂ) *
      ((conjStarAlgAut ℂ _ hY.eigenvectorUnitary).symm A) i j = 0 := by
  let e := (conjStarAlgAut ℂ _ hY.eigenvectorUnitary).restrictScalars ℝ
  have heY : e.symm Y = diagonal (fun i => (hY.eigenvalues i : ℂ)) := by
    exact (congrArg e.symm hY.spectral_theorem).trans (e.symm_apply_apply _)
  have heF : e.symm (cfc f Y) = diagonal (fun i => (f (hY.eigenvalues i) : ℂ)) := by
    rw [hY.cfc_eq, IsHermitian.cfc]
    exact e.symm_apply_apply _
  have he := congrArg e.symm h
  simp only [map_mul, map_add, map_smul, heY, heF] at he
  intro i j
  have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) he
  simp only [diagonal_mul, mul_diagonal, Matrix.add_apply, Matrix.smul_apply] at hij
  change ((f (hY.eigenvalues i) * f (hY.eigenvalues j) - a -
    b * hY.eigenvalues i * hY.eigenvalues j : ℝ) : ℂ) * e.symm A i j = 0
  simp only [Algebra.smul_def] at hij
  push_cast
  linear_combination hij

lemma affine_three (g : ℝ → ℝ)
    (hg : StrictConvexOn ℝ (Set.Ioi 0) g ∨ StrictConcaveOn ℝ (Set.Ioi 0) g)
    (a b x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ex : g x = a + b * x) (ey : g y = a + b * y) (ez : g z = a + b * z) : False := by
  have ho : ∀ x y z : ℝ, 0 < x → x < y → y < z →
      g x = a + b * x → g y = a + b * y → g z = a + b * z → False := by
    intro x y z hx hxy hyz ex ey ez
    have hs : (g y - g x) / (y - x) = (g z - g y) / (z - y) := by
      rw [ex, ey, ez]
      field_simp [sub_ne_zero.mpr hxy.ne', sub_ne_zero.mpr hyz.ne']
      ring
    rcases hg with hg | hg
    · exact (ne_of_lt ((strictConvexOn_iff_slope_strict_mono_adjacent.mp hg).2
        (x := x) (y := y) (z := z) hx (show 0 < z by linarith) hxy hyz)) hs
    · exact (ne_of_gt ((strictConcaveOn_iff_slope_strict_anti_adjacent.mp hg).2
        (x := x) (y := y) (z := z) hx (show 0 < z by linarith) hxy hyz)) hs
  rcases lt_or_gt_of_ne hxy with hxy | hxy <;>
    rcases lt_or_gt_of_ne hxz with hxz | hxz <;>
    rcases lt_or_gt_of_ne hyz with hyz | hyz
  all_goals first
    | exact ho x y z hx hxy hyz ex ey ez
    | exact ho x z y hx hxz hyz ex ez ey
    | exact ho y x z hy hxy hxz ey ex ez
    | exact ho y z x hy hyz hxz ey ez ex
    | exact ho z x y hz hxz hxy ez ex ey
    | exact ho z y x hz hyz hxy ez ey ex

private lemma off_diagonal_factor (f : ℝ → ℝ)
    (hi : Set.InjOn f (Set.Ioi 0))
    (hq : Set.InjOn (fun x => f x / x) (Set.Ioi 0))
    (a b x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hne : x ≠ y)
    (ex : f x ^ 2 = a + b * x ^ 2) (ey : f y ^ 2 = a + b * y ^ 2) :
    f x * f y - a - b * x * y ≠ 0 := by
  intro he
  have hp : (f x - f y) * (y * f x - x * f y) = 0 := by
    linear_combination y * ex + x * ey - (x + y) * he
  rcases mul_eq_zero.mp hp with h | h
  · exact hne (hi hx hy (sub_eq_zero.mp h))
  · exact hne (hq hx hy ((div_eq_div_iff hx.ne' hy.ne').mpr (by linarith)))

private lemma necessary_spectrum_and_commute {n : ℕ} (f : ℝ → ℝ)
    (hi : Set.InjOn f (Set.Ioi 0))
    (hq : Set.InjOn (fun x => f x / x) (Set.Ioi 0))
    (hg : StrictConvexOn ℝ (Set.Ioi 0) (fun s => f (Real.sqrt s) ^ 2) ∨
      StrictConcaveOn ℝ (Set.Ioi 0) (fun s => f (Real.sqrt s) ^ 2))
    {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hl : Linearizable f A B) :
    A * B = B * A ∧ (spectrum ℝ (gmInv A B)).ncard ≤ 2 := by
  let Y := gmInv A B
  have hY : Y.PosDef := (riccati hA hB).1
  have hR : Y * A * Y = B := (riccati hA hB).2
  let t := hY.isHermitian.eigenvalues
  let e := (conjStarAlgAut ℂ _ hY.isHermitian.eigenvectorUnitary).restrictScalars ℝ
  let C := e.symm A
  have hC : C.PosDef := spectral_pos hA hY.isHermitian
  obtain ⟨a, b, hab⟩ := hl
  have hab' : cfc f Y * A * cfc f Y = a • A + b • (Y * A * Y) := by
    simpa only [hR, altMean] using hab
  have he := spectral_entries hY.isHermitian f a b hab'
  have hd : ∀ i, f (t i) ^ 2 = a + b * t i ^ 2 := by
    intro i
    have hc : C i i ≠ 0 := ne_of_gt hC.diag_pos
    have hzero := (mul_eq_zero.mp (he i i)).resolve_right hc
    have hr := Complex.ofReal_eq_zero.mp hzero
    dsimp [t]
    nlinarith
  have ht : ∀ i, 0 < t i := hY.eigenvalues_pos
  have hcard : (spectrum ℝ Y).ncard ≤ 2 := by
    rw [hY.isHermitian.spectrum_real_eq_range_eigenvalues]
    by_contra hn
    obtain ⟨x, y, z, ⟨i, rfl⟩, ⟨j, rfl⟩, ⟨k, rfl⟩, hxy, hxz, hyz⟩ :=
      (Set.two_lt_ncard_iff (Set.finite_range _)).mp (lt_of_not_ge hn)
    apply affine_three (fun s => f (Real.sqrt s) ^ 2) hg a b
      (t i ^ 2) (t j ^ 2) (t k ^ 2)
      (sq_pos_of_pos (ht i)) (sq_pos_of_pos (ht j)) (sq_pos_of_pos (ht k))
    · intro heq; apply hxy; change t i = t j; nlinarith [ht i, ht j]
    · intro heq; apply hxz; change t i = t k; nlinarith [ht i, ht k]
    · intro heq; apply hyz; change t j = t k; nlinarith [ht j, ht k]
    · simpa only [Real.sqrt_sq (ht i).le] using hd i
    · simpa only [Real.sqrt_sq (ht j).le] using hd j
    · simpa only [Real.sqrt_sq (ht k).le] using hd k
  refine ⟨?_, hcard⟩
  have heY : e.symm Y = diagonal (fun i => (t i : ℂ)) :=
    (congrArg e.symm hY.isHermitian.spectral_theorem).trans (e.symm_apply_apply _)
  have hCY : C * diagonal (fun i => (t i : ℂ)) = diagonal (fun i => (t i : ℂ)) * C := by
    ext i j
    simp only [mul_diagonal, diagonal_mul]
    by_cases hij : t i = t j
    · rw [hij]; ring
    · have hc : C i j = 0 := (mul_eq_zero.mp (he i j)).resolve_left
        (Complex.ofReal_ne_zero.mpr (off_diagonal_factor f hi hq a b (t i) (t j)
          (ht i) (ht j) hij (hd i) (hd j)))
      rw [hc]; simp
  have hAY : Commute A Y := by
    apply e.symm.injective
    change e.symm (A * Y) = e.symm (Y * A)
    simpa only [map_mul, heY] using hCY
  rw [← hR]
  exact ((hAY.mul_right (Commute.refl A)).mul_right hAY).eq

private lemma commute_gm {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (h : Commute A B) : Commute A (gmInv A B) := by
  have hS := ((Commute.refl A).cfc_real (fun x : ℝ => x ^ (1 / 2 : ℝ))).symm
  have hT := ((Commute.refl A).cfc_real (fun x : ℝ => x ^ (-(1 / 2 : ℝ)))).symm
  have hM := (hS.mul_right h).mul_right hS
  exact (hT.mul_right ((hM.symm.cfc_real _).symm)).mul_right hT

private lemma interpolate_two {n : ℕ} (t : Fin n → ℝ) (hp : ∀ i, 0 < t i)
    (hc : (Set.range t).ncard ≤ 2) (f : ℝ → ℝ) :
    ∃ a b : ℝ, ∀ i, f (t i) ^ 2 = a + b * t i ^ 2 := by
  classical
  by_cases hn : Nonempty (Fin n)
  · obtain ⟨i⟩ := hn
    by_cases he : ∀ j, t j = t i
    · exact ⟨f (t i) ^ 2, 0, fun j => by rw [he j]; ring⟩
    · push Not at he
      obtain ⟨j, hj⟩ := he
      have ht : ∀ k, t k = t i ∨ t k = t j := by
        intro k
        by_contra hk
        push Not at hk
        have hs : {t i, t j, t k} ⊆ Set.range t := by
          intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl | rfl <;> exact Set.mem_range_self _
        have hc3 : ({t i, t j, t k} : Set ℝ).ncard = 3 := by
          simp [Set.ncard_insert_of_notMem, hj.symm, hk.1.symm, hk.2.symm]
        have := Set.ncard_le_ncard hs (Set.finite_range t)
        omega
      have hd : t j ^ 2 - t i ^ 2 ≠ 0 := by
        have := hp i
        have := hp j
        intro hd
        have hh : t j ^ 2 = t i ^ 2 := sub_eq_zero.mp hd
        exact hj ((sq_eq_sq₀ (hp j).le (hp i).le).mp hh)
      refine ⟨(t j ^ 2 * f (t i) ^ 2 - t i ^ 2 * f (t j) ^ 2) / (t j ^ 2 - t i ^ 2),
        (f (t j) ^ 2 - f (t i) ^ 2) / (t j ^ 2 - t i ^ 2), ?_⟩
      intro k
      rcases ht k with hk | hk <;> rw [hk] <;> field_simp <;> ring
  · exact ⟨0, 0, fun i => (hn ⟨i⟩).elim⟩

private lemma linearizable_of_commute_card {n : ℕ} (f : ℝ → ℝ)
    {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hcomm : A * B = B * A) (hcard : (spectrum ℝ (gmInv A B)).ncard ≤ 2) :
    Linearizable f A B := by
  let Y := gmInv A B
  have hY := (riccati hA hB).1
  have hAY : Commute A Y := commute_gm hcomm
  have hAF : Commute A (cfc f Y) := (hAY.symm.cfc_real f).symm
  have hc : (Set.range hY.isHermitian.eigenvalues).ncard ≤ 2 := by
    rwa [← hY.isHermitian.spectrum_real_eq_range_eigenvalues]
  obtain ⟨a, b, hab⟩ := interpolate_two hY.isHermitian.eigenvalues hY.eigenvalues_pos hc f
  have hFF : cfc f Y * cfc f Y = a • (1 : Matrix (Fin n) (Fin n) ℂ) + b • (Y * Y) := by
    let e := (conjStarAlgAut ℂ _ hY.isHermitian.eigenvectorUnitary).restrictScalars ℝ
    have heY : e.symm Y = diagonal (fun i => (hY.isHermitian.eigenvalues i : ℂ)) :=
      (congrArg e.symm hY.isHermitian.spectral_theorem).trans (e.symm_apply_apply _)
    have heF : e.symm (cfc f Y) = diagonal (fun i => (f (hY.isHermitian.eigenvalues i) : ℂ)) := by
      rw [hY.isHermitian.cfc_eq, IsHermitian.cfc]
      exact e.symm_apply_apply _
    apply e.symm.injective
    change e.symm (cfc f Y * cfc f Y) = e.symm (a • (1 : Matrix (Fin n) (Fin n) ℂ) + b • (Y * Y))
    simp only [map_mul, map_add, map_smul, map_one, heY, heF]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [diagonal_mul, diagonal_apply_eq, Matrix.add_apply, Matrix.smul_apply,
        Matrix.one_apply_eq, Complex.real_smul]
      simpa only [pow_two, Complex.ofReal_add, Complex.ofReal_mul, mul_one] using congrArg Complex.ofReal (hab i)
    · simp [Matrix.one_apply_ne hij, hij]
  refine ⟨a, b, ?_⟩
  change cfc f Y * A * cfc f Y = a • A + b • B
  rw [← hAF.eq, mul_assoc, hFF, mul_add, mul_smul_comm, mul_one, mul_smul_comm]
  congr 1
  congr 1
  rw [← mul_assoc, hAY.eq]
  exact (riccati hA hB).2

private lemma sufficient_rigid (f : ℝ → ℝ)
    (hi : Set.InjOn f (Set.Ioi 0))
    (hq : Set.InjOn (fun x => f x / x) (Set.Ioi 0))
    (hg : StrictConvexOn ℝ (Set.Ioi 0) (fun s => f (Real.sqrt s) ^ 2) ∨
      StrictConcaveOn ℝ (Set.Ioi 0) (fun s => f (Real.sqrt s) ^ 2)) : Rigid f := by
  intro n A B hA hB
  exact ⟨necessary_spectrum_and_commute f hi hq hg hA hB,
    fun h => linearizable_of_commute_card f hA hB h.1 h.2⟩

private lemma diagonal_real_spectrum {n : ℕ} (t : Fin n → ℝ) :
    spectrum ℝ (diagonal (fun i => (t i : ℂ))) = Set.range t := by
  ext s
  rw [← spectrum.algebraMap_mem_iff ℂ, spectrum_diagonal]
  simp

private lemma witness_pos : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℂ).PosDef := by
  let J : Matrix (Fin 1) (Fin 2) ℂ := !![1, 1]
  convert (Matrix.PosDef.one : (1 : Matrix (Fin 2) (Fin 2) ℂ).PosDef).add_posSemidef
    (posSemidef_conjTranspose_mul_self J) using 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [J, Matrix.mul_apply, Matrix.conjTranspose_apply]

private lemma witness_commute {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℂ) *
      (diagonal ![(x : ℂ), (y : ℂ)] * !![2, 1; 1, 2] * diagonal ![(x : ℂ), (y : ℂ)]) =
      (diagonal ![(x : ℂ), (y : ℂ)] * !![2, 1; 1, 2] * diagonal ![(x : ℂ), (y : ℂ)]) *
        !![2, 1; 1, 2]) : x = y := by
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 1).re) h
  simp [Matrix.mul_apply, Fin.sum_univ_two, diagonal, Complex.mul_re] at he
  nlinarith [sq_nonneg (x - y)]

private lemma rigid_injective (f : ℝ → ℝ) (hR : Rigid f) : Set.InjOn f (Set.Ioi 0) := by
  intro x hx y hy hxy
  let A : Matrix (Fin 2) (Fin 2) ℂ := !![2, 1; 1, 2]
  let Y : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![(x : ℂ), (y : ℂ)]
  have hY : Y.PosDef := by
    apply PosDef.diagonal
    intro i
    fin_cases i
    · simpa [Y] using (show (0 : ℂ) < (x : ℂ) from by exact_mod_cast hx)
    · simpa [Y] using (show (0 : ℂ) < (y : ℂ) from by exact_mod_cast hy)
  have hB : (Y * A * Y).PosDef := by
    simpa only [star_eq_conjTranspose, hY.isHermitian.eq] using
      hY.isUnit.posDef_star_right_conjugate_iff.mpr witness_pos
  have hgm : gmInv A (Y * A * Y) = Y := riccati_unique witness_pos hY rfl
  have hF : cfc f Y = (f x) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    calc
      cfc f Y = cfc (fun _ : ℝ => f x) Y := by
        apply cfc_congr
        intro z hz
        have hz' : z ∈ Set.range ![x, y] := by
          have heq : Y = diagonal (fun i => ((![x, y] : Fin 2 → ℝ) i : ℂ)) := by
            ext i j
            fin_cases i <;> fin_cases j <;> rfl
          rwa [heq, diagonal_real_spectrum] at hz
        obtain ⟨i, rfl⟩ := hz'
        fin_cases i <;> simp [hxy]
      _ = _ := by
        simpa only [Algebra.algebraMap_eq_smul_one] using
          cfc_const (R := ℝ) (f x) Y (show IsSelfAdjoint Y from hY.isHermitian)
  apply witness_commute hx hy
  exact (hR 2 A (Y * A * Y) witness_pos hB).mp ⟨(f x)^2, 0, by
    simp [altMean, hgm, hF, smul_smul, pow_two]⟩ |>.1

private lemma rigid_quotient_injective (f : ℝ → ℝ) (hR : Rigid f) :
    Set.InjOn (fun x => f x / x) (Set.Ioi 0) := by
  intro x hx y hy hxy
  let A : Matrix (Fin 2) (Fin 2) ℂ := !![2, 1; 1, 2]
  let Y : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![(x : ℂ), (y : ℂ)]
  have hY : Y.PosDef := by
    apply PosDef.diagonal
    intro i
    fin_cases i
    · simpa [Y] using (show (0 : ℂ) < (x : ℂ) from by exact_mod_cast hx)
    · simpa [Y] using (show (0 : ℂ) < (y : ℂ) from by exact_mod_cast hy)
  have hB : (Y * A * Y).PosDef := by
    simpa only [star_eq_conjTranspose, hY.isHermitian.eq] using
      hY.isUnit.posDef_star_right_conjugate_iff.mpr witness_pos
  have hgm : gmInv A (Y * A * Y) = Y := riccati_unique witness_pos hY rfl
  have hF : cfc f Y = (f x / x) • Y := by
    calc
      cfc f Y = cfc (fun t : ℝ => (f x / x) * t) Y := by
        apply cfc_congr
        intro z hz
        have hz' : z ∈ Set.range ![x, y] := by
          have heq : Y = diagonal (fun i => ((![x, y] : Fin 2 → ℝ) i : ℂ)) := by
            ext i j
            fin_cases i <;> fin_cases j <;> rfl
          rwa [heq, diagonal_real_spectrum] at hz
        obtain ⟨i, rfl⟩ := hz'
        fin_cases i
        · simpa using (div_mul_cancel₀ (f x) (ne_of_gt hx)).symm
        · change f y = (f x / x) * y
          change f x / x = f y / y at hxy
          rw [hxy, div_mul_cancel₀ _ (ne_of_gt hy)]
      _ = _ := cfc_const_mul_id (f x / x) Y (show IsSelfAdjoint Y from hY.isHermitian)
  apply witness_commute hx hy
  exact (hR 2 A (Y * A * Y) witness_pos hB).mp ⟨0, (f x / x)^2, by
    simp [altMean, hgm, hF, smul_smul, pow_two]⟩ |>.1

private def diagHom (n : ℕ) : (Fin n → ℂ) →⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toAlgHom := diagonalAlgHom (n := Fin n) (α := ℂ) ℂ
  map_star' a := by ext i j; simp [diagonal]; split_ifs <;> simp_all

private lemma cfc_diag {n : ℕ} [NeZero n] (f : ℝ → ℝ) (d : Fin n → ℝ) :
    cfc f (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => (f (d i) : ℂ)) := by
  let : ContinuousFunctionalCalculus ℂ ℂ IsStarNormal := IsStarNormal.instContinuousFunctionalCalculus
  let : ContinuousFunctionalCalculus ℂ (Fin n → ℂ) IsStarNormal := IsStarNormal.instContinuousFunctionalCalculus
  let : ContinuousFunctionalCalculus ℝ (Fin n → ℂ) IsSelfAdjoint := IsSelfAdjoint.instContinuousFunctionalCalculus
  have hc : ContinuousOn f (spectrum ℝ (fun i => (d i : ℂ))) := by
    apply Set.Finite.continuousOn _ f
    rw [Pi.spectrum_eq]
    apply Set.finite_iUnion
    intro i
    change (spectrum ℝ (algebraMap ℝ ℂ (d i))).Finite
    rw [CFC.spectrum_algebraMap_eq]
    exact Set.finite_singleton _
  have hmap := (diagHom n).map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint) f (fun i => (d i : ℂ)) hc (by
    change Continuous (fun d : Fin n → ℂ => diagonal d)
    apply continuous_pi; intro i; apply continuous_pi; intro j
    by_cases h : i = j <;> simp [diagonal, h] <;> fun_prop) (by
      change star (fun i => (d i : ℂ)) = _
      ext i; simp) (by
      exact (isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)).isSelfAdjoint)
  change cfc f ((diagHom n) (fun i => (d i : ℂ))) = _
  rw [← hmap, cfc_map_pi (S := ℂ) (p := IsSelfAdjoint) (q := fun _ => IsSelfAdjoint) f (fun i => (d i : ℂ)) (by simpa only [Pi.spectrum_eq] using hc)
    (by change star (fun i => (d i : ℂ)) = _; ext i; simp)
    (by intro i; change star (d i : ℂ) = _; simp)]
  change diagonal (fun i => cfc f (d i : ℂ)) = _
  congr 1
  funext i
  simpa using (cfc_algebraMap (A := ℂ) (d i) f)

private lemma rigid_no_collinear (f : ℝ → ℝ) (hr : Rigid f)
    (s t u : ℝ) (hs : 0 < s) (hst : s < t) (htu : t < u) :
    (f (Real.sqrt t) ^ 2 - f (Real.sqrt s) ^ 2) / (t-s) ≠
    (f (Real.sqrt u) ^ 2 - f (Real.sqrt t) ^ 2) / (u-t) := by
  intro he
  let d : Fin 3 → ℝ := ![s,t,u]
  let Y : Matrix (Fin 3) (Fin 3) ℂ := diagonal (fun i => (Real.sqrt (d i) : ℂ))
  let B : Matrix (Fin 3) (Fin 3) ℂ := diagonal (fun i => (d i : ℂ))
  have hd : ∀ i, 0 < d i := by intro i; fin_cases i <;> dsimp [d] <;> linarith
  have hY : Y.PosDef := .diagonal (fun i => by exact_mod_cast Real.sqrt_pos.2 (hd i))
  have hB : B.PosDef := .diagonal (fun i => by exact_mod_cast hd i)
  have hYY : Y * 1 * Y = B := by
    simp only [mul_one, Y, B, diagonal_mul_diagonal]
    congr 1; ext i
    exact_mod_cast Real.mul_self_sqrt (hd i).le
  have hgm : gmInv 1 B = Y := riccati_unique Matrix.PosDef.one hY hYY
  let b := (f (Real.sqrt t)^2 - f (Real.sqrt s)^2) / (t-s)
  let a := f (Real.sqrt s)^2 - b*s
  have hst0 : t-s ≠ 0 := by linarith
  have htu0 : u-t ≠ 0 := by linarith
  have ht : f (Real.sqrt t)^2 = a + b*t := by dsimp [a,b]; field_simp; ring
  have hu : f (Real.sqrt u)^2 = a + b*u := by
    have hb : f (Real.sqrt u)^2 - f (Real.sqrt t)^2 = b*(u-t) := by
      dsimp [b]; rw [he]; exact (div_mul_cancel₀ _ htu0).symm
    dsimp [a] at *; nlinarith
  have hlin : Linearizable f 1 B := by
    refine ⟨a,b,?_⟩
    rw [altMean, hgm]
    dsimp [Y]
    rw [cfc_diag]
    simp only [mul_one, diagonal_mul_diagonal]
    ext i j
    by_cases hij : i=j
    · subst j
      simp only [diagonal_apply_eq, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
        Complex.real_smul, mul_one, B, diagonal_apply_eq]
      have hi : f (Real.sqrt (d i))^2 = a + b*d i := by
        fin_cases i
        · dsimp [d,a]; ring
        · exact ht
        · exact hu
      exact_mod_cast (by simpa only [pow_two] using hi)
    · simp [diagonal, hij, B]
  have hcard := ((hr 3 1 B Matrix.PosDef.one hB).mp hlin).2
  rw [hgm, diagonal_real_spectrum] at hcard
  have hthree : 2 < (Set.range (fun i : Fin 3 => Real.sqrt (d i))).ncard := by
    apply (Set.two_lt_ncard (Set.finite_range _)).mpr
    refine ⟨Real.sqrt s, ⟨0,rfl⟩, Real.sqrt t, ⟨1,rfl⟩,
      Real.sqrt u, ⟨2,rfl⟩, ?_, ?_, ?_⟩
    · exact (Real.sqrt_lt_sqrt hs.le hst).ne
    · exact (Real.sqrt_lt_sqrt hs.le (hst.trans htu)).ne
    · exact (Real.sqrt_lt_sqrt (by linarith) htu).ne
  omega


private lemma strictConvex_or_strictConcave_of_no_collinear
    (g : ℝ → ℝ) (hc : ContinuousOn g (Set.Ioi 0))
    (hne : ∀ s t u : ℝ, 0 < s → s < t → t < u →
      (g t - g s) / (t - s) ≠ (g u - g t) / (u - t)) :
    StrictConvexOn ℝ (Set.Ioi 0) g ∨ StrictConcaveOn ℝ (Set.Ioi 0) g := by
  let T : Set (ℝ × ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2.1 ∧ p.2.1 < p.2.2}
  let d : (ℝ × ℝ × ℝ) → ℝ := fun p =>
    (g p.2.1 - g p.1) / (p.2.1 - p.1) -
      (g p.2.2 - g p.2.1) / (p.2.2 - p.2.1)
  have hT : Convex ℝ T := by
    intro p hp q hq a b ha hb hab
    simp only [T, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] at *
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using hq
    have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    constructor
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hp.1) (mul_nonneg hb hq.1.le)
    constructor
    · nlinarith [mul_pos ha' (sub_pos.mpr hp.2.1),
        mul_nonneg hb (sub_pos.mpr hq.2.1).le]
    · nlinarith [mul_pos ha' (sub_pos.mpr hp.2.2),
        mul_nonneg hb (sub_pos.mpr hq.2.2).le]
  have h0 : ContinuousOn (fun p : ℝ × ℝ × ℝ => p.1) T := continuous_fst.continuousOn
  have h1 : ContinuousOn (fun p : ℝ × ℝ × ℝ => p.2.1) T :=
    (continuous_fst.comp continuous_snd).continuousOn
  have h2 : ContinuousOn (fun p : ℝ × ℝ × ℝ => p.2.2) T :=
    (continuous_snd.comp continuous_snd).continuousOn
  have hg0 := hc.comp h0 (fun p hp => hp.1)
  have hg1 := hc.comp h1 (fun p hp => lt_trans hp.1 hp.2.1)
  have hg2 := hc.comp h2 (fun p hp => lt_trans (lt_trans hp.1 hp.2.1) hp.2.2)
  have hd : ContinuousOn d T :=
    ((hg1.sub hg0).div (h1.sub h0) (fun p hp => sub_ne_zero.mpr hp.2.1.ne')).sub
      ((hg2.sub hg1).div (h2.sub h1) (fun p hp => sub_ne_zero.mpr hp.2.2.ne'))
  have hdne : ∀ p ∈ T, d p ≠ 0 := by
    intro p hp
    exact sub_ne_zero.mpr (hne p.1 p.2.1 p.2.2 hp.1 hp.2.1 hp.2.2)
  rcases hT.isPreconnected.mapsTo_Ioi_or_Iio hd hdne with hpos | hneg
  · right
    apply strictConcaveOn_of_slope_strict_anti_adjacent (convex_Ioi 0)
    intro x y z hx hz hxy hyz
    have h := hpos (show (x, y, z) ∈ T from ⟨hx, hxy, hyz⟩)
    exact sub_pos.mp h
  · left
    apply strictConvexOn_of_slope_strict_mono_adjacent (convex_Ioi 0)
    intro x y z hx hz hxy hyz
    have h := hneg (show (x, y, z) ∈ T from ⟨hx, hxy, hyz⟩)
    exact sub_neg.mp h

set_option linter.unusedVariables false in
/-- Characterization of the alternative means whose linearizability detects commutation
and at most two geometric spectral values, uniformly over complex matrix sizes. -/
theorem result (f : ℝ → ℝ) (hc : ContinuousOn f (Set.Ioi 0))
    (hpos : ∀ x, 0 < x → 0 < f x) (h1 : f 1 = 1) :
    Rigid f ↔ (Set.InjOn f (Set.Ioi 0) ∧
      Set.InjOn (fun x => f x / x) (Set.Ioi 0) ∧
      (StrictConvexOn ℝ (Set.Ioi 0) (fun s => f (Real.sqrt s) ^ 2) ∨
        StrictConcaveOn ℝ (Set.Ioi 0) (fun s => f (Real.sqrt s) ^ 2))) := by
  clear hpos h1
  constructor
  · intro hr
    refine ⟨rigid_injective f hr, rigid_quotient_injective f hr, ?_⟩
    apply strictConvex_or_strictConcave_of_no_collinear
    · exact (hc.comp Real.continuous_sqrt.continuousOn
        (fun s hs => Real.sqrt_pos.2 hs)).pow 2
    · exact rigid_no_collinear f hr
  · rintro ⟨hi, hq, hg⟩
    exact sufficient_rigid f hi hq hg

end D5.S3.Quantum.Matrix.AlternativeMeanLinearization
