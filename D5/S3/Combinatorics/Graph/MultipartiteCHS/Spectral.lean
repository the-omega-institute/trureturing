/- GID: D5/S3/Combinatorics/Graph/MultipartiteCHS/Spectral
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/MultipartiteCHS/Spectral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff]
   utility: none
   digest: Multipartite adjacency determinants and complete homogeneous spectral recurrence. -/

import D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs
import D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! Determinant reduction and reciprocal-series coefficients. -/

open scoped BigOperators
open Finset Polynomial Matrix
open D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs

namespace D5.S3.Combinatorics.Graph.MultipartiteCHS.Spectral

private def vertexAdj {R : Type*} [Zero R] [One R] {r : ℕ} (a : Fin r → ℕ) :
    Matrix (Vtx a) (Vtx a) R := fun x y => if x.1 = y.1 then 0 else 1

private def partAdj {R : Type*} [NatCast R] [Zero R] {r : ℕ} (a : Fin r → ℕ) :
    Matrix (Fin r) (Fin r) R := fun i j => if i = j then 0 else (a j : R)

private theorem det_reduce {R : Type*} [CommRing R] {r : ℕ} (a : Fin r → ℕ) (t : R) :
    (1 + t • vertexAdj (R := R) a).det = (1 + t • partAdj (R := R) a).det := by
  classical
  let U : Matrix (Vtx a) (Fin r) R := fun x i => if x.1 = i then 1 else 0
  let B : Matrix (Fin r) (Vtx a) R := fun i y => if i = y.1 then 0 else t
  have hUB : U * B = t • vertexAdj a := by
    apply Matrix.ext
    intro x y
    change (∑ k : Fin r, (if x.1 = k then 1 else 0) *
      (if k = y.1 then 0 else t)) = t * (if x.1 = y.1 then 0 else 1)
    rw [Finset.sum_eq_single x.1]
    · split_ifs <;> simp_all
    · intro k hk h
      simp [Ne.symm h]
    · simp
  have hBU : B * U = t • partAdj a := by
    apply Matrix.ext
    intro i j
    change (∑ x : Vtx a, (if i = x.1 then 0 else t) *
      (if x.1 = j then 1 else 0)) = t * (if i = j then 0 else (a j : R))
    rw [Fintype.sum_sigma]
    rw [Finset.sum_eq_single j]
    · by_cases h : i = j <;> simp [h, mul_comm]
    · intro k hk h
      simp [h]
    · simp
  rw [← hUB, Matrix.det_one_add_mul_comm, hBU]

private theorem det_identity_sub_ones {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (Matrix.of (fun i j : ι => (if i = j then (1 : ℝ) else 0) - 1)).det =
      1 - Fintype.card ι := by
  have h := Matrix.det_one_add_replicateCol_mul_replicateRow
    (ι := Unit) (fun _ : ι => (-1 : ℝ)) (fun _ : ι => (1 : ℝ))
  convert h using 1
  · congr 1
    apply Matrix.ext
    intro i j
    simp [Matrix.one_apply, Matrix.mul_apply, sub_eq_add_neg]
  · simp [dotProduct, sub_eq_add_neg]

private theorem part_minor {r : ℕ} (a : Fin r → ℕ) (s : Finset (Fin r)) :
    ((-partAdj (R := ℝ) a).submatrix (Subtype.val : s → Fin r) Subtype.val).det =
      (1 - (s.card : ℝ)) * ∏ i ∈ s, (a i : ℝ) := by
  classical
  have he : ((-partAdj (R := ℝ) a).submatrix (Subtype.val : s → Fin r) Subtype.val) =
      Matrix.of (fun i j : s => (a j.val : ℝ) * ((if i = j then 1 else 0) - 1)) := by
    apply Matrix.ext
    intro i j
    by_cases h : i = j
    · subst j
      simp [partAdj]
    · have hn : i.val ≠ j.val := fun h' => h (Subtype.ext h')
      simp [partAdj, h, hn]
  rw [he]
  have h := Matrix.det_mul_row (fun j : s => (a j.val : ℝ))
    (Matrix.of (fun i j : s => (if i = j then (1 : ℝ) else 0) - 1))
  change (Matrix.of (fun i j : s => (a j.val : ℝ) *
    ((if i = j then 1 else 0) - 1))).det = _ at h
  rw [h, det_identity_sub_ones]
  rw [Fintype.card_coe, mul_comm]
  congr 1
  exact Finset.prod_coe_sort (f := fun i => (a i : ℝ)) (s := s)

private theorem part_pencil_coeff {r : ℕ} (a : Fin r → ℕ) (k : ℕ) :
    ((1 : Matrix (Fin r) (Fin r) ℝ[X]) +
      (Polynomial.X : ℝ[X]) • (-partAdj (R := ℝ) a).map Polynomial.C).det.coeff k =
      (1 - (k : ℝ)) *
        ∑ s ∈ (univ : Finset (Fin r)).powersetCard k, ∏ i ∈ s, (a i : ℝ) := by
  classical
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  simp_rw [part_minor]
  rw [mul_sum]
  apply sum_congr rfl
  intro s hs
  rw [(Finset.mem_powersetCard.mp hs).2]

private theorem spectral_product {r : ℕ} (a : Fin r → ℕ) :
    (adj a).charpolyRev =
      ∏ i : Vtx a, (1 - Polynomial.C ((adj_isHermitian a).eigenvalues i) * Polynomial.X) := by
  classical
  have h1 : (1 : ℝ[X]).reverse = 1 := by
    simpa using (Polynomial.reverse_C (1 : ℝ))
  rw [← Matrix.reverse_charpoly, (adj_isHermitian a).charpoly_eq]
  have hr (s : Finset (Vtx a)) :
      (∏ i ∈ s, (Polynomial.X - Polynomial.C ((adj_isHermitian a).eigenvalues i))).reverse =
        ∏ i ∈ s, (1 - Polynomial.C ((adj_isHermitian a).eigenvalues i) * Polynomial.X) := by
    induction s using Finset.induction_on with
    | empty => simp [h1]
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Polynomial.reverse_mul_of_domain, ih]
      congr 1
      rw [sub_eq_add_neg, ← map_neg Polynomial.C, Polynomial.reverse_add_C]
      simp [show (Polynomial.X : ℝ[X]).reverse = 1 by
        simpa [h1] using (Polynomial.reverse_X_mul (1 : ℝ[X]))]
      ring
  exact hr univ

private theorem pencil_coeff {r : ℕ} (a : Fin r → ℕ) (k : ℕ) :
    (adj a).charpolyRev.coeff k =
      (1 - (k : ℝ)) *
        ∑ s ∈ (univ : Finset (Fin r)).powersetCard k, ∏ i ∈ s, (a i : ℝ) := by
  have h := det_reduce (R := ℝ[X]) a (-Polynomial.X)
  have hv : vertexAdj (R := ℝ[X]) a = (adj a).map Polynomial.C := by
    apply Matrix.ext
    intro x y
    simp [vertexAdj, adj]
  have hp : partAdj (R := ℝ[X]) a = (partAdj (R := ℝ) a).map Polynomial.C := by
    apply Matrix.ext
    intro i j
    by_cases hij : i = j <;> simp [partAdj, hij]
  rw [hv, hp] at h
  have he : (adj a).charpolyRev =
      ((1 : Matrix (Fin r) (Fin r) ℝ[X]) +
        (Polynomial.X : ℝ[X]) • (-partAdj (R := ℝ) a).map Polynomial.C).det := by
    simpa [Matrix.charpolyRev, sub_eq_add_neg, Matrix.map_neg, smul_neg, neg_smul] using h
  rw [he, part_pencil_coeff]

private noncomputable def detPolynomial {r : ℕ} (a : Fin r → ℕ) : ℝ[X] :=
  ∑ k ∈ range (r + 1), Polynomial.C ((1 - (k : ℝ)) *
    ∑ s ∈ (univ : Finset (Fin r)).powersetCard k, ∏ i ∈ s, (a i : ℝ)) * Polynomial.X ^ k

private theorem det_formula {r : ℕ} (a : Fin r → ℕ) :
    (adj a).charpolyRev = detPolynomial a := by
  classical
  apply Polynomial.ext
  intro k
  rw [pencil_coeff]
  by_cases hk : k < r + 1
  · simp only [detPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    simp [hk]
  · have he : (univ : Finset (Fin r)).powersetCard k = ∅ :=
      Finset.powersetCard_eq_empty.mpr (by simpa using (show r < k by omega))
    simp only [detPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    simp [hk, he]

private theorem chs_series_product {r : ℕ} (a : Fin r → ℕ) :
    (PowerSeries.mk fun d => chs a d) * (detPolynomial a : PowerSeries ℝ) = 1 := by
  classical
  have h := D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm.hsymm_series_product
    (adj_isHermitian a).eigenvalues
  let f : ℝ[X] →+* PowerSeries ℝ := Polynomial.coeToPowerSeries.ringHom
  have hp := congrArg f (spectral_product a)
  rw [det_formula] at hp
  have hp' : (detPolynomial a : PowerSeries ℝ) =
      ∏ i : Vtx a, (1 - PowerSeries.C ((adj_isHermitian a).eigenvalues i) * PowerSeries.X) := by
    simpa [f] using hp
  simpa only [chs, hp'] using h

private theorem chs_recurrence {r : ℕ} (a : Fin r → ℕ) {d : ℕ} (hd : 1 ≤ d) :
    chs a d = ∑ j ∈ Icc 2 d, ((j : ℝ) - 1) *
      (∑ s ∈ (univ : Finset (Fin r)).powersetCard j, ∏ i ∈ s, (a i : ℝ)) * chs a (d - j) := by
  classical
  have hc := congrArg (PowerSeries.coeff (R := ℝ) d) (chs_series_product a)
  rw [mul_comm] at hc
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  have hp (j : ℕ) : PowerSeries.coeff j (detPolynomial a : PowerSeries ℝ) =
      (1 - (j : ℝ)) *
        ∑ s ∈ (univ : Finset (Fin r)).powersetCard j, ∏ i ∈ s, (a i : ℝ) := by
    rw [Polynomial.coeff_coe, ← det_formula, pencil_coeff]
  simp only [hp, PowerSeries.coeff_mk, PowerSeries.coeff_one,
    if_neg (show d ≠ 0 by omega)] at hc
  let F : ℕ → ℝ := fun j => (1 - (j : ℝ)) *
    (∑ s ∈ (univ : Finset (Fin r)).powersetCard j, ∏ i ∈ s, (a i : ℝ)) * chs a (d - j)
  have hs : ∑ j ∈ range (d + 1), F j = ∑ j ∈ insert 0 (Icc 2 d), F j := by
    symm
    apply Finset.sum_subset
    · intro j hj
      simp only [mem_insert, mem_Icc, mem_range] at *
      omega
    · intro j hj hj'
      have hj1 : j = 1 := by
        simp only [mem_insert, mem_Icc, mem_range] at *
        omega
      simp [F, hj1]
  have hz : F 0 = chs a d := by simp [F]
  have hn : (0 : ℕ) ∉ Icc 2 d := by simp
  have hf : ∑ j ∈ Icc 2 d, F j =
      -(∑ j ∈ Icc 2 d, ((j : ℝ) - 1) *
        (∑ s ∈ (univ : Finset (Fin r)).powersetCard j, ∏ i ∈ s, (a i : ℝ)) * chs a (d - j)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [F]
    ring
  change (∑ j ∈ range (d + 1), F j) = 0 at hc
  rw [hs, Finset.sum_insert hn, hz, hf] at hc
  linarith

end D5.S3.Combinatorics.Graph.MultipartiteCHS.Spectral
