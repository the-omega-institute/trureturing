/- GID: D5/S3/Combinatorics/Graph/RegularCHS/TwoRegular
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/RegularCHS/TwoRegular
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Basic.Real.Basic, mathlib/module/Mathlib.Tactic.Linarith, mathlib/module/Mathlib.Tactic.Positivity, mathlib/module/Mathlib.RingTheory.PowerSeries.Substitution, mathlib/module/Mathlib.RingTheory.PowerSeries.WellKnown, mathlib/module/Mathlib.RingTheory.PowerSeries.Catalan, mathlib/module/Mathlib.Tactic.Ring, mathlib/module/Mathlib.RingTheory.Localization.FractionRing, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected, mathlib/module/Mathlib.Combinatorics.SimpleGraph.AdjMatrix, mathlib/module/Mathlib.LinearAlgebra.Matrix.Block, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Matching, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: none
   digest: Cycle partitions and complete homogeneous coefficient domination for two-regular graphs. -/

import D5.S3.Combinatorics.Graph.Brooks.General
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.Tactic.Ring
import D5.S3.Combinatorics.SpectralGraph.CyclicTridiagonalTransferTrace
import D5.S0.Observation.MatrixTracePowerSum
import Mathlib.RingTheory.Localization.FractionRing
import D5.S3.Combinatorics.Graph.RegularCHS.Defs
import D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
import D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Finite




noncomputable section
open Classical PowerSeries Finset
open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular

/-- The cycle denominator factor after the Catalan change of variable. -/
def cycleKernel (l : ℕ) : PowerSeries ℝ :=
  (mk fun k : ℕ => (k + 1 : ℝ)).subst ((X : PowerSeries ℝ) ^ l)

private theorem coeff_cycleKernel {l : ℕ} (hl : 0 < l) (k : ℕ) :
    coeff k (cycleKernel l) = if l ∣ k then ((k / l : ℕ) : ℝ) + 1 else 0 := by
  simp [cycleKernel, coeff_subst_X_pow (Nat.ne_of_gt hl)]

private theorem cycleKernel_nonneg {l : ℕ} (hl : 0 < l) (k : ℕ) :
    0 ≤ coeff k (cycleKernel l) := by
  rw [coeff_cycleKernel hl]
  split_ifs <;> positivity

private theorem coeff_mul_ge_single (A B : PowerSeries ℝ)
    (hA : ∀ k, 0 ≤ coeff k A) (hB : ∀ k, 0 ≤ coeff k B) (i j : ℕ) :
    coeff i A * coeff j B ≤ coeff (i + j) (A * B) := by
  rw [coeff_mul]
  exact Finset.single_le_sum (f := fun p : ℕ × ℕ => coeff p.1 A * coeff p.2 B)
    (fun p _ => mul_nonneg (hA p.1) (hB p.2))
    (by simp : (i, j) ∈ Finset.HasAntidiagonal.antidiagonal (i + j))

/-- Merging two positive cycle lengths decreases every denominator coefficient. -/
private theorem cycleKernel_add_le {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (k : ℕ) :
    coeff k (cycleKernel (a + b)) ≤ coeff k (cycleKernel a * cycleKernel b) := by
  by_cases hd : a + b ∣ k
  · obtain ⟨j, rfl⟩ := hd
    have he : (a + b) * j = a * j + b * j := Nat.add_mul a b j
    rw [he]
    have h := coeff_mul_ge_single (cycleKernel a) (cycleKernel b)
      (cycleKernel_nonneg ha) (cycleKernel_nonneg hb) (a * j) (b * j)
    have hleft : coeff (a * j + b * j) (cycleKernel (a + b)) = (j + 1 : ℝ) := by
      rw [← he, coeff_cycleKernel (by omega), if_pos (dvd_mul_right _ _),
        Nat.mul_div_cancel_left j (by omega : 0 < a + b)]
    rw [hleft]
    rw [coeff_cycleKernel ha, coeff_cycleKernel hb,
      if_pos (dvd_mul_right a j), if_pos (dvd_mul_right b j),
      Nat.mul_div_cancel_left j ha, Nat.mul_div_cancel_left j hb] at h
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  · rw [coeff_cycleKernel (by omega), if_neg hd, coeff_mul]
    exact Finset.sum_nonneg fun p _ =>
      mul_nonneg (cycleKernel_nonneg ha p.1) (cycleKernel_nonneg hb p.2)

private theorem coeff_mul_mono_left (A B C : PowerSeries ℝ)
    (hA : ∀ k, 0 ≤ coeff k A) (hBC : ∀ k, coeff k B ≤ coeff k C) (k : ℕ) :
    coeff k (A * B) ≤ coeff k (A * C) := by
  simp only [coeff_mul]
  exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hBC p.2) (hA p.1)

/-- A single cycle denominator is dominated by the product for a partition of its length. -/
theorem cycleKernel_sum_le_prod (ls : List ℕ) (hne : ls ≠ [])
    (hpos : ∀ l ∈ ls, 0 < l) (k : ℕ) :
    coeff k (cycleKernel ls.sum) ≤ coeff k (ls.map cycleKernel).prod := by
  induction ls generalizing k with
  | nil => exact (hne rfl).elim
  | cons a ls ih =>
    cases ls with
    | nil => simp
    | cons b tail =>
      have ha := hpos a (by simp)
      have hrest : ∀ l ∈ b :: tail, 0 < l := by
        intro l hl
        exact hpos l (List.mem_cons_of_mem a hl)
      have hb : 0 < (b :: tail).sum := by
        have := hrest b (by simp)
        simp only [List.sum_cons]
        omega
      calc
        coeff k (cycleKernel (a :: b :: tail).sum) ≤
            coeff k (cycleKernel a * cycleKernel (b :: tail).sum) :=
          cycleKernel_add_le ha hb k
        _ ≤ coeff k (cycleKernel a * ((b :: tail).map cycleKernel).prod) :=
          coeff_mul_mono_left _ _ _ (cycleKernel_nonneg ha)
            (fun j => ih (by simp) hrest j) k
        _ = _ := by simp

/-- The denominator factor is the reciprocal of the squared cycle polynomial. -/
private theorem cycleKernel_mul_denominator {l : ℕ} (hl : 0 < l) :
    cycleKernel l * (1 - (X : PowerSeries ℝ) ^ l) ^ 2 = 1 := by
  have hmk : (mk fun k : ℕ => (k + 1 : ℝ)) = (mk 1 : PowerSeries ℝ) ^ 2 := by
    simpa [Nat.choose_one_right, Nat.cast_add, Nat.cast_one, add_comm] using
      (mk_one_pow_eq_mk_choose_add ℝ 1).symm
  have he : (mk fun k : ℕ => (k + 1 : ℝ)) * (1 - (X : PowerSeries ℝ)) ^ 2 = 1 := by
    rw [hmk, ← mul_pow, mk_one_mul_one_sub_eq_one, one_pow]
  have hs := congrArg (subst ((X : PowerSeries ℝ) ^ l)) he
  have hh : HasSubst ((X : PowerSeries ℝ) ^ l) := .X_pow (Nat.ne_of_gt hl)
  simpa [cycleKernel, subst_mul hh, subst_pow hh, subst_sub hh, subst_X hh,
    ← coe_substAlgHom hh] using hs

end D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular


noncomputable section
open Classical PowerSeries Finset
open scoped BigOperators
namespace D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular

private theorem series_mul_nonneg (A B : PowerSeries ℝ)
    (hA : ∀ k, 0 ≤ coeff k A) (hB : ∀ k, 0 ≤ coeff k B) (k : ℕ) :
    0 ≤ coeff k (A * B) := by
  rw [coeff_mul]
  exact Finset.sum_nonneg fun p _ => mul_nonneg (hA p.1) (hB p.2)

private theorem series_pow_nonneg (A : PowerSeries ℝ)
    (hA : ∀ k, 0 ≤ coeff k A) (e k : ℕ) : 0 ≤ coeff k (A ^ e) := by
  induction e generalizing k with
  | zero => simp only [pow_zero, coeff_one]; split_ifs <;> positivity
  | succ e ih =>
    rw [pow_succ]
    exact series_mul_nonneg _ _ (fun j => ih j) hA k

private theorem series_subst_mono (A B q : PowerSeries ℝ) (hs : HasSubst q)
    (hq : ∀ k, 0 ≤ coeff k q) (hAB : ∀ k, coeff k A ≤ coeff k B) (k : ℕ) :
    coeff k (A.subst q) ≤ coeff k (B.subst q) := by
  rw [coeff_subst' hs, coeff_subst' hs]
  apply finsum_le_finsum (coeff_subst_finite' hs A k) (coeff_subst_finite' hs B k)
  intro j
  simpa only [smul_eq_mul] using
    mul_le_mul_of_nonneg_right (hAB j) (series_pow_nonneg q hq j k)

end D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular

namespace D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular

/-- The odd Catalan series solves the change of variable for adjacency cycles. -/
private def oddCatalan : PowerSeries ℝ :=
  X * (PowerSeries.catalanSeries.map (Nat.castRingHom ℝ)).subst
    ((X : PowerSeries ℝ) ^ 2)

private theorem oddCatalan_constantCoeff : constantCoeff oddCatalan = 0 := by
  simp [oddCatalan]

private theorem oddCatalan_nonneg (k : ℕ) : 0 ≤ coeff k oddCatalan := by
  apply series_mul_nonneg
  · intro j
    simp only [coeff_X]
    split_ifs <;> positivity
  · intro j
    rw [coeff_subst_X_pow (by decide : (2 : ℕ) ≠ 0)]
    split_ifs <;> simp [coeff_map, catalanSeries_coeff]

private theorem oddCatalan_equation : oddCatalan = X * (1 + oddCatalan ^ 2) := by
  let F : PowerSeries ℝ := PowerSeries.catalanSeries.map (Nat.castRingHom ℝ)
  let C : PowerSeries ℝ := F.subst ((X : PowerSeries ℝ) ^ 2)
  have hm : F ^ 2 * X + 1 = F := by
    simpa [F] using congrArg (PowerSeries.map (Nat.castRingHom ℝ))
      PowerSeries.catalanSeries_sq_mul_X_add_one
  have hs : C ^ 2 * X ^ 2 + 1 = C := by
    have h := congrArg (substAlgHom (R := ℝ) (S := ℝ)
      (HasSubst.X_pow (by decide : (2 : ℕ) ≠ 0))) hm
    simpa only [map_add, map_mul, map_pow, map_one, substAlgHom_X,
      coe_substAlgHom, C] using h
  change X * C = X * (1 + (X * C) ^ 2)
  calc
    X * C = X * (C ^ 2 * X ^ 2 + 1) := by rw [hs]
    _ = _ := by ring

end D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular

namespace D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular

/-- The Catalan change of variable preserves the comparison of cycle partitions. -/
private theorem cycleKernel_partition_bound (ls : List ℕ) (hne : ls ≠ [])
    (hpos : ∀ l ∈ ls, 0 < l) (k : ℕ) :
    coeff k ((1 + oddCatalan ^ 2) ^ ls.sum * (cycleKernel ls.sum).subst oddCatalan) ≤
      coeff k ((1 + oddCatalan ^ 2) ^ ls.sum *
        (ls.map fun l => (cycleKernel l).subst oddCatalan).prod) := by
  have hs : HasSubst oddCatalan := .of_constantCoeff_zero oddCatalan_constantCoeff
  have hS (j : ℕ) : 0 ≤ coeff j ((1 + oddCatalan ^ 2) ^ ls.sum) := by
    apply series_pow_nonneg
    intro i
    rw [map_add]
    have hi : (0 : ℝ) ≤ coeff i (1 : PowerSeries ℝ) := by
      simp only [coeff_one]; split_ifs <;> positivity
    exact add_nonneg hi (series_pow_nonneg oddCatalan oddCatalan_nonneg 2 i)
  have hprod : ((ls.map cycleKernel).prod).subst oddCatalan =
      (ls.map fun l => (cycleKernel l).subst oddCatalan).prod := by
    clear hne hpos hS
    induction ls with
    | nil => simp [← coe_substAlgHom hs]
    | cons l ls ih => simp only [List.map_cons, List.prod_cons, subst_mul hs, ih]
  rw [← hprod]
  exact coeff_mul_mono_left _ _ _ hS
    (series_subst_mono _ _ _ hs oddCatalan_nonneg
      (cycleKernel_sum_le_prod ls hne hpos)) k

end D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular

noncomputable section
open Classical Matrix
open scoped BigOperators Matrix
open D5.S3.Combinatorics.SpectralGraph.CyclicTridiagonalTransferTrace
open D5.S0.Observation.MatrixTracePowerSum

namespace D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular

private theorem evolution_const {R : Type*} [CommRing R] (d : R) (n : ℕ) :
    evolution (fun _ => d) n = transfer d ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [evolution, ih, pow_succ']

/-- The cycle determinant after clearing the Catalan denominator. -/
private theorem det_cycle_pencil {R : Type*} [CommRing R] [IsDomain R] (n : ℕ) [DecidableRel (SimpleGraph.cycleGraph (n + 3)).Adj] (q : R) :
    ((1 + q ^ 2) • (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) R) -
      q • (SimpleGraph.cycleGraph (n + 3)).adjMatrix R).det = (1 - q ^ (n + 3)) ^ 2 := by
  let f : R →+* FractionRing R := algebraMap R (FractionRing R)
  have hm : (((1 + q ^ 2) • (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) R) -
      q • (SimpleGraph.cycleGraph (n + 3)).adjMatrix R).map f) =
      (1 + (f q) ^ 2) • (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) (FractionRing R)) -
        f q • (SimpleGraph.cycleGraph (n + 3)).adjMatrix (FractionRing R) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
      Matrix.one_apply, SimpleGraph.adjMatrix_apply, map_sub, map_mul, map_add, map_one, map_pow]
    split_ifs <;> simp
  apply IsFractionRing.injective R (FractionRing R)
  change f _ = f _
  rw [f.map_det]
  change (((1 + q ^ 2) • (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) R) -
    q • (SimpleGraph.cycleGraph (n + 3)).adjMatrix R).map f).det =
      f ((1 - q ^ (n + 3)) ^ 2)
  rw [hm]
  have hf : ((1 + (f q) ^ 2) •
      (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) (FractionRing R)) -
      f q • (SimpleGraph.cycleGraph (n + 3)).adjMatrix (FractionRing R)).det =
        (1 - (f q) ^ (n + 3)) ^ 2 := by
    generalize f q = z
    by_cases hq : z = 0
    · subst z
      simp
    let d : FractionRing R := (1 + z ^ 2) / z
    let T : Matrix (Fin 2) (Fin 2) (FractionRing R) := transfer d
    have hqd : z * d = 1 + z ^ 2 := by dsimp [d]; field_simp
    have htrace : Matrix.trace ((z • T) ^ (n + 3)) = 1 + z ^ (2 * (n + 3)) := by
      have ht : Matrix.trace (z • T) = 1 + z ^ 2 := by
        simpa [T, transfer, Matrix.trace_fin_two] using hqd
      have hd : (z • T).det = 1 * z ^ 2 := by
        simp [T, Matrix.det_smul, transfer_det]
      simpa [one_pow, pow_mul] using trace_pow_eq_add_pow (z • T) 1 (z ^ 2) ht hd (n + 3)
    have htrace' : z ^ (n + 3) * Matrix.trace (T ^ (n + 3)) =
        1 + z ^ (2 * (n + 3)) := by
      simpa [smul_pow, Matrix.trace_smul, smul_eq_mul] using htrace
    have hmat : (1 + z ^ 2) • (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) (FractionRing R)) -
        z • (SimpleGraph.cycleGraph (n + 3)).adjMatrix (FractionRing R) =
        z • cycleDiag (n + 3) (fun _ => d) := by
      ext i j
      simp only [cycleDiag, Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal_apply,
        Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp_all [mul_sub]
    rw [hmat, Matrix.det_smul, Fintype.card_fin, cycleDiag_det_transfer, evolution_const]
    change z ^ (n + 3) * (Matrix.trace (T ^ (n + 3)) - 2) = _
    rw [mul_sub, htrace']
    ring
  simpa only [map_pow, map_sub, map_one] using hf

end D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular


noncomputable section
open Classical Matrix Finset PowerSeries
open scoped BigOperators
open D5.S3.Combinatorics.Graph.RegularCHS.Defs
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
open D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm (hsymm_series_product)

namespace D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular

private theorem pencil_poly_spectrum {n : ℕ} (G : SimpleGraph (Fin n)) :
    (1 - (Polynomial.X : Polynomial ℝ) • G.adjMatrix (Polynomial ℝ)).det =
      ∏ i, (1 - Polynomial.C ((adjMatrix_isHermitian G).eigenvalues i) * Polynomial.X) := by
  apply Polynomial.funext
  intro t
  let f : Polynomial ℝ →+* ℝ := Polynomial.evalRingHom t
  let M : Matrix (Fin n) (Fin n) (Polynomial ℝ) :=
    1 - (Polynomial.X : Polynomial ℝ) • G.adjMatrix (Polynomial ℝ)
  have hm : M.map f = 1 - t • G.adjMatrix ℝ := by
    ext i j
    simp only [M, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      SimpleGraph.adjMatrix_apply, smul_eq_mul]
    split_ifs <;> simp [f]
  change f M.det = _
  rw [f.map_det]
  change (M.map f).det = _
  rw [hm]
  simpa only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_neg, sub_eq_add_neg, neg_smul, neg_mul, mul_comm] using
      det_one_add_smul_hermitian (G.adjMatrix ℝ) (adjMatrix_isHermitian G) (-t)

private theorem pencil_series_spectrum {n : ℕ} (G : SimpleGraph (Fin n)) :
    (1 - (X : PowerSeries ℝ) • G.adjMatrix (PowerSeries ℝ)).det =
      ∏ i, (1 - C ((adjMatrix_isHermitian G).eigenvalues i) * X) := by
  let f : Polynomial ℝ →+* PowerSeries ℝ := Polynomial.coeToPowerSeries.ringHom
  have h := congrArg f (pencil_poly_spectrum G)
  rw [f.map_det, map_prod] at h
  have hm : (1 - (Polynomial.X : Polynomial ℝ) • G.adjMatrix (Polynomial ℝ)).map f =
      1 - (X : PowerSeries ℝ) • G.adjMatrix (PowerSeries ℝ) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      SimpleGraph.adjMatrix_apply, smul_eq_mul]
    split_ifs <;> simp [f]
  change ((1 - (Polynomial.X : Polynomial ℝ) • G.adjMatrix (Polynomial ℝ)).map f).det = _ at h
  rw [hm] at h
  simpa only [f, map_sub, map_one, map_mul, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_C, Polynomial.coe_X] using h

private theorem chs_series_mul_pencil {n : ℕ} (G : SimpleGraph (Fin n)) :
    (mk fun d => chs G d) * (1 - (X : PowerSeries ℝ) •
      G.adjMatrix (PowerSeries ℝ)).det = 1 := by
  rw [pencil_series_spectrum]
  exact hsymm_series_product (adjMatrix_isHermitian G).eigenvalues

end D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular

namespace D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular

private theorem chs_series_of_cycle_pencil {n : ℕ} (G : SimpleGraph (Fin n))
    (ls : List ℕ) (hpos : ∀ l ∈ ls, 0 < l)
    (hdet : ((1 + oddCatalan ^ 2) • (1 : Matrix (Fin n) (Fin n) (PowerSeries ℝ)) -
      oddCatalan • G.adjMatrix (PowerSeries ℝ)).det =
        (ls.map fun l => (1 - oddCatalan ^ l) ^ 2).prod) :
    (mk fun d => chs G d) = (1 + oddCatalan ^ 2) ^ n *
      (ls.map fun l => (cycleKernel l).subst oddCatalan).prod := by
  let S := 1 + oddCatalan ^ 2
  let D := (1 - (X : PowerSeries ℝ) • G.adjMatrix (PowerSeries ℝ)).det
  have hn : S ^ n * D = (ls.map fun l => (1 - oddCatalan ^ l) ^ 2).prod := by
    have hmat : S • (1 - (X : PowerSeries ℝ) • G.adjMatrix (PowerSeries ℝ)) =
        S • (1 : Matrix (Fin n) (Fin n) (PowerSeries ℝ)) -
          oddCatalan • G.adjMatrix (PowerSeries ℝ) := by
      rw [smul_sub, smul_smul]
      have he : S * X = oddCatalan := by
        simpa [S, mul_comm] using oddCatalan_equation.symm
      rw [he]
    have he := congrArg Matrix.det hmat
    rw [Matrix.det_smul, Fintype.card_fin] at he
    exact he.trans hdet
  have hs : HasSubst oddCatalan := .of_constantCoeff_zero oddCatalan_constantCoeff
  have hinv : (ls.map fun l => (cycleKernel l).subst oddCatalan).prod *
      (ls.map fun l => (1 - oddCatalan ^ l) ^ 2).prod = 1 := by
    have hi (l : ℕ) (hl : 0 < l) :
        (cycleKernel l).subst oddCatalan * (1 - oddCatalan ^ l) ^ 2 = 1 := by
      have h := congrArg (substAlgHom (R := ℝ) (S := ℝ) hs)
        (cycleKernel_mul_denominator hl)
      simpa only [map_mul, map_pow, map_sub, map_one, substAlgHom_X,
        coe_substAlgHom] using h
    clear hn hdet
    induction ls with
    | nil => simp
    | cons l ls ih =>
      simp only [List.map_cons, List.prod_cons]
      have he := hi l (hpos l (by simp))
      have ht := ih (fun a ha => hpos a (by simp [ha]))
      calc
        _ = ((cycleKernel l).subst oddCatalan * (1 - oddCatalan ^ l) ^ 2) *
          ((ls.map fun l => (cycleKernel l).subst oddCatalan).prod *
            (ls.map fun l => (1 - oddCatalan ^ l) ^ 2).prod) := by ring
        _ = 1 := by rw [he, ht, one_mul]
  have hH : (mk fun d => chs G d) * D = 1 := chs_series_mul_pencil G
  calc
    (mk fun d => chs G d) = (mk fun d => chs G d) *
        ((ls.map fun l => (cycleKernel l).subst oddCatalan).prod *
          (ls.map fun l => (1 - oddCatalan ^ l) ^ 2).prod) := by rw [hinv, mul_one]
    _ = (S ^ n * (ls.map fun l => (cycleKernel l).subst oddCatalan).prod) *
        ((mk fun d => chs G d) * D) := by rw [← hn]; ring
    _ = _ := by rw [hH, mul_one]

private theorem cycle_chs_series (n : ℕ) :
    (mk fun d => chs (SimpleGraph.cycleGraph (n + 3)) d) =
      (1 + oddCatalan ^ 2) ^ (n + 3) * (cycleKernel (n + 3)).subst oddCatalan := by
  simpa using chs_series_of_cycle_pencil (SimpleGraph.cycleGraph (n + 3)) [n + 3]
    (by simp) (by
      convert det_cycle_pencil n oddCatalan using 2
      ext i j
      by_cases hi : i = j <;> by_cases ha : (SimpleGraph.cycleGraph (n + 3)).Adj i j <;>
        simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
          SimpleGraph.adjMatrix_apply, hi, ha]
      all_goals simp)

/-- A cycle factorization of the normalized adjacency pencil implies CHS domination. -/
private theorem chs_cycle_le_of_pencil_partition {n : ℕ} (hn : 3 ≤ n)
    (G : SimpleGraph (Fin n)) (ls : List ℕ) (hne : ls ≠ [])
    (hpos : ∀ l ∈ ls, 0 < l) (hsum : ls.sum = n)
    (hdet : ((1 + oddCatalan ^ 2) • (1 : Matrix (Fin n) (Fin n) (PowerSeries ℝ)) -
      oddCatalan • G.adjMatrix (PowerSeries ℝ)).det =
        (ls.map fun l => (1 - oddCatalan ^ l) ^ 2).prod) (d : ℕ) :
    chs (SimpleGraph.cycleGraph n) d ≤ chs G d := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hC := cycle_chs_series k
  have hG := chs_series_of_cycle_pencil G ls hpos hdet
  have h := cycleKernel_partition_bound ls hne hpos d
  rw [hsum] at h
  rw [← hC, ← hG] at h
  simpa only [coeff_mk] using h

end D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular



set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Classical Matrix Finset
open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular

private theorem det_scaled_pencil_components {V R : Type*} [Fintype V] [DecidableEq V]
    [CommRing R] (G : SimpleGraph V) [DecidableRel G.Adj] [LinearOrder G.ConnectedComponent] (s t : R) :
    (s • (1 : Matrix V V R) - t • G.adjMatrix R).det =
      ∏ c : G.ConnectedComponent, (s • (1 : Matrix c c R) - t • c.toSimpleGraph.adjMatrix R).det := by
  have htri : BlockTriangular (s • (1 : Matrix V V R) - t • G.adjMatrix R) G.connectedComponentMk := by
    intro i j hij
    have hne : i ≠ j := by intro h; subst j; exact (lt_irrefl _ hij)
    have hn : ¬G.Adj i j := by
      intro h
      exact (ne_of_lt hij) (SimpleGraph.ConnectedComponent.sound h.reachable).symm
    simp [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
      SimpleGraph.adjMatrix_apply, hne, hn]
  rw [htri.det_fintype]
  apply Finset.prod_congr rfl
  intro c _
  let e : {a // G.connectedComponentMk a = c} ≃ c :=
    { toFun := fun a => ⟨a.val, a.property⟩
      invFun := fun a => ⟨a.val, a.property⟩
      left_inv := fun a => rfl
      right_inv := fun a => rfl }
  have hm : ((s • (1 : Matrix V V R) - t • G.adjMatrix R).toSquareBlock G.connectedComponentMk c).reindex e e =
      (s • (1 : Matrix c c R) - t • c.toSimpleGraph.adjMatrix R) := by
    ext i j
    simp only [Matrix.reindex_apply, Matrix.toSquareBlock_def, Matrix.of_apply,
      Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      SimpleGraph.adjMatrix_apply, SimpleGraph.ConnectedComponent.toSimpleGraph,
      SimpleGraph.induce_adj]
    change s * (if i.val = j.val then 1 else 0) - t * (if G.Adj i.val j.val then 1 else 0) =
      s * (if i = j then 1 else 0) - t * (if G.Adj i.val j.val then 1 else 0)
    simp only [Subtype.ext_iff]
  rw [← Matrix.det_reindex_self e, hm]



end D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular


set_option backward.isDefEq.respectTransparency false

noncomputable section
open Classical Finset

namespace D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular

private theorem component_twoRegular {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsRegularOfDegree 2) (c : G.ConnectedComponent) :
    c.toSimpleGraph.IsRegularOfDegree 2 := by
  intro v
  have hsub : G.neighborSet v.val ⊆ c.supp := by
    intro w hw
    exact (c.mem_supp_congr_adj hw).mp v.property
  calc
    c.toSimpleGraph.degree v = (c.toSimpleGraph.neighborSet v).ncard :=
      (c.toSimpleGraph.ncard_neighborSet v).symm
    _ = (G.neighborSet v.val).ncard := Set.ncard_congr' {
      toFun := fun x => ⟨x.val.val, x.property⟩
      invFun := fun x => ⟨⟨x.val, hsub x.property⟩, x.property⟩
      left_inv := fun x => by cases x; rfl
      right_inv := fun x => by cases x; rfl }
    _ = G.degree v.val := G.ncard_neighborSet v.val
    _ = 2 := hG v.val

private theorem component_exists_cycle {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsRegularOfDegree 2) (c : G.ConnectedComponent) :
    ∃ (u : c) (p : c.toSimpleGraph.Walk u u), p.IsCycle := by
  let H := c.toSimpleGraph
  have hdeg := component_twoRegular G hG c
  have hncard (v : c) : (H.neighborSet v).ncard = 2 := by
    rw [Set.ncard_eq_toFinset_card', ← H.neighborFinset_def, H.card_neighborFinset_eq_degree]
    exact hdeg v
  have hcyc : H.IsCycles := by intro v _; exact hncard v
  let v : c := Classical.choice c.connected_toSimpleGraph.nonempty
  have hv : v ∈ (H.connectedComponentMk v).supp := rfl
  have hn : (H.neighborSet v).Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hncard]; decide)
  obtain ⟨p, hp, _⟩ := hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hv hn
  exact ⟨v, p, hp⟩

end D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular

namespace D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular

private theorem det_scaled_pencil_iso {V W R : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] [CommRing R]
    (F : SimpleGraph V) (G : SimpleGraph W)
    [DecidableRel F.Adj] [DecidableRel G.Adj] (e : F ≃g G) (s t : R) :
    (s • (1 : Matrix V V R) - t • F.adjMatrix R).det =
      (s • (1 : Matrix W W R) - t • G.adjMatrix R).det := by
  rw [← Matrix.det_reindex_self e.toEquiv]
  apply congrArg Matrix.det
  ext i j
  have he : F.Adj (e.symm i) (e.symm j) ↔ G.Adj i j := e.symm.map_adj_iff
  by_cases h : G.Adj i j
  · have hf := he.mpr h
    simp [Matrix.reindex_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      SimpleGraph.adjMatrix_apply, h, hf]
    exact fun hbad => (hbad hf).elim
  · have hf : ¬ F.Adj (e.symm i) (e.symm j) := fun hf => h (he.mp hf)
    simp [Matrix.reindex_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      SimpleGraph.adjMatrix_apply, h, hf]
    exact fun hbad => (hf hbad).elim

/-- Component cycle isomorphisms supply the normalized adjacency pencil partition. -/
private theorem chs_cycle_le_of_component_cycles {n : ℕ} (hn : 3 ≤ n)
    (G : SimpleGraph (Fin n))
    (hcycles : ∀ c : G.ConnectedComponent, ∃ l, 3 ≤ l ∧
      Nonempty (SimpleGraph.cycleGraph l ≃g c.toSimpleGraph)) (d : ℕ) :
    chs (SimpleGraph.cycleGraph n) d ≤ chs G d := by
  choose len hlen he using hcycles
  let iso (c : G.ConnectedComponent) := (he c).some
  let e := (Fintype.equivFin G.ConnectedComponent).symm
  letI : LinearOrder G.ConnectedComponent := LinearOrder.lift' e.symm e.symm.injective
  have hcard (c : G.ConnectedComponent) : len c = Fintype.card c := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (iso c).toEquiv
  let ls : List ℕ := List.ofFn (fun i => len (e i))
  have hsumc : ∑ c : G.ConnectedComponent, len c = n := by
    let es : (Σ c : G.ConnectedComponent, c) ≃ Fin n := {
      toFun := fun p => p.2.val
      invFun := fun v => ⟨G.connectedComponentMk v, ⟨v, rfl⟩⟩
      left_inv := by
        rintro ⟨c, v, hv⟩
        change G.connectedComponentMk v = c at hv
        subst c
        rfl
      right_inv := fun _ => rfl }
    have hc := Fintype.card_congr es
    rw [Fintype.card_sigma, Fintype.card_fin] at hc
    calc
      ∑ c : G.ConnectedComponent, len c = ∑ c : G.ConnectedComponent, Fintype.card c :=
        Finset.sum_congr rfl (fun c _ => hcard c)
      _ = n := hc
  have hsum : ls.sum = n := by
    calc
      ls.sum = ∑ i, len (e i) := List.sum_ofFn
      _ = ∑ c, len c := e.sum_comp len
      _ = n := hsumc
  have hpos : ∀ l ∈ ls, 0 < l := by
    intro l hl
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    exact lt_of_lt_of_le (by decide : 0 < 3) (hlen _)
  have hne : ls ≠ [] := by
    intro h
    rw [h, List.sum_nil] at hsum
    omega
  apply chs_cycle_le_of_pencil_partition hn G ls hne hpos hsum
  have hcomp := det_scaled_pencil_components G (1 + oddCatalan ^ 2) oddCatalan
  convert hcomp.trans ?_ using 1
  have hc (c : G.ConnectedComponent) :
      ((1 + oddCatalan ^ 2) • (1 : Matrix c c (PowerSeries ℝ)) -
        oddCatalan • c.toSimpleGraph.adjMatrix (PowerSeries ℝ)).det =
          (1 - oddCatalan ^ len c) ^ 2 := by
    have hi := det_scaled_pencil_iso _ _ (iso c) (1 + oddCatalan ^ 2) oddCatalan
    apply hi.symm.trans
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hlen c)
    have hlenk : len c = k + 3 := by omega
    rw [hlenk]
    convert det_cycle_pencil k oddCatalan using 2
  calc
    _ = ∏ c : G.ConnectedComponent, (1 - oddCatalan ^ len c) ^ 2 :=
      Finset.prod_congr rfl (fun c _ => hc c)
    _ = (ls.map fun l => (1 - oddCatalan ^ l) ^ 2).prod := by
      rw [List.map_ofFn, List.prod_ofFn]
      exact (e.prod_comp (fun c => (1 - oddCatalan ^ len c) ^ 2)).symm

end D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular



open private SimpleGraph.cycle_iso_of_connected_degree_le_two from
  D5.S3.Combinatorics.Graph.Brooks.General

namespace D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular

/-- A two-regular graph dominates the cycle in every CHS coefficient. -/
theorem chs_cycle_le_twoRegular {n : ℕ} (hn : 3 ≤ n)
    (G : SimpleGraph (Fin n)) (hG : G.IsRegularOfDegree 2) (d : ℕ) :
    chs (SimpleGraph.cycleGraph n) d ≤ chs G d := by
  apply chs_cycle_le_of_component_cycles hn G ?_ d
  intro c
  obtain ⟨u, p, hp⟩ := component_exists_cycle G hG c
  refine ⟨p.length, hp.three_le_length, ?_⟩
  exact SimpleGraph.cycle_iso_of_connected_degree_le_two c.toSimpleGraph
    c.connected_toSimpleGraph
    (c.toSimpleGraph.maxDegree_le_of_forall_degree_le 2
      (fun v => le_of_eq (component_twoRegular G hG c v))) p hp

end D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular

