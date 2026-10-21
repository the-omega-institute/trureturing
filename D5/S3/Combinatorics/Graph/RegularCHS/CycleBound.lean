/- GID: D5/S3/Combinatorics/Graph/RegularCHS/CycleBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/RegularCHS/CycleBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Gershgorin, mathlib/module/Mathlib.LinearAlgebra.Eigenspace.Matrix, mathlib/module/Mathlib.RingTheory.PowerSeries.Derivative, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Even adjacency coefficients of cycles are bounded by the comparison sequence. -/

import D5.S3.Combinatorics.Graph.RegularCHS.Interface
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic

noncomputable section
open Classical Finset PowerSeries
open scoped BigOperators
open D5.S3.Combinatorics.Graph.RegularCHS.Defs
open D5.S3.Combinatorics.Graph.RegularCHS.Interface
namespace D5.S3.Combinatorics.Graph.RegularCHS.CycleBound

private def geom (a : ℝ) : PowerSeries ℝ := mk fun k => a ^ k

private lemma geom_linear (a : ℝ) : geom a * (1 - C a * X) = 1 :=
  D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm.geometric_mul_linear a

private lemma geom_split (a b : ℝ) :
    C (a - b) * (geom a * geom b) = C a * geom a - C b * geom b  := by
  rw [map_sub]
  have ha := geom_linear a
  have hb := geom_linear b
  calc
    _ = C a * geom a * (geom b * (1 - C b * X)) -
        C b * geom b * (geom a * (1 - C a * X)) := by ring
    _ = _ := by rw [ha, hb]; ring

private lemma coeff_prod_geom_nonneg {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (k : ℕ) : 0 ≤ coeff k (∏ i ∈ s, geom (a i)) := by
  rw [coeff_prod]
  exact Finset.sum_nonneg fun f _ => Finset.prod_nonneg fun i hi => by
    simpa only [geom, coeff_mk] using pow_nonneg (ha i hi) (f i)

private lemma rescale_geom (a b : ℝ) : rescale a (geom b) = geom (a * b) := by
  ext k
  simp [geom, coeff_rescale, mul_pow]

private lemma coeff_prod_geom_even_nonneg {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (m : ℕ) : 0 ≤ coeff (2 * m) (∏ i ∈ s, geom (a i)) := by
  classical
  refine Finset.strongInductionOn s ?_
  intro s ih
  by_cases hp : ∀ i ∈ s, 0 ≤ a i
  · exact coeff_prod_geom_nonneg s a hp _
  by_cases hn : ∀ i ∈ s, a i ≤ 0
  · have h := coeff_prod_geom_nonneg s (fun i => -a i)
      (fun i hi => neg_nonneg.mpr (hn i hi)) (2 * m)
    have he : (∏ i ∈ s, geom (-a i)) = rescale (-1 : ℝ) (∏ i ∈ s, geom (a i)) := by
      simp only [map_prod, rescale_geom, neg_one_mul]
    simpa only [he, coeff_rescale, Even.neg_one_pow (even_two_mul m), one_mul] using h
  push Not at hp hn
  obtain ⟨i, hi, hneg⟩ := hp
  obtain ⟨j, hj, hpos⟩ := hn
  have hij : i ≠ j := by intro h; subst j; linarith
  let t := (s.erase i).erase j
  have hsi : s.erase i ⊂ s := Finset.erase_ssubset hi
  have hsj : s.erase j ⊂ s := Finset.erase_ssubset hj
  have hpi := ih (s.erase i) hsi
  have hpj := ih (s.erase j) hsj
  have hprod : (∏ k ∈ s, geom (a k)) = geom (a i) * geom (a j) * ∏ k ∈ t, geom (a k) := by
    rw [← Finset.mul_prod_erase s _ hi,
      ← Finset.mul_prod_erase (s.erase i) _ (mem_erase.mpr ⟨Ne.symm hij, hj⟩)]
    dsimp [t]
    ring
  have hprod_i : (∏ k ∈ s.erase i, geom (a k)) = geom (a j) * ∏ k ∈ t, geom (a k) := by
    exact (Finset.mul_prod_erase _ _ (mem_erase.mpr ⟨Ne.symm hij, hj⟩)).symm
  have hprod_j : (∏ k ∈ s.erase j, geom (a k)) = geom (a i) * ∏ k ∈ t, geom (a k) := by
    rw [← Finset.mul_prod_erase _ _ (mem_erase.mpr ⟨hij, hi⟩), Finset.erase_right_comm]
  have he : C (a j - a i) * (∏ k ∈ s, geom (a k)) =
      C (a j) * (∏ k ∈ s.erase i, geom (a k)) -
      C (a i) * (∏ k ∈ s.erase j, geom (a k)) := by
    rw [hprod, hprod_i, hprod_j]
    have hs := congrArg (fun f : PowerSeries ℝ => f * ∏ k ∈ t, geom (a k))
      (geom_split (a j) (a i))
    convert hs using 1 <;> ring
  have hc := congrArg (coeff (2 * m)) he
  rw [coeff_C_mul] at hc
  simp only [map_sub, coeff_C_mul] at hc
  have hnn : 0 ≤ a j * coeff (2 * m) (∏ k ∈ s.erase i, geom (a k)) -
      a i * coeff (2 * m) (∏ k ∈ s.erase j, geom (a k)) :=
    sub_nonneg.mpr (le_trans (mul_nonpos_of_nonpos_of_nonneg hneg.le hpj)
      (mul_nonneg hpos.le hpi))
  exact nonneg_of_mul_nonneg_right (hc.symm ▸ hnn)
    (sub_pos.mpr (lt_trans hneg hpos))

private lemma geom_ode (a : ℝ) :
    (1 - C 4 * X ^ 2) * (C a * geom a) =
      C a + C 4 * X - X * C (4 - a ^ 2) * geom a := by
  have h := geom_linear a
  simp only [map_sub, map_pow] 
  linear_combination (C a + C 4 * X) * h

private lemma prod_geom_ode {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (1 - C 4 * X ^ 2) * derivative (∏ i ∈ s, geom (a i)) =
      C (∑ i ∈ s, a i) * (∏ i ∈ s, geom (a i)) +
      C (4 * (s.card : ℝ)) * X * (∏ i ∈ s, geom (a i)) -
      X * ∑ i ∈ s, C (4 - a i ^ 2) * ((∏ j ∈ s, geom (a j)) * geom (a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    let H := ∏ j ∈ s, geom (a j)
    have hd := (derivative (R := ℝ)).leibniz_of_mul_eq_one (geom_linear (a i))
    simp only [map_sub, derivative_one, Derivation.leibniz, derivative_C,
      derivative_X, smul_eq_mul, mul_one, mul_zero, add_zero, zero_sub, mul_neg] at hd
    have hsum : (∑ j ∈ s, C (4 - a j ^ 2) * ((geom (a i) * H) * geom (a j))) =
        geom (a i) * ∑ j ∈ s, C (4 - a j ^ 2) * (H * geom (a j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    simp only [prod_insert hi, sum_insert hi, Finset.card_insert_of_notMem hi,
      Nat.cast_add, Nat.cast_one, Derivation.leibniz, smul_eq_mul]
    change (1 - C 4 * X ^ 2) *
      (geom (a i) * derivative H + H * derivative (geom (a i))) = _
    rw [hsum, hd]
    change (1 - C 4 * X ^ 2) * derivative H = _ at ih
    have hg := geom_ode (a i)
    simp only [map_add, map_mul, map_natCast, map_one] at ih hg ⊢
    linear_combination geom (a i) * ih + H * geom (a i) * hg

private lemma coeff_X_derivative (f : PowerSeries ℝ) (k : ℕ) :
    coeff k (X * derivative f) = (k : ℝ) * coeff k f := by
  cases k with
  | zero => simp
  | succ k => rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

private lemma prod_geom_step {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (htrace : ∑ i ∈ s, a i = 0) (hbound : ∀ i ∈ s, a i ^ 2 ≤ 4) (m : ℕ) :
    (2 * (m + 1) : ℝ) * coeff (2 * (m + 1)) (∏ i ∈ s, geom (a i)) ≤
      4 * ((s.card : ℝ) + 2 * m) * coeff (2 * m) (∏ i ∈ s, geom (a i)) := by
  classical
  let H := ∏ i ∈ s, geom (a i)
  let R := ∑ i ∈ s, C (4 - a i ^ 2) * (H * geom (a i))
  have hR : 0 ≤ coeff (2 * m) R := by
    dsimp [R]
    rw [map_sum]
    apply Finset.sum_nonneg
    intro i hi
    rw [coeff_C_mul]
    apply mul_nonneg (sub_nonneg.mpr (hbound i hi))
    have hp := coeff_prod_geom_even_nonneg
      (insert (none : Option ι) (s.image some)) (fun j => j.elim (a i) a) m
    have hn : (none : Option ι) ∉ s.image some := by simp
    rw [prod_insert hn, prod_image] at hp
    · simpa only [Option.elim_none, Option.elim_some, mul_comm, H] using hp
    · intro x _ y _ h
      exact Option.some.inj h
  have ho := prod_geom_ode s a
  rw [htrace, map_zero, zero_mul, zero_add] at ho
  change (1 - C 4 * X ^ 2) * derivative H = C (4 * (s.card : ℝ)) * X * H - X * R at ho
  have hc := congrArg (coeff (2 * m + 1)) ho
  have he : (1 - C 4 * X ^ 2) * derivative H =
      derivative H - C 4 * (X * (X * derivative H)) := by ring
  rw [he] at hc
  have he' : C (4 * (s.card : ℝ)) * X * H = C (4 * (s.card : ℝ)) * (X * H) := by ring
  rw [he'] at hc
  simp only [map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_X_derivative,
    coeff_derivative] at hc
  have hn : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
  rw [hn] at hc
  dsimp [H] at hc ⊢
  push_cast at hc
  nlinarith

private lemma chs_eq_coeff_prod {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ) :
    chs G d = coeff d (∏ i, geom ((adjMatrix_isHermitian G).eigenvalues i)) := by
  let a := (adjMatrix_isHermitian G).eigenvalues
  let H : PowerSeries ℝ := mk fun k => MvPolynomial.eval a (MvPolynomial.hsymm (Fin n) ℝ k)
  let P : PowerSeries ℝ := ∏ i, (1 - C (a i) * X)
  have hH : H * P = 1 :=
    D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm.hsymm_series_product a
  have hg : (∏ i, geom (a i)) * P = 1 := by
    dsimp [P]
    rw [← Finset.prod_mul_distrib]
    simp only [geom_linear, Finset.prod_const_one]
  have he : H = ∏ i, geom (a i) :=
    inv_unique (by simpa only [mul_comm] using hH)
      (by simpa only [mul_comm] using hg)
  simpa only [H, coeff_mk, chs, a] using congrArg (coeff d) he

private lemma eigenvalues_sum_zero {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∑ i, (adjMatrix_isHermitian G).eigenvalues i = 0 := by
  have h := (adjMatrix_isHermitian G).trace_eq_sum_eigenvalues
  simpa [Matrix.trace, SimpleGraph.adjMatrix_apply] using h.symm

private lemma eigenvalues_sq_le_four {n : ℕ} (G : SimpleGraph (Fin n))
    (hdeg : ∀ v, G.degree v ≤ 2) (i : Fin n) :
    (adjMatrix_isHermitian G).eigenvalues i ^ 2 ≤ 4 := by
  let a := (adjMatrix_isHermitian G).eigenvalues i
  have hev : Module.End.HasEigenvalue (Matrix.toLin' (G.adjMatrix ℝ)) a := by
    apply Module.End.HasEigenvalue.of_mem_spectrum
    rw [Matrix.spectrum_toLin']
    exact (adjMatrix_isHermitian G).eigenvalues_mem_spectrum_real i
  obtain ⟨v, hv⟩ := eigenvalue_mem_ball hev
  have hr : ∑ j ∈ Finset.univ.erase v, ‖(G.adjMatrix ℝ) v j‖ = (G.degree v : ℝ) := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ v)]
    have hn (j : Fin n) : ‖(G.adjMatrix ℝ) v j‖ = (G.adjMatrix ℝ) v j := by
      simp only [SimpleGraph.adjMatrix_apply]
      split_ifs <;> norm_num
    simp_rw [hn]
    have hh := SimpleGraph.adjMatrix_mulVec_const_apply
      (G := G) (α := ℝ) (v := v) (a := 1)
    simpa only [Matrix.mulVec, dotProduct, Function.const_apply, mul_one,
      SimpleGraph.adjMatrix_apply, ite_false, G.irrefl, sub_zero] using hh
  rw [hr] at hv
  have hb : |a| ≤ 2 := by
    have h := (show (G.degree v : ℝ) ≤ 2 by exact_mod_cast hdeg v)
    have ha : |a| ≤ (G.degree v : ℝ) := by
      simpa [mem_closedBall_iff_norm, SimpleGraph.adjMatrix_apply] using hv
    exact ha.trans h
  change a ^ 2 ≤ 4
  nlinarith [sq_abs a, abs_nonneg a]

private lemma chs_le_bseq_of_degree_le_two {n : ℕ} (G : SimpleGraph (Fin n))
    (hdeg : ∀ v, G.degree v ≤ 2) (m : ℕ) : chs G (2 * m) ≤ bseq n 4 m := by
  let a := (adjMatrix_isHermitian G).eigenvalues
  rw [chs_eq_coeff_prod]
  change coeff (2 * m) (∏ i, geom (a i)) ≤ bseq n 4 m
  induction m with
  | zero => simp [geom]
  | succ m ih =>
    have hs := prod_geom_step (Finset.univ : Finset (Fin n)) a
      (eigenvalues_sum_zero G) (fun i _ => eigenvalues_sq_le_four G hdeg i) m
    simp only [Finset.card_univ, Fintype.card_fin] at hs
    have hb := bseq_succ n 4 m
    norm_num only [Nat.cast_ofNat] at hb
    have hfactor : 0 ≤ 4 * ((n : ℝ) + 2 * m) := by positivity
    have hmul := mul_le_mul_of_nonneg_left ih hfactor
    have hden : (0 : ℝ) < 2 * (m + 1) := by positivity
    apply (mul_le_mul_iff_right₀ hden).mp
    nlinarith

/-- Every even cycle coefficient is bounded by the degree-four comparison sequence. -/
theorem chs_cycle_le_bseq {n : ℕ} (hn : 3 ≤ n) (m : ℕ) :
    chs (SimpleGraph.cycleGraph n) (2 * m) ≤ bseq n 4 m := by
  apply chs_le_bseq_of_degree_le_two
  intro v
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  have he : n = k + 3 := by omega
  rcases he with rfl
  have hd := SimpleGraph.cycleGraph_degree_three_le (n := k) (v := v)
  rw [← SimpleGraph.ncard_neighborSet] at hd ⊢
  exact hd.le

end D5.S3.Combinatorics.Graph.RegularCHS.CycleBound
