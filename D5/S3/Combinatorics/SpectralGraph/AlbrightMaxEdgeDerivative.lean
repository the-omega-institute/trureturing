/- GID: D5/S3/Combinatorics/SpectralGraph/AlbrightMaxEdgeDerivative
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/AlbrightMaxEdgeDerivative
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The normalized Laplacian edge derivative has sharp upper bound one. -/

/- Judgement form.
   admission_basis: open-problem-resolution (#28967; Proved).
   Direct frozen supplier: AlbrightKemenyEdgeDerivativeRefutation,
     statement_id: sha256:c0b89b4b6882605547b15450771019bb0238a86bd1aa67e9cc670937ce0db860.
   escape_witness: nonedge_mass, consumed by summand_le_one and edgeDerivative_le.
   content: nonedge_mass, summand_le_one, edgeDerivative_le, result.
   Consumed bind-only helpers (helper -> immediate consumer):
     degree_row -> unperturbed, normAdj_lower, lapEntry_hasDerivAt
     normAdj_apply -> normAdj_symm, unperturbed, nonedge_mass, lapEntry_hasDerivAt
     normAdj_symm -> dot_normAdj_comm
     unperturbed -> eigen_normAdj
     normAdj_mulVec -> quad_normAdj, leaf_eigen
     quad_normAdj -> normAdj_upper, normAdj_lower
     diag_energy -> normAdj_upper, normAdj_lower
     normAdj_upper -> summand_le_one
     normAdj_lower -> nonedge_mass, summand_le_one
     dot_normAdj_comm -> nonedge_mass, quad_slope
     leaf_eigen, scaled_sq_le -> summand_le_one
     invSqrt_hasDerivAt -> lapEntry_hasDerivAt -> quad_hasDerivAt
     scaled_dot_halfRate -> quad_slope
     quad_hasDerivAt, quad_slope -> rayleighAverage_hasDerivAt
     eigen_normAdj -> rayleighAverage_hasDerivAt, edgeDerivative_le
     dot_self -> edgeDerivative_le, endpoint_unit, path_attains
     rayleighAverage_eq_trace -> basis_independent
     rayleighAverage_hasDerivAt -> basis_independent, result
     path_adj, path_pair -> path_weighted_adj -> path_lap
     path_lap -> path_vector_eq, path_eigenspace_dim
     path_vector_eq -> endpointEigen, path_attains
     endpoint_unit, path_eigenspace_dim -> path_attains
     path_attains, path_eigenspace_dim, basis_independent -> result
-/

import D5.S3.Combinatorics.SpectralGraph.AlbrightKemenyEdgeDerivativeRefutation
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.Trace
import OmegaBuild.Commands

/-! The sharp upper bound in Albright et al., Conjecture 2.20. -/

compile_only_with_mathlib

open Matrix
open scoped BigOperators InnerProductSpace

noncomputable section

namespace D5.S3.Combinatorics.SpectralGraph.AlbrightMaxEdgeDerivative

open AlbrightKemenyEdgeDerivativeRefutation (paramAdj normLap edgeDegrees paramAdj_degrees)

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

private abbrev degree (i : Fin n) : ℝ := G.degree i

private def normAdj : Matrix (Fin n) (Fin n) ℝ :=
  diagonal (fun i => (Real.sqrt (degree G i))⁻¹) *
    G.adjMatrix ℝ * diagonal (fun i => (Real.sqrt (degree G i))⁻¹)

private def scaled (u : Fin n → ℝ) (i : Fin n) : ℝ := u i / Real.sqrt (degree G i)

private theorem degree_row (i : Fin n) : ∑ j, G.adjMatrix ℝ i j = degree G i := by
  simpa [Matrix.mulVec, dotProduct] using
    (G.adjMatrix_mulVec_const_apply (α := ℝ) (a := 1) (v := i))

private theorem normAdj_apply (i j : Fin n) :
    normAdj G i j = G.adjMatrix ℝ i j /
      (Real.sqrt (degree G i) * Real.sqrt (degree G j)) := by
  simp only [normAdj, Matrix.mul_diagonal, Matrix.diagonal_mul, div_eq_mul_inv,
    _root_.mul_inv_rev]
  ring

private theorem normAdj_symm : (normAdj G).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  rw [normAdj_apply, normAdj_apply, (G.isSymm_adjMatrix (α := ℝ)).apply i j, mul_comm]

private theorem unperturbed (x y : Fin n) :
    normLap (paramAdj G x y 0) = 1 - normAdj G := by
  simp only [paramAdj, zero_smul, add_zero, normLap, degree_row]
  congr 1
  ext i j
  simpa only [Matrix.of_apply] using (normAdj_apply G i j).symm

private theorem normAdj_mulVec (z : Fin n → ℝ) (i : Fin n) :
    (normAdj G *ᵥ z) i =
      (Real.sqrt (degree G i))⁻¹ * (G.adjMatrix ℝ *ᵥ scaled G z) i := by
  simp only [normAdj, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
  congr 2
  funext j
  simp [Matrix.mulVec_diagonal, scaled, div_eq_mul_inv, mul_comm]

private theorem quad_normAdj (z : Fin n → ℝ) :
    z ⬝ᵥ (normAdj G *ᵥ z) = scaled G z ⬝ᵥ (G.adjMatrix ℝ *ᵥ scaled G z) := by
  simp only [dotProduct, normAdj_mulVec, scaled, div_eq_mul_inv, mul_assoc]

private theorem diag_energy (hd : ∀ i, 0 < G.degree i) (z : Fin n → ℝ) :
    scaled G z ⬝ᵥ (G.degMatrix ℝ *ᵥ scaled G z) = z ⬝ᵥ z := by
  rw [G.dotProduct_mulVec_degMatrix]
  apply Finset.sum_congr rfl
  intro i _
  have hi : 0 < degree G i := by exact_mod_cast hd i
  have hs := Real.sq_sqrt hi.le
  unfold scaled
  field_simp [(Real.sqrt_pos.2 hi).ne']
  rw [hs]
  ring

private theorem normAdj_upper (hd : ∀ i, 0 < G.degree i) (z : Fin n → ℝ) :
    z ⬝ᵥ (normAdj G *ᵥ z) ≤ z ⬝ᵥ z := by
  have h := (G.posSemidef_lapMatrix ℝ).dotProduct_mulVec_nonneg (scaled G z)
  simp only [star_trivial, SimpleGraph.lapMatrix, Matrix.sub_mulVec, dotProduct_sub,
    diag_energy G hd, ← quad_normAdj G] at h
  linarith

private theorem normAdj_lower (hd : ∀ i, 0 < G.degree i) (z : Fin n → ℝ) :
    0 ≤ z ⬝ᵥ z + z ⬝ᵥ (normAdj G *ᵥ z) := by
  let g := scaled G z
  have hrow (i : Fin n) : ∑ j, G.adjMatrix ℝ i j * (g i * g i) =
      degree G i * g i * g i := by
    rw [← Finset.sum_mul, degree_row, mul_assoc]
  have hleft : (∑ i, ∑ j, G.adjMatrix ℝ i j * (g i * g i)) = z ⬝ᵥ z := by
    simp_rw [hrow]
    rw [← G.dotProduct_mulVec_degMatrix]
    exact diag_energy G hd z
  have hright : (∑ i, ∑ j, G.adjMatrix ℝ i j * (g j * g j)) = z ⬝ᵥ z := by
    rw [Finset.sum_comm]
    simp_rw [(G.isSymm_adjMatrix (α := ℝ)).apply]
    exact hleft
  have hcross : (∑ i, ∑ j, G.adjMatrix ℝ i j * (g i * g j)) =
      z ⬝ᵥ (normAdj G *ᵥ z) := by
    rw [quad_normAdj]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    congr 1 with i
    congr 1 with j
    ring
  have hpos : 0 ≤ ∑ i, ∑ j, G.adjMatrix ℝ i j * (g i + g j)^2 := by
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    exact mul_nonneg (by simp [SimpleGraph.adjMatrix_apply]; split <;> norm_num) (sq_nonneg _)
  have hsplit (i j : Fin n) :
      G.adjMatrix ℝ i j * (g i + g j)^2 =
        G.adjMatrix ℝ i j * (g i * g i) + 2 * (G.adjMatrix ℝ i j * (g i * g j)) +
          G.adjMatrix ℝ i j * (g j * g j) := by ring
  simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, hleft, hright, hcross] at hpos
  linarith

private theorem dot_normAdj_comm (u v : Fin n → ℝ) :
    u ⬝ᵥ (normAdj G *ᵥ v) = v ⬝ᵥ (normAdj G *ᵥ u) := by
  have h := Matrix.dotProduct_transpose_mulVec (normAdj G) u v
  rwa [(normAdj_symm G).eq] at h

private def summand (x y : Fin n) (s : ℝ) (u : Fin n → ℝ) : ℝ :=
  s * ((scaled G u x)^2 + (scaled G u y)^2) - 2 * scaled G u x * scaled G u y

private theorem leaf_eigen (u : Fin n → ℝ) (s : ℝ)
    (he : normAdj G *ᵥ u = s • u) {x y : Fin n}
    (hxy : G.Adj x y) (hx : G.degree x = 1) :
    scaled G u y = s * scaled G u x := by
  have hmem : y ∈ G.neighborFinset x := (G.mem_neighborFinset x y).mpr hxy
  have hcard : (G.neighborFinset x).card = 1 := hx
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  have heq : y = j := by simpa [hj] using hmem
  subst j
  have h := congrFun he x
  rw [normAdj_mulVec, SimpleGraph.adjMatrix_mulVec_apply, hj, Finset.sum_singleton] at h
  simpa [scaled, show degree G x = 1 by exact_mod_cast hx] using h

private theorem scaled_sq_le (u : Fin n → ℝ) (i : Fin n) (c : ℝ)
    (hc : 0 < c) (hi : c ≤ degree G i) :
    (scaled G u i)^2 ≤ (u i)^2 / c := by
  rw [scaled, div_pow, Real.sq_sqrt (hc.le.trans hi)]
  exact div_le_div_of_nonneg_left (sq_nonneg _) hc hi

private theorem nonedge_mass (hd : ∀ i, 0 < G.degree i) (u : Fin n → ℝ) (s : ℝ)
    (he : normAdj G *ᵥ u = s • u) (hu : u ⬝ᵥ u = 1)
    {x y : Fin n} (hxy : x ≠ y) (hn : ¬ G.Adj x y) :
    (1 + s) * ((u x)^2 + (u y)^2) ≤ 1 := by
  let B := normAdj G
  let w : Fin n → ℝ := Pi.single x (u x) + Pi.single y (u y)
  let m := (u x)^2 + (u y)^2
  have hwu : w ⬝ᵥ u = m := by simp [w, m, add_dotProduct, single_dotProduct, pow_two]
  have huw : u ⬝ᵥ w = m := (dotProduct_comm _ _).trans hwu
  have hww : w ⬝ᵥ w = m := by
    simp [w, m, hxy, hxy.symm, pow_two]
  have hn' : ¬ G.Adj y x := fun h => hn h.symm
  have hwwB : w ⬝ᵥ (B *ᵥ w) = 0 := by
    simp [w, B, add_dotProduct, single_dotProduct, Matrix.mulVec_add, Matrix.mulVec_single,
      normAdj_apply, SimpleGraph.adjMatrix_apply, hn, hn']
  have hwBu : w ⬝ᵥ (B *ᵥ u) = s * m := by
    rw [show B *ᵥ u = s • u from he, dotProduct_smul, hwu]
    rfl
  have huBw : u ⬝ᵥ (B *ᵥ w) = s * m := (dot_normAdj_comm G u w).trans hwBu
  have huBu : u ⬝ᵥ (B *ᵥ u) = s := by
    rw [show B *ᵥ u = s • u from he, dotProduct_smul, hu]
    simp
  have hp := normAdj_lower G hd (w - m • u)
  change 0 ≤ (w - m • u) ⬝ᵥ (w - m • u) + (w - m • u) ⬝ᵥ (B *ᵥ (w - m • u)) at hp
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, hww, hwu, huw, hu, hwwB, hwBu, huBw, huBu,
    smul_eq_mul] at hp
  have hm : 0 ≤ m := by dsimp [m]; positivity
  rcases hm.eq_or_lt with hm | hm
  · rw [← show m = (u x)^2 + (u y)^2 from rfl, ← hm, mul_zero]
    norm_num
  · apply (mul_le_mul_iff_left₀ hm).mp
    nlinarith only [hp]

private theorem summand_le_one (hd : ∀ i, 0 < G.degree i)
    {x y : Fin n} (hxy : x ≠ y) (u : Fin n → ℝ) (s : ℝ)
    (he : normAdj G *ᵥ u = s • u) (hu : u ⬝ᵥ u = 1) :
    summand G x y s u ≤ 1 := by
  have hneg := normAdj_lower G hd u
  have hpos := normAdj_upper G hd u
  simp only [he, dotProduct_smul, hu, smul_eq_mul, mul_one] at hneg hpos
  have hm : (u x)^2 + (u y)^2 ≤ 1 := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (s := {x, y}) (t := Finset.univ) (f := fun i => u i * u i)
      (by simp) (fun i _ _ => mul_self_nonneg (u i))
    change _ ≤ u ⬝ᵥ u at h
    simpa [Finset.sum_insert, hxy, pow_two, hu] using h
  have hq : summand G x y s u ≤ (1 + s) * ((scaled G u x)^2 + (scaled G u y)^2) := by
    unfold summand
    nlinarith only [sq_nonneg (scaled G u x + scaled G u y)]
  have hdeg (i : Fin n) : 1 ≤ degree G i := by exact_mod_cast hd i
  have hm₁ : (scaled G u x)^2 + (scaled G u y)^2 ≤ (u x)^2 + (u y)^2 := by
    simpa using add_le_add (scaled_sq_le G u x 1 zero_lt_one (hdeg x))
      (scaled_sq_le G u y 1 zero_lt_one (hdeg y))
  by_cases hs : s ≤ 0
  · refine hq.trans ((mul_le_mul_of_nonneg_left (hm₁.trans hm) hneg).trans ?_)
    linarith
  by_cases ha : G.Adj x y
  · by_cases hx : G.degree x = 1
    · have h := leaf_eigen G u s he ha hx
      rw [summand, h]
      have hs' : 0 ≤ s := le_of_not_ge hs
      have hs2 : s^2 ≤ 1 := by nlinarith only [mul_nonneg hs' (sub_nonneg.mpr hpos), hpos]
      have hz := mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg hs' (sq_nonneg (scaled G u x))) (sub_nonpos.mpr hs2)
      nlinarith only [hz]
    by_cases hy : G.degree y = 1
    · have h := leaf_eigen G u s he ha.symm hy
      rw [summand, h]
      have hs' : 0 ≤ s := le_of_not_ge hs
      have hs2 : s^2 ≤ 1 := by nlinarith only [mul_nonneg hs' (sub_nonneg.mpr hpos), hpos]
      have hz := mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg hs' (sq_nonneg (scaled G u y))) (sub_nonpos.mpr hs2)
      nlinarith only [hz]
    have hx' : (2 : ℝ) ≤ degree G x := by
      exact_mod_cast (show 2 ≤ G.degree x by have := hd x; omega)
    have hy' : (2 : ℝ) ≤ degree G y := by
      exact_mod_cast (show 2 ≤ G.degree y by have := hd y; omega)
    have h₂ := add_le_add (scaled_sq_le G u x 2 (by norm_num) hx')
      (scaled_sq_le G u y 2 (by norm_num) hy')
    refine hq.trans ((mul_le_mul_of_nonneg_left (show _ ≤ (1 : ℝ) / 2 by linarith) hneg).trans ?_)
    linarith
  · exact hq.trans ((mul_le_mul_of_nonneg_left hm₁ hneg).trans
      (nonedge_mass G hd u s he hu hxy ha))

private def halfRate (x y : Fin n) (i : Fin n) : ℝ :=
  edgeDegrees x y i / (2 * degree G i)

private def perturbedPair (x y : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.single x y 1 + Matrix.single y x 1

private def degreeScale : Matrix (Fin n) (Fin n) ℝ :=
  diagonal fun i => (Real.sqrt (degree G i))⁻¹

private def lapSlope (x y : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal (halfRate G x y) * normAdj G + normAdj G * diagonal (halfRate G x y) -
    degreeScale G * perturbedPair x y * degreeScale G

private theorem invSqrt_hasDerivAt (d k : ℝ) (hd : 0 < d) :
    HasDerivAt (fun t : ℝ => (Real.sqrt (d + t * k))⁻¹)
      (-(k / (2 * d)) * (Real.sqrt d)⁻¹) 0 := by
  have hlin : HasDerivAt (fun t : ℝ => d + t * k) k 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const k).const_add d
  have hs₀ : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt d)) (d + 0 * k) := by
    simpa using Real.hasDerivAt_sqrt hd.ne'
  have hs := hs₀.comp 0 hlin
  have hs' : HasDerivAt (fun t : ℝ => Real.sqrt (d + t * k)) ((1 / (2 * Real.sqrt d)) * k) 0 := by
    simpa [Function.comp_def] using hs
  have hi := hs'.inv (by simpa using (Real.sqrt_pos.2 hd).ne')
  convert hi using 1
  simp only [zero_mul, add_zero, Real.sq_sqrt hd.le]
  have hr := (Real.sqrt_pos.2 hd).ne'
  field_simp [hr, hd.ne']

private theorem lapEntry_hasDerivAt (hd : ∀ i, 0 < G.degree i)
    (x y i j : Fin n) :
    HasDerivAt (fun t => normLap (paramAdj G x y t) i j) (lapSlope G x y i j) 0 := by
  let f := fun (v : Fin n) (t : ℝ) => (Real.sqrt (degree G v + t * edgeDegrees x y v))⁻¹
  have hf (v : Fin n) : HasDerivAt (f v) (-(halfRate G x y v) * f v 0) 0 := by
    simpa [f, halfRate] using invSqrt_hasDerivAt (degree G v) (edgeDegrees x y v)
      (by exact_mod_cast hd v)
  have ha : HasDerivAt (fun t : ℝ => G.adjMatrix ℝ i j + t * perturbedPair x y i j)
      (perturbedPair x y i j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (perturbedPair x y i j)).const_add
      (G.adjMatrix ℝ i j)
  have h := (hasDerivAt_const (0 : ℝ) ((1 : Matrix (Fin n) (Fin n) ℝ) i j)).sub
    (((hf i).mul ha).mul (hf j))
  convert h using 1
  · ext t
    simp only [normLap, Matrix.sub_apply, Matrix.of_apply,
      paramAdj_degrees G x y (degree G) (degree_row G)]
    simp only [paramAdj, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, perturbedPair, f]
    simp only [div_eq_mul_inv, _root_.mul_inv_rev, Pi.sub_apply, Pi.mul_apply]
    ring
  · simp only [lapSlope, Matrix.sub_apply, Matrix.add_apply,
      Matrix.diagonal_mul, Matrix.mul_diagonal, degreeScale, normAdj_apply, f,
      Pi.mul_apply, zero_mul, add_zero, zero_sub, div_eq_mul_inv, _root_.mul_inv_rev]
    ring

private theorem quad_hasDerivAt (hd : ∀ i, 0 < G.degree i)
    (x y : Fin n) (u : Fin n → ℝ) :
    HasDerivAt (fun t => u ⬝ᵥ (normLap (paramAdj G x y t) *ᵥ u))
      (u ⬝ᵥ (lapSlope G x y *ᵥ u)) 0 := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  exact ((lapEntry_hasDerivAt G hd x y i j).mul_const (u j)).const_mul (u i)

private theorem scaled_dot_halfRate (hd : ∀ i, 0 < G.degree i)
    (x y : Fin n) (u : Fin n → ℝ) :
    u ⬝ᵥ (diagonal (halfRate G x y) *ᵥ u) =
      ((scaled G u x)^2 + (scaled G u y)^2) / 2 := by
  have he (i : Fin n) :
      u i * (halfRate G x y i * u i) = edgeDegrees x y i * ((scaled G u i)^2 / 2) := by
    have hdi : (0 : ℝ) < degree G i := by exact_mod_cast hd i
    rw [scaled, div_pow, Real.sq_sqrt hdi.le]
    unfold halfRate
    ring
  simp only [Matrix.mulVec_diagonal, dotProduct, he]
  change (edgeDegrees x y ⬝ᵥ (fun i => (scaled G u i)^2 / 2)) = _
  simp only [edgeDegrees, add_dotProduct, single_dotProduct, one_mul]
  ring

private theorem quad_slope (hd : ∀ i, 0 < G.degree i)
    (x y : Fin n) (s : ℝ) (u : Fin n → ℝ) (he : normAdj G *ᵥ u = s • u) :
    u ⬝ᵥ (lapSlope G x y *ᵥ u) = summand G x y s u := by
  let H := diagonal (halfRate G x y)
  let B := normAdj G
  let P := degreeScale G
  have hsymm (d v w : Fin n → ℝ) :
      v ⬝ᵥ (diagonal d *ᵥ w) = (diagonal d *ᵥ v) ⬝ᵥ w := by
    simp only [Matrix.mulVec_diagonal, dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hP : P *ᵥ u = scaled G u := by
    ext i
    simp [P, degreeScale, Matrix.mulVec_diagonal, scaled, div_eq_mul_inv, mul_comm]
  have hC : scaled G u ⬝ᵥ (perturbedPair x y *ᵥ scaled G u) =
      2 * scaled G u x * scaled G u y := by
    simp [perturbedPair, Matrix.add_mulVec, Matrix.single_mulVec_eq, dotProduct_add,
      dotProduct_single]
    ring
  have hHB : u ⬝ᵥ ((H * B) *ᵥ u) = s * (u ⬝ᵥ (H *ᵥ u)) := by
    rw [← Matrix.mulVec_mulVec, show B *ᵥ u = s • u from he, Matrix.mulVec_smul, dotProduct_smul]
    rfl
  have hBH : u ⬝ᵥ ((B * H) *ᵥ u) = s * (u ⬝ᵥ (H *ᵥ u)) := by
    rw [← Matrix.mulVec_mulVec, dot_normAdj_comm G u (H *ᵥ u),
      show B *ᵥ u = s • u from he, dotProduct_smul, dotProduct_comm (H *ᵥ u) u]
    rfl
  have hPCP : u ⬝ᵥ ((P * perturbedPair x y * P) *ᵥ u) =
      2 * scaled G u x * scaled G u y := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hP]
    rw [show u ⬝ᵥ (P *ᵥ (perturbedPair x y *ᵥ scaled G u)) =
      (P *ᵥ u) ⬝ᵥ (perturbedPair x y *ᵥ scaled G u) from hsymm _ _ _, hP, hC]
  change u ⬝ᵥ ((H * B + B * H - P * perturbedPair x y * P) *ᵥ u) = _
  rw [Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub, dotProduct_add,
    hHB, hBH, hPCP, show u ⬝ᵥ (H *ᵥ u) = _ from scaled_dot_halfRate G hd x y u]
  unfold summand
  ring

/-- The full eigenspace of the unperturbed normalized Laplacian. -/
abbrev eigenspace (x y : Fin n) (lam : ℝ) :=
  Module.End.eigenspace (normLap (paramAdj G x y 0)).toEuclideanLin lam

/-- The normalized trace of the perturbed Laplacian compressed to the fixed eigenspace. -/
def rayleighAverage (x y : Fin n) (lam : ℝ) {k : ℕ}
    (b : OrthonormalBasis (Fin k) ℝ (eigenspace G x y lam)) (t : ℝ) : ℝ :=
  (∑ i, let u := WithLp.ofLp ((b i : eigenspace G x y lam) : EuclideanSpace ℝ (Fin n))
        u ⬝ᵥ (normLap (paramAdj G x y t) *ᵥ u)) / k

/-- The singleton-pair specialization of Albright et al., Lemma 2.3. -/
def edgeDerivative (x y : Fin n) (lam : ℝ) {k : ℕ}
    (b : OrthonormalBasis (Fin k) ℝ (eigenspace G x y lam)) : ℝ :=
  (∑ i, summand G x y (1 - lam)
    (WithLp.ofLp ((b i : eigenspace G x y lam) : EuclideanSpace ℝ (Fin n)))) / k

private theorem eigen_normAdj {x y : Fin n} {lam : ℝ} (u : eigenspace G x y lam) :
    normAdj G *ᵥ WithLp.ofLp u.val = (1 - lam) • WithLp.ofLp u.val := by
  have h := congrArg (fun v : EuclideanSpace ℝ (Fin n) => WithLp.ofLp v)
    (Module.End.mem_eigenspace_iff.mp u.property)
  change normLap (paramAdj G x y 0) *ᵥ WithLp.ofLp u.val =
    lam • WithLp.ofLp u.val at h
  rw [unperturbed, Matrix.sub_mulVec, Matrix.one_mulVec] at h
  rw [sub_smul, one_smul]
  calc
    _ = WithLp.ofLp u.val - (WithLp.ofLp u.val - normAdj G *ᵥ WithLp.ofLp u.val) := by
      abel
    _ = _ := by rw [h]

private theorem dot_self (u : EuclideanSpace ℝ (Fin n)) :
    WithLp.ofLp u ⬝ᵥ WithLp.ofLp u = ‖u‖^2 := by
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using
    real_inner_self_eq_norm_sq u

private theorem rayleighAverage_hasDerivAt (hd : ∀ i, 0 < G.degree i)
    (x y : Fin n) (lam : ℝ) {k : ℕ}
    (b : OrthonormalBasis (Fin k) ℝ (eigenspace G x y lam)) :
    HasDerivAt (rayleighAverage G x y lam b) (edgeDerivative G x y lam b) 0 := by
  unfold rayleighAverage edgeDerivative
  apply HasDerivAt.div_const
  apply HasDerivAt.fun_sum
  intro i _
  let u := WithLp.ofLp (b i).val
  change HasDerivAt (fun t => u ⬝ᵥ (normLap (paramAdj G x y t) *ᵥ u))
    (summand G x y (1 - lam) u) 0
  rw [← quad_slope G hd x y (1 - lam) u (eigen_normAdj G (b i))]
  exact quad_hasDerivAt G hd x y u

private theorem edgeDerivative_le (hd : ∀ i, 0 < G.degree i)
    {x y : Fin n} (hxy : x ≠ y) (lam : ℝ) {k : ℕ} (hk : 0 < k)
    (b : OrthonormalBasis (Fin k) ℝ (eigenspace G x y lam)) :
    edgeDerivative G x y lam b ≤ 1 := by
  unfold edgeDerivative
  apply (div_le_iff₀ (show 0 < (k : ℝ) by exact_mod_cast hk)).2
  rw [one_mul, ← show (∑ _ : Fin k, (1 : ℝ)) = k by simp]
  apply Finset.sum_le_sum
  intro i _
  have hunit : WithLp.ofLp (b i).val ⬝ᵥ WithLp.ofLp (b i).val = 1 := by
    rw [dot_self]
    change ‖b i‖^2 = 1
    rw [b.orthonormal.norm_eq_one i, one_pow]
  exact summand_le_one G hd hxy _ _ (eigen_normAdj G (b i)) hunit

private theorem rayleighAverage_eq_trace (x y : Fin n) (lam : ℝ) {k : ℕ}
    (b : OrthonormalBasis (Fin k) ℝ (eigenspace G x y lam)) (t : ℝ) :
    let E := eigenspace G x y lam
    let T := E.orthogonalProjectionOnto.toLinearMap ∘ₗ
      (normLap (paramAdj G x y t)).toEuclideanLin ∘ₗ E.subtype
    rayleighAverage G x y lam b t = LinearMap.trace ℝ E T / (k : ℝ) := by
  dsimp only
  rw [LinearMap.trace_eq_sum_inner _ b]
  unfold rayleighAverage
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  change _ = ⟪b i, (eigenspace G x y lam).orthogonalProjectionOnto
    ((normLap (paramAdj G x y t)).toEuclideanLin (b i).val)⟫_ℝ
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
    EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin, star_trivial, dotProduct_comm]
  rfl

private theorem basis_independent (hd : ∀ i, 0 < G.degree i) (x y : Fin n) (lam : ℝ) {k : ℕ}
    (b c : OrthonormalBasis (Fin k) ℝ (eigenspace G x y lam)) :
    edgeDerivative G x y lam b = edgeDerivative G x y lam c := by
  have h : rayleighAverage G x y lam b = rayleighAverage G x y lam c := by
    funext t
    rw [rayleighAverage_eq_trace, rayleighAverage_eq_trace]
  exact (rayleighAverage_hasDerivAt G hd x y lam b).unique
    (h.symm ▸ rayleighAverage_hasDerivAt G hd x y lam c)

private abbrev path := SimpleGraph.pathGraph 3

private def endpointVector : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(Real.sqrt 2)⁻¹, 0, -(Real.sqrt 2)⁻¹]

private theorem path_adj : path.adjMatrix ℝ = !![0, 1, 0; 1, 0, 1; 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem path_pair : perturbedPair (0 : Fin 3) 2 = !![0, 0, 1; 0, 0, 0; 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [perturbedPair, Matrix.single]

private theorem path_weighted_adj (t : ℝ) :
    paramAdj path (0 : Fin 3) 2 t = !![0, 1, t; 1, 0, 1; t, 1, 0] := by
  change path.adjMatrix ℝ + t • perturbedPair 0 2 = _
  rw [path_adj, path_pair]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem path_lap (t : ℝ) (ht : 0 ≤ 1 + t) :
    normLap (paramAdj path (0 : Fin 3) 2 t) =
      let a := 1 / (Real.sqrt (1 + t) * Real.sqrt 2)
      let c := t / (1 + t)
      !![1, -a, -c; -a, 1, -a; -c, -a, 1] := by
  rw [path_weighted_adj]
  ext i j
  simp only [normLap, Matrix.sub_apply, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.one_apply, Fin.sum_univ_three, add_comm t 1,
      Real.mul_self_sqrt ht, mul_comm (Real.sqrt 2)]

private theorem path_vector_eq (t : ℝ) (ht : 0 ≤ 1 + t) :
    (normLap (paramAdj path (0 : Fin 3) 2 t)).toEuclideanLin endpointVector =
      (1 + t / (1 + t)) • endpointVector := by
  rw [path_lap t ht]
  apply WithLp.ofLp_injective 2
  ext i
  fin_cases i <;>
    simp [endpointVector] <;>
    ring

private theorem endpoint_unit : ‖endpointVector‖ = 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs₀ : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have h := dot_self endpointVector
  have hq : WithLp.ofLp endpointVector ⬝ᵥ WithLp.ofLp endpointVector = 1 := by
    simp [endpointVector, dotProduct, Fin.sum_univ_three]
    field_simp [hs₀]
    linarith
  rw [hq] at h
  nlinarith [norm_nonneg endpointVector]

private def endpointEigen : eigenspace path 0 2 1 :=
  ⟨endpointVector, Module.End.mem_eigenspace_iff.mpr
    (by simpa using path_vector_eq 0 (by norm_num))⟩

private theorem path_eigenspace_dim :
    Module.finrank ℝ (eigenspace path 0 2 1) = 1 := by
  have hunit : ‖endpointEigen‖ = 1 := endpoint_unit
  have hne : endpointEigen ≠ 0 := by
    intro h
    simp [h] at hunit
  have hlo : 0 < Module.finrank ℝ (eigenspace path 0 2 1) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨endpointEigen, hne⟩
  have hhi : Module.finrank ℝ (eigenspace path 0 2 1) ≤ 1 := by
    apply finrank_le_one endpointEigen
    intro w
    let u := WithLp.ofLp w.val
    have h := Module.End.mem_eigenspace_iff.mp w.property
    change (normLap (paramAdj path (0 : Fin 3) 2 0)).toEuclideanLin w.val = 1 • w.val at h
    rw [path_lap 0 (by norm_num), one_smul] at h
    have h0 := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => WithLp.ofLp z 0) h
    have h1 := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => WithLp.ofLp z 1) h
    have hs : (-(Real.sqrt 2)⁻¹ : ℝ) ≠ 0 := by
      exact neg_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.2 (by norm_num)).ne')
    change _ = u 0 at h0
    change _ = u 1 at h1
    simp [Matrix.ofLp_toLpLin, Matrix.mulVec, dotProduct, Fin.sum_univ_three, u] at h0 h1
    have hu1 : u 1 = 0 := h0
    have hu2 : u 2 = -u 0 := by
      change -((Real.sqrt 2)⁻¹ * u 0) + u 1 + -((Real.sqrt 2)⁻¹ * u 2) = u 1 at h1
      have hzero : -(Real.sqrt 2)⁻¹ * (u 0 + u 2) = 0 := by linarith only [h1]
      have := (mul_eq_zero.mp hzero).resolve_left hs
      linarith
    refine ⟨u 0 * Real.sqrt 2, Subtype.ext ?_⟩
    apply WithLp.ofLp_injective 2
    ext i
    have hr : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
    change (u 0 * Real.sqrt 2) * WithLp.ofLp endpointVector i = u i
    fin_cases i <;> simp [endpointVector, hu1, hu2, hr]
  omega

private theorem path_attains :
    ∃ b : OrthonormalBasis (Fin 1) ℝ (eigenspace path 0 2 1),
      HasDerivAt (rayleighAverage path 0 2 1 b) 1 0 := by
  let b := FiniteDimensional.orthonormalBasisSingleton (Fin 1) ℝ
    path_eigenspace_dim endpointEigen (show ‖endpointEigen‖ = 1 from endpoint_unit)
  refine ⟨b, ?_⟩
  have hlin : HasDerivAt (fun t : ℝ => 1 + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add 1
  have hbranch : HasDerivAt (fun t : ℝ => 1 + t / (1 + t)) 1 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).div hlin (by norm_num)).const_add 1)
  apply hbranch.congr_of_eventuallyEq
  have hpos : ∀ᶠ t : ℝ in nhds 0, 0 < 1 + t :=
    continuousAt_const.eventually_lt hlin.continuousAt (by norm_num)
  filter_upwards [hpos] with t ht
  have hv := congrArg (WithLp.ofLp (p := 2)) (path_vector_eq t ht.le)
  change normLap (paramAdj path 0 2 t) *ᵥ WithLp.ofLp endpointVector =
    (1 + t / (1 + t)) • WithLp.ofLp endpointVector at hv
  simp [rayleighAverage, b, endpointEigen, hv, dotProduct_smul, dot_self, endpoint_unit]

/-- Albright et al., Conjecture 2.20, with the Lemma 2.3 derivative and its attaining graph. -/
def claim : Prop :=
  (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    2 ≤ n → G.Connected → ∀ (x y : Fin n), x ≠ y → ∀ (lam : ℝ) (k : ℕ), 0 < k →
    ∀ b : OrthonormalBasis (Fin k) ℝ (eigenspace G x y lam),
      HasDerivAt (rayleighAverage G x y lam b) (edgeDerivative G x y lam b) 0 ∧
      edgeDerivative G x y lam b ≤ 1 ∧
      ∀ c : OrthonormalBasis (Fin k) ℝ (eigenspace G x y lam),
        edgeDerivative G x y lam b = edgeDerivative G x y lam c) ∧
  (SimpleGraph.pathGraph 3).Connected ∧ (0 : Fin 3) ≠ 2 ∧
  ¬ (SimpleGraph.pathGraph 3).Adj 0 2 ∧
  Module.finrank ℝ (eigenspace (SimpleGraph.pathGraph 3) 0 2 1) = 1 ∧
  ∃ b : OrthonormalBasis (Fin 1) ℝ (eigenspace (SimpleGraph.pathGraph 3) 0 2 1),
    HasDerivAt (rayleighAverage (SimpleGraph.pathGraph 3) 0 2 1 b) 1 0 ∧
    edgeDerivative (SimpleGraph.pathGraph 3) 0 2 1 b = 1

theorem result : claim := by
  refine ⟨?_, SimpleGraph.connected_pathGraph_add_one 2, by decide, by decide,
    path_eigenspace_dim, ?_⟩
  · intro n G _ hn hG x y hxy lam k hk b
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
    have hd (i : Fin n) : 0 < G.degree i := hG.preconnected.degree_pos_of_nontrivial i
    exact ⟨rayleighAverage_hasDerivAt G hd x y lam b, edgeDerivative_le G hd hxy lam hk b,
      fun c => basis_independent G hd x y lam b c⟩
  · obtain ⟨b, hb⟩ := path_attains
    have hd (i : Fin 3) : 0 < path.degree i :=
      (SimpleGraph.preconnected_pathGraph 3).degree_pos_of_nontrivial i
    exact ⟨b, hb, (rayleighAverage_hasDerivAt path hd 0 2 1 b).unique hb⟩

end D5.S3.Combinatorics.SpectralGraph.AlbrightMaxEdgeDerivative
