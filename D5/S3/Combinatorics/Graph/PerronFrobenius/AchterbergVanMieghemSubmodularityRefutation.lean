/- GID: D5/S3/Combinatorics/Graph/PerronFrobenius/AchterbergVanMieghemSubmodularityRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PerronFrobenius/AchterbergVanMieghemSubmodularityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/PerronFrobenius/AchterbergVanMieghemSubmodularityRefutation.claim; result=D5/S3/Combinatorics/Graph/PerronFrobenius/AchterbergVanMieghemSubmodularityRefutation.result; claim=D5/S3/Combinatorics/Graph/PerronFrobenius/AchterbergVanMieghemSubmodularityRefutation.claim
   digest: Five-vertex graphs refute edge-set submodularity of the spectral degree exponent. -/

/-
result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#19958; Refuted)
  Direct frozen dependencies: D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate.edgeMax
  statement_id: sha256:6416e2e7abba3e008affb30098eb2a08ab052a1034a0e202e7ca7e9755d50f4c.
  Direct frozen dependency: D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.adjMatrix_complex_map
  statement_id: sha256:13faeb9446e7b59a5f4a8f4a6f01e5c0aabea91496b226b359439545494ea33b.
Private auxiliary statements (escape_witness: none):
spectral_sup_eq_edgeMax: proof_shape: bind-only; consumers: spectral_bracket, exponent_of_endpoints.
union_graph: proof_shape: bind-only; consumers: result.
inter_graph: proof_shape: bind-only; consumers: result.
degrees0: proof_shape: bind-only; consumers: mean0_three, mean0_four.
degreese: proof_shape: bind-only; consumers: meane_two, meane_three.
degreesf: proof_shape: bind-only; consumers: meane_two, meane_three.
degreesef: proof_shape: bind-only; consumers: meanef_three, meanef_four.
graph_degree0: proof_shape: bind-only; consumers: nonregular.
graph_degree1: proof_shape: bind-only; consumers: nonregular.
nonregular: proof_shape: bind-only; consumers: exponent0, exponente, exponentef.
charpoly0_eval: proof_shape: bind-only; consumers: spectral0.
charpolye_eval: proof_shape: bind-only; consumers: charpoly_single_eval.
charpolyf_eval: proof_shape: bind-only; consumers: charpoly_single_eval.
charpolyef_eval: proof_shape: bind-only; consumers: spectralef.
mean_nonneg: proof_shape: bind-only; consumers: mean0_four, meane_three, meanef_four.
mean_continuous: proof_shape: bind-only; consumers: exponent_of_endpoints.
mean_pow_nat: proof_shape: bind-only; consumers: mean0_three, mean0_four, meane_two, meane_three, meanef_three, meanef_four.
exponent_of_endpoints: proof_shape: bind-only; consumers: exponent0, exponente, exponentef.
root_between: proof_shape: bind-only; consumers: spectral0, spectrale, spectralef.
spectral_bracket: proof_shape: bind-only; consumers: spectral0, spectrale, spectralef.
cubic0_pos: proof_shape: bind-only; consumers: spectral0.
cubice_pos: proof_shape: bind-only; consumers: spectrale.
cubicef_pos: proof_shape: bind-only; consumers: spectralef.
spectral0: proof_shape: bind-only; consumers: exponent0.
charpoly_single_eval: proof_shape: bind-only; consumers: spectrale.
spectrale: proof_shape: bind-only; consumers: exponente.
spectralef: proof_shape: bind-only; consumers: exponentef.
mean0_three: proof_shape: bind-only; consumers: exponent0.
mean0_four: proof_shape: bind-only; consumers: exponent0.
meane_two: proof_shape: bind-only; consumers: exponente.
meane_three: proof_shape: bind-only; consumers: exponente.
meanef_three: proof_shape: bind-only; consumers: exponentef.
meanef_four: proof_shape: bind-only; consumers: exponentef.
exponent0: proof_shape: bind-only; consumers: result.
exponente: proof_shape: bind-only; consumers: result.
exponentef: proof_shape: bind-only; consumers: result.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
The published adjacency-map owner's escape audit is unfinished: https://github.com/the-omega-institute/trureturing/issues/22239.
The source real spectral supremum is inlined in IsSpectralDegreeExponent; proofs use
SpikeEdgeEstimate.edgeMax through the consumed spectral_sup_eq_edgeMax correspondence.
The graph degrees, real spectral supremum and degree power mean represent Definition 2.1
and equation (2.1) of Achterberg and Van Mieghem, arXiv:2502.01815v1, pp. 1–2.
The claim asks about edge sets on a fixed vertex set and finite exponents.
No exponent uniqueness or global monotonicity theorem is used.
-/

import D5.S3.Quantum.BlockNorm.SpikeEdgeEstimate
import D5.S3.Combinatorics.Graph.TokenGraph.CutBoundRefutation

namespace D5.S3.Combinatorics.Graph.PerronFrobenius.AchterbergVanMieghemSubmodularityRefutation

open SimpleGraph

open Classical in
/-- Eq. (2.1): the power mean `((1/N) Σ dᵢ^q)^{1/q}` of the degrees. -/
noncomputable def degreePowerMean {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℝ) : ℝ :=
  ((1 / n : ℝ) * ∑ v, (G.degree v : ℝ) ^ q) ^ (1 / q)

open Classical in
/-- `G` is regular. -/
def IsRegular {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ r, G.IsRegularOfDegree r

open Classical in
/-- Definition 2.1 with Theorem 2.2: `q` is the SDE of the non-regular graph `G`, a finite `q ≥ 2` with `λ₁ = M_q`. -/
def IsSpectralDegreeExponent {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℝ) : Prop :=
  ¬ IsRegular G ∧ 2 ≤ q ∧ sSup (spectrum ℝ (G.adjMatrix ℝ)) = degreePowerMean G q

/-- Submodularity of the SDE on the edge sets of a fixed vertex set. -/
def claim : Prop :=
  ∀ (n : ℕ) (G H : SimpleGraph (Fin n)) (qG qH qU qI : ℝ),
    IsSpectralDegreeExponent G qG → IsSpectralDegreeExponent H qH →
      IsSpectralDegreeExponent (G ⊔ H) qU → IsSpectralDegreeExponent (G ⊓ H) qI →
        qU + qI ≤ qG + qH

end D5.S3.Combinatorics.Graph.PerronFrobenius.AchterbergVanMieghemSubmodularityRefutation

namespace D5.S3.Combinatorics.Graph.PerronFrobenius.AchterbergVanMieghemSubmodularityRefutation
open SimpleGraph Matrix Polynomial
open scoped BigOperators

private def graph (e f : Bool) : SimpleGraph (Fin 5) where
  Adj a b := ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) ∨ ((a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0)) ∨ ((a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 0)) ∨ ((a = 1 ∧ b = 4) ∨ (a = 4 ∧ b = 1)) ∨
    ((a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2)) ∨ (e = true ∧ ((a = 2 ∧ b = 4) ∨ (a = 4 ∧ b = 2))) ∨ (f = true ∧ ((a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 3)))
  symm := ⟨by intro a b; fin_cases a <;> fin_cases b <;> simp⟩
  loopless := ⟨by intro a; fin_cases a <;> simp⟩
private instance (priority := 0) graphAdjDecidable (e f : Bool) : DecidableRel (graph e f).Adj := by
  intro a b
  unfold graph
  infer_instance

private theorem union_graph : (graph true false) ⊔ (graph false true) = (graph true true) := by
  ext a b; fin_cases a <;> fin_cases b <;> decide
private theorem inter_graph : (graph true false) ⊓ (graph false true) = (graph false false) := by
  ext a b; fin_cases a <;> fin_cases b <;> decide

private theorem degrees0 (v : Fin 5) [Fintype ((graph false false).neighborSet v)] :
    (graph false false).degree v = ![3,2,2,2,1] v := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  trans (Finset.univ.filter ((graph false false).Adj v)).card
  · apply Fintype.card_of_finset'
    intro w
    simp
  · fin_cases v <;> decide

private theorem degreese (v : Fin 5) [Fintype ((graph true false).neighborSet v)] :
    (graph true false).degree v = ![3,2,3,2,2] v := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  trans (Finset.univ.filter ((graph true false).Adj v)).card
  · apply Fintype.card_of_finset'
    intro w
    simp
  · fin_cases v <;> decide

private theorem degreesf (v : Fin 5) [Fintype ((graph false true).neighborSet v)] :
    (graph false true).degree v = ![3,2,2,3,2] v := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  trans (Finset.univ.filter ((graph false true).Adj v)).card
  · apply Fintype.card_of_finset'
    intro w
    simp
  · fin_cases v <;> decide

private theorem degreesef (v : Fin 5) [Fintype ((graph true true).neighborSet v)] :
    (graph true true).degree v = ![3,2,3,3,3] v := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  trans (Finset.univ.filter ((graph true true).Adj v)).card
  · apply Fintype.card_of_finset'
    intro w
    simp
  · fin_cases v <;> decide

private theorem graph_degree0 (e f : Bool) [Fintype ((graph e f).neighborSet 0)] :
    (graph e f).degree 0 = 3 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  trans (Finset.univ.filter ((graph e f).Adj 0)).card
  · apply Fintype.card_of_finset'
    intro w
    simp
  · cases e <;> cases f <;> decide

private theorem graph_degree1 (e f : Bool) [Fintype ((graph e f).neighborSet 1)] :
    (graph e f).degree 1 = 2 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  trans (Finset.univ.filter ((graph e f).Adj 1)).card
  · apply Fintype.card_of_finset'
    intro w
    simp
  · cases e <;> cases f <;> decide

private theorem nonregular (e f : Bool) : ¬ IsRegular (graph e f) := by
  rintro ⟨r,hr⟩
  have hh := (hr 0).trans (hr 1).symm
  rw [graph_degree0, graph_degree1] at hh
  norm_num at hh

private theorem charpoly0_eval (z : ℝ) [DecidableRel (graph false false).Adj] : ((graph false false).adjMatrix ℝ).charpoly.eval z =
    (z - 1) * (z + 1) * (z^3 - 4*z - 2) := by
  rw [Matrix.eval_charpoly]
  norm_num [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_two,
    Matrix.submatrix_apply, SimpleGraph.adjMatrix, graph,
    Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.map_apply, Fin.succAbove]
  ring

private theorem charpolye_eval (z : ℝ) [DecidableRel (graph true false).Adj] : ((graph true false).adjMatrix ℝ).charpoly.eval z =
    z * (z + 2) * (z^3 - 2*z^2 - 2*z + 2) := by
  rw [Matrix.eval_charpoly]
  norm_num [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_two,
    Matrix.submatrix_apply, SimpleGraph.adjMatrix, graph,
    Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.map_apply, Fin.succAbove]
  ring

private theorem charpolyf_eval (z : ℝ) [DecidableRel (graph false true).Adj] : ((graph false true).adjMatrix ℝ).charpoly.eval z =
    z * (z + 2) * (z^3 - 2*z^2 - 2*z + 2) := by
  rw [Matrix.eval_charpoly]
  norm_num [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_two,
    Matrix.submatrix_apply, SimpleGraph.adjMatrix, graph,
    Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.map_apply, Fin.succAbove]
  ring

private theorem charpolyef_eval (z : ℝ) [DecidableRel (graph true true).Adj] : ((graph true true).adjMatrix ℝ).charpoly.eval z =
    z * (z + 1) * (z^3 - z^2 - 6*z + 2) := by
  rw [Matrix.eval_charpoly]
  norm_num [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_fin_two,
    Matrix.submatrix_apply, SimpleGraph.adjMatrix, graph,
    Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.map_apply, Fin.succAbove]
  ring


open Classical
private theorem spectral_sup_eq_edgeMax {n : ℕ} (G : SimpleGraph (Fin n)) :
    sSup (spectrum ℝ (G.adjMatrix ℝ)) =
      D5.S3.Quantum.BlockNorm.SpikeEdgeEstimate.edgeMax (G.adjMatrix ℂ) := by
  unfold D5.S3.Quantum.BlockNorm.SpikeEdgeEstimate.edgeMax
  congr 1
  ext x
  rw [← spectrum.algebraMap_mem_iff ℂ (a := G.adjMatrix ℂ), Matrix.mem_spectrum_iff_isRoot_charpoly,
      Matrix.mem_spectrum_iff_isRoot_charpoly]
  have hm : G.adjMatrix ℂ = (G.adjMatrix ℝ).map (algebraMap ℝ ℂ) := by
    simpa using
      (D5.S3.Combinatorics.Graph.TokenGraph.CutBoundRefutation.adjMatrix_complex_map G).symm
  rw [hm, Matrix.charpoly_map, Polynomial.IsRoot.def, Polynomial.IsRoot.def]
  rw [Polynomial.eval_map_apply, map_eq_zero]

private theorem mean_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℝ) :
    0 ≤ degreePowerMean G q := by
  unfold degreePowerMean
  apply Real.rpow_nonneg
  positivity

private theorem mean_continuous {n : ℕ} (G : SimpleGraph (Fin n)) :
    ContinuousOn (degreePowerMean G) (Set.Icc (2 : ℝ) 4) := by
  classical
  unfold degreePowerMean
  have hs : ContinuousOn (fun q : ℝ => (1 / n : ℝ) * ∑ v, (G.degree v : ℝ) ^ q)
      (Set.Icc (2 : ℝ) 4) := by
    apply continuousOn_const.mul
    apply continuousOn_finsetSum
    intro v _
    apply continuousOn_const.rpow continuousOn_id
    intro q hq
    right
    change 0 < q
    linarith [hq.1]
  have hi : ContinuousOn (fun q : ℝ => 1 / q) (Set.Icc (2 : ℝ) 4) := by
    apply continuousOn_const.div continuousOn_id
    intro q hq
    change q ≠ 0
    linarith [hq.1]
  apply hs.rpow hi
  intro q hq
  exact Or.inr (one_div_pos.mpr (by linarith [hq.1]))

private theorem mean_pow_nat {n k : ℕ} (G : SimpleGraph (Fin n)) (hk : k ≠ 0) :
    degreePowerMean G (k : ℝ) ^ k = (1 / n : ℝ) * ∑ v, (G.degree v : ℝ) ^ k := by
  classical
  unfold degreePowerMean
  simpa only [one_div, Real.rpow_natCast] using
    (Real.rpow_inv_natCast_pow
      (show 0 ≤ (1 / n : ℝ) * ∑ v, (G.degree v : ℝ) ^ (k : ℝ) by positivity) hk)

private theorem exponent_of_endpoints {n : ℕ} (G : SimpleGraph (Fin n))
    (hnr : ¬ IsRegular G)
    (a b : ℝ) (ha : 2 ≤ a) (hb : b ≤ 4) (hab : a ≤ b)
    (hl : degreePowerMean G a < (D5.S3.Quantum.BlockNorm.SpikeEdgeEstimate.edgeMax (G.adjMatrix ℂ)))
    (hu : (D5.S3.Quantum.BlockNorm.SpikeEdgeEstimate.edgeMax (G.adjMatrix ℂ)) < degreePowerMean G b) :
    ∃ q ∈ Set.Ioo a b, IsSpectralDegreeExponent G q := by
  have hc := (mean_continuous G).mono (show Set.Icc a b ⊆ Set.Icc (2 : ℝ) 4 by
    intro q hq; exact ⟨ha.trans hq.1, hq.2.trans hb⟩)
  obtain ⟨q, hq, heq⟩ := intermediate_value_Ioo hab hc ⟨hl, hu⟩
  exact ⟨q, hq, hnr, ha.trans hq.1.le, (spectral_sup_eq_edgeMax G).trans heq.symm⟩


private theorem root_between (p : ℝ → ℝ) (hp : Continuous p) (lo hi : ℝ)
    (hli : lo < hi) (hl : p lo < 0) (hu : 0 < p hi) :
    ∃ z ∈ Set.Ioo lo hi, p z = 0 := by
  exact intermediate_value_Ioo hli.le hp.continuousOn ⟨hl, hu⟩

private theorem spectral_bracket {n : ℕ} (G : SimpleGraph (Fin n)) (lo hi : ℝ)
    (hex : ∃ z, lo < z ∧ z ∈ spectrum ℝ (G.adjMatrix ℝ))
    (hu : ∀ z ∈ spectrum ℝ (G.adjMatrix ℝ), z < hi) :
    lo < (D5.S3.Quantum.BlockNorm.SpikeEdgeEstimate.edgeMax (G.adjMatrix ℂ)) ∧ (D5.S3.Quantum.BlockNorm.SpikeEdgeEstimate.edgeMax (G.adjMatrix ℂ)) < hi := by
  classical
  rw [← spectral_sup_eq_edgeMax]
  have hf := (G.adjMatrix ℝ).finite_spectrum
  obtain ⟨z, hzlo, hz⟩ := hex
  have hn : (spectrum ℝ (G.adjMatrix ℝ)).Nonempty := ⟨z, hz⟩
  exact ⟨hzlo.trans_le (le_csSup hf.bddAbove hz), (hf.csSup_lt_iff hn).mpr hu⟩

private theorem cubic0_pos (z : ℝ) (hz : (9:ℝ)/4 ≤ z) : 0 < z^3-4*z-2 := by
  have ht : 0 ≤ z - 9/4 := sub_nonneg.mpr hz
  have hh : z^3-4*z-2 = (z-9/4)^3 + (27/4:ℝ)*(z-9/4)^2 +
      (179/16:ℝ)*(z-9/4) + 25/64 := by ring
  rw [hh]
  positivity

private theorem cubice_pos (z : ℝ) (hz : (249:ℝ)/100 ≤ z) :
    0 < z^3-2*z^2-2*z+2 := by
  have ht : 0 ≤ z - 249/100 := sub_nonneg.mpr hz
  have hh : z^3-2*z^2-2*z+2 = (z-249/100)^3 + (547/100:ℝ)*(z-249/100)^2 +
      (66403/10000:ℝ)*(z-249/100) + 58049/1000000 := by ring
  rw [hh]
  positivity

private theorem cubicef_pos (z : ℝ) (hz : (143:ℝ)/50 ≤ z) :
    0 < z^3-z^2-6*z+2 := by
  have ht : 0 ≤ z - 143/50 := sub_nonneg.mpr hz
  have hh : z^3-z^2-6*z+2 = (z-143/50)^3 + (379/50:ℝ)*(z-143/50)^2 +
      (32047/2500:ℝ)*(z-143/50) + 6757/125000 := by ring
  rw [hh]
  positivity

private theorem spectral0 : (11:ℝ)/5 < (D5.S3.Quantum.BlockNorm.SpikeEdgeEstimate.edgeMax ((graph false false).adjMatrix ℂ)) ∧
    (D5.S3.Quantum.BlockNorm.SpikeEdgeEstimate.edgeMax ((graph false false).adjMatrix ℂ)) < (9:ℝ)/4 := by
  apply spectral_bracket
  · obtain ⟨z, hz, hr⟩ := root_between (fun z : ℝ => z^3-4*z-2)
      (by fun_prop) (11/5) (9/4) (by norm_num) (by norm_num) (by norm_num)
    refine ⟨z, hz.1, Matrix.mem_spectrum_iff_isRoot_charpoly.mpr ?_⟩
    rw [Polynomial.IsRoot.def, charpoly0_eval, hr, mul_zero]
  · intro z hz
    have he := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
    rw [Polynomial.IsRoot.def, charpoly0_eval] at he
    by_contra hn
    have hge := not_lt.mp hn
    have hp := cubic0_pos z hge
    have hf1 : 0 < z - 1 := by linarith
    have hf2 : 0 < z + 1 := by linarith
    have := mul_pos (mul_pos hf1 hf2) hp
    linarith

private theorem charpoly_single_eval (e f : Bool)
    (hef : (e = true ∧ f = false) ∨ (e = false ∧ f = true))
    (z : ℝ) [DecidableRel (graph e f).Adj] :
    ((graph e f).adjMatrix ℝ).charpoly.eval z = z * (z+2) * (z^3-2*z^2-2*z+2) := by
  rcases hef with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact charpolye_eval z
  · exact charpolyf_eval z

private theorem spectrale (e f : Bool) (hef : (e = true ∧ f = false) ∨
    (e = false ∧ f = true)) :
    (49:ℝ)/20 < (D5.S3.Quantum.BlockNorm.SpikeEdgeEstimate.edgeMax ((graph e f).adjMatrix ℂ)) ∧
      (D5.S3.Quantum.BlockNorm.SpikeEdgeEstimate.edgeMax ((graph e f).adjMatrix ℂ)) < (249:ℝ)/100 := by
  apply spectral_bracket
  · obtain ⟨z, hz, hr⟩ := root_between (fun z : ℝ => z^3-2*z^2-2*z+2)
      (by fun_prop) (49/20) (249/100) (by norm_num) (by norm_num) (by norm_num)
    refine ⟨z, hz.1, Matrix.mem_spectrum_iff_isRoot_charpoly.mpr ?_⟩
    rw [Polynomial.IsRoot.def, charpoly_single_eval e f hef, hr, mul_zero]
  · intro z hz
    have he := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
    rw [Polynomial.IsRoot.def, charpoly_single_eval e f hef] at he
    by_contra hn
    have hge := not_lt.mp hn
    have hp := cubice_pos z hge
    have hf1 : 0 < z := by linarith
    have hf2 : 0 < z + 2 := add_pos hf1 zero_lt_two
    have := mul_pos (mul_pos hf1 hf2) hp
    linarith

private theorem spectralef : (571:ℝ)/200 < (D5.S3.Quantum.BlockNorm.SpikeEdgeEstimate.edgeMax ((graph true true).adjMatrix ℂ)) ∧
    (D5.S3.Quantum.BlockNorm.SpikeEdgeEstimate.edgeMax ((graph true true).adjMatrix ℂ)) < (143:ℝ)/50 := by
  apply spectral_bracket
  · obtain ⟨z, hz, hr⟩ := root_between (fun z : ℝ => z^3-z^2-6*z+2)
      (by fun_prop) (571/200) (143/50) (by norm_num) (by norm_num) (by norm_num)
    refine ⟨z, hz.1, Matrix.mem_spectrum_iff_isRoot_charpoly.mpr ?_⟩
    rw [Polynomial.IsRoot.def, charpolyef_eval, hr, mul_zero]
  · intro z hz
    have he := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
    rw [Polynomial.IsRoot.def, charpolyef_eval] at he
    by_contra hn
    have hge := not_lt.mp hn
    have hp := cubicef_pos z hge
    have hf1 : 0 < z := by linarith
    have hf2 : 0 < z + 1 := add_pos hf1 zero_lt_one
    have := mul_pos (mul_pos hf1 hf2) hp
    linarith

private theorem mean0_three : degreePowerMean (graph false false) 3 < (11:ℝ)/5 := by
  have he := mean_pow_nat (graph false false) (k := 3) (by decide)
  norm_num [degrees0, Fin.sum_univ_succ] at he
  by_contra hn
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 11/5) (not_lt.mp hn) 3
  nlinarith

private theorem mean0_four : (9:ℝ)/4 < degreePowerMean (graph false false) 4 := by
  have he := mean_pow_nat (graph false false) (k := 4) (by decide)
  norm_num [degrees0, Fin.sum_univ_succ] at he
  by_contra hn
  have hp := pow_le_pow_left₀ (mean_nonneg (graph false false) 4) (not_lt.mp hn) 4
  norm_num at hp
  linarith

private theorem meane_two (e f : Bool) (hef : (e = true ∧ f = false) ∨
    (e = false ∧ f = true)) : degreePowerMean (graph e f) 2 < (49:ℝ)/20 := by
  rcases hef with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have he := mean_pow_nat (graph true false) (k := 2) (by decide)
    norm_num [degreese, Fin.sum_univ_succ] at he
    by_contra hn
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 49/20) (not_lt.mp hn) 2
    nlinarith
  · have he := mean_pow_nat (graph false true) (k := 2) (by decide)
    norm_num [degreesf, Fin.sum_univ_succ] at he
    by_contra hn
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 49/20) (not_lt.mp hn) 2
    nlinarith

private theorem meane_three (e f : Bool) (hef : (e = true ∧ f = false) ∨
    (e = false ∧ f = true)) : (249:ℝ)/100 < degreePowerMean (graph e f) 3 := by
  rcases hef with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have he := mean_pow_nat (graph true false) (k := 3) (by decide)
    norm_num [degreese, Fin.sum_univ_succ] at he
    by_contra hn
    have hp := pow_le_pow_left₀ (mean_nonneg (graph true false) 3) (not_lt.mp hn) 3
    norm_num at hp
    linarith
  · have he := mean_pow_nat (graph false true) (k := 3) (by decide)
    norm_num [degreesf, Fin.sum_univ_succ] at he
    by_contra hn
    have hp := pow_le_pow_left₀ (mean_nonneg (graph false true) 3) (not_lt.mp hn) 3
    norm_num at hp
    linarith

private theorem meanef_three : degreePowerMean (graph true true) 3 < (571:ℝ)/200 := by
  have he := mean_pow_nat (graph true true) (k := 3) (by decide)
  norm_num [degreesef, Fin.sum_univ_succ] at he
  by_contra hn
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 571/200) (not_lt.mp hn) 3
  nlinarith

private theorem meanef_four : (143:ℝ)/50 < degreePowerMean (graph true true) 4 := by
  have he := mean_pow_nat (graph true true) (k := 4) (by decide)
  norm_num [degreesef, Fin.sum_univ_succ] at he
  by_contra hn
  have hp := pow_le_pow_left₀ (mean_nonneg (graph true true) 4) (not_lt.mp hn) 4
  norm_num at hp
  linarith

private theorem exponent0 : ∃ q, IsSpectralDegreeExponent (graph false false) q ∧ 3 < q := by
  obtain ⟨q,hq,he⟩ := exponent_of_endpoints (graph false false) (nonregular _ _)
    3 4 (by norm_num) (by norm_num) (by norm_num)
    (mean0_three.trans spectral0.1) (spectral0.2.trans mean0_four)
  exact ⟨q,he,hq.1⟩

private theorem exponente (e f : Bool) (hef : (e = true ∧ f = false) ∨
    (e = false ∧ f = true)) :
    ∃ q, IsSpectralDegreeExponent (graph e f) q ∧ q < 3 := by
  have hs := spectrale e f hef
  obtain ⟨q,hq,he⟩ := exponent_of_endpoints (graph e f) (nonregular _ _)
    2 3 (by norm_num) (by norm_num) (by norm_num)
    ((meane_two e f hef).trans hs.1) (hs.2.trans (meane_three e f hef))
  exact ⟨q,he,hq.2⟩

private theorem exponentef : ∃ q, IsSpectralDegreeExponent (graph true true) q ∧ 3 < q := by
  obtain ⟨q,hq,he⟩ := exponent_of_endpoints (graph true true) (nonregular _ _)
    3 4 (by norm_num) (by norm_num) (by norm_num)
    (meanef_three.trans spectralef.1) (spectralef.2.trans meanef_four)
  exact ⟨q,he,hq.1⟩

theorem result : ¬ D5.S3.Combinatorics.Graph.PerronFrobenius.AchterbergVanMieghemSubmodularityRefutation.claim := by
  intro hc
  obtain ⟨q0,h0,hq0⟩ := exponent0
  obtain ⟨qe,he,hqe⟩ := exponente true false (Or.inl ⟨rfl,rfl⟩)
  obtain ⟨qf,hf,hqf⟩ := exponente false true (Or.inr ⟨rfl,rfl⟩)
  obtain ⟨qu,hu,hqu⟩ := exponentef
  have hin : IsSpectralDegreeExponent ((graph true false) ⊓ (graph false true)) q0 := by rwa [inter_graph]
  have hun : IsSpectralDegreeExponent ((graph true false) ⊔ (graph false true)) qu := by rwa [union_graph]
  have hs := hc 5 (graph true false) (graph false true) qe qf qu q0 he hf hun hin
  linarith


end D5.S3.Combinatorics.Graph.PerronFrobenius.AchterbergVanMieghemSubmodularityRefutation
