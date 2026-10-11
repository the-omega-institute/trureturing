/- GID: D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.claim; result=D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.result; claim=D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.claim
   digest: Block-star trees refute the star maximum for graph-state formation. -/

/-
proof_shape: BraunsteinGhoshSeveriniStarRefutation.starGraph_adj: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.star_degree, BraunsteinGhoshSeveriniStarRefutation.Star.star_sigma_entry
proof_shape: BraunsteinGhoshSeveriniStarRefutation.degreeSum_pos: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.sigma_trace
proof_shape: BraunsteinGhoshSeveriniStarRefutation.trace_lapMatrix: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.sigma_trace
proof_shape: BraunsteinGhoshSeveriniStarRefutation.sigma_trace: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.graph_ensemble_nonempty
proof_shape: BraunsteinGhoshSeveriniStarRefutation.sigma_posSemidef: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.graph_ensemble_nonempty
proof_shape: BraunsteinGhoshSeveriniStarRefutation.graph_ensemble_nonempty: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.measured_ensemble, BraunsteinGhoshSeveriniStarRefutation.family_lower
proof_shape: BraunsteinGhoshSeveriniStarRefutation.R_decomposition: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.R_density
proof_shape: BraunsteinGhoshSeveriniStarRefutation.R_density: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Witness.R_lower
proof_shape: BraunsteinGhoshSeveriniStarRefutation.witnessW_unit: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Witness.R_lower
proof_shape: BraunsteinGhoshSeveriniStarRefutation.R_witness_value: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Witness.R_lower
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Witness.R_lower: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.family_lower
proof_shape: BraunsteinGhoshSeveriniStarRefutation.centerOf_center: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Gk_root_reaches
proof_shape: BraunsteinGhoshSeveriniStarRefutation.centerOf_block: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Gk_root_reaches
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Gk_root_reaches: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Gk_connected
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Gk_connected: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.result
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Gk_edge_nonempty: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.measured_ensemble, BraunsteinGhoshSeveriniStarRefutation.family_lower, BraunsteinGhoshSeveriniStarRefutation.result
proof_shape: BraunsteinGhoshSeveriniStarRefutation.adj_local: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.degree_noncenter, BraunsteinGhoshSeveriniStarRefutation.degree_center, BraunsteinGhoshSeveriniStarRefutation.nonhub_matrix
proof_shape: BraunsteinGhoshSeveriniStarRefutation.degree_local_sum: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.degree_noncenter, BraunsteinGhoshSeveriniStarRefutation.degree_center
proof_shape: BraunsteinGhoshSeveriniStarRefutation.degree_noncenter: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.local_degree_total, BraunsteinGhoshSeveriniStarRefutation.nonhub_matrix
proof_shape: BraunsteinGhoshSeveriniStarRefutation.degree_center: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.local_degree_total, BraunsteinGhoshSeveriniStarRefutation.nonhub_matrix
proof_shape: BraunsteinGhoshSeveriniStarRefutation.sum_local_degrees: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Gk_degreeSum
proof_shape: BraunsteinGhoshSeveriniStarRefutation.local_degree_total: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Gk_degreeSum, BraunsteinGhoshSeveriniStarRefutation.compressed_trace
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Gk_degreeSum: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.compressed_trace, BraunsteinGhoshSeveriniStarRefutation.nonhub_matrix
proof_shape: BraunsteinGhoshSeveriniStarRefutation.compressed_trace: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.measured_trace
proof_shape: BraunsteinGhoshSeveriniStarRefutation.localV_injective: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.nonhub_matrix
proof_shape: BraunsteinGhoshSeveriniStarRefutation.project_as_embed: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.measured_nonhub
proof_shape: BraunsteinGhoshSeveriniStarRefutation.nonhub_matrix: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.measured_nonhub
proof_shape: BraunsteinGhoshSeveriniStarRefutation.branchProb_pos: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.measured_average, BraunsteinGhoshSeveriniStarRefutation.measured_trace, BraunsteinGhoshSeveriniStarRefutation.measured_ensemble, BraunsteinGhoshSeveriniStarRefutation.family_lower
proof_shape: BraunsteinGhoshSeveriniStarRefutation.measured_average: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.measured_ensemble, BraunsteinGhoshSeveriniStarRefutation.family_lower
proof_shape: BraunsteinGhoshSeveriniStarRefutation.measured_trace: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.measured_ensemble, BraunsteinGhoshSeveriniStarRefutation.family_lower
proof_shape: BraunsteinGhoshSeveriniStarRefutation.measured_nonhub: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.family_lower
proof_shape: BraunsteinGhoshSeveriniStarRefutation.measured_ensemble: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.family_lower
proof_shape: BraunsteinGhoshSeveriniStarRefutation.family_lower: content; consumer BraunsteinGhoshSeveriniStarRefutation.family
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.normalize_unit: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.normalizedU_entropy, BraunsteinGhoshSeveriniStarRefutation.Star.normalizedP_entropy, BraunsteinGhoshSeveriniStarRefutation.Star.starPsi_unit, BraunsteinGhoshSeveriniStarRefutation.Star.star_cost_bound
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.normalize_outer: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.normalize_marginal, BraunsteinGhoshSeveriniStarRefutation.Star.star_ensemble_average
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.rawU_mass: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.normalizedU_det, BraunsteinGhoshSeveriniStarRefutation.Star.normalizedU_entropy, BraunsteinGhoshSeveriniStarRefutation.Star.starPsi_unit, BraunsteinGhoshSeveriniStarRefutation.Star.star_ensemble_average
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.rawT_mass: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.starPsi_unit, BraunsteinGhoshSeveriniStarRefutation.Star.star_ensemble_average, BraunsteinGhoshSeveriniStarRefutation.Star.star_cost_bound
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.rawZ_mass: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.starPsi_unit, BraunsteinGhoshSeveriniStarRefutation.Star.star_ensemble_average, BraunsteinGhoshSeveriniStarRefutation.Star.star_cost_bound
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.rawP_mass: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.normalizedP_entropy, BraunsteinGhoshSeveriniStarRefutation.Star.starPsi_unit, BraunsteinGhoshSeveriniStarRefutation.Star.star_ensemble_average
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.root_zero: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.star_degree, BraunsteinGhoshSeveriniStarRefutation.Star.star_sigma_entry
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.star_degree: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.star_degreeSum, BraunsteinGhoshSeveriniStarRefutation.Star.star_sigma_entry
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.star_degreeSum: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.star_sigma_entry
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.frame_entry: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.product_frame
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.product_frame: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.star_raw_reconstruction
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.star_sigma_entry: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.star_raw_reconstruction
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.star_raw_reconstruction: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.star_ensemble_average
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.rawU_marginal: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.normalizedU_det
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.normalize_marginal: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.normalizedU_det
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.normalizedU_det: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.normalizedU_entropy
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.normalizedU_entropy: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.normalizedU_entropy_bound, BraunsteinGhoshSeveriniStarRefutation.Star.star_cost_bound, BraunsteinGhoshSeveriniStarRefutation.Star.star_upper
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.cStar_sq: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.normalizedU_entropy_bound
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.normalizedU_entropy_bound: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.star_upper
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.single_row_entropy: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.normalizedP_entropy
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.normalizedP_entropy: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.star_cost_bound
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.starWeight_nonneg: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.starEnsemble
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.starWeight_total: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.starEnsemble
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.starPsi_unit: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.starEnsemble
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.star_ensemble_average: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.starEnsemble
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.starEnsemble_cost: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.star_cost_bound
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.star_cost_bound: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.Star.star_upper
proof_shape: BraunsteinGhoshSeveriniStarRefutation.Star.star_upper: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.family
proof_shape: BraunsteinGhoshSeveriniStarRefutation.family: content; consumer BraunsteinGhoshSeveriniStarRefutation.result
proof_shape: BraunsteinGhoshSeveriniStarRefutation.result: content
escape_witness: not needed (open-problem-resolution); content through family_lower
admission_basis: open-problem-resolution (#13813; Refuted)
Direct frozen dependencies (declaration statement_id):
  D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity
    sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3
  D5/S3/Weil/Probability/FiniteGaussianSchoenberg.ofReal_posSemidef
    sha256:e43b63bc2ba962082673f10ac6003f58de8e5074d7a6467d794c4842e8856cd3
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight
    sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77
  D5/S3/Quantum/Information/PartialTraceMutualInformation.trace_partialTraceRight
    sha256:2e0d10f59a41befee8bb5e380b1d8d7db7e14a2bbed6d47af5089807c0905813
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight_posSemidef
    sha256:534be990ab7c643fd18c2a086aa7a7b696bb02a8baa49a26c15e479b63e74944
Supporting modules in this delivery are not baseline-frozen prerequisites.
Information-escape registration is paused under CLAUDE.md §3.9 「信息逃逸登记暂缓」.
-/

import D5.S3.Quantum.Entanglement.GraphDensity.SelectiveFormationBounds
import D5.S3.Weil.Probability.FiniteGaussianSchoenberg
import Mathlib.Analysis.Normed.Module.Normalize

open private weight_le_one_of_total
  from D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Set Matrix
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight partialTraceLeft)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation (partialTransposeB)
open D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Witness
open D5.S3.Quantum.Entanglement.GraphDensity.SelectiveFormationBounds D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Selective
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.Entanglement.GraphDensity.BraunsteinGhoshSeveriniStarRefutation
open D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Witness
def degreeSum {p q : ℕ} (G : SimpleGraph ((Fin p × Fin q))) : ℕ := by
  classical
  exact ∑ v, G.degree v

def sigma {p q : ℕ} (G : SimpleGraph ((Fin p × Fin q))) : (Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ) := by
  classical
  exact ((1 / (degreeSum G : ℝ) : ℝ) : ℂ) • G.lapMatrix ℂ

def root {p q : ℕ} (x : (Fin p × Fin q)) : Prop := x.1.val = 0 ∧ x.2.val = 0

def starGraph (p q : ℕ) : SimpleGraph (Fin p × Fin q) :=
  if h : 0 < p ∧ 0 < q then
    SimpleGraph.starGraph (⟨0,h.1⟩,⟨0,h.2⟩)
  else ⊥
private theorem starGraph_adj {p q : ℕ} (x y : Fin p × Fin q) :
    (starGraph p q).Adj x y ↔ x ≠ y ∧ (root x ∨ root y) := by
  have hp : 0 < p := Nat.zero_le x.1.val |>.trans_lt x.1.isLt
  have hq : 0 < q := Nat.zero_le x.2.val |>.trans_lt x.2.isLt
  have h : 0 < p ∧ 0 < q := ⟨hp,hq⟩
  simp only [starGraph,dif_pos h,SimpleGraph.starGraph_adj]
  simp [root,Prod.ext_iff,Fin.ext_iff]

def center {k : ℕ} (x : (Fin 2 × Fin (2*k))) : Prop := x.1.val = 0 ∧ x.2.val % 2 = 0

def Gk (k : ℕ) : SimpleGraph ((Fin 2 × Fin (2*k))) where
  Adj x y := x ≠ y ∧
    ((x.2.val / 2 = y.2.val / 2 ∧ (center x ∨ center y)) ∨
      (center x ∧ center y ∧ (root x ∨ root y)))
  symm := ⟨by
    intro x y h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h | h
    · exact Or.inl ⟨h.1.symm, h.2.symm⟩
    · exact Or.inr ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

def claim : Prop :=
  ∀ (p q : ℕ) (G : SimpleGraph ((Fin p × Fin q))), G.Connected → G.edgeSet.Nonempty →
    E_F (sigma G) ≤ E_F (sigma (starGraph p q))
private theorem degreeSum_pos {p q : ℕ} (G : SimpleGraph ((Fin p × Fin q))) (he : G.edgeSet.Nonempty) :
    0 < degreeSum G := by
  classical
  obtain ⟨x,y,hxy⟩ := G.ne_bot_iff_exists_adj.mp (G.edgeSet_nonempty.mp he)
  have hp : 0 < G.degree x := (G.degree_pos_iff_exists_adj x).mpr ⟨y,hxy⟩
  apply hp.trans_le
  unfold degreeSum
  exact Finset.single_le_sum (fun i _ => Nat.zero_le (G.degree i)) (Finset.mem_univ x)
private theorem trace_lapMatrix {p q : ℕ} (G : SimpleGraph ((Fin p × Fin q))) :
    (G.lapMatrix ℂ).trace = (degreeSum G : ℂ) := by
  classical
  simp [SimpleGraph.lapMatrix,SimpleGraph.degMatrix,SimpleGraph.adjMatrix,Matrix.trace,
    degreeSum,Complex.ofReal_sum]
private theorem sigma_trace {p q : ℕ} (G : SimpleGraph ((Fin p × Fin q))) (he : G.edgeSet.Nonempty) :
    (sigma G).trace = 1 := by
  classical
  have hd : (degreeSum G : ℂ) ≠ 0 := by exact_mod_cast (degreeSum_pos G he).ne'
  simp only [sigma,Matrix.trace_smul,trace_lapMatrix,smul_eq_mul]
  push_cast
  simpa only [one_div] using inv_mul_cancel₀ hd
private theorem sigma_posSemidef {p q : ℕ} (G : SimpleGraph ((Fin p × Fin q))) : (sigma G).PosSemidef := by
  classical
  have hc : G.lapMatrix ℂ = fun x y => ((G.lapMatrix ℝ) x y : ℂ) := by
    ext x y
    simp [SimpleGraph.lapMatrix,SimpleGraph.degMatrix,SimpleGraph.adjMatrix,Matrix.diagonal]
    split_ifs <;> simp
  have hp := D5.S3.Weil.Probability.FiniteGaussianSchoenberg.ofReal_posSemidef
    (G.lapMatrix ℝ) (G.posSemidef_lapMatrix ℝ)
  rw [← hc] at hp
  unfold sigma
  exact hp.smul (by positivity)
private theorem graph_ensemble_nonempty {p q : ℕ} (G : SimpleGraph ((Fin p × Fin q)))
    (he : G.edgeSet.Nonempty) : Nonempty (Ensemble (sigma G)) :=
  spectral_ensemble_nonempty _ (sigma_posSemidef G) (sigma_trace G he)
private def R : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := fun x y =>
  if x=y then (if x=(0,0) then 4/7 else 1/7)
  else if x=(0,0) ∨ y=(0,0) then -1/7 else 0
private def witnessW : ((Fin 2 × Fin 2) → ℂ) := fun x => ![![1/3,2/3],![2/3,0]] x.1 x.2
private theorem R_decomposition : R = (1/7:ℂ) •
    (rankOneDensity ((Pi.single (0,0) (1:ℂ))-(Pi.single (0,1) (1:ℂ))) +
     rankOneDensity ((Pi.single (0,0) (1:ℂ))-(Pi.single (1,0) (1:ℂ))) +
     rankOneDensity ((Pi.single (0,0) (1:ℂ))-(Pi.single (1,1) (1:ℂ))) + rankOneDensity ((Pi.single (0,0) (1:ℂ)))) := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [R,rankOneDensity,Pi.single_apply,Matrix.vecMulVec_apply]
private theorem R_density : R.PosSemidef ∧ R.trace=1 := by
  constructor
  · rw [R_decomposition]
    exact (((Matrix.posSemidef_vecMulVec_self_star _).add
      (Matrix.posSemidef_vecMulVec_self_star _)).add
      (Matrix.posSemidef_vecMulVec_self_star _)).add
      (Matrix.posSemidef_vecMulVec_self_star _) |>.smul (by norm_num [Complex.le_def])
  · norm_num [R,Matrix.trace,Fintype.sum_prod_type,Fin.sum_univ_two]
private theorem witnessW_unit : ∑ x, ‖witnessW x‖^2 = 1 := by
  simp_rw [← Complex.normSq_eq_norm_sq]
  norm_num [witnessW,Fintype.sum_prod_type,Fin.sum_univ_two]
private theorem R_witness_value :
    (dotProduct (star witnessW) ((partialTransposeB R).mulVec witnessW)).re = -4/63 := by
  norm_num [partialTransposeB,R,witnessW,Matrix.mulVec,dotProduct,
    Fintype.sum_prod_type,Fin.sum_univ_two,Complex.star_def,map_div₀,map_ofNat]

end D5.S3.Quantum.Entanglement.GraphDensity.BraunsteinGhoshSeveriniStarRefutation

namespace D5.S3.Quantum.Entanglement.GraphDensity.BraunsteinGhoshSeveriniStarRefutation.Witness
open D5.S3.Quantum.Entanglement.GraphDensity.BraunsteinGhoshSeveriniStarRefutation D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Witness
private theorem R_lower : D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic.f (8/63) ≤ E_F R := by
  have hh := witness_lower (spectral_ensemble_nonempty R R_density.1 R_density.2)
    witnessW witnessW_unit
  have he : W witnessW R=4/63 := by
    simp only [W,expectation,R_witness_value]
    norm_num
  rw [he] at hh
  norm_num at hh ⊢
  exact hh

end D5.S3.Quantum.Entanglement.GraphDensity.BraunsteinGhoshSeveriniStarRefutation.Witness

namespace D5.S3.Quantum.Entanglement.GraphDensity.BraunsteinGhoshSeveriniStarRefutation
open D5.S3.Quantum.Entanglement.GraphDensity.BraunsteinGhoshSeveriniStarRefutation.Witness D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Witness
private def rootK (k : ℕ) (hk : 0 < k) : (Fin 2 × Fin (2*k)) := (0,⟨0,by omega⟩)
private def centerOf {k : ℕ} (x : (Fin 2 × Fin (2*k))) : (Fin 2 × Fin (2*k)) :=
  (0,⟨2*(x.2.val/2),by have hh := x.2.isLt; omega⟩)
private theorem centerOf_center {k : ℕ} (x : (Fin 2 × Fin (2*k))) : center (centerOf x) := by
  simp [center,centerOf]
private theorem centerOf_block {k : ℕ} (x : (Fin 2 × Fin (2*k))) :
    (centerOf x).2.val/2=x.2.val/2 := by simp [centerOf]
private theorem Gk_root_reaches {k : ℕ} (hk : 0 < k) (x : (Fin 2 × Fin (2*k))) :
    (Gk k).Reachable (rootK k hk) x := by
  have hroot : root (rootK k hk) := by simp [root,rootK]
  have hcroot : center (rootK k hk) := by simp [center,rootK]
  have hrc : (Gk k).Reachable (rootK k hk) (centerOf x) := by
    by_cases he : rootK k hk=centerOf x
    · simpa only [he] using (SimpleGraph.Reachable.rfl :
        (Gk k).Reachable (centerOf x) (centerOf x))
    · exact SimpleGraph.Adj.reachable ⟨he,Or.inr ⟨hcroot,centerOf_center x,Or.inl hroot⟩⟩
  by_cases he : centerOf x=x
  · rwa [he] at hrc
  · exact hrc.trans (SimpleGraph.Adj.reachable
      ⟨he,Or.inl ⟨centerOf_block x,Or.inl (centerOf_center x)⟩⟩)
private theorem Gk_connected {k : ℕ} (hk : 0 < k) : (Gk k).Connected := by
  letI : Nonempty ((Fin 2 × Fin (2*k))) := ⟨rootK k hk⟩
  apply SimpleGraph.Connected.mk
  intro x y
  exact (Gk_root_reaches hk x).symm.trans (Gk_root_reaches hk y)
private theorem Gk_edge_nonempty {k : ℕ} (hk : 0 < k) : (Gk k).edgeSet.Nonempty := by
  let y : (Fin 2 × Fin (2*k)) := (1,⟨0,by omega⟩)
  exact ⟨s(rootK k hk,y), (Gk k).mem_edgeSet.mpr
    ⟨by simp [rootK,y],Or.inl ⟨by simp [rootK,y],Or.inl (by simp [center,rootK])⟩⟩⟩
private def localV {k : ℕ} (j : Fin k) (x : (Fin 2 × Fin 2)) : (Fin 2 × Fin (2*k)) := Prod.map id (fun b => pairEquiv k (j,b)) x
private theorem adj_local {k : ℕ} (j l : Fin k) (x y : (Fin 2 × Fin 2)) :
    (Gk k).Adj (localV j x) (localV l y) ↔
    (j,x)≠(l,y) ∧ ((j=l ∧ (x=(0,0) ∨ y=(0,0))) ∨
      (x=(0,0) ∧ y=(0,0) ∧ (j.val=0 ∨ l.val=0))) := by
  have hs (j : Fin k) (b : Fin 2) : (pairEquiv k (j, b)).val/2=j.val := by
    rw [pairEquiv_val]
    have hb := b.isLt
    omega
  have hm (j : Fin k) (b : Fin 2) : (pairEquiv k (j, b)).val%2=b.val := by
    rw [pairEquiv_val]
    have hb := b.isLt
    omega
  have hc (j : Fin k) (x : (Fin 2 × Fin 2)) : center (localV j x) ↔ x=(0,0) := by
    simp only [center,localV,Prod.fst,Prod.snd,hm,Prod.map,Function.comp_apply,id_eq]
    simp [Prod.ext_iff]
  have hr (j : Fin k) (x : (Fin 2 × Fin 2)) : root (localV j x) ↔ j.val=0 ∧ x=(0,0) := by
    simp only [root,localV,Prod.fst,Prod.snd,pairEquiv_val,Prod.map,Function.comp_apply,id_eq]
    have he : x.2.val+2*j.val=0 ↔ x.2.val=0 ∧ j.val=0 := by omega
    rw [he]
    simp [Prod.ext_iff,and_left_comm,and_comm]
  have heq : localV j x=localV l y ↔ (j,x)=(l,y) := by
    simp only [localV,Prod.ext_iff,Fin.ext_iff,pairEquiv_val,Prod.map,Function.comp_apply,id_eq]
    have hx := x.2.isLt
    have hy := y.2.isLt
    omega
  change (localV j x≠localV l y ∧
    (((pairEquiv k (j, x.2)).val/2=(pairEquiv k (l, y.2)).val/2 ∧
      (center (localV j x) ∨ center (localV l y))) ∨
      (center (localV j x) ∧ center (localV l y) ∧
        (root (localV j x) ∨ root (localV l y))))) ↔ _
  have hjl : j.val=l.val ↔ j=l := Fin.ext_iff.symm
  simp only [heq,hs,hc,hr,hjl]
  tauto
private theorem degree_local_sum {k : ℕ} (j : Fin k) (x : (Fin 2 × Fin 2)) :
    (Gk k).degree (localV j x)=
      ∑ l : Fin k, ∑ y : (Fin 2 × Fin 2), if (Gk k).Adj (localV j x) (localV l y) then 1 else 0 := by
  classical
  have hd := (Gk k).degree_eq_sum_if_adj (R := ℕ) (localV j x)
  simp only [Nat.cast_id] at hd
  rw [hd,Fintype.sum_prod_type]
  simp_rw [← (pairEquiv k).sum_comp,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Fintype.sum_prod_type,localV,Prod.map,Function.comp_apply,id_eq]
private theorem degree_noncenter {k : ℕ} (j : Fin k) (x : (Fin 2 × Fin 2)) (hx : x≠(0,0)) :
    (Gk k).degree (localV j x)=1 := by
  classical
  rw [degree_local_sum]
  simp_rw [adj_local,Fintype.sum_prod_type,Fin.sum_univ_two]
  rcases x with ⟨a,b⟩
  fin_cases a <;> fin_cases b <;>
    simp_all [Fintype.sum_prod_type,Fin.sum_univ_two,Prod.ext_iff]
private theorem degree_center {k : ℕ} (j : Fin k) :
    (Gk k).degree (localV j (0,0))=if j.val=0 then k+2 else 4 := by
  classical
  rw [degree_local_sum]
  have hs (l : Fin k) :
      (∑ y : (Fin 2 × Fin 2), if (Gk k).Adj (localV j (0,0)) (localV l y) then 1 else 0) =
        (if l=j then 3 else 0)+(if l≠j ∧ (j.val=0 ∨ l.val=0) then 1 else 0) := by
    simp_rw [adj_local]
    simp only [Fintype.sum_prod_type,Fin.sum_univ_two,Prod.ext_iff]
    by_cases hl : l=j
    · subst l; simp
    · have hlj : j≠l := Ne.symm hl
      by_cases hj : j.val=0 <;> by_cases hl0 : l.val=0 <;> simp [hl,hlj,hj,hl0]
  simp_rw [hs]
  rw [Finset.sum_add_distrib]
  have hk : 0<k := Nat.zero_lt_of_lt j.isLt
  by_cases hj : j.val=0
  · simp only [hj,↓reduceIte,true_or,and_true]
    have hn : (∑ l : Fin k, if l≠j then 1 else 0) = k-1 := by
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero,add_zero,Finset.sum_const,smul_eq_mul,mul_one]
      have hf : Finset.univ.filter (fun x : Fin k => x≠j)=Finset.univ.erase j := by
        ext x
        simp [ne_eq,and_comm]
      rw [hf,Finset.card_erase_of_mem (Finset.mem_univ j)]
      simp
    rw [hn]
    simp
    omega
  · have hj0 : j≠⟨0,hk⟩ := by simpa [Fin.ext_iff] using hj
    have he (l : Fin k) : (l≠j ∧ (j.val=0 ∨ l.val=0)) ↔ l=⟨0,hk⟩ := by
      simp only [hj,false_or,Fin.ext_iff]
      omega
    simp_rw [he]
    simp [hj]
private theorem sum_local_degrees {k : ℕ} : degreeSum (Gk k)=
    ∑ j : Fin k, ∑ x : (Fin 2 × Fin 2), (Gk k).degree (localV j x) := by
  unfold degreeSum
  rw [Fintype.sum_prod_type]
  simp_rw [← (pairEquiv k).sum_comp,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fintype.sum_prod_type,localV,Prod.map,Function.comp_apply,id_eq]
private theorem local_degree_total {k : ℕ} (j : Fin k) :
    (∑ x : (Fin 2 × Fin 2), (Gk k).degree (localV j x))=(if j.val=0 then k+2 else 4)+3 := by
  rw [Fintype.sum_prod_type,Fin.sum_univ_two,Fin.sum_univ_two,Fin.sum_univ_two]
  rw [degree_center,degree_noncenter j (0,1) (by decide),
    degree_noncenter j (1,0) (by decide),degree_noncenter j (1,1) (by decide)]
  omega
private theorem Gk_degreeSum {k : ℕ} (hk : 2 ≤ k) : degreeSum (Gk k)=8*k-2 := by
  classical
  rw [sum_local_degrees]
  simp_rw [local_degree_total]
  have hterm (j : Fin k) : (if j.val=0 then k+2 else 4)+3=
      (if j=⟨0,by omega⟩ then k-2 else 0)+7 := by
    simp only [Fin.ext_iff]
    split_ifs <;> omega
  simp_rw [hterm]
  simp [Finset.sum_add_distrib]
  omega
private def branchProb {k : ℕ} (j : Fin k) : ℝ :=
  (if j.val=0 then (k:ℝ)+5 else 7)/(8*(k:ℝ)-2)
private theorem compressed_trace {k : ℕ} (hk : 2 ≤ k) (j : Fin k) :
    (projectBlock (fun b => ((pairEquiv k).symm b).1) j (sigma (Gk k))).trace.re=branchProb j := by
  classical
  have hd : ((8*k-2:ℕ):ℝ)=8*(k:ℝ)-2 := by rw [Nat.cast_sub (by omega)]; norm_num
  simp only [Matrix.trace,Matrix.diag_apply]
  rw [Fintype.sum_prod_type]
  simp_rw [← (pairEquiv k).sum_comp,Fintype.sum_prod_type]
  try simp only [projectBlock,Equiv.symm_apply_apply,and_self,Set.indicator,Function.curry,Function.uncurry,Set.mem_ofPred_eq]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single j _ (by simp)]
  swap
  · intro l _ hl
    simp [projectBlock,Equiv.symm_apply_apply,hl,Set.indicator,Function.curry,Function.uncurry,Set.mem_ofPred_eq]
  simp only [projectBlock,Equiv.symm_apply_apply,eq_self,and_self,if_true,Set.indicator,Function.curry,Function.uncurry,Set.mem_ofPred_eq]
  simp only [sigma,Matrix.smul_apply,smul_eq_mul,SimpleGraph.lapMatrix,SimpleGraph.degMatrix,SimpleGraph.adjMatrix,Matrix.sub_apply,Matrix.of_apply,Matrix.diagonal_apply,if_pos rfl,SimpleGraph.irrefl,if_false,if_true,sub_zero]
  have hsum : (∑ a : Fin 2, ∑ b : Fin 2,
      ((Gk k).degree (localV j (a,b)):ℂ)) =
      ((if j.val=0 then k+2 else 4)+3:ℕ) := by
    norm_cast
    simpa only [Fintype.sum_prod_type] using local_degree_total j
  simp only [← Finset.mul_sum]
  change ((((1/(degreeSum (Gk k):ℝ)):ℝ):ℂ)*
    (∑ a : Fin 2, ∑ b : Fin 2, ((Gk k).degree (localV j (a,b)):ℂ))).re=branchProb j
  rw [hsum,Gk_degreeSum hk]
  unfold branchProb
  split_ifs <;> push_cast <;> simp [hd] <;> ring
private theorem localV_injective {k : ℕ} (j : Fin k) : Function.Injective (localV j) := by
  exact Function.injective_id.prodMap
    ((pairEquiv k).injective.comp (Prod.mk_right_injective j))
private theorem project_as_embed {k : ℕ} (j : Fin k) (ρ : (Matrix (Fin 2 × Fin (2*k)) (Fin 2 × Fin (2*k)) ℂ)) :
    projectBlock (fun b => ((pairEquiv k).symm b).1) j ρ=embedState j (ρ.submatrix (localV j) (localV j)) := by
  ext x y
  by_cases hx : ((pairEquiv k).symm x.2).1=j <;> by_cases hy : ((pairEquiv k).symm y.2).1=j
  · have hx2 : pairEquiv k (j, ((pairEquiv k).symm x.2).2)=x.2 := by
      rw [← hx]; exact (pairEquiv k).apply_symm_apply x.2
    have hy2 : pairEquiv k (j, ((pairEquiv k).symm y.2).2)=y.2 := by
      rw [← hy]; exact (pairEquiv k).apply_symm_apply y.2
    simp [projectBlock,embedState,hx,hy,Matrix.submatrix_apply,localV,hx2,hy2,Set.indicator,Function.curry,Function.uncurry,Set.mem_ofPred_eq,Prod.map,Function.comp_apply,id_eq,Set.indicator,Function.curry,Function.uncurry,Set.mem_ofPred_eq,Prod.map,Function.comp_apply,id_eq,Matrix.submatrix_apply]
  all_goals simp [projectBlock,embedState,hx,hy,Set.indicator,Function.curry,Function.uncurry,Set.mem_ofPred_eq,Set.indicator,Function.curry,Function.uncurry,Set.mem_ofPred_eq,Prod.map,Function.comp_apply,id_eq,Matrix.submatrix_apply]
private theorem nonhub_matrix {k : ℕ} (hk : 2 ≤ k) (j : Fin k) (hj : j.val≠0) :
    (sigma (Gk k)).submatrix (localV j) (localV j)=
      ((7/(8*(k:ℝ)-2):ℝ):ℂ) • R := by
  classical
  have hd : ((8*k-2:ℕ):ℝ)=8*(k:ℝ)-2 := by rw [Nat.cast_sub (by omega)]; norm_num
  have heq (x y : (Fin 2 × Fin 2)) : localV j x=localV j y ↔ x=y := (localV_injective j).eq_iff
  have hdeg (x : (Fin 2 × Fin 2)) : (Gk k).degree (localV j x)=if x=(0,0) then 4 else 1 := by
    by_cases hx : x=(0,0)
    · subst x
      simp [degree_center,hj]
    · simp only [hx,if_false]
      exact degree_noncenter j x hx
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  all_goals simp only [Matrix.submatrix_apply,sigma,Matrix.smul_apply,smul_eq_mul,
    SimpleGraph.lapMatrix,SimpleGraph.degMatrix,SimpleGraph.adjMatrix,
    Matrix.diagonal_apply,Matrix.sub_apply,Matrix.of_apply,heq,
    hdeg,
    adj_local,Gk_degreeSum hk]
  all_goals simp [R,hj,hd]
  all_goals push_cast
  all_goals ring
private theorem branchProb_pos {k : ℕ} (hk : 2 ≤ k) (j : Fin k) : 0<branchProb j := by
  have hkR : 2≤(k:ℝ) := by exact_mod_cast hk
  have hd : 0<8*(k:ℝ)-2 := by linarith
  unfold branchProb
  split_ifs <;> positivity
private def measuredState {k : ℕ} (j : Fin k) : (Matrix (Fin 2 × Fin (2*k)) (Fin 2 × Fin (2*k)) ℂ) :=
  (((1/branchProb j):ℝ):ℂ) • projectBlock (fun b => ((pairEquiv k).symm b).1) j (sigma (Gk k))
private theorem measured_average {k : ℕ} (hk : 2 ≤ k) (j : Fin k) :
    projectBlock (fun b => ((pairEquiv k).symm b).1) j (sigma (Gk k))=(branchProb j:ℂ) • measuredState j := by
  have hpC : (branchProb j:ℂ)≠0 := by exact_mod_cast (branchProb_pos hk j).ne'
  simp only [measuredState,smul_smul,Complex.ofReal_div,Complex.ofReal_one]
  rw [mul_one_div_cancel hpC,one_smul]
private theorem measured_trace {k : ℕ} (hk : 2 ≤ k) (j : Fin k) : (measuredState j).trace=1 := by
  have hi : (projectBlock (fun b => ((pairEquiv k).symm b).1) j (sigma (Gk k))).trace.im=0 := by
    simp [Matrix.trace,projectBlock,apply_ite,sigma,SimpleGraph.lapMatrix,
      SimpleGraph.degMatrix,SimpleGraph.adjMatrix,Matrix.diagonal,Matrix.smul_apply,
      smul_eq_mul,Complex.im_sum,Complex.mul_im,Set.indicator,Function.curry,Function.uncurry,Set.mem_ofPred_eq]
  have hc : (projectBlock (fun b => ((pairEquiv k).symm b).1) j (sigma (Gk k))).trace=(branchProb j:ℂ) := by
    apply Complex.ext
    · simpa using compressed_trace hk j
    · simpa using hi
  have hpC : (branchProb j:ℂ)≠0 := by exact_mod_cast (branchProb_pos hk j).ne'
  simp only [measuredState,Matrix.trace_smul,smul_eq_mul,Complex.ofReal_div,Complex.ofReal_one]
  rw [hc,one_div_mul_cancel hpC]
private theorem measured_nonhub {k : ℕ} (hk : 2 ≤ k) (j : Fin k) (hj : j.val≠0) :
    measuredState j=embedState j R := by
  have hkR : 2≤(k:ℝ) := by exact_mod_cast hk
  have hd : (8*(k:ℝ)-2)≠0 := by linarith
  rw [measuredState,project_as_embed,nonhub_matrix hk j hj]
  ext x y
  by_cases hxy : ((pairEquiv k).symm x.2).1=j ∧ ((pairEquiv k).symm y.2).1=j
  · simp only [embedState,hxy,if_true,branchProb,hj,if_false,
      Matrix.smul_apply,smul_eq_mul,Complex.ofReal_div,Complex.ofReal_one,
      Complex.ofReal_ofNat,Complex.ofReal_sub,Complex.ofReal_mul,Set.indicator,Function.curry,Function.uncurry,Set.mem_ofPred_eq,Prod.map,Function.comp_apply,id_eq,Matrix.submatrix_apply]
    have hdC : (8*(k:ℂ)-2)≠0 := by exact_mod_cast hd
    simp only [and_self,if_true]
    push_cast
    field_simp
    <;> ring
  · simp only [embedState,hxy,if_false,Matrix.smul_apply,smul_eq_mul,mul_zero,Set.indicator,Function.curry,Function.uncurry,Set.mem_ofPred_eq,Prod.map,Function.comp_apply,id_eq,Matrix.submatrix_apply]
private theorem measured_ensemble {k : ℕ} (hk : 2 ≤ k) (j : Fin k) :
    Nonempty (Ensemble (measuredState j)) := by
  let e := Classical.choice (graph_ensemble_nonempty (Gk k) (Gk_edge_nonempty (by omega)))
  exact ⟨conditionalEnsemble e (fun b => ((pairEquiv k).symm b).1) j (branchProb j) (branchProb_pos hk j)
    (measuredState j) (measured_trace hk j) (measured_average hk j)⟩
private theorem family_lower {k : ℕ} (hk : 32 ≤ k) : 499751/16646144 < E_F (sigma (Gk k)) := by
  classical
  have hk2 : 2≤k := by omega
  have hm := selective_formation
    (graph_ensemble_nonempty (Gk k) (Gk_edge_nonempty (by omega))) (fun b => ((pairEquiv k).symm b).1)
    branchProb (fun j => (branchProb_pos hk2 j).le) measuredState
    (measured_trace hk2) (measured_average hk2)
  have heach (j : Fin k) :
      (if j.val=0 then 0 else (7/(8*(k:ℝ)-2))*E_F R) ≤ branchProb j*E_F (measuredState j) := by
    by_cases hj : j.val=0
    · simp only [hj,↓reduceIte]
      exact mul_nonneg (branchProb_pos hk2 j).le (formation_nonneg _ (measured_ensemble hk2 j))
    · have he : Nonempty (Ensemble (embedState j R)) := by
        rw [← measured_nonhub hk2 j hj]; exact measured_ensemble hk2 j
      have hh := embedded_formation_lower j R he
      rw [← measured_nonhub hk2 j hj] at hh
      simpa [branchProb,hj] using mul_le_mul_of_nonneg_left hh (branchProb_pos hk2 j).le
  have hsum : (∑ j : Fin k, if j.val=0 then (0:ℝ) else (7/(8*(k:ℝ)-2))*E_F R)=
      (7*((k:ℝ)-1)/(8*(k:ℝ)-2))*E_F R := by
    have hterm (j : Fin k) : (if j.val=0 then (0:ℝ) else (7/(8*(k:ℝ)-2))*E_F R)=
        (7/(8*(k:ℝ)-2))*E_F R-(if j=⟨0,by omega⟩ then (7/(8*(k:ℝ)-2))*E_F R else 0) := by
      simp only [Fin.ext_iff]
      split_ifs <;> ring
    simp_rw [hterm]
    simp [Finset.sum_sub_distrib]
    ring
  have hp : 0 ≤ 7*((k:ℝ)-1)/(8*(k:ℝ)-2) := by
    have hkR : 32≤(k:ℝ) := by exact_mod_cast hk
    exact div_nonneg (by linarith) (by linarith)
  have hl := mul_le_mul_of_nonneg_left D5.S3.Quantum.Entanglement.GraphDensity.BraunsteinGhoshSeveriniStarRefutation.Witness.R_lower hp
  have ha : (∑ j : Fin k, if j.val=0 then (0:ℝ) else (7/(8*(k:ℝ)-2))*E_F R) ≤
      ∑ j : Fin k, branchProb j*E_F (measuredState j) :=
    Finset.sum_le_sum (fun j _ => heach j)
  rw [hsum] at ha
  exact (D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic.lower_rational hk).trans_le (hl.trans (ha.trans hm))

end D5.S3.Quantum.Entanglement.GraphDensity.BraunsteinGhoshSeveriniStarRefutation

namespace D5.S3.Quantum.Entanglement.GraphDensity.BraunsteinGhoshSeveriniStarRefutation.Star
open D5.S3.Quantum.Entanglement.GraphDensity.BraunsteinGhoshSeveriniStarRefutation D5.S3.Quantum.Entanglement.GraphDensity.BraunsteinGhoshSeveriniStarRefutation.Witness D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Witness
private def normalize {q : ℕ} (ψ : ((Fin 2 × Fin q) → ℂ)) : ((Fin 2 × Fin q) → ℂ) :=
  (NormedSpace.normalize (WithLp.toLp 2 ψ : EuclideanSpace ℂ (Fin 2 × Fin q))).ofLp
private theorem normalize_unit {q : ℕ} (ψ : ((Fin 2 × Fin q) → ℂ)) (hp : 0<(∑ x, ‖ψ x‖^2)) :
    ∑ x, ‖normalize ψ x‖^2=1 := by
  have hnz : (WithLp.toLp 2 ψ : EuclideanSpace ℂ (Fin 2 × Fin q)) ≠ 0 := by
    intro hz
    have hnorm : ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Fin 2 × Fin q))‖^2 = 0 := by
      rw [hz]
      simp
    have hzero : (∑ x, ‖ψ x‖^2) = 0 := by
      simpa [EuclideanSpace.norm_sq_eq] using hnorm
    linarith
  have hn := NormedSpace.norm_normalize hnz
  have hs := EuclideanSpace.norm_sq_eq
    (NormedSpace.normalize (WithLp.toLp 2 ψ : EuclideanSpace ℂ (Fin 2 × Fin q)))
  simpa only [normalize, hn, one_pow] using hs.symm

private theorem normalize_outer {q : ℕ} (ψ : ((Fin 2 × Fin q) → ℂ)) (hp : 0<(∑ x, ‖ψ x‖^2)) :
    rankOneDensity (normalize ψ) = ((1/(∑ x, ‖ψ x‖^2):ℝ):ℂ) • rankOneDensity ψ := by
  have normalization : normalize ψ = ((((1/Real.sqrt (∑ x, ‖ψ x‖^2)) : ℝ) : ℂ) • ψ) := by
    simp only [normalize, NormedSpace.normalize, EuclideanSpace.norm_eq, WithLp.ofLp_smul, one_div]
    rfl
  rw [normalization]
  have he : (1/Real.sqrt ((∑ x, ‖ψ x‖^2)))^2=1/(∑ x, ‖ψ x‖^2) := by
    rw [div_pow,one_pow,Real.sq_sqrt hp.le]
  have hec := congrArg Complex.ofReal he
  push_cast at hec
  ext x y
  simp [normalize,rankOneDensity,Matrix.vecMulVec_apply,Matrix.smul_apply,Pi.smul_apply,
    smul_eq_mul,map_mul,map_div₀]
  calc
    _ = (1/(Real.sqrt ((∑ x, ‖ψ x‖^2)):ℂ))^2*(ψ x*star (ψ y)) := by
      rw [Complex.star_def]; ring
    _ = _ := by rw [hec]; simp [Complex.star_def]
private def rawU (m : ℕ) : ((Fin 2 × Fin (m+1)) → ℂ) := fun x =>
  if x=(0,0) then (2*(m:ℝ)+1:ℝ) else -1
private def rawT (m : ℕ) : ((Fin 2 × Fin (m+1)) → ℂ) := fun x =>
  if x.2=0 then 0 else if x.1=0 then 1 else -1
private def rawZ (m : ℕ) : ((Fin 2 × Fin (m+1)) → ℂ) := fun x =>
  if x.2=0 then (if x.1=0 then 0 else (-2*(m:ℝ):ℝ)) else 1
private def rawP (m : ℕ) (a : Fin 2) (b : Fin m) : ((Fin 2 × Fin (m+1)) → ℂ) := fun x =>
  if x.1=a ∧ x.2≠0 then ((if x.2=b.succ then 1 else 0)-(1/(m:ℝ):ℝ)) else 0
private theorem rawU_mass (m : ℕ) : (∑ x, ‖(rawU m) x‖^2)=2*((m:ℝ)+1)*(2*(m:ℝ)+1) := by
  simp_rw [← Complex.normSq_eq_norm_sq]
  simp [rawU,Fintype.sum_prod_type,Fin.sum_univ_two,Fin.sum_univ_succ,Complex.normSq_apply]
  ring
private theorem rawT_mass (m : ℕ) : (∑ x, ‖(rawT m) x‖^2)=2*(m:ℝ) := by
  simp_rw [← Complex.normSq_eq_norm_sq]
  simp [rawT,Fintype.sum_prod_type,Fin.sum_univ_two,Fin.sum_univ_succ]
  ring
private theorem rawZ_mass (m : ℕ) : (∑ x, ‖(rawZ m) x‖^2)=2*(m:ℝ)*(2*(m:ℝ)+1) := by
  simp_rw [← Complex.normSq_eq_norm_sq]
  simp [rawZ,Fintype.sum_prod_type,Fin.sum_univ_two,Fin.sum_univ_succ,Complex.normSq_apply]
  ring
private theorem rawP_mass {m : ℕ} (hm : 0 < m) (a : Fin 2) (b : Fin m) :
    (∑ x, ‖(rawP m a b) x‖^2)=((m:ℝ)-1)/(m:ℝ) := by
  classical
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hid : (∑ c : Fin m, ((if c=b then (1:ℝ) else 0)-1/(m:ℝ))^2) =
      (1-1/(m:ℝ))^2-1/(m:ℝ)^2+(m:ℝ)*(1/(m:ℝ))^2 := by
    calc
      _ = ∑ c : Fin m, ((if c=b then (1-1/(m:ℝ))^2-(1/(m:ℝ))^2 else 0)+(1/(m:ℝ))^2) := by
        apply Finset.sum_congr rfl
        intro c _
        split_ifs <;> ring
      _ = _ := by simp [Finset.sum_add_distrib]
  have hnorm : (∑ x, ‖(rawP m a b) x‖^2)=∑ c : Fin m, ((if c=b then (1:ℝ) else 0)-1/(m:ℝ))^2 := by
    simp_rw [← Complex.normSq_eq_norm_sq]
    fin_cases a <;>
      simp [rawP,Fintype.sum_prod_type,Fin.sum_univ_two,Fin.sum_univ_succ,
        Complex.normSq_apply,apply_ite,pow_two]
  rw [hnorm,hid]
  field_simp
  ring
private theorem root_zero {m : ℕ} (x : (Fin 2 × Fin (m+1))) : root x ↔ x=(0,0) := by
  simp [root,Prod.ext_iff]
private theorem star_degree {m : ℕ} (x : (Fin 2 × Fin (m+1))) :
    (starGraph 2 (m+1)).degree x=if x=(0,0) then 2*m+1 else 1 := by
  classical
  have heq : starGraph 2 (m+1) = SimpleGraph.starGraph (0,0) := by
    simp [starGraph]
  rw [heq]
  simp only [SimpleGraph.degree, SimpleGraph.neighborFinset,
    Set.toFinset_card, Fintype.card_eq_nat_card]
  by_cases hx : x=(0,0)
  · have hd := SimpleGraph.degree_starGraph_center (r := ((0,0) : Fin 2 × Fin (m+1)))
    simp only [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.toFinset_card,
      Fintype.card_eq_nat_card, Nat.card_prod, Nat.card_fin] at hd
    rw [hx, hd]
    simp
    omega
  · have hd := SimpleGraph.degree_starGraph_of_ne_center hx
    simp only [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.toFinset_card,
      Fintype.card_eq_nat_card] at hd
    rw [hd, if_neg hx]
private theorem star_degreeSum (m : ℕ) : degreeSum (starGraph 2 (m+1))=4*m+2 := by
  classical
  unfold degreeSum
  simp_rw [star_degree]
  have hterm (x : (Fin 2 × Fin (m+1))) :
      (if x=(0,0) then 2*m+1 else 1)=(if x=(0,0) then 2*m else 0)+1 := by
    split_ifs <;> omega
  simp_rw [hterm]
  simp [Finset.sum_add_distrib,Fintype.card_prod]
  omega
private theorem frame_entry {m : ℕ} (hm : 0 < m) (c d : Fin m) :
    (∑ b : Fin m, ((if c=b then (1:ℂ) else 0)-1/(m:ℂ))*
      ((if d=b then (1:ℂ) else 0)-1/(m:ℂ))) =
      (if c=d then 1 else 0)-1/(m:ℂ) := by
  classical
  have hmC : (m:ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hterm (b : Fin m) :
      ((if c=b then (1:ℂ) else 0)-1/(m:ℂ))*((if d=b then (1:ℂ) else 0)-1/(m:ℂ)) =
      (if b=c ∧ b=d then 1 else 0)-
      (if b=c then 1/(m:ℂ) else 0)-(if b=d then 1/(m:ℂ) else 0)+1/(m:ℂ)^2 := by
    by_cases hc : c=b
    · subst c
      by_cases hd : d=b
      · subst d; simp; ring
      · have hbd : b≠d := Ne.symm hd
        simp [hd,hbd]; ring
    · have hbc : b≠c := Ne.symm hc
      by_cases hd : d=b
      · subst d; simp [hc,hbc]; ring
      · have hbd : b≠d := Ne.symm hd
        simp [hc,hbc,hd,hbd]; ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib]
  have hcd : (∑ b : Fin m, if b=c ∧ b=d then (1:ℂ) else 0)=if c=d then 1 else 0 := by
    by_cases he : c=d
    · simp [he]
    · have hh (b : Fin m) : ¬(b=c ∧ b=d) := by intro h; exact he (h.1.symm.trans h.2)
      simp [hh,he]
  rw [hcd]
  simp
  field_simp
  ring
private theorem product_frame {m : ℕ} (hm : 0 < m) (x y : (Fin 2 × Fin (m+1))) :
    (∑ a : Fin 2, ∑ b : Fin m, rankOneDensity (rawP m a b)) x y =
      if x.1=y.1 ∧ x.2≠0 ∧ y.2≠0 then
        (if x.2=y.2 then 1 else 0)-1/(m:ℂ) else 0 := by
  classical
  rcases x with ⟨a,c⟩
  rcases y with ⟨d,e⟩
  fin_cases a <;> fin_cases d <;> cases c using Fin.cases <;> cases e using Fin.cases
  all_goals simp [Matrix.sum_apply,rankOneDensity,Matrix.vecMulVec_apply,rawP,Fin.sum_univ_two,
    Complex.star_def,map_sub,map_div₀,frame_entry hm,Complex.ofReal_natCast,Complex.ofReal_div]
  all_goals simpa only [one_div] using frame_entry hm _ _
private theorem star_sigma_entry (m : ℕ) (x y : (Fin 2 × Fin (m+1))) :
    sigma (starGraph 2 (m+1)) x y =
      (1/(2*(2*(m:ℂ)+1))) *
        ((if x=y then (if x=(0,0) then 2*(m:ℂ)+1 else 1) else 0)-
          (if x≠y ∧ (x=(0,0) ∨ y=(0,0)) then 1 else 0)) := by
  classical
  have ha : (starGraph 2 (m+1)).Adj x y ↔ x≠y ∧ (x=(0,0) ∨ y=(0,0)) := by
    rw [starGraph_adj]
    rw [root_zero,root_zero]
  change (((1/(degreeSum (starGraph 2 (m+1)):ℝ)):ℝ):ℂ)*
    (starGraph 2 (m+1)).lapMatrix ℂ x y = _
  rw [star_degreeSum]
  simp only [SimpleGraph.lapMatrix,SimpleGraph.degMatrix,SimpleGraph.adjMatrix,
    Matrix.diagonal_apply,Matrix.sub_apply,Matrix.of_apply,star_degree,ha]
  split_ifs <;> push_cast <;> ring
private theorem star_raw_reconstruction {m : ℕ} (hm : 0 < m) :
    ((1/(2*(2*(m:ℝ)+1)^2):ℝ):ℂ) • rankOneDensity (rawU m) +
    ((1/(4*(m:ℝ)*(2*(m:ℝ)+1)):ℝ):ℂ) • rankOneDensity (rawT m) +
    ((1/(4*(m:ℝ)*(2*(m:ℝ)+1)^2):ℝ):ℂ) • rankOneDensity (rawZ m) +
    ((1/(2*(2*(m:ℝ)+1)):ℝ):ℂ) • (∑ a : Fin 2, ∑ b : Fin m, rankOneDensity (rawP m a b)) =
    sigma (starGraph 2 (m+1)) := by
  classical
  have hmR : 0<(m:ℝ) := by exact_mod_cast hm
  have hmC : (m:ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hdC : 2*(m:ℂ)+1 ≠ 0 := by
    have hh : (2*(m:ℝ)+1) ≠ 0 := by positivity
    exact_mod_cast hh
  have hz (b : Fin m) : (0:Fin (m+1))≠b.succ := (Fin.succ_ne_zero b).symm
  ext ⟨a,c⟩ ⟨d,e⟩
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,product_frame hm,star_sigma_entry]
  fin_cases a <;> fin_cases d <;> cases c using Fin.cases <;> cases e using Fin.cases
  all_goals simp [rankOneDensity,Matrix.vecMulVec_apply,rawU,rawT,rawZ,Complex.star_def,
    map_div₀,map_sub,Prod.ext_iff,hz]
  all_goals try split_ifs
  all_goals try simp_all only [hz,Fin.succ_ne_zero]
  all_goals push_cast
  all_goals field_simp [hmC,hdC]
  all_goals ring
private theorem rawU_marginal (m : ℕ) :
    partialTraceRight (rankOneDensity (rawU m)) =
      Matrix.of (fun a c => (((!![(2*(m:ℝ)+1)^2+(m:ℝ), -(m:ℝ)-1;
         -(m:ℝ)-1, (m:ℝ)+1] : Matrix (Fin 2) (Fin 2) ℝ) a c):ℂ)) := by
  ext a c
  fin_cases a <;> fin_cases c <;>
    simp [partialTraceRight,D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
      rankOneDensity,Matrix.vecMulVec_apply,rawU,Fin.sum_univ_succ,Complex.star_def] <;>
    push_cast <;> (try simp only [starRingEnd_apply,star_ofNat]) <;> ring
private theorem normalize_marginal {q : ℕ} (ψ : ((Fin 2 × Fin q) → ℂ)) (hp : 0<(∑ x, ‖ψ x‖^2)) :
    partialTraceRight (rankOneDensity (normalize ψ))=((1/(∑ x, ‖ψ x‖^2):ℝ):ℂ) • partialTraceRight (rankOneDensity ψ) := by
  rw [normalize_outer ψ hp]
  ext a c
  simp [partialTraceRight,D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
    Matrix.smul_apply,Finset.mul_sum]
private theorem normalizedU_det {m : ℕ} (hm : 0 < m) :
    (partialTraceRight (rankOneDensity (normalize (rawU m)))).det.re = (m:ℝ)/(2*(m:ℝ)+1)^2 := by
  have hmR : 0<(m:ℝ) := by exact_mod_cast hm
  have hp : 0<(∑ x, ‖(rawU m) x‖^2) := by rw [rawU_mass]; positivity
  rw [normalize_marginal _ hp,rawU_marginal,rawU_mass]
  simp only [Matrix.det_fin_two,Matrix.smul_apply,smul_eq_mul,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons,
    ← Complex.ofReal_mul,← Complex.ofReal_sub,Complex.ofReal_re]
  field_simp
  ring
private def cStar (m : ℕ) : ℝ := 2*Real.sqrt (m:ℝ)/(2*(m:ℝ)+1)
private theorem normalizedU_entropy {m : ℕ} (hm : 0 < m) :
    S (partialTraceRight (rankOneDensity (normalize (rawU m))))=D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic.f (cStar m) := by
  have hmR : 0<(m:ℝ) := by exact_mod_cast hm
  have hp : 0<(∑ x, ‖(rawU m) x‖^2) := by rw [rawU_mass]; positivity
  have hunit := normalize_unit (rawU m) hp
  have ht : (partialTraceRight (rankOneDensity (normalize (rawU m)))).trace=1 := by
    rw [marginal_trace,hunit]; norm_num
  have hf := qubit_entropy_det (partialTraceRight (rankOneDensity (normalize (rawU m))))
    (D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight_posSemidef
      (Matrix.posSemidef_vecMulVec_self_star (normalize (rawU m)))) ht
  rw [hf,normalizedU_det hm]
  unfold D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic.f cStar
  congr 3
  rw [div_pow,mul_pow,Real.sq_sqrt hmR.le]
  ring
private theorem cStar_sq {m : ℕ} (hm : 0 < m) : (cStar m)^2 ≤ 1/((m:ℝ)+1) := by
  have hmR : 0<(m:ℝ) := by exact_mod_cast hm
  unfold cStar
  rw [div_pow,mul_pow,Real.sq_sqrt hmR.le]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith
private theorem normalizedU_entropy_bound {m : ℕ} (hm : 63 ≤ m) :
    S (partialTraceRight (rankOneDensity (normalize (rawU m))))<1/25 := by
  have hpos : 0 < m := by omega
  have hmR : 63≤(m:ℝ) := by exact_mod_cast hm
  rw [normalizedU_entropy hpos]
  apply D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic.star_root_upper (by unfold cStar; positivity)
  exact (cStar_sq hpos).trans (by rw [div_le_iff₀ (by positivity)]; linarith)
private theorem single_row_entropy {q : ℕ} (ψ : ((Fin 2 × Fin q) → ℂ)) (a : Fin 2)
    (hunit : ∑ x, ‖ψ x‖^2=1) (hs : ∀ x, x.1≠a → ψ x=0) :
    S (partialTraceRight (rankOneDensity ψ))=0 := by
  have hdet : (partialTraceRight (rankOneDensity ψ)).det=0 := by
    fin_cases a
    · have hz (b : Fin q) : ψ (1,b)=0 := hs (1,b) (by simp)
      simp [Matrix.det_fin_two,partialTraceRight,
        D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
        rankOneDensity,Matrix.vecMulVec_apply,hz]
    · have hz (b : Fin q) : ψ (0,b)=0 := hs (0,b) (by simp)
      simp [Matrix.det_fin_two,partialTraceRight,
        D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
        rankOneDensity,Matrix.vecMulVec_apply,hz]
  have ht : (partialTraceRight (rankOneDensity ψ)).trace=1 := by rw [marginal_trace,hunit]; norm_num
  have hf := qubit_entropy_det (partialTraceRight (rankOneDensity ψ))
    (D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight_posSemidef
      (Matrix.posSemidef_vecMulVec_self_star ψ)) ht
  rw [hf,hdet]
  norm_num [D5.S3.Quantum.CloningMachine.binaryEntropyBits, Real.logb]
private theorem normalizedP_entropy {m : ℕ} (hm : 2 ≤ m) (a : Fin 2) (b : Fin m) :
    S (partialTraceRight (rankOneDensity (normalize (rawP m a b))))=0 := by
  have hmR : 2≤(m:ℝ) := by exact_mod_cast hm
  have hp : 0<(∑ x, ‖(rawP m a b) x‖^2) := by rw [rawP_mass (by omega)]; exact div_pos (by linarith) (by linarith)
  apply single_row_entropy _ a (normalize_unit _ hp)
  intro x hx
  simp [normalize, NormedSpace.normalize, WithLp.ofLp_smul,rawP,hx]
private def starPsi (m : ℕ) : (Fin 3 ⊕ (Fin 2 × Fin m)) → ((Fin 2 × Fin (m+1)) → ℂ) :=
  Sum.elim (fun i => normalize (![rawU m,rawT m,rawZ m] i))
    (fun ab => normalize (rawP m ab.1 ab.2))
private def starWeight (m : ℕ) : (Fin 3 ⊕ (Fin 2 × Fin m)) → ℝ :=
  Sum.elim (fun i => ![((m:ℝ)+1)/(2*(m:ℝ)+1),
    1/(2*(2*(m:ℝ)+1)),1/(2*(2*(m:ℝ)+1))] i)
    (fun _ => ((m:ℝ)-1)/((m:ℝ)*2*(2*(m:ℝ)+1)))
private theorem starWeight_nonneg {m : ℕ} (hm : 2 ≤ m) (i : (Fin 3 ⊕ (Fin 2 × Fin m))) : 0 ≤ starWeight m i := by
  have hmR : 2≤(m:ℝ) := by exact_mod_cast hm
  rcases i with i | ⟨a,b⟩
  · fin_cases i <;> simp [starWeight] <;> positivity
  · change 0 ≤ ((m:ℝ)-1)/((m:ℝ)*2*(2*(m:ℝ)+1))
    exact div_nonneg (by linarith) (by positivity)
private theorem starWeight_total {m : ℕ} (hm : 2 ≤ m) : ∑ i, starWeight m i=1 := by
  have hmR : 2≤(m:ℝ) := by exact_mod_cast hm
  simp [starWeight,Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_three]
  field_simp
  ring
private theorem starPsi_unit {m : ℕ} (hm : 2 ≤ m) (i : (Fin 3 ⊕ (Fin 2 × Fin m))) :
    ∑ x, ‖starPsi m i x‖^2=1 := by
  have hmR : 2≤(m:ℝ) := by exact_mod_cast hm
  rcases i with i | ⟨a,b⟩
  · fin_cases i
    · change ∑ x, ‖normalize (rawU m) x‖^2=1
      apply normalize_unit
      rw [rawU_mass]; positivity
    · change ∑ x, ‖normalize (rawT m) x‖^2=1
      apply normalize_unit
      rw [rawT_mass]; positivity
    · change ∑ x, ‖normalize (rawZ m) x‖^2=1
      apply normalize_unit
      rw [rawZ_mass]; positivity
  · apply normalize_unit
    rw [rawP_mass (by omega)]; exact div_pos (by linarith) (by linarith)
private theorem star_ensemble_average {m : ℕ} (hm : 2 ≤ m) :
    ∑ i, (starWeight m i:ℂ) • rankOneDensity (starPsi m i) = sigma (starGraph 2 (m+1)) := by
  have hmR : 2≤(m:ℝ) := by exact_mod_cast hm
  have hpU : 0<(∑ x, ‖(rawU m) x‖^2) := by rw [rawU_mass]; positivity
  have hpT : 0<(∑ x, ‖(rawT m) x‖^2) := by rw [rawT_mass]; positivity
  have hpZ : 0<(∑ x, ‖(rawZ m) x‖^2) := by rw [rawZ_mass]; positivity
  have hpP (a : Fin 2) (b : Fin m) : 0<(∑ x, ‖(rawP m a b) x‖^2) := by
    rw [rawP_mass (by omega)]; exact div_pos (by linarith) (by linarith)
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,starPsi,starWeight,
    Sum.elim_inl,Sum.elim_inr,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  simp_rw [normalize_outer _ hpU,normalize_outer _ hpT,normalize_outer _ hpZ,
    normalize_outer _ (hpP _ _),smul_smul,← Complex.ofReal_mul,
    rawU_mass,rawT_mass,rawZ_mass,rawP_mass (by omega : 0 < m)]
  have hU : (((m:ℝ)+1)/(2*(m:ℝ)+1))*(1/(2*((m:ℝ)+1)*(2*(m:ℝ)+1)))=
      1/(2*(2*(m:ℝ)+1)^2) := by field_simp <;> ring
  have hT : (1/(2*(2*(m:ℝ)+1)))*(1/(2*(m:ℝ)))=
      1/(4*(m:ℝ)*(2*(m:ℝ)+1)) := by field_simp <;> ring
  have hZ : (1/(2*(2*(m:ℝ)+1)))*(1/(2*(m:ℝ)*(2*(m:ℝ)+1)))=
      1/(4*(m:ℝ)*(2*(m:ℝ)+1)^2) := by field_simp <;> ring
  have hP : (((m:ℝ)-1)/((m:ℝ)*2*(2*(m:ℝ)+1)))*(1/(((m:ℝ)-1)/(m:ℝ)))=
      1/(2*(2*(m:ℝ)+1)) := by
    have hm0 : (m:ℝ)≠0 := by linarith
    have hm1 : (m:ℝ)-1≠0 := by linarith
    field_simp [hm0,hm1]
  simp_rw [hU,hT,hZ,hP]
  simp_rw [← Finset.smul_sum]
  convert star_raw_reconstruction (by omega : 0 < m) using 1 <;> module
private def starEnsemble {m : ℕ} (hm : 2 ≤ m) : Ensemble (sigma (starGraph 2 (m+1))) := by
  classical
  let e := Fintype.equivFin ((Fin 3 ⊕ (Fin 2 × Fin m)))
  refine {
    N := Fintype.card ((Fin 3 ⊕ (Fin 2 × Fin m)))
    weight := fun i => starWeight m (e.symm i)
    nonneg := fun i => starWeight_nonneg hm _
    le_one := fun i => weight_le_one_of_total
      _ (starWeight_nonneg hm) (starWeight_total hm) (e.symm i)
    total := ?_
    psi := fun i => starPsi m (e.symm i)
    unit := fun i => starPsi_unit hm _
    average := ?_
  }
  · rw [Equiv.sum_comp e.symm]; exact starWeight_total hm
  · exact (Equiv.sum_comp e.symm (fun i => (starWeight m i:ℂ) • rankOneDensity (starPsi m i))).trans (star_ensemble_average hm)
private theorem starEnsemble_cost {m : ℕ} (hm : 2 ≤ m) :
    ensembleCost (starEnsemble hm)=∑ i, starWeight m i*S (partialTraceRight (rankOneDensity (starPsi m i))) := by
  classical
  change (∑ i, starWeight m ((Fintype.equivFin ((Fin 3 ⊕ (Fin 2 × Fin m)))).symm i)*
    S (partialTraceRight (rankOneDensity (starPsi m ((Fintype.equivFin ((Fin 3 ⊕ (Fin 2 × Fin m)))).symm i)))))=_
  exact Equiv.sum_comp (Fintype.equivFin ((Fin 3 ⊕ (Fin 2 × Fin m)))).symm
    (fun i : (Fin 3 ⊕ (Fin 2 × Fin m)) => starWeight m i * S (partialTraceRight (rankOneDensity (starPsi m i))))
private theorem star_cost_bound {m : ℕ} (hm : 2 ≤ m) :
    ensembleCost (starEnsemble hm) ≤
      (((m:ℝ)+1)/(2*(m:ℝ)+1))*D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic.f (cStar m)+1/(2*(m:ℝ)+1) := by
  have hmR : 2≤(m:ℝ) := by exact_mod_cast hm
  have hunitT : ∑ x, ‖normalize (rawT m) x‖^2=1 :=
    normalize_unit _ (by rw [rawT_mass]; positivity)
  have hunitZ : ∑ x, ‖normalize (rawZ m) x‖^2=1 :=
    normalize_unit _ (by rw [rawZ_mass]; positivity)
  rw [starEnsemble_cost]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,starWeight,starPsi,
    Sum.elim_inl,Sum.elim_inr,Fin.sum_univ_three,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  simp_rw [normalizedP_entropy hm]
  simp only [mul_zero,Finset.sum_const_zero,add_zero,normalizedU_entropy (by omega : 0 < m)]
  have hT := pure_qubit_le_one (normalize (rawT m)) hunitT
  have hZ := pure_qubit_le_one (normalize (rawZ m)) hunitZ
  have hp : 0 ≤ 1/(2*(2*(m:ℝ)+1)) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hT hp
  have h2 := mul_le_mul_of_nonneg_left hZ hp
  have he : 1/(2*(2*(m:ℝ)+1))+1/(2*(2*(m:ℝ)+1))=1/(2*(m:ℝ)+1) := by
    field_simp
    <;> ring
  linarith
private theorem star_upper {m : ℕ} (hm : 63 ≤ m) : E_F (sigma (starGraph 2 (m+1))) < 89/3175 := by
  have hmR : 63≤(m:ℝ) := by exact_mod_cast hm
  have hc := star_cost_bound (by omega : 2 ≤ m)
  have hu := normalizedU_entropy_bound hm
  rw [normalizedU_entropy (by omega)] at hu
  have hp : 0<((m:ℝ)+1)/(2*(m:ℝ)+1) := by positivity
  have hr := D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic.upper_rational (q := m+1) (by omega : 64 ≤ m+1)
  push_cast at hr
  have hmul := mul_lt_mul_of_pos_left hu hp
  have he : (((m:ℝ)+1)/(2*(m:ℝ)+1))*(1/25)+1/(2*(m:ℝ)+1)=
      (((m:ℝ)+1)/25+1)/(2*((m:ℝ)+1)-1) := by ring
  have hf := formation_le_cost (starEnsemble (by omega : 2 ≤ m))
  rw [← he] at hr
  linarith

end D5.S3.Quantum.Entanglement.GraphDensity.BraunsteinGhoshSeveriniStarRefutation.Star

namespace D5.S3.Quantum.Entanglement.GraphDensity.BraunsteinGhoshSeveriniStarRefutation
open D5.S3.Quantum.Entanglement.GraphDensity.BraunsteinGhoshSeveriniStarRefutation.Witness D5.S3.Quantum.Entanglement.GraphDensity.BraunsteinGhoshSeveriniStarRefutation.Star D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Witness
theorem family (k : ℕ) (hk : 32 ≤ k) :
    E_F (sigma (Gk k)) > 499751/16646144 ∧
    E_F (sigma (starGraph 2 (2*k))) < 89/3175 := by
  refine ⟨family_lower hk,?_⟩
  have hm : 63 ≤ 2*k-1 := by omega
  have hn : (2*k-1)+1=2*k := by omega
  rw [← hn]
  exact D5.S3.Quantum.Entanglement.GraphDensity.BraunsteinGhoshSeveriniStarRefutation.Star.star_upper hm

theorem result : ¬ claim := by
  intro hc
  have hl := (family 32 (by norm_num)).1
  have hu := (family 32 (by norm_num)).2
  have hclaim := hc 2 64 (Gk 32) (Gk_connected (by norm_num)) (Gk_edge_nonempty (by norm_num))
  norm_num at hclaim hl hu
  linarith

end D5.S3.Quantum.Entanglement.GraphDensity.BraunsteinGhoshSeveriniStarRefutation
