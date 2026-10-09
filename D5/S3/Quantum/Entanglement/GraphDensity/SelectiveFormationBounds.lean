/- GID: D5/S3/Quantum/Entanglement/GraphDensity/SelectiveFormationBounds
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/GraphDensity/SelectiveFormationBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coordinate-block embedding and formation lower bounds. -/

/-
proof_shape: SelectiveFormationBounds.zero_diagonal_ensemble_support: bind-only; consumer SelectiveFormationBounds.ensemble_block_support
proof_shape: SelectiveFormationBounds.pairEquiv_val: bind-only; consumer BraunsteinGhoshSeveriniStarRefutation.adj_local
proof_shape: SelectiveFormationBounds.unpair_slot: bind-only; consumer SelectiveFormationBounds.compressEnsemble
proof_shape: SelectiveFormationBounds.embedVec_norm: bind-only; consumer SelectiveFormationBounds.compress_unit
proof_shape: SelectiveFormationBounds.embedVec_outer: bind-only; consumer SelectiveFormationBounds.embedVec_marginal
proof_shape: SelectiveFormationBounds.embedVec_marginal: bind-only; consumer SelectiveFormationBounds.compress_marginal
proof_shape: SelectiveFormationBounds.embed_compress_supported: bind-only; consumer SelectiveFormationBounds.compress_unit, SelectiveFormationBounds.compress_marginal
proof_shape: SelectiveFormationBounds.ensemble_block_support: bind-only; consumer SelectiveFormationBounds.compress_unit, SelectiveFormationBounds.compress_marginal
proof_shape: SelectiveFormationBounds.compress_unit: bind-only; consumer SelectiveFormationBounds.compressEnsemble
proof_shape: SelectiveFormationBounds.compress_marginal: bind-only; consumer SelectiveFormationBounds.compress_cost
proof_shape: SelectiveFormationBounds.compress_cost: bind-only; consumer SelectiveFormationBounds.embedded_formation_lower
proof_shape: SelectiveFormationBounds.embedded_formation_lower: content; consumer BraunsteinGhoshSeveriniStarRefutation.family_lower
escape_witness: D5.S3.Quantum.Entanglement.GraphDensity.SelectiveFormationBounds.embedded_formation_lower; compressEnsemble constructs an ensemble of the
original state from an arbitrary ensemble of its coordinate embedding, preserving its cost.
The lower bound is consumed by BraunsteinGhoshSeveriniStarRefutation.family_lower.
admission_basis: escape-witness
Direct frozen dependencies (declaration statement_id):
  D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.ensemble_kernel
    sha256:fec418675286733bd12e43ceb3ba94c5bc1bc272f135d8832da0cde24ff11a87
  D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity
    sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight
    sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77
  D5/S3/Quantum/Information/PartialTraceMutualInformation.trace_partialTraceRight
    sha256:2e0d10f59a41befee8bb5e380b1d8d7db7e14a2bbed6d47af5089807c0905813
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight_posSemidef
    sha256:534be990ab7c643fd18c2a086aa7a7b696bb02a8baa49a26c15e479b63e74944
Supporting modules in this delivery are not baseline-frozen prerequisites.
Information-escape registration is paused under CLAUDE.md §3.9 「信息逃逸登记暂缓」.
-/

import D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction
import D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Set Matrix
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight partialTraceLeft)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation (partialTransposeB)
open D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Witness
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.Entanglement.GraphDensity.SelectiveFormationBounds
open D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Analytic D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Witness
private theorem zero_diagonal_ensemble_support {p q : ℕ} {ρ : (Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ)} (e : Ensemble ρ)
    (x : (Fin p × Fin q)) (hx : ρ x x=0) (i : Fin e.N) (hi : 0 < e.weight i) : e.psi i x=0 := by
  have hzero : star (Pi.single x (1 : ℂ)) ⬝ᵥ
      ((∑ j, e.weight j • rankOneDensity (e.psi j)) *ᵥ Pi.single x (1 : ℂ)) = 0 := by
    have hav : (∑ j, e.weight j • rankOneDensity (e.psi j)) = ρ := by
      ext a b
      have hh := congrArg (fun M => M a b) e.average
      simpa [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul] using hh
    rw [hav]
    simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using hx
  have hz := D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.ensemble_kernel
    e.psi e.weight e.nonneg (Pi.single x (1 : ℂ)) hzero i hi
  simpa [dotProduct, Pi.single_apply] using hz

def pairEquiv (k : ℕ) : Fin k × Fin 2 ≃ Fin (2*k) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm k 2))



@[simp] theorem pairEquiv_val {k : ℕ} (j : Fin k) (b : Fin 2) :
    (pairEquiv k (j, b)).val=b.val+2*j.val := rfl

@[simp] private theorem unpair_slot {k : ℕ} (j : Fin k) (b : Fin 2) :
    (pairEquiv k).symm (pairEquiv k (j, b))=(j,b) := (pairEquiv k).symm_apply_apply _

private def embedVec {k : ℕ} (j : Fin k) (ψ : ((Fin 2 × Fin 2) → ℂ)) : ((Fin 2 × Fin (2*k)) → ℂ) :=
  Set.indicator {x | ((pairEquiv k).symm x.2).1=j}
    (ψ ∘ Prod.map id (fun b => ((pairEquiv k).symm b).2))

def embedState {k : ℕ} (j : Fin k) (ρ : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) : (Matrix (Fin 2 × Fin (2*k)) (Fin 2 × Fin (2*k)) ℂ) :=
  Function.curry (Set.indicator
    {xy | ((pairEquiv k).symm xy.1.2).1=j ∧ ((pairEquiv k).symm xy.2.2).1=j}
    (Function.uncurry (ρ.submatrix
      (Prod.map id (fun b => ((pairEquiv k).symm b).2))
      (Prod.map id (fun b => ((pairEquiv k).symm b).2)))))

private def compressVec {k : ℕ} (j : Fin k) (ψ : ((Fin 2 × Fin (2*k)) → ℂ)) : ((Fin 2 × Fin 2) → ℂ) :=
  ψ ∘ Prod.map id (fun b => pairEquiv k (j,b))

private theorem embedVec_norm {k : ℕ} (j : Fin k) (ψ : ((Fin 2 × Fin 2) → ℂ)) :
    ∑ x, ‖embedVec j ψ x‖^2 = ∑ x, ‖ψ x‖^2 := by
  classical
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [← (pairEquiv k).sum_comp]
  simp only [Fintype.sum_prod_type,embedVec,Equiv.symm_apply_apply,Set.indicator,Function.curry,Function.uncurry,Set.mem_ofPred_eq,Prod.map,Function.comp_apply,id_eq,Matrix.submatrix_apply]
  rw [Finset.sum_comm]
  simp [apply_ite]

private theorem embedVec_outer {k : ℕ} (j : Fin k) (ψ : ((Fin 2 × Fin 2) → ℂ)) :
    rankOneDensity (embedVec j ψ)=embedState j (rankOneDensity ψ) := by
  ext x y
  simp only [rankOneDensity,Matrix.vecMulVec_apply,Pi.star_apply,embedVec,embedState,Set.indicator,Function.curry,Function.uncurry,Set.mem_ofPred_eq,Prod.map,Function.comp_apply,id_eq,Matrix.submatrix_apply]
  split_ifs <;> simp_all

private theorem embedVec_marginal {k : ℕ} (j : Fin k) (ψ : ((Fin 2 × Fin 2) → ℂ)) :
    partialTraceRight (rankOneDensity (embedVec j ψ))=partialTraceRight (rankOneDensity ψ) := by
  classical
  rw [embedVec_outer]
  ext a a'
  simp only [partialTraceRight,D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight]
  rw [← (pairEquiv k).sum_comp]
  simp only [Fintype.sum_prod_type,embedState,Equiv.symm_apply_apply,Set.indicator,Function.curry,Function.uncurry,Set.mem_ofPred_eq,Prod.map,Function.comp_apply,id_eq,Matrix.submatrix_apply]
  rw [Finset.sum_comm]
  simp

private theorem embed_compress_supported {k : ℕ} (j : Fin k) (ψ : ((Fin 2 × Fin (2*k)) → ℂ))
    (hs : ∀ x, ((pairEquiv k).symm x.2).1 ≠ j → ψ x=0) : embedVec j (compressVec j ψ)=ψ := by
  ext x
  by_cases hx : ((pairEquiv k).symm x.2).1=j
  · simp only [embedVec,hx,↓reduceIte,compressVec,Prod.map,Function.comp_apply,id_eq,Set.indicator,Function.curry,Function.uncurry,Set.mem_ofPred_eq,Prod.map,Function.comp_apply,id_eq,Matrix.submatrix_apply]
    congr 1
    apply Prod.ext
    · rfl
    · change pairEquiv k (j,((pairEquiv k).symm x.2).2)=x.2
      rw [← hx]
      exact (pairEquiv k).apply_symm_apply x.2
  · simp [embedVec,hx,hs x hx,Set.indicator,Function.curry,Function.uncurry,Set.mem_ofPred_eq,Prod.map,Function.comp_apply,id_eq,Matrix.submatrix_apply]

private theorem ensemble_block_support {k : ℕ} (j : Fin k) (ρ : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
    (e : Ensemble (embedState j ρ)) (i : Fin e.N) (hi : 0<e.weight i) :
    ∀ x, ((pairEquiv k).symm x.2).1 ≠ j → e.psi i x=0 := by
  intro x hx
  exact zero_diagonal_ensemble_support e x (by simp [embedState,hx,Set.indicator,Function.curry,Function.uncurry,Set.mem_ofPred_eq,Prod.map,Function.comp_apply,id_eq,Matrix.submatrix_apply]) i hi

private theorem compress_unit {k : ℕ} (j : Fin k) (ρ : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
    (e : Ensemble (embedState j ρ)) (i : Fin e.N) (hi : 0<e.weight i) :
    ∑ x, ‖compressVec j (e.psi i) x‖^2=1 := by
  rw [← embedVec_norm j,embed_compress_supported j _ (ensemble_block_support j ρ e i hi)]
  exact e.unit i

private theorem compress_marginal {k : ℕ} (j : Fin k) (ρ : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
    (e : Ensemble (embedState j ρ)) (i : Fin e.N) (hi : 0<e.weight i) :
    partialTraceRight (rankOneDensity (compressVec j (e.psi i)))=partialTraceRight (rankOneDensity (e.psi i)) := by
  rw [← embedVec_marginal j,embed_compress_supported j _ (ensemble_block_support j ρ e i hi)]

private def compressEnsemble {k : ℕ} (j : Fin k) (ρ : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
    (e : Ensemble (embedState j ρ)) : Ensemble ρ := by
  classical
  refine {
    N := e.N
    weight := e.weight
    nonneg := e.nonneg
    le_one := e.le_one
    total := e.total
    psi := fun i => if e.weight i=0 then (Pi.single (0,0) (1:ℂ)) else compressVec j (e.psi i)
    unit := ?_
    average := ?_
  }
  · intro i
    by_cases hz : e.weight i=0
    · simp only [hz,↓reduceIte]
      simp [Pi.single_apply,Fintype.sum_prod_type,Fin.sum_univ_two]
    · simp only [hz,↓reduceIte]
      exact compress_unit j ρ e i (lt_of_le_of_ne (e.nonneg i) (Ne.symm hz))
  · ext x y
    have hh := congrArg (fun M : (Matrix (Fin 2 × Fin (2*k)) (Fin 2 × Fin (2*k)) ℂ) => M (x.1,pairEquiv k (j, x.2)) (y.1,pairEquiv k (j, y.2))) e.average
    simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,embedState,
      unpair_slot,true_and,↓reduceIte,Set.indicator,Function.curry,Function.uncurry,Set.mem_ofPred_eq,Prod.map,Function.comp_apply,id_eq,Matrix.submatrix_apply] at hh
    simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
    change (∑ i, (e.weight i:ℂ)*rankOneDensity
      (if e.weight i=0 then (Pi.single (0,0) (1:ℂ)) else compressVec j (e.psi i)) x y)=ρ x y
    rw [← hh]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hz : e.weight i=0
    · simp [hz]
    · simp [hz,rankOneDensity,compressVec,Matrix.vecMulVec_apply,Prod.map,Function.comp_apply,id_eq]

private theorem compress_cost {k : ℕ} (j : Fin k) (ρ : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
    (e : Ensemble (embedState j ρ)) : ensembleCost (compressEnsemble j ρ e)=ensembleCost e := by
  classical
  unfold ensembleCost
  apply Finset.sum_congr rfl
  intro i _
  change e.weight i*S (partialTraceRight (rankOneDensity
    (if e.weight i=0 then (Pi.single (0,0) (1:ℂ)) else compressVec j (e.psi i))))=_
  by_cases hz : e.weight i=0
  · simp [hz]
  · simp only [hz,↓reduceIte]
    rw [compress_marginal j ρ e i (lt_of_le_of_ne (e.nonneg i) (Ne.symm hz))]

theorem embedded_formation_lower {k : ℕ} (j : Fin k) (ρ : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
    (he : Nonempty (Ensemble (embedState j ρ))) : E_F ρ ≤ E_F (embedState j ρ) := by
  apply le_csInf ((cost_set_nonempty_iff _).mpr he)
  rintro c ⟨e,rfl⟩
  have hh := formation_le_cost (compressEnsemble j ρ e)
  rwa [compress_cost] at hh

end D5.S3.Quantum.Entanglement.GraphDensity.SelectiveFormationBounds
