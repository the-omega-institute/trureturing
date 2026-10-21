/- GID: D5/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence.claim; result=D5/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence.result; claim=D5/S3/Quantum/QuantumChannels/LogNegativityCapacityResourceDependence.claim
   digest: Separable and assisted log-negativity capacities differ for a two-qutrit CPTP map. -/
/-
admission_basis: open-problem-resolution (#17047; Refuted)
proof_shape: result: bind-only; all private theorems: bind-only, with consumers in the handover table.
escape_witness: none
Direct frozen dependencies (declaration statement_id):
D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.partialTranspose; sha256:2373e14505428583f492752adc05d104ae8b1567265ff8182e03646de824c089
D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.IsDensity; sha256:fc9bb0824d5818ff419f72f26095faecc04e62ab59bf26f4f2bcefbb2d380448
D5/S3/Quantum/Foundation/FiniteKrausChannel.MatrixMap; sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7
D5/S3/Quantum/Foundation/FiniteKrausChannel.of_kraus; sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287
D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm; sha256:12ad034b5758446e6d628c75121b3ad5f0c80bb305937e8c9ff87e82076bc059
D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_nonneg; sha256:7412f30d565d9b30ebbf77bf0f5b93d44fe0082f8be41fd64fea60f00cdf2dfa
D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_of_posSemidef; sha256:4f19dad9c3563d9aba3fa6f97f41f0e49ed46af1457c14f015225ae27d019565
D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft; sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d
D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight; sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77
D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight_posSemidef; sha256:534be990ab7c643fd18c2a086aa7a7b696bb02a8baa49a26c15e479b63e74944
D5/S3/Quantum/Information/PartialTraceMutualInformation.trace_partialTraceRight; sha256:2e0d10f59a41befee8bb5e380b1d8d7db7e14a2bbed6d47af5089807c0905813
D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.columnEmbed; sha256:90be5a8efba6ec28dd555743414d7841200202313bed4d00b015b3f850c82649
D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.psd_rank_sum; sha256:0b6a0bd45673c43d78d4ead13493930e84c4c0fb00fad6bf81c97bba006ff283
D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.weighted_rank; sha256:06a413190a8dda44041fb9923e7011d0ba136c608a253287583a13bba92d626b
D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.weighted_sum; sha256:e148e260feed76665cc04e32767858cca168e6f30d9b9fb5cac3fbd423f3cec9
D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.trace_projector_overlap; sha256:16c22f6afc9e8fb50eb0719207c54acb9fd1b28fea9be941cd590e668e812f8e
D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.reindex_traceNorm; sha256:2422ccb9af655e75065a2ca7f28f6fdcc73bda08849c764524e19f7de31b786b
Escape audit unfinished for the supporting owner theorems: https://github.com/the-omega-institute/trureturing/issues/17573
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
-/
import D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity
import D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound
import D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction
import D5.S3.QuantumChannels.SchurChannelMixedUnitaryDistance
open Matrix
open scoped Kronecker MatrixOrder ComplexOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound (IsDensity)
open D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence (IsSeparable weighted weighted_psd)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
section
namespace D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Gap
variable {I J : Type*} [Fintype I] [Fintype J]
open scoped Matrix.Norms.Frobenius in
private theorem frobenius_mulVec (D : Matrix I J ℂ) (x : J → ℂ) :
    (∑ i, ‖(D *ᵥ x) i‖ ^ 2) ≤ (∑ i, ∑ j, ‖D i j‖ ^ 2) * (∑ i, ‖x i‖ ^ 2) := by
  have h := Matrix.frobenius_norm_mul D (Matrix.replicateCol Unit x)
  have he : D * Matrix.replicateCol Unit x = Matrix.replicateCol Unit (D *ᵥ x) := rfl
  rw [he, Matrix.frobenius_norm_replicateCol, Matrix.frobenius_norm_replicateCol] at h
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hs
  convert hs using 1
  congr 1
  simp only [Matrix.frobenius_norm_def, Real.rpow_two, ← Real.sqrt_eq_rpow]
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)]
variable [DecidableEq I]
private theorem inverse_frame_bound (C D : Matrix I I ℂ) (hDC : D*C=1)
    (hD : (∑ i, ∑ j, ‖D i j‖ ^ 2) ≤ 9) (x : I → ℂ) :
    (∑ i, ‖x i‖ ^ 2) ≤ 9 * (∑ i, ‖(C *ᵥ x) i‖ ^ 2) := by
  have h := frobenius_mulVec D (C *ᵥ x)
  rw [Matrix.mulVec_mulVec, hDC, Matrix.one_mulVec] at h
  exact h.trans (mul_le_mul_of_nonneg_right hD (Finset.sum_nonneg fun i _ => sq_nonneg _))
end D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Gap
end
section
namespace D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Gap
variable {I : Type*} [Fintype I]
private theorem rankOne_trace_product (v z : I → ℂ) :
    (Matrix.trace (Matrix.vecMulVec v (star v) * Matrix.vecMulVec z (star z))).re =
      ‖star v ⬝ᵥ z‖ ^ 2 := by
  have h := congrArg Complex.re
    (D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.trace_projector_overlap v z)
  simpa only [D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq] using h
end D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Gap
end
section
namespace D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Kraus
variable {H O : Type*} [Fintype H] [Fintype O]
  [DecidableEq H] [DecidableEq O]
private theorem ket_gram (v : O → ℂ) (U : Matrix H H ℂ) :
    ∑ k, ((Matrix.vecMulVec v (U k)))ᴴ * (Matrix.vecMulVec v (U k)) =
      (∑ i, star (v i) * v i) • (Uᴴ * U) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  change (∑ k, ∑ a, star (v a * U k i) * (v a * U k j)) =
    (∑ a, star (v a) * v a) * (∑ k, star (U k i) * U k j)
  simp only [star_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro a _
  ring
private theorem ket_action (v : O → ℂ) (U X : Matrix H H ℂ) :
    ∑ k, (Matrix.vecMulVec v (U k)) * X * ((Matrix.vecMulVec v (U k)))ᴴ =
      (U * X * Uᴴ).trace • Matrix.vecMulVec v (star v) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  change (∑ k, ∑ a, (∑ b, (v i * U k b) * X b a) * star (v j * U k a)) =
    (∑ k, ∑ a, (∑ b, U k b * X b a) * star (U k a)) * (v i * star (v j))
  simp only [star_mul]
  try dsimp only [Matrix] at U X ⊢
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring
end D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Kraus
end
section
namespace D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Conditional
variable {A B X Y : Type*} [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
private def conditional (M : Matrix (A × B) (A × B) ℂ)
    (σ : Matrix ((A × X) × (B × Y)) ((A × X) × (B × Y)) ℂ) :
    Matrix (X × Y) (X × Y) ℂ := by
  classical
  exact partialTraceLeft ((M ⊗ₖ (1 : Matrix (X × Y) (X × Y) ℂ)) *
    σ.submatrix (Equiv.prodProdProdComm A B X Y) (Equiv.prodProdProdComm A B X Y))
private theorem conditional_apply (M : Matrix (A × B) (A × B) ℂ)
    (σ : Matrix ((A × X) × (B × Y)) ((A × X) × (B × Y)) ℂ) (i j : X × Y) :
    conditional M σ i j = ∑ a, ∑ b, ∑ c, ∑ d,
      M (c, d) (a, b) * σ ((a, i.1), (b, i.2)) ((c, j.1), (d, j.2)) := by
  classical
  simp only [conditional, partialTraceLeft, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Matrix.submatrix_apply, Equiv.prodProdProdComm_apply]
  conv_lhs => enter [2,c]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  conv_lhs => enter [2,c]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
private theorem conditional_partialTranspose
    (M : Matrix (A × B) (A × B) ℂ)
    (σ : Matrix ((A × X) × (B × Y)) ((A × X) × (B × Y)) ℂ) :
    (fun i j : X × Y => conditional M σ (i.1,j.2) (j.1,i.2)) =
      conditional ((fun i j : A × B => M (i.1,j.2) (j.1,i.2))) ((fun i j : (A × X) × (B × Y) => σ (i.1,j.2) (j.1,i.2))) := by
  ext i j
  rw [conditional_apply, conditional_apply]
  change (∑ a, ∑ b, ∑ c, ∑ d,
    M (c,d) (a,b) * σ ((a,i.1),(b,j.2)) ((c,j.1),(d,i.2))) =
    ∑ a, ∑ b, ∑ c, ∑ d,
    M (c,b) (a,d) * σ ((a,i.1),(d,j.2)) ((c,j.1),(b,i.2))
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.sum_comm]
  calc
    _ = ∑ c, ∑ d, ∑ b,
      M (c,d) (a,b) * σ ((a,i.1),(b,j.2)) ((c,j.1),(d,i.2)) := by
      apply Finset.sum_congr rfl; intro c _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]
variable {H R : Type*} [Fintype H] [Fintype R]
  [DecidableEq H] [DecidableEq R]
private theorem conditionalNatural_apply (M : Matrix H H ℂ)
    (σ : Matrix (H × R) (H × R) ℂ) (i j : R) :
    (fun M σ => partialTraceLeft ((M ⊗ₖ 1) * σ)) M σ i j = ∑ a, ∑ b, M b a * σ (a, i) (b, j) := by
  simp only [partialTraceLeft, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
private theorem conditionalNatural_positive (M : Matrix H H ℂ)
    (σ : Matrix (H × R) (H × R) ℂ)
    (hM : M.PosSemidef) (hσ : σ.PosSemidef) :
    (partialTraceLeft ((M ⊗ₖ (1 : Matrix R R ℂ)) * σ)).PosSemidef := by
  let e := (Fintype.equivFin H).symm
  let f := (Fintype.equivFin R).symm
  have hp := weighted_psd (M.submatrix e e)
    (σ.submatrix (Equiv.prodCongr e f) (Equiv.prodCongr e f))
    (hM.submatrix _) (hσ.submatrix _)
  have hw (u v : Fin (Fintype.card R)) :
      weighted (M.submatrix e e)
        (σ.submatrix (Equiv.prodCongr e f) (Equiv.prodCongr e f)) u v =
      ∑ a, ∑ b, M (e a) (e b) * σ (e b, f u) (e a, f v) := rfl
  have ht (i j : R) : partialTraceLeft ((M ⊗ₖ (1 : Matrix R R ℂ)) * σ) i j =
      ∑ a, ∑ b, M a b * σ (b, i) (a, j) := by
    calc
      _ = ∑ a, ∑ b, M b a * σ (a, i) (b, j) := conditionalNatural_apply M σ i j
      _ = _ := Finset.sum_comm
  have he : partialTraceLeft ((M ⊗ₖ (1 : Matrix R R ℂ)) * σ) =
      (weighted (M.submatrix e e)
        (σ.submatrix (Equiv.prodCongr e f) (Equiv.prodCongr e f))).submatrix f.symm f.symm := by
    ext i j
    rw [ht]
    change _ = weighted _ _ (f.symm i) (f.symm j)
    rw [hw]
    simp only [Equiv.apply_symm_apply]
    symm
    calc
      _ = ∑ a : H, ∑ b : Fin (Fintype.card H),
          M a (e b) * σ (e b, i) (a, j) :=
        e.sum_comp (fun a : H => ∑ b : Fin (Fintype.card H), M a (e b) * σ (e b, i) (a, j))
      _ = _ := Finset.sum_congr rfl (fun a _ =>
        e.sum_comp (fun b : H => M a b * σ (b, i) (a, j)))
  rw [he]
  exact hp.submatrix _

end D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Conditional
end
section
open Matrix D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Conditional D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence
namespace D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Conditional
variable {A B X Y : Type*} [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
  [DecidableEq A] [DecidableEq B] [DecidableEq X] [DecidableEq Y]
private theorem conditional_reindex (M : Matrix (A × B) (A × B) ℂ)
    (σ : Matrix ((A × X) × (B × Y)) ((A × X) × (B × Y)) ℂ) :
    conditional M σ = (fun M σ => partialTraceLeft ((M ⊗ₖ 1) * σ)) M
      (σ.submatrix (Equiv.prodProdProdComm A B X Y) (Equiv.prodProdProdComm A B X Y)) := by
  ext i j
  simp only [conditional_apply, conditionalNatural_apply, Fintype.sum_prod_type,
    Matrix.submatrix_apply, Equiv.prodProdProdComm_apply]
private theorem conditional_positive (M : Matrix (A × B) (A × B) ℂ)
    (σ : Matrix ((A × X) × (B × Y)) ((A × X) × (B × Y)) ℂ)
    (hM : M.PosSemidef) (hσ : σ.PosSemidef) : (conditional M σ).PosSemidef := by
  rw [conditional_reindex]
  exact conditionalNatural_positive M _ hM (hσ.submatrix _)
theorem separable_ppt (σ : Matrix (A×B) (A×B) ℂ) (hσ : IsSeparable σ) :
    Matrix.PosSemidef (fun i j : A × B => σ (i.1,j.2) (j.1,i.2)) := by
  let a := (Fintype.equivFin A).symm
  let b := (Fintype.equivFin B).symm
  let e := Equiv.prodCongr a b
  have hc : D5.S3.Resource.CompositeCones.separableCone (σ.submatrix e e) := by
    obtain ⟨n,p,S,T,hp,_,hST,rfl⟩ := hσ
    refine ⟨n, (fun t => (p t : ℂ) • (S t).submatrix a a),
      (fun t => (T t).submatrix b b), ?_, ?_⟩
    · intro t
      exact ⟨((hST t).1.1.submatrix _).smul (by simpa [Complex.nonneg_iff] using hp t),
        (hST t).2.1.submatrix _⟩
    · ext i j
      simp [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_apply,
        Matrix.kronecker_apply, e, Equiv.prodCongr_apply, mul_assoc]
  have ht := D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity.separableCone_partialTranspose_posSemidef hc
  have hh := ht.submatrix e.symm
  convert hh using 1 <;> ext i j <;>
    simp [partialTranspose, Matrix.submatrix_apply, e, Equiv.prodCongr_apply, mul_assoc]
private theorem conditional_ppt (M : Matrix (A×B) (A×B) ℂ)
    (σ : Matrix ((A×X)×(B×Y)) ((A×X)×(B×Y)) ℂ)
    (hM : Matrix.PosSemidef (fun i j : A × B => M (i.1,j.2) (j.1,i.2))) (hσ : IsSeparable σ) :
    Matrix.PosSemidef (fun i j : X × Y => conditional M σ (i.1,j.2) (j.1,i.2)) := by
  rw [conditional_partialTranspose]
  exact conditional_positive _ _ hM (separable_ppt σ hσ)
end D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Conditional
end
section
open Matrix D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Conditional
open D5.S3.Quantum.Information.PartialTraceMutualInformation
namespace D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Marginal
variable {A B X Y : Type*} [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
  [DecidableEq A] [DecidableEq B] [DecidableEq X] [DecidableEq Y]
private def marginal (σ : Matrix ((A×X)×(B×Y)) ((A×X)×(B×Y)) ℂ) :
    Matrix (A×B) (A×B) ℂ := partialTraceRight
      (σ.submatrix (Equiv.prodProdProdComm A B X Y) (Equiv.prodProdProdComm A B X Y))
private theorem marginal_density (σ : Matrix ((A×X)×(B×Y)) ((A×X)×(B×Y)) ℂ)
    (hσ : (σ.PosSemidef ∧ σ.trace = 1)) : ((marginal σ).PosSemidef ∧ (marginal σ).trace = 1) := by
  refine ⟨partialTraceRight_posSemidef (hσ.1.submatrix _),?_⟩
  rw [marginal,trace_partialTraceRight]
  exact ((Equiv.prodProdProdComm A B X Y).sum_comp (fun i => σ i i)).trans hσ.2
private theorem marginal_product (S : Matrix (A×X) (A×X) ℂ) (T : Matrix (B×Y) (B×Y) ℂ) :
    marginal (S⊗ₖT)=partialTraceRight S ⊗ₖ partialTraceRight T := by
  ext i j
  simp only [marginal,partialTraceRight,Matrix.submatrix_apply,Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type,Equiv.prodProdProdComm_apply]
  rw [Finset.sum_mul_sum]
private theorem marginal_separable (σ : Matrix ((A×X)×(B×Y)) ((A×X)×(B×Y)) ℂ)
    (hσ : IsSeparable σ) : IsSeparable (marginal σ) := by
  obtain ⟨n,p,S,T,hp,hs,hST,rfl⟩ := hσ
  refine ⟨n,p,(fun t => partialTraceRight (S t)),(fun t => partialTraceRight (T t)),hp,hs,?_,?_⟩
  · intro t
    constructor
    · exact ⟨partialTraceRight_posSemidef (hST t).1.1,
        (trace_partialTraceRight _).trans (hST t).1.2⟩
    · exact ⟨partialTraceRight_posSemidef (hST t).2.1,
        (trace_partialTraceRight _).trans (hST t).2.2⟩
  · have he : marginal (∑t,(p t : ℂ) • (S t⊗ₖT t))=
        ∑t,(p t : ℂ) • marginal (S t⊗ₖT t) := by
      ext i j
      simp only [marginal,partialTraceRight,Matrix.submatrix_apply,Matrix.sum_apply,
        Matrix.smul_apply,Finset.mul_sum,Finset.sum_mul,smul_eq_mul]
      rw [Finset.sum_comm]
    rw [he]
    simp only [marginal_product]
private theorem conditionalNatural_trace {H R : Type*} [Fintype H] [Fintype R]
    [DecidableEq H] [DecidableEq R]
    (M : Matrix H H ℂ) (σ : Matrix (H×R) (H×R) ℂ) :
    ((fun M σ => partialTraceLeft ((M ⊗ₖ 1) * σ)) M σ).trace=(M*partialTraceRight σ).trace := by
  simp only [conditionalNatural_apply,partialTraceRight,Matrix.trace,Matrix.diag_apply,
    Matrix.mul_apply,Finset.mul_sum]
  conv_lhs => enter [2,i]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.sum_comm]
private theorem conditional_trace (M : Matrix (A×B) (A×B) ℂ)
    (σ : Matrix ((A×X)×(B×Y)) ((A×X)×(B×Y)) ℂ) :
    (conditional M σ).trace=(M*marginal σ).trace := by
  rw [conditional_reindex, conditionalNatural_trace]
  rfl
end D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Marginal
end
section
open Matrix D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Kraus D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Conditional
open scoped Kronecker
namespace D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Kraus
variable {H O R : Type*} [Fintype H] [Fintype O] [Fintype R]
  [DecidableEq H] [DecidableEq O] [DecidableEq R]
private theorem ket_ancilla_action (v : O → ℂ) (U : Matrix H H ℂ)
    (σ : Matrix (H×R) (H×R) ℂ) :
    (∑k,((Matrix.vecMulVec v (U k)) ⊗ₖ (1 : Matrix R R ℂ))*σ*
      ((Matrix.vecMulVec v (U k)) ⊗ₖ (1 : Matrix R R ℂ))ᴴ) =
      Matrix.vecMulVec v (star v) ⊗ₖ (fun M σ => partialTraceLeft ((M ⊗ₖ 1) * σ)) (Uᴴ*U) σ := by
  ext ⟨i,x⟩ ⟨j,y⟩
  simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.kronecker_apply,Fintype.sum_prod_type,conditionalNatural_apply,
    Matrix.vecMulVec_apply,Matrix.one_apply]
  simp only [mul_ite,ite_mul,mul_zero,zero_mul,apply_ite star,star_zero,
    Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,if_true]
  simp only [Pi.star_apply,star_mul,star_one,mul_one,Finset.mul_sum,Finset.sum_mul]
  conv_rhs => enter [2,a]; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]; enter [2,k]; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro a _
  ring
end D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Kraus
end
namespace D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence
open Conditional Marginal
variable {A B X Y : Type*} [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
  [DecidableEq A] [DecidableEq B] [DecidableEq X] [DecidableEq Y]
/-- A separable marginal overlap bound controls both PPT conditional ancillary matrices
and their flagged Bell trace-norm coefficient for arbitrary local ancillary systems. -/
private theorem conditional_ancilla_upper (M N : Matrix (A × B) (A × B) ℂ)
    (hM : Matrix.PosSemidef (fun i j : A × B => M (i.1, j.2) (j.1, i.2)))
    (hN : Matrix.PosSemidef (fun i j : A × B => N (i.1, j.2) (j.1, i.2)))
    (hsum : M + N = 1) (beta : ℝ)
    (hgap : ∀ rho : Matrix (A × B) (A × B) ℂ,
      rho.PosSemidef ∧ rho.trace = 1 → IsSeparable rho → (M * rho).trace.re ≤ beta)
    (sigma : Matrix ((A × X) × (B × Y)) ((A × X) × (B × Y)) ℂ)
    (hdensity : sigma.PosSemidef ∧ sigma.trace = 1) (hsep : IsSeparable sigma) :
    Matrix.PosSemidef (fun i j : X × Y => conditional M sigma (i.1, j.2) (j.1, i.2)) ∧
      Matrix.PosSemidef (fun i j : X × Y => conditional N sigma (i.1, j.2) (j.1, i.2)) ∧
      2 * (conditional M sigma).trace.re + (conditional N sigma).trace.re ≤ 1 + beta := by
  refine ⟨conditional_ppt M sigma hM hsep, conditional_ppt N sigma hN hsep, ?_⟩
  have hg : (conditional M sigma).trace.re ≤ beta := by
    rw [conditional_trace]
    exact hgap _ (marginal_density sigma hdensity) (marginal_separable sigma hsep)
  have hs : (conditional M sigma).trace + (conditional N sigma).trace = 1 := by
    rw [conditional_trace, conditional_trace, ← Matrix.trace_add, ← Matrix.add_mul,
      hsum, Matrix.one_mul, (marginal_density sigma hdensity).2]
  have hr := congrArg Complex.re hs
  simp only [Complex.add_re, Complex.one_re] at hr
  linarith
end D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence
namespace D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence
open Gap Kraus Conditional Marginal
/-- `Λ ⊗ id` with local ancillas `A'`, `B'`: the Kraus operators `K k ⊗ 1`, reordered to the cut
`A A' | B B'`. -/
def extend {dA dB a b r : ℕ} (K : Fin r → Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (ρ : Matrix ((Fin dA × Fin a) × (Fin dB × Fin b)) ((Fin dA × Fin a) × (Fin dB × Fin b)) ℂ) :
    Matrix ((Fin dA × Fin a) × (Fin dB × Fin b)) ((Fin dA × Fin a) × (Fin dB × Fin b)) ℂ :=
  MatrixMap.of_kraus
    (fun k => Matrix.reindex (Equiv.prodProdProdComm (Fin dA) (Fin dB) (Fin a) (Fin b))
      (Equiv.prodProdProdComm (Fin dA) (Fin dB) (Fin a) (Fin b))
      (K k ⊗ₖ (1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)))
    (fun k => Matrix.reindex (Equiv.prodProdProdComm (Fin dA) (Fin dB) (Fin a) (Fin b))
      (Equiv.prodProdProdComm (Fin dA) (Fin dB) (Fin a) (Fin b))
      (K k ⊗ₖ (1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ))) ρ
/-- The unassisted log-negativity entangling capacity, Eq. (1): separable inputs, free local ancillas. -/
def capSep {dA dB r : ℕ} (K : Fin r → Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) : EReal :=
  ⨆ (a : ℕ) (b : ℕ)
    (σ : Matrix ((Fin dA × Fin a) × (Fin dB × Fin b)) ((Fin dA × Fin a) × (Fin dB × Fin b)) ℂ)
    (_ : IsDensity σ ∧ IsSeparable σ),
    ((Real.logb 2 (traceNorm (partialTranspose (extend K σ))) : ℝ) : EReal)
/-- The resource-assisted capacity, Eq. (2): every density input, minus its own log-negativity. -/
def capAssisted {dA dB r : ℕ} (K : Fin r → Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) : EReal :=
  ⨆ (a : ℕ) (b : ℕ)
    (ρ : Matrix ((Fin dA × Fin a) × (Fin dB × Fin b)) ((Fin dA × Fin a) × (Fin dB × Fin b)) ℂ)
    (_ : IsDensity ρ),
    ((Real.logb 2 (traceNorm (partialTranspose (extend K ρ))) -
        Real.logb 2 (traceNorm (partialTranspose ρ)) : ℝ) : EReal)
/-- Resource independence of log-negativity EC for all CPTP maps (Campbell, Section VII). -/
def claim : Prop :=
  ∀ (dA dB r : ℕ) (K : Fin r → Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ),
    ∑ k, (K k)ᴴ * K k = 1 → capAssisted K = capSep K
private theorem capSep_upper_from_norm {dA dB r : ℕ}
    (K : Fin r → Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (B : ℝ) (hB : 1 < B)
    (hbound : ∀ (a b : ℕ) σ, IsDensity σ ∧ IsSeparable σ →
      traceNorm (partialTranspose (extend (a := a) (b := b) K σ)) ≤ B) :
    capSep K ≤ (Real.logb 2 B : ℝ) := by
  unfold capSep
  refine iSup_le fun a => iSup_le fun b => iSup_le fun σ => iSup_le fun hσ => ?_
  apply EReal.coe_le_coe_iff.mpr
  by_cases hz : traceNorm (partialTranspose (extend K σ)) = 0
  · simp only [hz, Real.logb_zero]
    exact le_of_lt (Real.logb_pos (by norm_num) hB)
  · exact Real.logb_le_logb_of_le (by norm_num)
      (lt_of_le_of_ne (D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_nonneg _) (Ne.symm hz))
      (hbound a b σ hσ)
private theorem capAssisted_lower_from_state {dA dB a b r : ℕ}
    (K : Fin r → Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (ρ : Matrix ((Fin dA × Fin a) × (Fin dB × Fin b))
      ((Fin dA × Fin a) × (Fin dB × Fin b)) ℂ)
    (hρ : IsDensity ρ) :
    ((Real.logb 2 (traceNorm (partialTranspose (extend K ρ))) -
      Real.logb 2 (traceNorm (partialTranspose ρ)) : ℝ) : EReal) ≤ capAssisted K := by
  unfold capAssisted
  exact le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le ρ (le_iSup_of_le hρ le_rfl)))
private theorem refutation_from_bounds {dA dB a b r : ℕ}
    (K : Fin r → Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hK : ∑ k, (K k)ᴴ * K k = 1)
    (ρ : Matrix ((Fin dA × Fin a) × (Fin dB × Fin b))
      ((Fin dA × Fin a) × (Fin dB × Fin b)) ℂ)
    (hρ : IsDensity ρ)
    (hin : traceNorm (partialTranspose ρ) = 1)
    (hout : traceNorm (partialTranspose (extend K ρ)) = 2)
    (hbound : ∀ (a b : ℕ) σ, IsDensity σ ∧ IsSeparable σ →
      traceNorm (partialTranspose (extend (a := a) (b := b) K σ)) ≤ (2 - 1/6561 : ℝ)) :
    ¬ claim := by
  intro hc
  have hu := capSep_upper_from_norm K (2 - 1/6561) (by norm_num) hbound
  have hl := capAssisted_lower_from_state K ρ hρ
  rw [hin, hout, Real.logb_self_eq_one (by norm_num), Real.logb_one, sub_zero,
    hc dA dB r K hK] at hl
  have strict : Real.logb 2 (2 - 1/6561 : ℝ) < 1 := by
    have h := Real.logb_lt_logb (b := 2) (by norm_num : (1:ℝ)<2)
      (by norm_num : (0:ℝ)<2-1/6561) (by norm_num : (2-1/6561:ℝ)<2)
    simpa using h
  exact not_le_of_gt (EReal.coe_lt_coe_iff.mpr strict) (le_trans hl hu)
section
private def aRat : Fin 5 → Fin 3 → ℚ :=
  ![![1,0,0], ![1,-1,0], ![0,0,1], ![0,1,-1], ![1,1,1]]
private def bRat : Fin 5 → Fin 3 → ℚ :=
  ![![1,-1,0], ![0,0,1], ![0,1,-1], ![1,0,0], ![1,1,1]]
private def wRat : Fin 5 → ℚ := ![1/2,1/2,1/2,1/2,1/9]
private def qTable : Matrix (Fin 9) (Fin 9) ℚ := ![![7/18,7/18,-1/9,-1/9,-1/9,-1/9,-1/9,-1/9,-1/9],![7/18,7/18,-1/9,-1/9,-1/9,-1/9,-1/9,-1/9,-1/9],![-1/9,-1/9,7/18,-1/9,-1/9,7/18,-1/9,-1/9,-1/9],![-1/9,-1/9,-1/9,7/18,-1/9,-1/9,7/18,-1/9,-1/9],![-1/9,-1/9,-1/9,-1/9,8/9,-1/9,-1/9,-1/9,-1/9],![-1/9,-1/9,7/18,-1/9,-1/9,7/18,-1/9,-1/9,-1/9],![-1/9,-1/9,-1/9,7/18,-1/9,-1/9,7/18,-1/9,-1/9],![-1/9,-1/9,-1/9,-1/9,-1/9,-1/9,-1/9,7/18,7/18],![-1/9,-1/9,-1/9,-1/9,-1/9,-1/9,-1/9,7/18,7/18]]
private def qRat : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℚ := qTable.submatrix finProdFinEquiv finProdFinEquiv
private def pRat : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℚ := 1-qRat
private def P : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := pRat.map (algebraMap ℚ ℂ)
private def Q : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := qRat.map (algebraMap ℚ ℂ)
private def Phi : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := fun i j =>
  if (i = (0,0) ∨ i = (1,1)) ∧ (j = (0,0) ∨ j = (1,1)) then 1/2 else 0
private def F : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := Matrix.single (2,2) (2,2) 1
private theorem qRat_square : qRat * qRat = qRat := by
  ext ⟨i,j⟩ ⟨k,l⟩; fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> decide +kernel
private theorem qRat_transpose : qRat.transpose = qRat := by
  exact Eq.symm (Matrix.ext_iff_trace_mul_left.mpr (congrFun rfl))
private theorem qRat_trace : Matrix.trace qRat = 4 := by
  decide +kernel
private theorem Q_square : Q * Q = Q := by
  simpa only [Q, Matrix.map_mul] using congrArg (fun X : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℚ =>
    X.map (algebraMap ℚ ℂ)) qRat_square
private theorem Q_hermitian : Q.IsHermitian := by
  ext i j
  have h := congrFun (congrFun qRat_transpose i) j
  simpa [Q, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply] using
    congrArg (algebraMap ℚ ℂ) h
private theorem Q_pt : partialTranspose Q = Q := by
  exact Matrix.ext_iff_trace_mul_left.mpr (congrFun rfl)
private theorem Q_trace : Matrix.trace Q = 4 := by
  simpa [Q, Matrix.trace, ← map_sum] using congrArg (algebraMap ℚ ℂ) qRat_trace
private theorem Q_pos : Q.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self Q
  rwa [Q_hermitian.eq, Q_square] at h
private def tau : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := (1/4 : ℂ) • Q
private theorem tau_density : IsDensity tau := by
  constructor
  · exact Q_pos.smul (by norm_num [Complex.nonneg_iff])
  · simp [tau, Matrix.trace_smul, Q_trace]
private theorem tau_pt : partialTranspose tau = tau := by
  change (1/4 : ℂ) • partialTranspose Q = _
  rw [Q_pt]
  rfl
private theorem tau_norm : traceNorm (partialTranspose tau) = 1 := by
  rw [tau_pt]
  have h := congrArg Complex.re
    (D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_of_posSemidef tau_density.1)
  simpa [tau_density.2] using h
end
section
private def triples (c : Fin 10) (j : Fin 3) : Fin 5 := if c = 0 then (if j = 0 then 0 else if j = 1 then 1 else 2) else (if c = 1 then (if j = 0 then 0 else if j = 1 then 1 else 3) else (if c = 2 then (if j = 0 then 0 else if j = 1 then 1 else 4) else (if c = 3 then (if j = 0 then 0 else if j = 1 then 2 else 3) else (if c = 4 then (if j = 0 then 0 else if j = 1 then 2 else 4) else (if c = 5 then (if j = 0 then 0 else if j = 1 then 3 else 4) else (if c = 6 then (if j = 0 then 1 else if j = 1 then 2 else 3) else (if c = 7 then (if j = 0 then 1 else if j = 1 then 2 else 4) else (if c = 8 then (if j = 0 then 1 else if j = 1 then 3 else 4) else (if c = 9 then (if j = 0 then 2 else if j = 1 then 3 else 4) else (4))))))))))
private def certC : Fin 10 → Matrix (Fin 3) (Fin 3) ℚ := ![![![1,0,0],![1,-1,0],![0,0,1]],![![1,0,0],![1,-1,0],![0,1,-1]],![![1,0,0],![1,-1,0],![1,1,1]],![![1,0,0],![0,0,1],![0,1,-1]],![![1,0,0],![0,0,1],![1,1,1]],![![1,0,0],![0,1,-1],![1,1,1]],![![1,-1,0],![0,0,1],![0,1,-1]],![![1,-1,0],![0,0,1],![1,1,1]],![![1,-1,0],![0,1,-1],![1,1,1]],![![0,0,1],![0,1,-1],![1,1,1]]]
private def certD : Fin 10 → Matrix (Fin 3) (Fin 3) ℚ := ![![![1,0,0],![1,-1,0],![0,0,1]],![![1,0,0],![1,-1,0],![1,-1,-1]],![![1,0,0],![1,-1,0],![-2,1,1]],![![1,0,0],![0,1,1],![0,1,0]],![![1,0,0],![-1,-1,1],![0,1,0]],![![1,0,0],![-1/2,1/2,1/2],![-1/2,-1/2,1/2]],![![1,1,1],![0,1,1],![0,1,0]],![![1/2,-1/2,1/2],![-1/2,-1/2,1/2],![0,1,0]],![![2/3,1/3,1/3],![-1/3,1/3,1/3],![-1/3,-2/3,1/3]],![![-2,-1,1],![1,1,0],![1,0,0]]]
private def certMass : Fin 10 → ℚ := ![4,6,9,4,5,5/2,6,5/2,5/3,9]
private theorem inverse_certificates : ∀ c : Fin 10,
    certD c * certC c = 1 ∧
    (∑ i, ∑ j, (certD c i j)^2) = certMass c ∧
    certMass c ≤ 9 := by
  intro c
  fin_cases c <;> refine ⟨?_, ?_, ?_⟩
  all_goals first
    | (ext i j; fin_cases i <;> fin_cases j <;> decide +kernel)
    | decide +kernel
end
section
open Matrix D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Gap
private theorem pRat_tiles : pRat = ∑ i : Fin 5, wRat i •
    Matrix.vecMulVec (fun u : (Fin 3 × Fin 3) => aRat i u.1 * bRat i u.2)
      (fun u : (Fin 3 × Fin 3) => aRat i u.1 * bRat i u.2) := by
  ext ⟨i,j⟩ ⟨k,l⟩; fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> decide +kernel
private theorem certificate_rows : ∀ c : Fin 10, ∀ i j : Fin 3,
    certC c i j = aRat (triples c i) j := by
  intro c i j
  fin_cases c <;> fin_cases i <;> fin_cases j <;> decide +kernel
private def permB : Fin 5 ≃ Fin 5 :=
  ⟨![1,2,3,0,4], ![3,0,1,2,4], by intro i; fin_cases i <;> decide +kernel,
    by intro i; fin_cases i <;> decide +kernel⟩
private theorem bRat_perm : ∀ i j, bRat i j = aRat (permB i) j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel
private theorem cast_frame_bound (C D : Matrix (Fin 3) (Fin 3) ℚ)
    (hDC : D*C=1) (hD : (∑ i, ∑ j, D i j ^ 2) ≤ 9) (x : Fin 3 → ℂ) :
    (∑ i, ‖x i‖ ^ 2) ≤ 9 * (∑ i, ‖(C.map (algebraMap ℚ ℂ) *ᵥ x) i‖ ^ 2) := by
  apply inverse_frame_bound _ (D.map (algebraMap ℚ ℂ)) _ _ x
  · simpa only [Matrix.map_mul, Matrix.map_one, map_zero, map_one] using
      congrArg (fun M : Matrix (Fin 3) (Fin 3) ℚ => M.map (algebraMap ℚ ℂ)) hDC
  · change (∑ i, ∑ j, ‖(D i j : ℂ)‖ ^ 2) ≤ 9
    simp only [Complex.norm_ratCast, sq_abs]
    exact_mod_cast hD
end
section
private theorem common_large_overlap_scaled (f g : Fin 5 → ℝ) (rx ry : ℝ)
    (hf : ∀ c : Fin 10, rx/9 ≤ ∑ j : Fin 3, f (triples c j))
    (hg : ∀ c : Fin 10, ry/9 ≤ ∑ j : Fin 3, g (triples c j)) :
    ∃ i, rx/27 ≤ f i ∧ ry/27 ≤ g i := by
  by_contra! h
  have bad (i : Fin 5) : f i < rx/27 ∨ g i < ry/27 := by
    rcases lt_or_ge (f i) (rx/27) with hi | hi
    · exact Or.inl hi
    · exact Or.inr (h i hi)
  have hf0 : rx/9 ≤ f 0 + f 1 + f 2 := by
    simpa [triples, Fin.sum_univ_three] using hf 0
  have hf1 : rx/9 ≤ f 0 + f 1 + f 3 := by
    simpa [triples, Fin.sum_univ_three] using hf 1
  have hf2 : rx/9 ≤ f 0 + f 1 + f 4 := by
    simpa [triples, Fin.sum_univ_three] using hf 2
  have hf3 : rx/9 ≤ f 0 + f 2 + f 3 := by
    simpa [triples, Fin.sum_univ_three] using hf 3
  have hf4 : rx/9 ≤ f 0 + f 2 + f 4 := by
    simpa [triples, Fin.sum_univ_three] using hf 4
  have hf5 : rx/9 ≤ f 0 + f 3 + f 4 := by
    simpa [triples, Fin.sum_univ_three] using hf 5
  have hf6 : rx/9 ≤ f 1 + f 2 + f 3 := by
    simpa [triples, Fin.sum_univ_three] using hf 6
  have hf7 : rx/9 ≤ f 1 + f 2 + f 4 := by
    simpa [triples, Fin.sum_univ_three] using hf 7
  have hf8 : rx/9 ≤ f 1 + f 3 + f 4 := by
    simpa [triples, Fin.sum_univ_three] using hf 8
  have hf9 : rx/9 ≤ f 2 + f 3 + f 4 := by
    simpa [triples, Fin.sum_univ_three] using hf 9
  have hg0 : ry/9 ≤ g 0 + g 1 + g 2 := by
    simpa [triples, Fin.sum_univ_three] using hg 0
  have hg1 : ry/9 ≤ g 0 + g 1 + g 3 := by
    simpa [triples, Fin.sum_univ_three] using hg 1
  have hg2 : ry/9 ≤ g 0 + g 1 + g 4 := by
    simpa [triples, Fin.sum_univ_three] using hg 2
  have hg3 : ry/9 ≤ g 0 + g 2 + g 3 := by
    simpa [triples, Fin.sum_univ_three] using hg 3
  have hg4 : ry/9 ≤ g 0 + g 2 + g 4 := by
    simpa [triples, Fin.sum_univ_three] using hg 4
  have hg5 : ry/9 ≤ g 0 + g 3 + g 4 := by
    simpa [triples, Fin.sum_univ_three] using hg 5
  have hg6 : ry/9 ≤ g 1 + g 2 + g 3 := by
    simpa [triples, Fin.sum_univ_three] using hg 6
  have hg7 : ry/9 ≤ g 1 + g 2 + g 4 := by
    simpa [triples, Fin.sum_univ_three] using hg 7
  have hg8 : ry/9 ≤ g 1 + g 3 + g 4 := by
    simpa [triples, Fin.sum_univ_three] using hg 8
  have hg9 : ry/9 ≤ g 2 + g 3 + g 4 := by
    simpa [triples, Fin.sum_univ_three] using hg 9
  rcases bad 0 with h0 | h0 <;> rcases bad 1 with h1 | h1 <;>
    rcases bad 2 with h2 | h2 <;> rcases bad 3 with h3 | h3 <;>
    rcases bad 4 with h4 | h4 <;> linarith
end
section
open Matrix D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Gap
private def triplePerm : Fin 10 → Fin 10 := ![6,0,7,1,8,2,3,9,4,5]
private theorem perm_triple_sum (f : Fin 5 → ℝ) (c : Fin 10) :
    (∑ j : Fin 3, f (permB (triples c j))) =
      ∑ j : Fin 3, f (triples (triplePerm c) j) := by
  fin_cases c <;> simp [triplePerm,permB,triples,Fin.sum_univ_three,Fin.ext_iff,-Fin.val_eq_zero_iff] <;> ring
private theorem overlapB_perm (x : Fin 3 → ℂ) (i : Fin 5) :
    ((fun k => (bRat i k : ℂ)) ⬝ᵥ x)=((fun k => (aRat (permB i) k : ℂ)) ⬝ᵥ x) := by simp [bRat_perm, dotProduct]
private theorem triples_bound_scaled (x : Fin 3 → ℂ) (c : Fin 10) :
    (∑ i, ‖x i‖ ^ 2)/9 ≤ ∑ j : Fin 3, ‖((fun k => (aRat (triples c j) k : ℂ)) ⬝ᵥ x)‖ ^ 2 := by
  have h := cast_frame_bound (certC c) (certD c) (inverse_certificates c).1
    ((inverse_certificates c).2.1.le.trans (inverse_certificates c).2.2) x
  have he : (∑ i, ‖(Matrix.mulVec ((certC c).map (algebraMap ℚ ℂ)) x) i‖ ^ 2) =
      ∑ j : Fin 3, ‖((fun k => (aRat (triples c j) k : ℂ)) ⬝ᵥ x)‖ ^ 2 := by
    unfold Matrix.mulVec dotProduct
    simp only [Matrix.map_apply,certificate_rows]
    rfl
  rw [he] at h
  linarith
private theorem triplesB_bound_scaled (y : Fin 3 → ℂ) (c : Fin 10) :
    (∑ i, ‖y i‖ ^ 2)/9 ≤ ∑ j : Fin 3, ‖((fun k => (bRat (triples c j) k : ℂ)) ⬝ᵥ y)‖ ^ 2 := by
  simp only [overlapB_perm]
  rw [perm_triple_sum (fun i => ‖((fun k => (aRat i k : ℂ)) ⬝ᵥ y)‖^2) c]
  exact triples_bound_scaled y (triplePerm c)
private def tilesKet (i : Fin 5) (u : (Fin 3 × Fin 3)) : ℂ := (aRat i u.1 : ℂ)*(bRat i u.2 : ℂ)
private theorem P_tiles : P=∑i : Fin 5,(wRat i : ℂ) • vecMulVec (tilesKet i) (star (tilesKet i)) := by
  ext u v
  have h := congrFun (congrFun pRat_tiles u) v
  have hc := congrArg (algebraMap ℚ ℂ) h
  simpa [P,Matrix.map_apply,Matrix.sum_apply,Matrix.smul_apply,vecMulVec_apply,
    tilesKet,smul_eq_mul,map_sum,map_mul] using hc
private theorem tiles_overlap (x y : Fin 3 → ℂ) (i : Fin 5) :
    star (tilesKet i) ⬝ᵥ (Matrix.vecMulVec x y).uncurry=((fun k => (aRat i k : ℂ)) ⬝ᵥ x)*((fun k => (bRat i k : ℂ)) ⬝ᵥ y) := by
  simp [tilesKet,Function.uncurry,Matrix.vecMulVec,dotProduct,Fintype.sum_prod_type,
    Finset.sum_mul,Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm]
  rw [Finset.sum_comm]
private theorem product_expectation (x y : Fin 3 → ℂ) :
    (P*vecMulVec ((Matrix.vecMulVec x y).uncurry) (star ((Matrix.vecMulVec x y).uncurry))).trace.re =
      ∑i : Fin 5,(wRat i : ℝ)*‖((fun k => (aRat i k : ℂ)) ⬝ᵥ x)‖^2*‖((fun k => (bRat i k : ℂ)) ⬝ᵥ y)‖^2 := by
  rw [P_tiles,Finset.sum_mul,Matrix.trace_sum,Complex.re_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Matrix.smul_mul,Matrix.trace_smul]
  have h := rankOne_trace_product (tilesKet i) ((Matrix.vecMulVec x y).uncurry)
  rw [tiles_overlap] at h
  simp only [smul_eq_mul,Complex.mul_re,Complex.ratCast_re,Complex.ratCast_im,zero_mul,sub_zero]
  rw [h,norm_mul,mul_pow]
  ring
private theorem wRat_nonneg (i : Fin 5) : (0 : ℝ) ≤ (wRat i : ℝ) := by
  fin_cases i <;> norm_num [wRat,Fin.ext_iff,-Fin.val_eq_zero_iff]
private theorem product_gap_homogeneous (x y : Fin 3 → ℂ) :
    (∑ i, ‖x i‖ ^ 2)*(∑ i, ‖y i‖ ^ 2)/6561 ≤
      (P*vecMulVec ((Matrix.vecMulVec x y).uncurry) (star ((Matrix.vecMulVec x y).uncurry))).trace.re := by
  obtain ⟨i,hi,hj⟩ := common_large_overlap_scaled
    (fun i => ‖((fun k => (aRat i k : ℂ)) ⬝ᵥ x)‖^2) (fun i => ‖((fun k => (bRat i k : ℂ)) ⬝ᵥ y)‖^2) ((∑ i, ‖x i‖ ^ 2)) ((∑ i, ‖y i‖ ^ 2))
    (triples_bound_scaled x) (triplesB_bound_scaled y)
  rw [product_expectation]
  have hw : (1/9 : ℝ) ≤ (wRat i : ℝ) := by
    fin_cases i <;> norm_num [wRat,Fin.ext_iff,-Fin.val_eq_zero_iff]
  have hx : 0 ≤ (∑ i, ‖x i‖ ^ 2) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hy : 0 ≤ (∑ i, ‖y i‖ ^ 2) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hm := mul_le_mul hi hj (div_nonneg hy (by norm_num)) (sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_right hw (mul_nonneg (sq_nonneg ‖((fun k => (aRat i k : ℂ)) ⬝ᵥ x)‖)
    (sq_nonneg ‖((fun k => (bRat i k : ℂ)) ⬝ᵥ y)‖))
  calc
    _ ≤ (wRat i : ℝ)*‖((fun k => (aRat i k : ℂ)) ⬝ᵥ x)‖^2*‖((fun k => (bRat i k : ℂ)) ⬝ᵥ y)‖^2 := by nlinarith
    _ ≤ _ := Finset.single_le_sum (f := fun j : Fin 5 => (wRat j : ℝ)*‖((fun k => (aRat j k : ℂ)) ⬝ᵥ x)‖^2*‖((fun k => (bRat j k : ℂ)) ⬝ᵥ y)‖^2) (fun j _ => mul_nonneg
      (mul_nonneg (wRat_nonneg j) (sq_nonneg _)) (sq_nonneg _))
      (Finset.mem_univ i)
end
section
open Matrix D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Kraus
private def bellKet (i : (Fin 3 × Fin 3)) : ℂ := if i=(0,0) ∨ i=(1,1) then (1+Complex.I)/2 else 0
private def flagKet (i : (Fin 3 × Fin 3)) : ℂ := if i=(2,2) then 1 else 0
private def krausAux (k : Fin 2 × (Fin 3 × Fin 3)) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  if k.1=0 then Matrix.vecMulVec bellKet (Q k.2) else Matrix.vecMulVec flagKet (P k.2)
private def K (k : Fin 18) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := krausAux (((Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans finProdFinEquiv : (Fin 2 × (Fin 3 × Fin 3)) ≃ Fin 18).symm k)
private theorem P_eq : P = 1-Q := by
  simp [P,pRat,Q,Matrix.map_sub,Matrix.map_one]
private theorem P_square : P*P=P := by
  rw [P_eq]
  noncomm_ring [Q_square]
private theorem P_hermitian : P.IsHermitian := by
  rw [P_eq]
  exact Matrix.isHermitian_one.sub Q_hermitian
private theorem P_pos : P.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self P
  rwa [P_hermitian.eq,P_square] at h
private theorem P_pt : partialTranspose P=P := by
  exact Matrix.ext_iff_trace_mul_left.mpr (congrFun rfl)
private theorem bell_norm : (∑ i : (Fin 3 × Fin 3), star (bellKet i)*bellKet i)=1 := by
  norm_num [Fin.ext_iff,-Fin.val_eq_zero_iff,map_ofNat,Complex.star_def,bellKet,Fintype.sum_prod_type,Fin.sum_univ_succ,Complex.ext_iff]
private theorem flag_norm : (∑ i : (Fin 3 × Fin 3), star (flagKet i)*flagKet i)=1 := by
  norm_num [Fin.ext_iff,-Fin.val_eq_zero_iff,map_ofNat,flagKet,Fintype.sum_prod_type,Fin.sum_univ_succ]
private theorem bell_outer : Matrix.vecMulVec bellKet (star bellKet)=Phi := by
  ext ⟨i,j⟩ ⟨k,l⟩; fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [Fin.ext_iff,-Fin.val_eq_zero_iff,map_ofNat,Complex.star_def,bellKet,Phi,Matrix.vecMulVec_apply,Complex.ext_iff]
private theorem flag_outer : Matrix.vecMulVec flagKet (star flagKet)=F := by
  ext ⟨i,j⟩ ⟨k,l⟩; fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [Fin.ext_iff,-Fin.val_eq_zero_iff,map_ofNat,flagKet,F,Matrix.single,Matrix.vecMulVec_apply]
private theorem K_complete : ∑ k, (K k)ᴴ*K k=1 := by
  rw [show (∑ k, (K k)ᴴ*K k) = ∑ k : Fin 2 × (Fin 3 × Fin 3), (krausAux k)ᴴ*krausAux k from
    (by simpa only [K] using ((Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans finProdFinEquiv : (Fin 2 × (Fin 3 × Fin 3)) ≃ Fin 18).symm.sum_comp (fun k => (krausAux k)ᴴ*krausAux k))]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two,krausAux,Fin.isValue,
    ite_true,show (1 : Fin 2) ≠ 0 from one_ne_zero,ite_false]
  rw [ket_gram,ket_gram,bell_norm,flag_norm,one_smul,one_smul,
    Q_hermitian.eq,P_hermitian.eq,Q_square,P_square,P_eq]
  noncomm_ring
private theorem K_action (X : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :
    MatrixMap.of_kraus K K X = (Q*X).trace • Phi + (P*X).trace • F := by
  change (∑ k, K k*X*(K k)ᴴ)=_
  rw [show (∑ k, K k*X*(K k)ᴴ)=∑k : Fin 2 × (Fin 3 × Fin 3),krausAux k*X*(krausAux k)ᴴ from
    (by simpa only [K] using ((Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans finProdFinEquiv : (Fin 2 × (Fin 3 × Fin 3)) ≃ Fin 18).symm.sum_comp (fun k => krausAux k*X*(krausAux k)ᴴ))]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two,krausAux,Fin.isValue,
    ite_true,show (1 : Fin 2) ≠ 0 from one_ne_zero,ite_false]
  rw [ket_action,ket_action,bell_outer,flag_outer,Q_hermitian.eq,P_hermitian.eq]
  congr 1
  · congr 1
    rw [Matrix.trace_mul_comm,← Matrix.mul_assoc,Q_square]
  · congr 1
    rw [Matrix.trace_mul_comm,← Matrix.mul_assoc,P_square]
end
section
private def bellAbs : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := Matrix.diagonal fun i =>
  if i.1.val<2 ∧ i.2.val<2 then 1/2 else 0
private theorem bellAbs_pos : bellAbs.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  dsimp [bellAbs]
  split_ifs <;> norm_num [Complex.nonneg_iff]
private theorem bellAbs_square : bellAbs*bellAbs=(partialTranspose Phi)ᴴ*partialTranspose Phi := by
  ext ⟨i,j⟩ ⟨k,l⟩; fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [bellAbs,Phi,partialTranspose,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.diagonal_apply,Fintype.sum_prod_type,Fin.sum_univ_succ,Fin.ext_iff,
      -Fin.val_eq_zero_iff,Complex.ext_iff]
private theorem bellAbs_trace : bellAbs.trace=2 := by
  norm_num [bellAbs,Matrix.trace,Fintype.sum_prod_type,Fin.sum_univ_succ]
private theorem Phi_pt_norm : traceNorm (partialTranspose Phi)=2 := by
  have hs := CFC.sqrt_unique bellAbs_square bellAbs_pos.nonneg
  change (CFC.sqrt ((partialTranspose Phi)ᴴ*partialTranspose Phi)).trace.re=2
  rw [hs,bellAbs_trace]
  norm_num
private theorem F_pos : F.PosSemidef := by
  rw [← flag_outer]
  exact Matrix.posSemidef_vecMulVec_self_star _
private theorem F_pt : partialTranspose F=F := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp [partialTranspose,F,Matrix.single,Prod.mk.injEq,and_comm,and_left_comm,and_assoc]
private theorem F_trace : F.trace=1 := by
  norm_num [F,Matrix.trace,Matrix.single,Fintype.sum_prod_type,Fin.sum_univ_succ,
    Fin.ext_iff,-Fin.val_eq_zero_iff]
end
section
namespace Norm
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
private theorem traceNorm_submatrix_equiv (e : m ≃ n) (A : Matrix n n ℂ) :
    traceNorm (A.submatrix e e)=traceNorm A := by
  simpa only [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
    Equiv.symm_symm] using
    D5.S3.QuantumChannels.SchurChannelMixedUnitaryDistance.reindex_traceNorm e.symm A
end Norm
end
section
open Matrix D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Kraus D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Conditional
private theorem extend_natural {a b : ℕ}
    (σ : Matrix ((Fin 3×Fin a)×(Fin 3×Fin b)) ((Fin 3×Fin a)×(Fin 3×Fin b)) ℂ) :
    extend K σ=Matrix.reindex (Equiv.prodProdProdComm (Fin 3) (Fin 3) (Fin a) (Fin b))
      (Equiv.prodProdProdComm (Fin 3) (Fin 3) (Fin a) (Fin b))
      (∑k,(K k⊗ₖ(1 : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ))*(σ.submatrix (Equiv.prodProdProdComm (Fin 3) (Fin 3) (Fin a) (Fin b)) (Equiv.prodProdProdComm (Fin 3) (Fin 3) (Fin a) (Fin b)))*
        (K k⊗ₖ(1 : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ))ᴴ) := by
  let e := Equiv.prodProdProdComm (Fin 3) (Fin 3) (Fin a) (Fin b)
  change (∑k,Matrix.reindex e e (K k⊗ₖ(1 : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ))*σ*
    (Matrix.reindex e e (K k⊗ₖ(1 : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ)))ᴴ)=_
  have hs (Z : Fin 18 → Matrix ((Fin 3 × Fin 3)×(Fin a×Fin b)) ((Fin 3 × Fin 3)×(Fin a×Fin b)) ℂ) :
      (∑k,Z k).submatrix e.symm e.symm=∑k,(Z k).submatrix e.symm e.symm := by
    ext i j
    simp only [Matrix.submatrix_apply,Matrix.sum_apply]
  simp only [Matrix.reindex_apply]
  change _ = (∑k,(K k⊗ₖ(1 : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ))*(σ.submatrix (Equiv.prodProdProdComm (Fin 3) (Fin 3) (Fin a) (Fin b)) (Equiv.prodProdProdComm (Fin 3) (Fin 3) (Fin a) (Fin b)))*
    (K k⊗ₖ(1 : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ))ᴴ).submatrix e.symm e.symm
  rw [hs]
  apply Finset.sum_congr rfl; intro k _
  rw [Matrix.conjTranspose_submatrix]
  change _=((K k⊗ₖ1)*σ.submatrix e e*(K k⊗ₖ1)ᴴ).submatrix e.symm e.symm
  rw [← Matrix.submatrix_mul_equiv _ _ e.symm e.symm e.symm]
  rw [← Matrix.submatrix_mul_equiv _ _ e.symm e.symm e.symm]
  simp [Matrix.submatrix_submatrix]
private theorem extend_decomposition {a b : ℕ}
    (σ : Matrix ((Fin 3×Fin a)×(Fin 3×Fin b)) ((Fin 3×Fin a)×(Fin 3×Fin b)) ℂ) :
    extend K σ=Matrix.reindex (Equiv.prodProdProdComm (Fin 3) (Fin 3) (Fin a) (Fin b))
      (Equiv.prodProdProdComm (Fin 3) (Fin 3) (Fin a) (Fin b))
      (Phi⊗ₖconditional Q σ+F⊗ₖconditional P σ) := by
  rw [extend_natural]
  congr 1
  unfold K
  rw [((Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans finProdFinEquiv : (Fin 2 × (Fin 3 × Fin 3)) ≃ Fin 18).symm.sum_comp (fun k =>
    (krausAux k⊗ₖ(1 : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ))*(σ.submatrix (Equiv.prodProdProdComm (Fin 3) (Fin 3) (Fin a) (Fin b)) (Equiv.prodProdProdComm (Fin 3) (Fin 3) (Fin a) (Fin b)))*
      (krausAux k⊗ₖ(1 : Matrix (Fin a×Fin b) (Fin a×Fin b) ℂ))ᴴ)]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two,krausAux,Fin.isValue,ite_true,
    show (1 : Fin 2) ≠ 0 from one_ne_zero,ite_false]
  rw [ket_ancilla_action,ket_ancilla_action,Q_hermitian.eq,P_hermitian.eq,
    Q_square,P_square,bell_outer,flag_outer]
  rw [← conditional_reindex, ← conditional_reindex]
end
section
open Matrix D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Norm
def symKet : (Fin 3 × Fin 3) → ℂ := (Pi.single (0,1) (1 : ℂ))+(Pi.single (1,0) (1 : ℂ))
def antiKet : (Fin 3 × Fin 3) → ℂ := (Pi.single (0,1) (1 : ℂ))-(Pi.single (1,0) (1 : ℂ))
private def ptPlus : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (1/2 : ℂ) • vecMulVec ((Pi.single (0,0) (1 : ℂ))) (star ((Pi.single (0,0) (1 : ℂ))))+
  (1/2 : ℂ) • vecMulVec ((Pi.single (1,1) (1 : ℂ))) (star ((Pi.single (1,1) (1 : ℂ))))+
  (1/4 : ℂ) • vecMulVec symKet (star symKet)
private def ptMinus : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := (1/4 : ℂ) • vecMulVec antiKet (star antiKet)
private theorem ptPlus_pos : ptPlus.PosSemidef := by
  apply Matrix.PosSemidef.add
  · apply Matrix.PosSemidef.add
    · exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.nonneg_iff])
    · exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.nonneg_iff])
  · exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.nonneg_iff])
private theorem ptMinus_pos : ptMinus.PosSemidef := by
  exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.nonneg_iff])
private theorem Phi_pt_jordan : partialTranspose Phi=ptPlus-ptMinus := by
  ext ⟨i,j⟩ ⟨k,l⟩; fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [Phi,partialTranspose,ptPlus,ptMinus,symKet,antiKet,Pi.single_apply,
      vecMulVec_apply,Fin.ext_iff,-Fin.val_eq_zero_iff,Complex.ext_iff]
private theorem pt_parts_orthogonal : ptPlus*ptMinus=0 ∧ F*ptMinus=0 := by
  constructor <;> ext ⟨i,j⟩ ⟨k,l⟩ <;>
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [ptPlus,ptMinus,symKet,antiKet,Pi.single_apply,F,Matrix.single,
      Matrix.mul_apply,Matrix.conjTranspose_apply,vecMulVec_apply,
      Fintype.sum_prod_type,Fin.sum_univ_succ,Fin.ext_iff,-Fin.val_eq_zero_iff,
      Complex.ext_iff]
private theorem pt_parts_trace : ptPlus.trace=3/2 ∧ ptMinus.trace=1/2 := by
  constructor <;> norm_num [ptPlus,ptMinus,symKet,antiKet,Pi.single_apply,
    Matrix.trace,vecMulVec_apply,Fintype.sum_prod_type,Fin.sum_univ_succ,
    Fin.ext_iff,-Fin.val_eq_zero_iff,Complex.ext_iff]
private theorem flagged_norm_exact {R : Type*} [Fintype R] [DecidableEq R]
    (X Y : Matrix R R ℂ) (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    traceNorm (partialTranspose Phi⊗ₖX+F⊗ₖY)=2*X.trace.re+Y.trace.re := by
  have he : partialTranspose Phi⊗ₖX+F⊗ₖY=
      (ptPlus⊗ₖX+F⊗ₖY)-(ptMinus⊗ₖX) := by
    rw [Phi_pt_jordan]
    ext i j
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.kroneckerMap_apply]
    ring
  have horth : (ptPlus⊗ₖX+F⊗ₖY)*(ptMinus⊗ₖX)=0 := by
    rw [add_mul,← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,
      pt_parts_orthogonal.1,pt_parts_orthogonal.2]
    simp
  rw [he,traceNorm_sub_orthogonal _ _
    ((ptPlus_pos.kronecker hX).add (F_pos.kronecker hY)) (ptMinus_pos.kronecker hX) horth]
  rw [Matrix.trace_add,Matrix.trace_kronecker,Matrix.trace_kronecker,Matrix.trace_kronecker,
    pt_parts_trace.1,pt_parts_trace.2,F_trace]
  simp [Complex.mul_re]
  ring
end
section
open Matrix D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Gap
private theorem pure_trace_mass {I : Type*} [Fintype I] (v : I → ℂ) :
    (vecMulVec v (star v)).trace.re=(∑ i, ‖v i‖ ^ 2) := by
  have h := congrArg Complex.re
    (D5.S3.Quantum.Entanglement.UniversalReplacementCapacityGrowth.pure_trace
      (WithLp.toLp 2 v : EuclideanSpace ℂ I))
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re,
    EuclideanSpace.norm_sq_eq] using h
private theorem product_mixed_gap (S T : Matrix (Fin 3) (Fin 3) ℂ)
    (hS : S.PosSemidef) (hT : T.PosSemidef) :
    S.trace.re*T.trace.re/6561 ≤ (P*(S⊗ₖT)).trace.re := by
  obtain ⟨m,v,hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hS
  obtain ⟨n,w,hw⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hT
  have htrS : S.trace.re=∑i,(∑ j, ‖v i j‖ ^ 2) := by
    rw [hv,Matrix.trace_sum,Complex.re_sum]
    simp only [pure_trace_mass]
  have htrT : T.trace.re=∑i,(∑ j, ‖w i j‖ ^ 2) := by
    rw [hw,Matrix.trace_sum,Complex.re_sum]
    simp only [pure_trace_mass]
  have hprod : S⊗ₖT=∑i,∑j,vecMulVec ((Matrix.vecMulVec (v i) (w j)).uncurry)
      (star ((Matrix.vecMulVec (v i) (w j)).uncurry)) := by
    rw [hv,hw]
    ext a b
    simp only [Matrix.kroneckerMap_apply,Matrix.sum_apply,vecMulVec_apply,
      Function.uncurry,Matrix.vecMulVec_apply,Pi.star_apply,star_mul]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [hprod]
  simp only [Finset.mul_sum,Matrix.trace_sum,Complex.re_sum]
  calc
    _ = ∑i,∑j,(∑ j, ‖v i j‖ ^ 2)*(∑ k, ‖w j k‖ ^ 2)/6561 := by
      rw [htrS, htrT, Finset.sum_mul_sum]
      simp_rw [Finset.sum_div]
    _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      product_gap_homogeneous (v i) (w j)
private theorem separable_P_gap (σ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (hσ : IsSeparable σ) :
    (1 : ℝ)/6561 ≤ (P*σ).trace.re := by
  obtain ⟨n,p,S,T,hp,hsum,hST,rfl⟩ := hσ
  simp only [Finset.mul_sum,Matrix.mul_smul,Matrix.trace_sum,Matrix.trace_smul,
    Complex.re_sum,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  calc
    _ = ∑i,p i*(1/6561) := by rw [← Finset.sum_mul,hsum]; ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (by simpa [(hST i).1.2,(hST i).2.2] using
        product_mixed_gap (S i) (T i) (hST i).1.1 (hST i).2.1) (hp i)
private theorem separable_Q_gap (σ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (hσ : IsDensity σ ∧ IsSeparable σ) :
    (Q*σ).trace.re ≤ 1-1/6561 := by
  have h := separable_P_gap σ hσ.2
  rw [P_eq,Matrix.sub_mul,Matrix.one_mul,Matrix.trace_sub,Complex.sub_re,hσ.1.2] at h
  norm_num at h
  linarith
end
section
open Matrix D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Norm
private def rho1 : Matrix ((Fin 3×Fin 1)×(Fin 3×Fin 1))
    ((Fin 3×Fin 1)×(Fin 3×Fin 1)) ℂ := tau.submatrix (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))) (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1)))
private theorem rho1_density : IsDensity rho1 := by
  exact ⟨tau_density.1.submatrix (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))),((Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))).sum_comp (fun i => tau i i)).trans tau_density.2⟩
private theorem rho1_pt_norm : traceNorm (partialTranspose rho1)=1 := by
  change traceNorm ((partialTranspose tau).submatrix (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))) (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))))=1
  rw [traceNorm_submatrix_equiv,tau_norm]
private theorem extend_single (L : Fin 18 → Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (X : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :
    extend L (X.submatrix (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))) (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))))=
      (MatrixMap.of_kraus L L X).submatrix (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))) (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))) := by
  have he (k : Fin 18) : Matrix.reindex
      (Equiv.prodProdProdComm (Fin 3) (Fin 3) (Fin 1) (Fin 1))
      (Equiv.prodProdProdComm (Fin 3) (Fin 3) (Fin 1) (Fin 1))
      (L k⊗ₖ(1 : Matrix (Fin 1×Fin 1) (Fin 1×Fin 1) ℂ))=(L k).submatrix (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))) (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))) := by
    ext ⟨⟨i,a⟩,⟨j,b⟩⟩ ⟨⟨k,c⟩,⟨l,d⟩⟩; fin_cases a; fin_cases b; fin_cases c; fin_cases d
    simp [Matrix.reindex_apply,Matrix.kroneckerMap_apply,Matrix.one_apply]
  change (∑k,Matrix.reindex _ _ (L k⊗ₖ1)*X.submatrix (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))) (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1)))*
    (Matrix.reindex _ _ (L k⊗ₖ1))ᴴ)=(∑k,L k*X*(L k)ᴴ).submatrix (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))) (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1)))
  simp only [he]
  ext i j
  simp only [Matrix.sum_apply,Matrix.submatrix_apply]
  apply Finset.sum_congr rfl; intro k _
  have hm : (L k).submatrix (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))) (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1)))*X.submatrix (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))) (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1)))*
      ((L k).submatrix (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))) (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))))ᴴ=(L k*X*(L k)ᴴ).submatrix (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))) (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))) := by
    rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv _ _ (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))) (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))) (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))),
      Matrix.submatrix_mul_equiv _ _ (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))) (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))) (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1)))]
  exact congrFun (congrFun hm i) j
private theorem tau_output : MatrixMap.of_kraus K K tau=Phi := by
  rw [K_action]
  have hq : (Q*tau).trace=1 := by
    rw [tau,Matrix.mul_smul,Q_square,Matrix.trace_smul,Q_trace]
    norm_num
  have hp : (P*tau).trace=0 := by
    rw [P_eq,Matrix.sub_mul,Matrix.one_mul,Matrix.trace_sub,hq,tau_density.2]
    ring
  rw [hq,hp,one_smul,zero_smul,add_zero]
private theorem rho1_output_norm : traceNorm (partialTranspose (extend K rho1))=2 := by
  rw [rho1,extend_single,tau_output]
  change traceNorm ((partialTranspose Phi).submatrix (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))) (Equiv.prodCongr (Equiv.prodUnique (Fin 3) (Fin 1)) (Equiv.prodUnique (Fin 3) (Fin 1))))=2
  rw [traceNorm_submatrix_equiv,Phi_pt_norm]
end
section
open Matrix D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Conditional D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Marginal D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence.Norm
private theorem extend_pt_decomposition {a b : ℕ}
    (σ : Matrix ((Fin 3×Fin a)×(Fin 3×Fin b)) ((Fin 3×Fin a)×(Fin 3×Fin b)) ℂ) :
    partialTranspose (extend K σ)=Matrix.reindex
      (Equiv.prodProdProdComm (Fin 3) (Fin 3) (Fin a) (Fin b))
      (Equiv.prodProdProdComm (Fin 3) (Fin 3) (Fin a) (Fin b))
      (partialTranspose Phi⊗ₖpartialTranspose (conditional Q σ)+
        F⊗ₖpartialTranspose (conditional P σ)) := by
  rw [extend_decomposition]
  have he : partialTranspose F=F := F_pt
  ext i j
  change (_+_ : ℂ)= _+_
  congr 1
  change partialTranspose F (i.1.1,i.2.1) (j.1.1,j.2.1) * _=
    F (i.1.1,i.2.1) (j.1.1,j.2.1) * _
  rw [he]
  rfl
private theorem unassisted_norm_upper (a b : ℕ)
    (σ : Matrix ((Fin 3×Fin a)×(Fin 3×Fin b)) ((Fin 3×Fin a)×(Fin 3×Fin b)) ℂ)
    (hσ : IsDensity σ ∧ IsSeparable σ) :
    traceNorm (partialTranspose (extend K σ)) ≤ 2-1/6561 := by
  obtain ⟨hQ, hP, hbound⟩ := conditional_ancilla_upper Q P
    (by change (partialTranspose Q).PosSemidef; rw [Q_pt]; exact Q_pos)
    (by change (partialTranspose P).PosSemidef; rw [P_pt]; exact P_pos)
    (by rw [P_eq]; noncomm_ring) (1 - 1 / 6561)
    (fun rho hd hs => separable_Q_gap rho ⟨hd, hs⟩) σ hσ.1 hσ.2
  change (partialTranspose (conditional Q σ)).PosSemidef at hQ
  change (partialTranspose (conditional P σ)).PosSemidef at hP
  rw [extend_pt_decomposition]
  change D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm ((partialTranspose Phi⊗ₖpartialTranspose (conditional Q σ)+
    F⊗ₖpartialTranspose (conditional P σ)).submatrix _ _) ≤ _
  rw [traceNorm_submatrix_equiv]
  rw [flagged_norm_exact _ _ hQ hP]
  have htQ : (partialTranspose (conditional Q σ)).trace=(conditional Q σ).trace := by
    rfl
  have htP : (partialTranspose (conditional P σ)).trace=(conditional P σ).trace := by
    rfl
  rw [htQ,htP]
  linarith
end
section
theorem result : ¬ claim :=
  refutation_from_bounds K K_complete rho1 rho1_density rho1_pt_norm rho1_output_norm
    unassisted_norm_upper
end
end D5.S3.Quantum.QuantumChannels.LogNegativityCapacityResourceDependence
