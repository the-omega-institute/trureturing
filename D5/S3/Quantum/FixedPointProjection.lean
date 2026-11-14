/- GID: D5/S3/Quantum/FixedPointProjection
   generality: G
   mirror-B: D5/B/S3/Quantum/FixedPointProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Faithful completely positive maps have commuting fixed projections. -/
import D5.S3.Quantum.Recovery.ActualChannelAlgebra
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Information.HedgingMajorityThreshold
import D5.S3.Quantum.Entanglement.LocalObservationPartialTraceEquivalence
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.Foundation.FiniteStateChannel

/-!
admission_basis: escape-witness
escape_witness: Channel.channelCommutingFixedProjection
The fixed-space argument constructs a nontrivial spectral projection commuting
with a faithful invariant state. Scalar and trace identities support that construction.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22403
-/

open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
section r2_marginal_bridge
open Matrix MatrixOrder ComplexOrder
noncomputable section
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
namespace D5.S3.Quantum.FixedPointProjection.Marginal
variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
lemma traceLocalLeft (ρ : Matrix (a × b) (a × b) ℂ) (X : Matrix a a ℂ) :
    (kroneckerMap (· * ·) X (1 : Matrix b b ℂ) * ρ).trace = (X * partialTraceRight ρ).trace := by
  let e : b × a ≃ a × b := Equiv.prodComm b a
  have hk : (kroneckerMap (· * ·) X (1 : Matrix b b ℂ)).submatrix e e =
      kroneckerMap (· * ·) (1 : Matrix b b ℂ) X := by
    ext i j
    change X i.2 j.2 * (1 : Matrix b b ℂ) i.1 j.1 =
      (1 : Matrix b b ℂ) i.1 j.1 * X i.2 j.2
    exact mul_comm _ _
  calc
    _ = ((kroneckerMap (· * ·) X (1 : Matrix b b ℂ) * ρ).submatrix e e).trace := by
      simpa only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply] using
        (e.sum_comp (fun i => (kroneckerMap (· * ·) X (1 : Matrix b b ℂ) * ρ) i i)).symm
    _ = (kroneckerMap (· * ·) (1 : Matrix b b ℂ) X * ρ.submatrix e e).trace := by
      rw [← Matrix.submatrix_mul_equiv _ _ e e e, hk]
    _ = _ := D5.S3.Quantum.Information.HedgingMajorityThreshold.trace_retained
      (ρ.submatrix e e) X
lemma traceLocalRight (ρ : Matrix (a × b) (a × b) ℂ) (Y : Matrix b b ℂ) :
    (kroneckerMap (· * ·) (1 : Matrix a a ℂ) Y * ρ).trace = (Y * partialTraceLeft ρ).trace := by
  exact D5.S3.Quantum.Information.HedgingMajorityThreshold.trace_retained ρ Y
lemma localTrace (ρ : Matrix (a × b) (a × b) ℂ) (X : Matrix a a ℂ) :
    ((kroneckerMap (· * ·) X (1 : Matrix b b ℂ))ᴴ * ρ *
      kroneckerMap (· * ·) X (1 : Matrix b b ℂ)).trace =
    (Xᴴ * partialTraceRight ρ * X).trace := by
  have hs : (kroneckerMap (· * ·) X (1 : Matrix b b ℂ))ᴴ =
      kroneckerMap (· * ·) Xᴴ (1 : Matrix b b ℂ) := by
    simpa only [Matrix.conjTranspose_one] using
      Matrix.conjTranspose_kronecker X (1 : Matrix b b ℂ)
  rw [hs, Matrix.trace_mul_cycle]
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, traceLocalLeft]
  exact (Matrix.trace_mul_cycle Xᴴ (partialTraceRight ρ) X).symm
end D5.S3.Quantum.FixedPointProjection.Marginal
end
end r2_marginal_bridge
section r2_choi_map
noncomputable section
open Matrix MatrixOrder ComplexOrder
namespace D5.S3.Quantum.FixedPointProjection.Choi
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.FixedPointProjection.Marginal
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
lemma fromBipartiteTrace (J : Matrix (a × b) (a × b) ℂ) (X : Matrix a a ℂ) :
    ((MatrixMap.of_choi_matrix ((J).submatrix Prod.swap Prod.swap)) X).trace = ((partialTraceRight J)ᵀ * X).trace := by
  change (∑ k : b, ∑ i : a, ∑ j : a, X i j * J (i,k) (j,k)) = _
  calc
    _ = ∑ i : a, ∑ j : a, ∑ k : b, X i j * J (i,k) (j,k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ((partialTraceRight J)ᵀ * X).trace := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Matrix.transpose_apply, partialTraceRight, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      exact mul_comm _ _
lemma fromBipartitePairing
    (J : Matrix (a × b) (a × b) ℂ) (X : Matrix a a ℂ) (Y : Matrix b b ℂ) :
    ((MatrixMap.of_choi_matrix ((J).submatrix Prod.swap Prod.swap)) X * Y).trace =
      (kroneckerMap (· * ·) Xᵀ Y * J).trace := by
  rw [Matrix.trace_mul_comm (kroneckerMap (· * ·) Xᵀ Y) J]
  change (∑ k : b, ∑ l : b,
      (∑ i : a, ∑ j : a, X i j * J (i,k) (j,l)) * Y l k) =
    ∑ u : a × b, ∑ v : a × b, J u v * (X u.1 v.1 * Y v.2 u.2)
  simp only [Fintype.sum_prod_type, Finset.sum_mul]
  calc
    _ = ∑ k : b, ∑ i : a, ∑ l : b, ∑ j : a,
        (X i j * J (i,k) (j,l)) * Y l k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
    _ = ∑ i : a, ∑ k : b, ∑ l : b, ∑ j : a,
        (X i j * J (i,k) (j,l)) * Y l k := by rw [Finset.sum_comm]
    _ = ∑ i : a, ∑ k : b, ∑ j : a, ∑ l : b,
        (X i j * J (i,k) (j,l)) * Y l k := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro l hl
      ring
end D5.S3.Quantum.FixedPointProjection.Choi
end
end r2_choi_map
section r2_choi_channel
open Matrix MatrixOrder ComplexOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.FixedPointProjection.Marginal
noncomputable section
namespace D5.S3.Quantum.FixedPointProjection.Choi
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
lemma fromBipartiteOne (J : Matrix (a × b) (a × b) ℂ) :
    (MatrixMap.of_choi_matrix ((J).submatrix Prod.swap Prod.swap)) 1 = partialTraceLeft J := by
  ext k l
  change (∑ i : a, ∑ j : a, (1 : Matrix a a ℂ) i j * J (i,k) (j,l)) =
    ∑ i : a, J (i,k) (i,l)
  simp [Matrix.one_apply]
lemma normalizedBipartiteChannel
    (J : Matrix (a × b) (a × b) ℂ) (hJ : J.PosSemidef)
    (S : Matrix a a ℂ) (hS : S.IsHermitian)
    (hnormal : S * (partialTraceRight J)ᵀ * S = 1) :
    ∃ E : QuantumChannel a b,
      (∀ X : Matrix a a ℂ,
        CStarMatrix.ofMatrix.symm
          (E.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
          (MatrixMap.of_choi_matrix ((J).submatrix Prod.swap Prod.swap)) (S * X * S)) ∧
      CStarMatrix.ofMatrix.symm
        (E.toCompletelyPositiveMap (CStarMatrix.ofMatrix (partialTraceRight J)ᵀ)) = partialTraceLeft J := by
  obtain ⟨K, hK⟩ := MatrixMap.exists_kraus_of_choi_PSD _ (hJ.submatrix Prod.swap)
  have hF (X : Matrix a a ℂ) : (MatrixMap.of_choi_matrix ((J).submatrix Prod.swap Prod.swap)) X = ∑ c, K c * X * (K c)ᴴ := by
    change MatrixMap.of_choi_matrix (J.submatrix Prod.swap Prod.swap) X = _
    rw [hK, MatrixMap.choi_map_inv]
    simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
  let L := fun c => K c * S
  let M := MatrixMap.of_kraus L L
  have hM (X : Matrix a a ℂ) : M X = (MatrixMap.of_choi_matrix ((J).submatrix Prod.swap Prod.swap)) (S * X * S) := by
    rw [hF]
    simp only [M, L, MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.conjTranspose_mul, hS.eq, Matrix.mul_assoc]
  have hTP (X : Matrix a a ℂ) : (M X).trace = X.trace := by
    rw [hM, fromBipartiteTrace]
    change ((partialTraceRight J)ᵀ * (S * X * S)).trace = _
    have ht : ((partialTraceRight J)ᵀ * (S * X * S)).trace =
        ((S * (partialTraceRight J)ᵀ * S) * X).trace := by
      simpa only [Matrix.mul_assoc] using
        Matrix.trace_mul_cycle ((partialTraceRight J)ᵀ * S) X S
    rw [ht, hnormal, Matrix.one_mul]
  have hcomplete : (∑ c, (L c)ᴴ * L c) = 1 :=
    Original8340Global.kraus_normalization_from_actual_trace L (by
      intro X
      simpa only [M, MatrixMap.of_kraus, LinearMap.sum_apply,
        LinearMap.coe_mk, AddHom.coe_mk] using hTP X)
  obtain ⟨E, hE⟩ := finite_kraus_quantum_channel L hcomplete
  have hEm (X : Matrix a a ℂ) :
      CStarMatrix.ofMatrix.symm
        (E.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = M X := by
    simpa only [M, MatrixMap.of_kraus, LinearMap.sum_apply,
      LinearMap.coe_mk, AddHom.coe_mk] using hE X
  refine ⟨E, fun X => (hEm X).trans (hM X), ?_⟩
  rw [hEm, hM, hnormal, fromBipartiteOne]
end D5.S3.Quantum.FixedPointProjection.Choi
end
end r2_choi_channel
section r2_fixed_projection
open Matrix MatrixOrder ComplexOrder
noncomputable section
namespace D5.S3.Quantum.FixedPointProjection.Faithful
variable {n : Type*} [Fintype n] [DecidableEq n]
private lemma weightedSquareZero (σ X : Matrix n n ℂ) (hσ : σ.PosDef)
    (hz : (X * σ * Xᴴ).trace = 0) : X = 0 := by
  letI : NormedAddCommGroup (Matrix n n ℂ) := σ.toMatrixNormedAddCommGroup hσ
  letI : InnerProductSpace ℂ (Matrix n n ℂ) := σ.toMatrixInnerProductSpace hσ.posSemidef
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  exact hz
lemma faithfulTraceZero (σ D : Matrix n n ℂ) (hσ : σ.PosDef)
    (hD : D.PosSemidef) (hz : (σ * D).trace = 0) : D = 0 := by
  obtain ⟨X, hX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hD.nonneg
  have hx : X = 0 := weightedSquareZero σ X hσ (by
    rw [hX] at hz
    change (σ * (Xᴴ * X)).trace = 0 at hz
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle] at hz
    exact hz)
  simp [hX, hx]
end D5.S3.Quantum.FixedPointProjection.Faithful

namespace D5.S3.Quantum.FixedPointProjection.Kraus
variable {n s : Type*} [Fintype n] [DecidableEq n] [Fintype s]
section Rectangular
variable {a b r : Type*} [Fintype a] [Fintype b] [Fintype r]
lemma rawStar (K : r → Matrix b a ℂ) (X : Matrix a a ℂ) :
    (∑ i, K i * X * (K i)ᴴ)ᴴ = ∑ i, K i * Xᴴ * (K i)ᴴ := by
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
lemma rawPair (K : r → Matrix b a ℂ) (X : Matrix a a ℂ) (Y : Matrix b b ℂ) :
    ((∑ i, K i * X * (K i)ᴴ) * Y).trace =
      (X * ∑ i, (K i)ᴴ * Y * K i).trace := by
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (K i) (X * (K i)ᴴ * Y)
end Rectangular
private lemma phiStar (K : s → Matrix n n ℂ) (X : Matrix n n ℂ) :
    (∑ i, ((K) i)ᴴ * (Xᴴ) * (K) i) = ((∑ i, ((K) i)ᴴ * (X) * (K) i))ᴴ := by
  simpa only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.conjTranspose_conjTranspose] using
      (rawStar (fun i => (K i)ᴴ) X).symm
private lemma commutatorDefect (K : s → Matrix n n ℂ) (X : Matrix n n ℂ) :
    (∑ i, (X * K i - K i * X)ᴴ * (X * K i - K i * X)) =
      (∑ i, ((K) i)ᴴ * ((Xᴴ * X)) * (K) i) - (∑ i, ((K) i)ᴴ * (Xᴴ) * (K) i) * X - Xᴴ * (∑ i, ((K) i)ᴴ * (X) * (K) i) + Xᴴ * (∑ i, ((K) i)ᴴ * (1) * (K) i) * X := by
  simp only [ Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum, Matrix.sum_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Matrix.mul_one,
    Matrix.mul_assoc]
  abel
private lemma fixedDefect (K : s → Matrix n n ℂ) (X : Matrix n n ℂ)
    (h1 : (∑ i, ((K) i)ᴴ * (1) * (K) i) = 1) (hX : (∑ i, ((K) i)ᴴ * (X) * (K) i) = X) :
    (∑ i, (X * K i - K i * X)ᴴ * (X * K i - K i * X)) =
      (∑ i, ((K) i)ᴴ * ((Xᴴ * X)) * (K) i) - Xᴴ * X := by
  rw [commutatorDefect, phiStar, hX, h1]
  simp only [Matrix.mul_one]
  abel
end D5.S3.Quantum.FixedPointProjection.Kraus

namespace D5.S3.Quantum.FixedPointProjection.Kraus
variable {n s : Type*} [Fintype n] [DecidableEq n] [Fintype s]
private lemma traceInvariance (K : s → Matrix n n ℂ) (σ : Matrix n n ℂ)
    (hσ : (∑ i, K i * σ * (K i)ᴴ) = σ) (D : Matrix n n ℂ) :
    (σ * (∑ i, ((K) i)ᴴ * (D) * (K) i)).trace = (σ * D).trace := by
  rw [← rawPair K σ D, hσ]
private lemma fixedKrausCommute (K : s → Matrix n n ℂ) (σ X : Matrix n n ℂ)
    (hσ : σ.PosDef) (hσinv : (∑ i, K i * σ * (K i)ᴴ) = σ)
    (h1 : (∑ i, ((K) i)ᴴ * (1) * (K) i) = 1) (hX : (∑ i, ((K) i)ᴴ * (X) * (K) i) = X) (i : s) :
    X * K i = K i * X := by
  let D := ∑ j, (X * K j - K j * X)ᴴ * (X * K j - K j * X)
  have hD : D.PosSemidef := by
    apply Matrix.posSemidef_sum
    intro j hj
    exact Matrix.posSemidef_conjTranspose_mul_self _
  have htrace : (σ * D).trace = 0 := by
    dsimp only [D]
    rw [fixedDefect K X h1 hX, Matrix.mul_sub, Matrix.trace_sub,
      traceInvariance K σ hσinv]
    exact sub_self _
  have hz : D = 0 := D5.S3.Quantum.FixedPointProjection.Faithful.faithfulTraceZero σ D hσ hD htrace
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ (Finset.univ : Finset s)) =>
      (Matrix.posSemidef_conjTranspose_mul_self (X * K j - K j * X)).nonneg)).mp hz
  exact sub_eq_zero.mp (Matrix.conjTranspose_mul_self_eq_zero.mp
    (hzero i (Finset.mem_univ i)))
private lemma fixedKrausStarCommute (K : s → Matrix n n ℂ) (σ X : Matrix n n ℂ)
    (hσ : σ.PosDef) (hσinv : (∑ i, K i * σ * (K i)ᴴ) = σ)
    (h1 : (∑ i, ((K) i)ᴴ * (1) * (K) i) = 1) (hX : (∑ i, ((K) i)ᴴ * (X) * (K) i) = X) (i : s) :
    (K i)ᴴ * X = X * (K i)ᴴ := by
  have hXstar : (∑ i, ((K) i)ᴴ * (Xᴴ) * (K) i) = Xᴴ := by rw [phiStar, hX]
  have h := congrArg Matrix.conjTranspose
    (fixedKrausCommute K σ Xᴴ hσ hσinv h1 hXstar i)
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using h
private lemma fixedMul (K : s → Matrix n n ℂ) (σ X Y : Matrix n n ℂ)
    (hσ : σ.PosDef) (hσinv : (∑ i, K i * σ * (K i)ᴴ) = σ)
    (h1 : (∑ i, ((K) i)ᴴ * (1) * (K) i) = 1) (hX : (∑ i, ((K) i)ᴴ * (X) * (K) i) = X) (hY : (∑ i, ((K) i)ᴴ * (Y) * (K) i) = Y) :
    (∑ i, ((K) i)ᴴ * ((X * Y)) * (K) i) = X * Y := by
  calc
    _ = ∑ i, X * ((K i)ᴴ * Y * K i) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        _ = ((K i)ᴴ * X) * Y * K i := by simp only [Matrix.mul_assoc]
        _ = (X * (K i)ᴴ) * Y * K i := by
          rw [fixedKrausStarCommute K σ X hσ hσinv h1 hX i]
        _ = _ := by simp only [Matrix.mul_assoc]
    _ = X * (∑ i, ((K) i)ᴴ * (Y) * (K) i) := by rw [ Matrix.mul_sum]
    _ = X * Y := by rw [hY]
private noncomputable def fixedAlgebra (K : s → Matrix n n ℂ) (σ : Matrix n n ℂ)
    (hσ : σ.PosDef) (hσinv : (∑ i, K i * σ * (K i)ᴴ) = σ)
    (h1 : (∑ i, ((K) i)ᴴ * (1) * (K) i) = 1) : StarSubalgebra ℂ (Matrix n n ℂ) where
  carrier := {X | (∑ i, ((K) i)ᴴ * (X) * (K) i) = X}
  zero_mem' := by simp []
  one_mem' := h1
  add_mem' := by
    intro X Y hX hY
    change (∑ i, ((K) i)ᴴ * ((X + Y)) * (K) i) = X + Y
    calc
      _ = (∑ i, ((K) i)ᴴ * (X) * (K) i) + (∑ i, ((K) i)ᴴ * (Y) * (K) i) := by
        simp only [ Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
      _ = X + Y := by rw [hX, hY]
  mul_mem' := by
    intro X Y hX hY
    exact fixedMul K σ X Y hσ hσinv h1 hX hY
  algebraMap_mem' := by
    intro c
    change (∑ i, ((K) i)ᴴ * ((algebraMap ℂ (Matrix n n ℂ) c)) * (K) i) = algebraMap ℂ (Matrix n n ℂ) c
    rw [Algebra.algebraMap_eq_smul_one]
    calc
      _ = c • (∑ i, ((K) i)ᴴ * (1) * (K) i) := by
        simp only [ Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]
      _ = c • (1 : Matrix n n ℂ) := by rw [h1]
  star_mem' := by
    intro X hX
    change (∑ i, ((K) i)ᴴ * (Xᴴ) * (K) i) = Xᴴ
    rw [phiStar, hX]
end D5.S3.Quantum.FixedPointProjection.Kraus

namespace D5.S3.Quantum.FixedPointProjection.Kraus
open D5.S3.Quantum.Foundation.FiniteKrausChannel
variable {n s : Type*} [Fintype n] [DecidableEq n] [Fintype s]
end D5.S3.Quantum.FixedPointProjection.Kraus

open Matrix MatrixOrder ComplexOrder
noncomputable section
namespace D5.S3.Quantum.FixedPointProjection.Projection
variable {n : Type*} [Fintype n] [DecidableEq n]
private lemma spectralProjection (A : StarSubalgebra ℂ (Matrix n n ℂ))
    (X S : Matrix n n ℂ) (hX : X.IsHermitian) (hXA : X ∈ A)
    (hSX : Commute S X) (i j : n) (hij : hX.eigenvalues i ≠ hX.eigenvalues j) :
    ∃ P : Matrix n n ℂ, P ∈ A ∧ P.IsHermitian ∧ P * P = P ∧
      P ≠ 0 ∧ P ≠ 1 ∧ Commute S P := by
  classical
  let f : ℝ → ℝ := fun t => if t = hX.eigenvalues i then 1 else 0
  let P := cfc f X
  have hclosed : IsClosed (A : Set (Matrix n n ℂ)) :=
    A.toSubalgebra.toSubmodule.closed_of_finiteDimensional
  letI : IsClosed (A : Set (Matrix n n ℂ)) := hclosed
  have hf : ContinuousOn f (spectrum ℝ X) := by
    rw [hX.spectrum_real_eq_range_eigenvalues]
    exact (Set.finite_range hX.eigenvalues).continuousOn f
  have hP : P ∈ A := cfc_mem f hXA
  have hPP : P * P = P := by
    dsimp [P]
    rw [← cfc_mul f f X hf hf]
    apply cfc_congr
    intro t ht
    dsimp [f]
    split_ifs <;> norm_num
  have hP0 : P ≠ 0 := by
    intro h
    have he : (spectrum ℝ X).EqOn f (0 : ℝ → ℝ) :=
      eqOn_of_cfc_eq_cfc (p := IsSelfAdjoint) (a := X)
        (show cfc f X = cfc (0 : ℝ → ℝ) X from
          (show cfc f X = 0 from h).trans (cfc_zero ℝ X).symm) hf continuousOn_const hX
    have hi := he (hX.eigenvalues_mem_spectrum_real i)
    simp [f] at hi
  have hP1 : P ≠ 1 := by
    intro h
    have he : (spectrum ℝ X).EqOn f (1 : ℝ → ℝ) :=
      eqOn_of_cfc_eq_cfc (p := IsSelfAdjoint) (a := X)
        (show cfc f X = cfc (1 : ℝ → ℝ) X from
          (show cfc f X = 1 from h).trans (cfc_one ℝ X hX).symm) hf continuousOn_const hX
    have hj := he (hX.eigenvalues_mem_spectrum_real j)
    simp [f, hij.symm] at hj
  exact ⟨P, hP, (cfc_predicate f X : IsSelfAdjoint P).isHermitian, hPP, hP0, hP1,
    (hSX.symm.cfc_real f).symm⟩
end D5.S3.Quantum.FixedPointProjection.Projection
namespace D5.S3.Quantum.FixedPointProjection.Projection
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
private lemma nonscalarSpectralProjection (A : StarSubalgebra ℂ (Matrix n n ℂ))
    (X S : Matrix n n ℂ) (hX : X.IsHermitian) (hXA : X ∈ A)
    (hSX : Commute S X) (hn : ¬ ∃ c : ℂ, X = c • (1 : Matrix n n ℂ)) :
    ∃ P : Matrix n n ℂ, P ∈ A ∧ P.IsHermitian ∧ P * P = P ∧
      P ≠ 0 ∧ P ≠ 1 ∧ Commute S P := by
  classical
  have hv : ∃ i j, hX.eigenvalues i ≠ hX.eigenvalues j := by
    by_contra h
    push_neg at h
    let i : n := Classical.arbitrary n
    apply hn
    refine ⟨(hX.eigenvalues i : ℂ), ?_⟩
    conv_lhs => rw [hX.spectral_theorem]
    have he : ((RCLike.ofReal : ℝ → ℂ) ∘ hX.eigenvalues) =
        fun _ : n => (hX.eigenvalues i : ℂ) := by
      funext j
      exact congrArg (fun r : ℝ => (r : ℂ)) (h j i)
    rw [he]
    have hd : Matrix.diagonal (fun _ : n => (hX.eigenvalues i : ℂ)) =
        (hX.eigenvalues i : ℂ) • (1 : Matrix n n ℂ) := by
      ext j k
      by_cases hjk : j = k <;> simp [hjk, Matrix.one_apply]
    rw [hd, map_smul, map_one]
  obtain ⟨i, j, hij⟩ := hv
  exact spectralProjection A X S hX hXA hSX i j hij
private lemma nonscalarHermitian (A : StarSubalgebra ℂ (Matrix n n ℂ))
    (hA : 1 < Module.finrank ℂ A) :
    ∃ X : Matrix n n ℂ, X ∈ A ∧ X.IsHermitian ∧
      ¬ ∃ c : ℂ, X = c • (1 : Matrix n n ℂ) := by
  classical
  have hex : ∃ X : Matrix n n ℂ, X ∈ A ∧
      ¬ ∃ c : ℂ, X = c • (1 : Matrix n n ℂ) := by
    by_contra h
    push_neg at h
    have hle : A.toSubalgebra.toSubmodule ≤ ℂ ∙ (1 : Matrix n n ℂ) := by
      intro X hX
      obtain ⟨c, hc⟩ := h X hX
      exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
    have hr := Submodule.finrank_mono hle
    have hb : Module.finrank ℂ (ℂ ∙ (1 : Matrix n n ℂ)) = 1 :=
      finrank_span_singleton (one_ne_zero : (1 : Matrix n n ℂ) ≠ 0)
    rw [hb] at hr
    exact (not_le_of_gt hA) hr
  obtain ⟨X, hXA, hn⟩ := hex
  have hre : (realPart X : Matrix n n ℂ) ∈ A := by
    rw [realPart_apply_coe, ← Complex.coe_smul]
    exact A.smul_mem (A.add_mem hXA ((show star X ∈ A from star_mem hXA))) _
  have him : (imaginaryPart X : Matrix n n ℂ) ∈ A := by
    rw [imaginaryPart_apply_coe, ← Complex.coe_smul]
    exact A.smul_mem (A.smul_mem (A.sub_mem hXA ((show star X ∈ A from star_mem hXA))) _) _
  by_cases hr : ∃ c : ℂ, (realPart X : Matrix n n ℂ) = c • (1 : Matrix n n ℂ)
  · refine ⟨imaginaryPart X, him, (imaginaryPart X).property, ?_⟩
    rintro ⟨d, hd⟩
    obtain ⟨c, hc⟩ := hr
    apply hn
    refine ⟨c + Complex.I * d, ?_⟩
    rw [← realPart_add_I_smul_imaginaryPart X, hc, hd, smul_smul, ← add_smul]
  · exact ⟨realPart X, hre, (realPart X).property, hr⟩
end D5.S3.Quantum.FixedPointProjection.Projection

open Matrix MatrixOrder ComplexOrder
noncomputable section
namespace D5.S3.Quantum.FixedPointProjection.Density
variable {n : Type*} [Fintype n] [DecidableEq n]
private lemma restrictionUnique (A : StarSubalgebra ℂ (Matrix n n ℂ))
    (S T : Matrix n n ℂ) (hS : S ∈ A) (hT : T ∈ A)
    (hp : ∀ X ∈ A, (S * X).trace = (T * X).trace) : S = T := by
  have hz := hp (S - T)ᴴ (star_mem (A.sub_mem hS hT))
  have ht : ((S - T) * (S - T)ᴴ).trace = 0 := by
    rw [Matrix.sub_mul, Matrix.trace_sub, hz, sub_self]
  have h0 : S - T = 0 := Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp ht
  exact sub_eq_zero.mp h0
private lemma traceDensity (A : StarSubalgebra ℂ (Matrix n n ℂ))
    (σ : Matrix n n ℂ) (hσ : σ.IsHermitian) :
    ∃ S : Matrix n n ℂ, S ∈ A ∧ S.IsHermitian ∧
      ∀ X ∈ A, (S * X).trace = (σ * X).trace := by
  letI : NormedAddCommGroup (Matrix n n ℂ) :=
    (1 : Matrix n n ℂ).toMatrixNormedAddCommGroup Matrix.PosDef.one
  letI : InnerProductSpace ℂ (Matrix n n ℂ) :=
    (1 : Matrix n n ℂ).toMatrixInnerProductSpace Matrix.PosSemidef.one
  let V := A.toSubalgebra.toSubmodule
  obtain ⟨S, hSA, hSorth⟩ := Submodule.HasOrthogonalProjection.exists_orthogonal (K := V) σ
  have hp : ∀ X ∈ A, (S * X).trace = (σ * X).trace := by
    intro X hX
    have h := (V.mem_orthogonal _).mp hSorth Xᴴ (show Xᴴ ∈ A from star_mem hX)
    change ((σ - S) * 1 * (Xᴴ)ᴴ).trace = 0 at h
    simpa only [Matrix.mul_one, Matrix.conjTranspose_conjTranspose, Matrix.sub_mul,
      Matrix.trace_sub, sub_eq_zero, eq_comm] using h
  have hstar : ∀ X ∈ A, (Sᴴ * X).trace = (σ * X).trace := by
    intro X hX
    have h := congrArg star (hp Xᴴ (show Xᴴ ∈ A from star_mem hX))
    simp only [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hσ.eq] at h
    exact (Matrix.trace_mul_comm Sᴴ X).trans
      (h.trans (Matrix.trace_mul_comm X σ))
  refine ⟨S, hSA, ?_, hp⟩
  exact restrictionUnique A Sᴴ S (star_mem hSA) hSA
    (fun X hX => (hstar X hX).trans (hp X hX).symm)
end D5.S3.Quantum.FixedPointProjection.Density

open Matrix MatrixOrder ComplexOrder
noncomputable section
namespace D5.S3.Quantum.FixedPointProjection.Dimension
variable {n s : Type*} [Fintype n] [DecidableEq n] [Fintype s]
private lemma phiLStar (K : s → Matrix n n ℂ) (X : Matrix n n ℂ) :
    (MatrixMap.of_kraus (fun i => ((K) i)ᴴ) (fun i => ((K) i)ᴴ)) Xᴴ = ((MatrixMap.of_kraus (fun i => ((K) i)ᴴ) (fun i => ((K) i)ᴴ)) X)ᴴ := by
  simpa only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.conjTranspose_conjTranspose] using
      D5.S3.Quantum.FixedPointProjection.Kraus.phiStar K X
private lemma tracePair (K : s → Matrix n n ℂ) (X Y : Matrix n n ℂ) :
    (X * (MatrixMap.of_kraus (fun i => ((K) i)ᴴ) (fun i => ((K) i)ᴴ)) Y).trace = ((MatrixMap.of_kraus K K) X * Y).trace := by
  simpa only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.conjTranspose_conjTranspose] using
      (D5.S3.Quantum.FixedPointProjection.Kraus.rawPair K X Y).symm
private lemma fixedDimension (K : s → Matrix n n ℂ) :
    Module.finrank ℂ ((MatrixMap.of_kraus (fun i => ((K) i)ᴴ) (fun i => ((K) i)ᴴ))).fixedSubmodule =
      Module.finrank ℂ ((MatrixMap.of_kraus K K)).fixedSubmodule := by
  letI : NormedAddCommGroup (Matrix n n ℂ) :=
    (1 : Matrix n n ℂ).toMatrixNormedAddCommGroup Matrix.PosDef.one
  letI : InnerProductSpace ℂ (Matrix n n ℂ) :=
    (1 : Matrix n n ℂ).toMatrixInnerProductSpace Matrix.PosSemidef.one
  have ha : (MatrixMap.of_kraus (fun i => ((K) i)ᴴ) (fun i => ((K) i)ᴴ)) = ((MatrixMap.of_kraus K K)).adjoint := by
    apply (LinearMap.eq_adjoint_iff _ _).mpr
    intro X Y
    change (Y * 1 * ((MatrixMap.of_kraus (fun i => ((K) i)ᴴ) (fun i => ((K) i)ᴴ)) X)ᴴ).trace =
      ((MatrixMap.of_kraus K K) Y * 1 * Xᴴ).trace
    simp only [Matrix.mul_one, ← phiLStar]
    exact tracePair K Y Xᴴ
  have hd : (((MatrixMap.of_kraus K K)) - LinearMap.id).adjoint =
      (MatrixMap.of_kraus (fun i => ((K) i)ᴴ) (fun i => ((K) i)ᴴ)) - LinearMap.id := by
    simp only [map_sub, LinearMap.adjoint_id, ← ha]
  rw [LinearMap.fixedSubmodule_eq_ker, LinearMap.fixedSubmodule_eq_ker]
  have hr := LinearMap.finrank_range_adjoint
    (((MatrixMap.of_kraus K K)) - LinearMap.id)
  rw [hd] at hr
  have h1 := ((MatrixMap.of_kraus (fun i => ((K) i)ᴴ) (fun i => ((K) i)ᴴ)) - LinearMap.id).finrank_range_add_finrank_ker
  have h2 := ((MatrixMap.of_kraus K K) - LinearMap.id).finrank_range_add_finrank_ker
  omega
end D5.S3.Quantum.FixedPointProjection.Dimension

namespace D5.S3.Quantum.FixedPointProjection.Separation
variable {n : Type*} [Fintype n] [DecidableEq n]
private lemma fixedTraceSeparation
    (A : StarSubalgebra ℂ (Matrix n n ℂ)) (σ : Matrix n n ℂ)
    (hσ : σ.PosDef) (Ψ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hdim : Module.finrank ℂ A = Module.finrank ℂ Ψ.fixedSubmodule)
    (hleft : ∀ X ∈ A, Ψ (σ * X) = σ * X)
    (D : Matrix n n ℂ) (hD : Ψ D = D)
    (hp : ∀ X ∈ A, (D * X).trace = 0) : D = 0 := by
  letI : FiniteDimensional ℂ A := FiniteDimensional.of_injective
    A.toSubalgebra.val.toLinearMap Subtype.val_injective
  let f : A →ₗ[ℂ] Ψ.fixedSubmodule := {
    toFun := fun X => ⟨σ * (X : Matrix n n ℂ), hleft X X.property⟩
    map_add' := by intro X Y; apply Subtype.ext; exact Matrix.mul_add _ _ _
    map_smul' := by intro c X; apply Subtype.ext; exact Matrix.mul_smul _ _ _ }
  have hf : Function.Injective f := by
    intro X Y h
    apply Subtype.ext
    apply hσ.isUnit.mul_right_injective
    exact congrArg Subtype.val h
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf
  obtain ⟨X, hX⟩ := hsurj ⟨D, hD⟩
  have he : σ * (X : Matrix n n ℂ) = D := congrArg Subtype.val hX
  have ht : (σ * ((X : Matrix n n ℂ) * (X : Matrix n n ℂ)ᴴ)).trace = 0 := by
    rw [← Matrix.mul_assoc, he]
    exact hp _ (star_mem X.property)
  have hz : (X : Matrix n n ℂ) * (X : Matrix n n ℂ)ᴴ = 0 :=
    D5.S3.Quantum.FixedPointProjection.Faithful.faithfulTraceZero σ _ hσ (Matrix.posSemidef_self_mul_conjTranspose _) ht
  have hx0 : (X : Matrix n n ℂ) = 0 :=
    Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp (by rw [hz, Matrix.trace_zero])
  rw [← he, hx0, Matrix.mul_zero]
end D5.S3.Quantum.FixedPointProjection.Separation

namespace D5.S3.Quantum.FixedPointProjection.Projection
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
private lemma commutingProjectionOfTraceSeparation
    (A : StarSubalgebra ℂ (Matrix n n ℂ)) (σ : Matrix n n ℂ)
    (hσ : σ.IsHermitian) (hA : 1 < Module.finrank ℂ A)
    (Ψ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hleft : ∀ X ∈ A, Ψ (σ * X) = σ * X)
    (hright : ∀ X ∈ A, Ψ (X * σ) = X * σ)
    (hsep : ∀ D : Matrix n n ℂ, Ψ D = D →
      (∀ X ∈ A, (D * X).trace = 0) → D = 0) :
    ∃ P : Matrix n n ℂ, P ∈ A ∧ P.IsHermitian ∧ P * P = P ∧
      P ≠ 0 ∧ P ≠ 1 ∧ Commute σ P := by
  classical
  obtain ⟨S, hSA, hS, hp⟩ := D5.S3.Quantum.FixedPointProjection.Density.traceDensity A σ hσ
  have hex : ∃ P : Matrix n n ℂ, P ∈ A ∧ P.IsHermitian ∧ P * P = P ∧
      P ≠ 0 ∧ P ≠ 1 ∧ Commute S P := by
    by_cases hs : ∃ c : ℂ, S = c • (1 : Matrix n n ℂ)
    · obtain ⟨X, hXA, hX, hn⟩ := nonscalarHermitian A hA
      apply nonscalarSpectralProjection A X S hX hXA _ hn
      obtain ⟨c, hc⟩ := hs
      rw [hc]
      change (c • (1 : Matrix n n ℂ)) * X = X * (c • (1 : Matrix n n ℂ))
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    · exact nonscalarSpectralProjection A S S hS hSA (Commute.refl S) hs
  obtain ⟨P, hPA, hP, hPP, hP0, hP1, hSP⟩ := hex
  have hd : Ψ (σ * P - P * σ) = σ * P - P * σ := by
    rw [map_sub, hleft P hPA, hright P hPA]
  have htrace : ∀ X ∈ A, ((σ * P - P * σ) * X).trace = 0 := by
    intro X hXA
    calc
      _ = (σ * (P * X)).trace - (σ * (X * P)).trace := by
        rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.mul_assoc]
        congr 1
        simpa only [Matrix.mul_assoc] using (Matrix.trace_mul_cycle σ X P).symm
      _ = (S * (P * X)).trace - (S * (X * P)).trace := by
        rw [← hp (P * X) (A.mul_mem hPA hXA),
          ← hp (X * P) (A.mul_mem hXA hPA)]
      _ = ((S * P - P * S) * X).trace := by
        rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.mul_assoc]
        congr 1
        simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle S X P
      _ = 0 := by rw [hSP.eq, sub_self, Matrix.zero_mul, Matrix.trace_zero]
  have hz := hsep _ hd htrace
  exact ⟨P, hPA, hP, hPP, hP0, hP1, sub_eq_zero.mp hz⟩
end D5.S3.Quantum.FixedPointProjection.Projection

namespace D5.S3.Quantum.FixedPointProjection.Kraus
open D5.S3.Quantum.FixedPointProjection.Dimension
variable {n s : Type*} [Fintype n] [DecidableEq n] [Fintype s] [Nonempty n]
private lemma dualFixedLeft (K : s → Matrix n n ℂ) (σ X : Matrix n n ℂ)
    (hσ : σ.PosDef) (hσinv : (∑ i, K i * σ * (K i)ᴴ) = σ)
    (h1 : (∑ i, ((K) i)ᴴ * (1) * (K) i) = 1) (hX : (∑ i, ((K) i)ᴴ * (X) * (K) i) = X) :
    (MatrixMap.of_kraus K K) (σ * X) = σ * X := by
  simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk, Matrix.conjTranspose_conjTranspose]
  calc
    _ = ∑ i, (K i * σ * (K i)ᴴ) * X := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Matrix.mul_assoc]
      rw [← fixedKrausStarCommute K σ X hσ hσinv h1 hX i]
    _ = (∑ i, K i * σ * (K i)ᴴ) * X := by rw [Matrix.sum_mul]
    _ = σ * X := by rw [hσinv]
private lemma dualFixedRight (K : s → Matrix n n ℂ) (σ X : Matrix n n ℂ)
    (hσ : σ.PosDef) (hσinv : (∑ i, K i * σ * (K i)ᴴ) = σ)
    (h1 : (∑ i, ((K) i)ᴴ * (1) * (K) i) = 1) (hX : (∑ i, ((K) i)ᴴ * (X) * (K) i) = X) :
    (MatrixMap.of_kraus K K) (X * σ) = X * σ := by
  have hx : (∑ i, ((K) i)ᴴ * (Xᴴ) * (K) i) = Xᴴ := by rw [phiStar, hX]
  have h := congrArg Matrix.conjTranspose (dualFixedLeft K σ Xᴴ hσ hσinv h1 hx)
  simpa only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hσ.isHermitian.eq, Matrix.mul_assoc] using h
private lemma fixedProjectionKraus (K : s → Matrix n n ℂ) (σ : Matrix n n ℂ)
    (hσ : σ.PosDef) (hσinv : (∑ i, K i * σ * (K i)ᴴ) = σ)
    (h1 : (∑ i, ((K) i)ᴴ * (1) * (K) i) = 1)
    (hd : 1 < Module.finrank ℂ ((MatrixMap.of_kraus K K)).fixedSubmodule) :
    ∃ P : Matrix n n ℂ, (∑ i, ((K) i)ᴴ * (P) * (K) i) = P ∧ P.IsHermitian ∧ P * P = P ∧
      P ≠ 0 ∧ P ≠ 1 ∧ Commute σ P := by
  let A := fixedAlgebra K σ hσ hσinv h1
  have hdim : Module.finrank ℂ A =
      Module.finrank ℂ ((MatrixMap.of_kraus K K)).fixedSubmodule := by
    have hA : A.toSubalgebra.toSubmodule =
        (MatrixMap.of_kraus (fun i => (K i)ᴴ) (fun i => (K i)ᴴ)).fixedSubmodule := by
      ext X
      change ((∑ i, (K i)ᴴ * X * K i) = X) ↔
        ((MatrixMap.of_kraus (fun i => (K i)ᴴ) (fun i => (K i)ᴴ)) X = X)
      simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
        AddHom.coe_mk, Matrix.conjTranspose_conjTranspose]
    change Module.finrank ℂ A.toSubalgebra.toSubmodule = _
    rw [hA]
    exact fixedDimension K
  have ha : 1 < Module.finrank ℂ A := by omega
  have hl : ∀ X ∈ A, (MatrixMap.of_kraus K K) (σ * X) = σ * X := by
    intro X hX
    exact dualFixedLeft K σ X hσ hσinv h1 hX
  have hr : ∀ X ∈ A, (MatrixMap.of_kraus K K) (X * σ) = X * σ := by
    intro X hX
    exact dualFixedRight K σ X hσ hσinv h1 hX
  exact D5.S3.Quantum.FixedPointProjection.Projection.commutingProjectionOfTraceSeparation A σ hσ.isHermitian ha
    ((MatrixMap.of_kraus K K)) hl hr
    (D5.S3.Quantum.FixedPointProjection.Separation.fixedTraceSeparation A σ hσ _ hdim hl)
end D5.S3.Quantum.FixedPointProjection.Kraus
end
end
end
end
end r2_fixed_projection
section r2_cp_fixed_projection
open Matrix MatrixOrder ComplexOrder
noncomputable section
namespace D5.S3.Quantum.FixedPointProjection.Projection
open D5.S3.Quantum.Foundation.FiniteKrausChannel D5.S3.Quantum.FixedPointProjection.Kraus D5.S3.Quantum.FixedPointProjection.Dimension
variable {n : Type*} [Fintype n] [DecidableEq n]
end D5.S3.Quantum.FixedPointProjection.Projection
end
end r2_cp_fixed_projection
section r2_channel_fixed_projection
open Matrix MatrixOrder ComplexOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.FixedPointProjection.Kraus D5.S3.Quantum.FixedPointProjection.Dimension D5.S3.Quantum.FixedPointProjection.Projection
noncomputable section
namespace D5.S3.Quantum.FixedPointProjection.Channel
variable {n : Type*} [Fintype n] [DecidableEq n]
lemma channelCommutingFixedProjection
    (T : QuantumChannel n n) (σ : Matrix n n ℂ) (hσ : σ.PosDef)
    (hTσ : (fun (Φ : CompletelyPositiveMap (CStarMatrix _ _ ℂ) (CStarMatrix _ _ ℂ)) => CStarMatrix.ofMatrixₗ.symm.conj Φ.toLinearMap) T.toCompletelyPositiveMap σ = σ)
    (hd : 1 < Module.finrank ℂ
      ((fun (Φ : CompletelyPositiveMap (CStarMatrix _ _ ℂ) (CStarMatrix _ _ ℂ)) => CStarMatrix.ofMatrixₗ.symm.conj Φ.toLinearMap) T.toCompletelyPositiveMap).fixedSubmodule) :
    ∃ P : Matrix n n ℂ, P.IsHermitian ∧ P * P = P ∧ P ≠ 0 ∧ P ≠ 1 ∧
      Commute σ P ∧ ∀ X : Matrix n n ℂ,
        (P * (fun (Φ : CompletelyPositiveMap (CStarMatrix _ _ ℂ) (CStarMatrix _ _ ℂ)) => CStarMatrix.ofMatrixₗ.symm.conj Φ.toLinearMap) T.toCompletelyPositiveMap X).trace = (P * X).trace := by
  haveI : Nonempty n := by
    rcases isEmpty_or_nonempty n with hn | hn
    · letI : IsEmpty n := hn
      have hz : Module.finrank ℂ
          ((fun (Φ : CompletelyPositiveMap (CStarMatrix _ _ ℂ) (CStarMatrix _ _ ℂ)) => CStarMatrix.ofMatrixₗ.symm.conj Φ.toLinearMap) T.toCompletelyPositiveMap).fixedSubmodule = 0 :=
        Module.finrank_zero_of_subsingleton
      omega
    · exact hn
  let L := krausRepresentation T.toCompletelyPositiveMap
  have hLraw (X : Matrix n n ℂ) :
      (fun (Φ : CompletelyPositiveMap (CStarMatrix _ _ ℂ) (CStarMatrix _ _ ℂ)) => CStarMatrix.ofMatrixₗ.symm.conj Φ.toLinearMap) T.toCompletelyPositiveMap X =
        ∑ i, L.val i * X * (L.val i)ᴴ := by
    change CStarMatrix.ofMatrix.symm
      (T.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = _
    exact L.property X
  have hL (X : Matrix n n ℂ) :
      (MatrixMap.of_kraus L.val L.val) X = (fun (Φ : CompletelyPositiveMap (CStarMatrix _ _ ℂ) (CStarMatrix _ _ ℂ)) => CStarMatrix.ofMatrixₗ.symm.conj Φ.toLinearMap) T.toCompletelyPositiveMap X := by
    simpa only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.conjTranspose_conjTranspose] using (hLraw X).symm
  have heq : (MatrixMap.of_kraus L.val L.val) = (fun (Φ : CompletelyPositiveMap (CStarMatrix _ _ ℂ) (CStarMatrix _ _ ℂ)) => CStarMatrix.ofMatrixₗ.symm.conj Φ.toLinearMap) T.toCompletelyPositiveMap := by
    apply LinearMap.ext
    intro X
    exact hL X
  have hσinv : (∑ i, L.val i * σ * (L.val i)ᴴ) = σ := by
    exact (hLraw σ).symm.trans hTσ
  have h1 : (∑ i, ((L.val) i)ᴴ * (1) * (L.val) i) = 1 := by
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro X
    have ht := tracePair L.val X (1 : Matrix n n ℂ)
    simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.conjTranspose_conjTranspose] at ht
    rw [ht, ← hLraw X, Matrix.mul_one, Matrix.mul_one]
    exact T.trace_preserving (CStarMatrix.ofMatrix X)
  have hdim : 1 < Module.finrank ℂ
      ((MatrixMap.of_kraus L.val L.val)).fixedSubmodule := by rwa [heq]
  obtain ⟨P, hPfix, hP, hPP, hP0, hP1, hcomm⟩ :=
    fixedProjectionKraus L.val σ hσ hσinv h1 hdim
  refine ⟨P, hP, hPP, hP0, hP1, hcomm, ?_⟩
  intro X
  rw [Matrix.trace_mul_comm P _, ← hL X, ← tracePair L.val X P]
  simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.conjTranspose_conjTranspose]
  rw [hPfix, Matrix.trace_mul_comm X P]
end D5.S3.Quantum.FixedPointProjection.Channel
end
end r2_channel_fixed_projection
section r2_projection_transport
open Matrix MatrixOrder ComplexOrder
noncomputable section
namespace D5.S3.Quantum.FixedPointProjection.Transport
variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
private lemma effectSquareLe (Q : Matrix b b ℂ) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) :
    Q * Q ≤ Q := by
  let S := CFC.sqrt Q
  have hS : Sᴴ = S := (Matrix.LE.le.posSemidef (CFC.sqrt_nonneg Q)).isHermitian.eq
  have hSS : S * S = Q := CFC.sqrt_mul_sqrt_self Q hQ0
  have hp := (Matrix.le_iff.mp hQ1).mul_mul_conjTranspose_same S
  apply Matrix.le_iff.mpr
  have heq : S * (1 - Q) * Sᴴ = Q - Q * Q := by
    rw [hS, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, ← hSS]
    simp only [Matrix.mul_assoc]
  rwa [heq] at hp
lemma projectionOfImageProjection
    (Ψ : Matrix b b ℂ →ₗ[ℂ] Matrix a a ℂ)
    (σ : Matrix a a ℂ) (τ : Matrix b b ℂ) (hτ : τ.PosDef)
    (hpos : ∀ D : Matrix b b ℂ, 0 ≤ D → 0 ≤ Ψ D)
    (hstate : ∀ D : Matrix b b ℂ, (σ * Ψ D).trace = (τ * D).trace)
    (hschwarz : ∀ D : Matrix b b ℂ, (Ψ D)ᴴ * Ψ D ≤ Ψ (Dᴴ * D))
    (P : Matrix a a ℂ) (hP : P.IsHermitian) (hPP : P * P = P)
    (Q : Matrix b b ℂ) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) (hQP : Ψ Q = P) :
    Q.IsHermitian ∧ Q * Q = Q := by
  have hQ : Q.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hQ0).isHermitian
  have hle : Q * Q ≤ Q := effectSquareLe Q hQ0 hQ1
  have hs : P ≤ Ψ (Q * Q) := by
    simpa only [hQP, hP.eq, hQ.eq, hPP] using hschwarz Q
  have hp : 0 ≤ Ψ (Q - Q * Q) := hpos _ (sub_nonneg.mpr hle)
  have hn : Ψ (Q - Q * Q) ≤ 0 := by
    rw [map_sub, hQP]
    exact sub_nonpos.mpr hs
  have hz : Ψ (Q - Q * Q) = 0 := le_antisymm hn hp
  have htrace : (τ * (Q - Q * Q)).trace = 0 := by
    rw [← hstate, hz, Matrix.mul_zero, Matrix.trace_zero]
  have heq : Q - Q * Q = 0 :=
    D5.S3.Quantum.FixedPointProjection.Faithful.faithfulTraceZero τ _ hτ (Matrix.le_iff.mp hle) htrace
  exact ⟨hQ, (sub_eq_zero.mp heq).symm⟩
end D5.S3.Quantum.FixedPointProjection.Transport
end
end r2_projection_transport
