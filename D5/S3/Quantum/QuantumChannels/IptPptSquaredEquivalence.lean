/- GID: D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equivalence of complex PPT-squared and real and complex IPT-squared. -/

/-
result
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#15391; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15525
Escape audit unfinished for weighted_psd: https://github.com/the-omega-institute/trureturing/issues/17573
Escape audit unfinished for prepare_eb: https://github.com/the-omega-institute/trureturing/issues/16693
Direct frozen dependencies (declaration statement_id):
D5/S3/Quantum/Foundation/FiniteKrausChannel.MatrixMap; sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7
D5/S3/Quantum/Foundation/FiniteKrausChannel.IsCompletelyPositive; sha256:31bd68fc3c839750d1a8ac1474555b08fcd9579b1627c81db36a58f3172e1252
D5/S3/Quantum/Foundation/FiniteKrausChannel.add; sha256:9ac4c5b7856928083ae6aacb766fd3eb958b2c365a91db6b7fea5d4fa8fcf6e4
D5/S3/Quantum/Foundation/FiniteKrausChannel.kron; sha256:6bbbe42180d7cde8ee171b8a1aeeb16449194862345f2042d95ec7c0b2055471
D5/S3/Quantum/Foundation/FiniteKrausChannel.kron_def; sha256:0a066df1b1de64e4fda175d1ac776d744674a6465abc8a7f13b12f185ce29405
D5/S3/Quantum/Foundation/FiniteKrausChannel.of_kraus; sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287
D5/S3/Quantum/Foundation/FiniteKrausChannel.of_kraus_isCompletelyPositive; sha256:522daaecff9970808def6ecdd938d4b89107d2820c79bafbf378ab083767f57f
D5/S3/Weil/Probability/FiniteGaussianSchoenberg.ofReal_posSemidef; sha256:e43b63bc2ba962082673f10ac6003f58de8e5074d7a6467d794c4842e8856cd3
The auxiliary theorems have proof_shape: bind-only and escape_witness: none.
Each auxiliary theorem is consumed by another declaration in the elaborated proof terms.
FiniteKrausRepresentation is closed and unregistered; state membership is not an import prerequisite.
The claim is (PPT2C ↔ IPT2 ℂ) ∧ (IPT2 ℂ ↔ IPT2 ℝ), with amplification
and complete positivity supplied by MatrixMap.kron and MatrixMap.IsCompletelyPositive;
kron_id_apply supplies their coordinate correspondence to the source expressions.
FiniteKrausRepresentation supplies MatrixMap.choi_matrix, choi_matrix_inj,
choi_matrix_eq_map_proj and choi_PSD_iff_CP_map. The source's input-first Choi
order is obtained by submatrix Prod.swap Prod.swap.
The generic separability and map predicates use RCLike scalars.
The zero-dimensional cases are vacuous; positive dimensions are the source domains.
The flag coordinates use (finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm.
-/

import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Weil.Probability.FiniteGaussianSchoenberg
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence
variable {𝕜 : Type} [RCLike 𝕜] {n m p r : ℕ}
/-- Finite convex mixtures of product density matrices. -/
def IsSeparable {X Y : Type*} [Fintype X] [Fintype Y] (ρ : Matrix (X × Y) (X × Y) ℂ) : Prop :=
  ∃ (n : ℕ) (p : Fin n → ℝ) (σ : Fin n → Matrix X X ℂ) (τ : Fin n → Matrix Y Y ℂ),
    (∀ t, 0 ≤ p t) ∧
      (∑ t, p t = 1) ∧
      (∀ t, ((σ t).PosSemidef ∧ (σ t).trace = 1) ∧ ((τ t).PosSemidef ∧ (τ t).trace = 1)) ∧
      ρ = ∑ t, (p t : ℂ) • (σ t ⊗ₖ τ t)

def SEP (𝕜 : Type) [RCLike 𝕜] (m r : ℕ) :
    Set (Matrix (Fin m × Fin r) (Fin m × Fin r) 𝕜) :=
  {X | ∃ (k : ℕ) (x : Fin k → Fin m → 𝕜) (y : Fin k → Fin r → 𝕜),
    X = ∑ j, Matrix.kroneckerMap (· * ·)
      (Matrix.vecMulVec (x j) (star (x j)))
      (Matrix.vecMulVec (y j) (star (y j)))}
def IsEB (Phi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜) : Prop :=
  ∀ r (P : Matrix (Fin n × Fin r) (Fin n × Fin r) 𝕜),
    P.PosSemidef → (MatrixMap.kron Phi (LinearMap.id : MatrixMap (Fin r) (Fin r) _)) P ∈ SEP 𝕜 m r
def ptFirst (C : Matrix (Fin n × Fin m) (Fin n × Fin m) 𝕜) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) 𝕜 :=
  fun a b => C (b.1, a.2) (a.1, b.2)
def IsPPT (Phi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜) : Prop :=
  MatrixMap.IsCompletelyPositive Phi ∧ (ptFirst (((MatrixMap.choi_matrix Phi).submatrix Prod.swap Prod.swap))).PosSemidef
def IsIPT (Phi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜) : Prop :=
  MatrixMap.IsCompletelyPositive Phi ∧ ptFirst (((MatrixMap.choi_matrix Phi).submatrix Prod.swap Prod.swap)) = ((MatrixMap.choi_matrix Phi).submatrix Prod.swap Prod.swap)
def PPT2C : Prop :=
  ∀ n (Phi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ), IsPPT Phi → IsEB (Phi ∘ₗ Phi)
def IPT2 (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∀ n (Phi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin n) (Fin n) 𝕜), IsIPT Phi → IsEB (Phi ∘ₗ Phi)
def claim : Prop := (PPT2C ↔ IPT2 ℂ) ∧ (IPT2 ℂ ↔ IPT2 ℝ)
private theorem map_expand (Phi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜) (A : Matrix (Fin n) (Fin n) 𝕜) :
    Phi A = ∑ i, ∑ j, A i j • Phi (Matrix.single i j 1) := by
  have he : A = ∑ i, ∑ j, A i j • Matrix.single i j (1 : 𝕜) := by
    simpa [Matrix.smul_single, smul_eq_mul] using Matrix.matrix_eq_sum_single A
  nth_rw 1 [he]
  simp only [map_sum, map_smul]
theorem kron_id_apply (Phi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜) (r : ℕ)
    (P : Matrix (Fin n × Fin r) (Fin n × Fin r) 𝕜) (a b : Fin m × Fin r) :
    MatrixMap.kron Phi (LinearMap.id : MatrixMap (Fin r) (Fin r) 𝕜) P a b =
      Phi (fun i j => P (i, a.2) (j, b.2)) a.1 b.1 := by
  rcases a with ⟨a,u⟩
  rcases b with ⟨b,v⟩
  symm
  rw [MatrixMap.kron_def]
  have he := congrFun (congrFun (map_expand Phi (fun i j => P (i,u) (j,v))) a) b
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at he
  rw [he]
  simp only [LinearMap.id_apply, Matrix.single, Matrix.of_apply, ite_and, mul_ite,
    mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single u]
  · rw [Finset.sum_eq_single v]
    · simp only [↓reduceIte]
      ring
    · intro vv _ hv
      simp [hv]
    · simp
  · intro uu _ hu
    simp [hu]
  · simp
private theorem sep_swap {X : Matrix (Fin n × Fin m) (Fin n × Fin m) 𝕜}
    (hX : X ∈ SEP 𝕜 n m) :
    X.submatrix Prod.swap Prod.swap ∈ SEP 𝕜 m n := by
  obtain ⟨k, x, y, rfl⟩ := hX
  refine ⟨k, y, x, ?_⟩
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.kroneckerMap_apply,
    Matrix.vecMulVec_apply, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _
private theorem choi_of_eb (Phi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜) (h : IsEB Phi) :
    (MatrixMap.choi_matrix Phi).submatrix Prod.swap Prod.swap ∈ SEP 𝕜 n m := by
  have hs := h n (Matrix.vecMulVec (fun a : Fin n × Fin n => if a.1 = a.2 then (1 : 𝕜) else 0)
    (star (fun a : Fin n × Fin n => if a.1 = a.2 then (1 : 𝕜) else 0)))
    (Matrix.posSemidef_vecMulVec_self_star _)
  change MatrixMap.kron Phi (MatrixMap.id (Fin n) 𝕜)
    (Matrix.vecMulVec (fun a : Fin n × Fin n => if a.1 = a.2 then (1 : 𝕜) else 0)
      (fun a => star (if a.1 = a.2 then (1 : 𝕜) else 0))) ∈ SEP 𝕜 m n at hs
  rw [← MatrixMap.choi_matrix_eq_map_proj] at hs
  exact sep_swap hs
theorem choi_psd_of_cp (Phi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜)
    (h : MatrixMap.IsCompletelyPositive Phi) :
    ((MatrixMap.choi_matrix Phi).submatrix Prod.swap Prod.swap).PosSemidef :=
  ((MatrixMap.choi_PSD_iff_CP_map Phi).mp h).submatrix Prod.swap
private theorem ipt_ppt {Phi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜} (h : IsIPT Phi) : IsPPT Phi :=
  ⟨h.1, h.2.symm ▸ choi_psd_of_cp Phi h.1⟩
private theorem ppt2c_ipt2c (h : PPT2C) : IPT2 ℂ :=
  fun n Phi hPhi => h n Phi (ipt_ppt hPhi)
private theorem ampl_comp (Phi : Matrix (Fin m) (Fin m) 𝕜 →ₗ[𝕜] Matrix (Fin p) (Fin p) 𝕜) (Psi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜) (r : ℕ)
    (P : Matrix (Fin n × Fin r) (Fin n × Fin r) 𝕜) :
    (MatrixMap.kron (Phi ∘ₗ Psi) (LinearMap.id : MatrixMap (Fin r) (Fin r) _)) P = (MatrixMap.kron Phi (LinearMap.id : MatrixMap (Fin r) (Fin r) _)) ((MatrixMap.kron Psi (LinearMap.id : MatrixMap (Fin r) (Fin r) _)) P) := by
  ext a b
  simp only [kron_id_apply, LinearMap.comp_apply]
theorem cp_comp {Phi : Matrix (Fin m) (Fin m) 𝕜 →ₗ[𝕜] Matrix (Fin p) (Fin p) 𝕜} {Psi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜}
    (hPhi : MatrixMap.IsCompletelyPositive Phi) (hPsi : MatrixMap.IsCompletelyPositive Psi) : MatrixMap.IsCompletelyPositive (Phi ∘ₗ Psi) := by
  intro r P hP
  rw [ampl_comp]
  exact hPhi r (hPsi r hP)
private theorem eb_pre {Phi : Matrix (Fin m) (Fin m) 𝕜 →ₗ[𝕜] Matrix (Fin p) (Fin p) 𝕜} {Psi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜}
    (hPhi : IsEB Phi) (hPsi : MatrixMap.IsCompletelyPositive Psi) : IsEB (Phi ∘ₗ Psi) := by
  intro r P hP
  rw [ampl_comp]
  exact hPhi r _ (hPsi r hP)
private theorem psd_rank_sum {I : Type} [Fintype I] [DecidableEq I]
    (C : Matrix I I 𝕜) (hC : C.PosSemidef) :
    ∃ x : I → I → 𝕜, C = ∑ j, (fun x => Matrix.vecMulVec x (star x)) (x j) := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_mul_star_self.mp
    (Matrix.nonneg_iff_posSemidef.mpr hC)
  refine ⟨fun j i => B i j, ?_⟩
  rw [hB]
  ext i j
  simp [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.sum_apply, Matrix.vecMulVec_apply]
private theorem sep_of_family {I : Type} [Fintype I]
    (x : I → Fin n → 𝕜) (y : I → Fin m → 𝕜) :
    (∑ j, (Matrix.kroneckerMap (· * ·)) ((fun x => Matrix.vecMulVec x (star x)) (x j)) ((fun x => Matrix.vecMulVec x (star x)) (y j))) ∈ SEP 𝕜 n m := by
  classical
  let e := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I, fun j => x (e j), fun j => y (e j), ?_⟩
  exact (e.sum_comp _).symm
private theorem sep_psd_product (A : Matrix (Fin n) (Fin n) 𝕜)
    (B : Matrix (Fin m) (Fin m) 𝕜) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.kroneckerMap (· * ·)) A B ∈ SEP 𝕜 n m := by
  obtain ⟨x, rfl⟩ := psd_rank_sum A hA
  obtain ⟨y, rfl⟩ := psd_rank_sum B hB
  have hs := sep_of_family (fun j : Fin n × Fin m => x j.1) (fun j => y j.2)
  convert hs using 1
  ext a b
  simp only [Matrix.kroneckerMap_apply, Matrix.sum_apply, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
private theorem sep_sum {I : Type} [Fintype I]
    (F : I → Matrix (Fin n × Fin m) (Fin n × Fin m) 𝕜)
    (hF : ∀ j, F j ∈ SEP 𝕜 n m) : (∑ j, F j) ∈ SEP 𝕜 n m := by
  classical
  choose k x y h using hF
  have hs := sep_of_family (fun j : Σ i : I, Fin (k i) => x j.1 j.2)
    (fun j => y j.1 j.2)
  convert hs using 1
  rw [Fintype.sum_sigma]
  exact Finset.sum_congr rfl (fun j _ => h j)
private theorem ampl_kron (Phi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜) (r : ℕ)
    (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin r) (Fin r) 𝕜) :
    (MatrixMap.kron Phi (LinearMap.id : MatrixMap (Fin r) (Fin r) _)) ((Matrix.kroneckerMap (· * ·)) A B) = (Matrix.kroneckerMap (· * ·)) (Phi A) B := by
  ext a b
  rw [kron_id_apply]
  have he : (fun i j => A i j * B a.2 b.2) = B a.2 b.2 • A := by
    ext i j
    simp [Matrix.smul_apply, smul_eq_mul, mul_comm]
  change Phi (fun i j => A i j * B a.2 b.2) a.1 b.1 = Phi A a.1 b.1 * B a.2 b.2
  rw [he, map_smul]
  simp [Matrix.smul_apply, smul_eq_mul, mul_comm]
private theorem cp_pos {Phi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜} (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (A : Matrix (Fin n) (Fin n) 𝕜) (hA : A.PosSemidef) : (Phi A).PosSemidef := by
  have hs := hPhi 1
    (hA.kronecker Matrix.PosSemidef.one)
  rw [ampl_kron] at hs
  have ht := hs.submatrix (fun i : Fin m => (i, 0))
  have he : ((Matrix.kroneckerMap (· * ·)) (Phi A) (1 : Matrix (Fin 1) (Fin 1) 𝕜)).submatrix
      (fun i : Fin m => (i, 0)) (fun i : Fin m => (i, 0)) = Phi A := by
    ext i j
    simp [Matrix.kroneckerMap_apply, Matrix.submatrix_apply]
  rw [he] at ht
  exact ht
private theorem ampl_sum (Phi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜) (r : ℕ) {I : Type} [Fintype I]
    (F : I → Matrix (Fin n × Fin r) (Fin n × Fin r) 𝕜) :
    (MatrixMap.kron Phi (LinearMap.id : MatrixMap (Fin r) (Fin r) _)) (∑ j, F j) = ∑ j, (MatrixMap.kron Phi (LinearMap.id : MatrixMap (Fin r) (Fin r) _)) (F j) := by
  exact map_sum _ _ _
private theorem sep_ampl {Phi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜} (hPhi : MatrixMap.IsCompletelyPositive Phi) (r : ℕ)
    {X : Matrix (Fin n × Fin r) (Fin n × Fin r) 𝕜}
    (hX : X ∈ SEP 𝕜 n r) : (MatrixMap.kron Phi (LinearMap.id : MatrixMap (Fin r) (Fin r) _)) X ∈ SEP 𝕜 m r := by
  obtain ⟨k, x, y, rfl⟩ := hX
  rw [ampl_sum]
  apply sep_sum
  intro j
  rw [ampl_kron]
  apply sep_psd_product
  · exact cp_pos hPhi _ (Matrix.posSemidef_vecMulVec_self_star _)
  · exact Matrix.posSemidef_vecMulVec_self_star _
private theorem eb_post {Phi : Matrix (Fin m) (Fin m) 𝕜 →ₗ[𝕜] Matrix (Fin p) (Fin p) 𝕜} {Psi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜}
    (hPhi : MatrixMap.IsCompletelyPositive Phi) (hPsi : IsEB Psi) : IsEB (Phi ∘ₗ Psi) := by
  intro r P hP
  rw [ampl_comp]
  exact sep_ampl hPhi r (hPsi r P hP)
def weighted (M : Matrix (Fin n) (Fin n) 𝕜)
    (P : Matrix (Fin n × Fin r) (Fin n × Fin r) 𝕜) : Matrix (Fin r) (Fin r) 𝕜 :=
  fun u v =>
    let Q : Matrix (Fin n) (Fin n) 𝕜 := fun i j => P (i, u) (j, v)
    Matrix.trace (M * Q)
private def columnEmbed (x : Fin n → 𝕜) : Matrix (Fin n × Fin r) (Fin r) 𝕜 :=
  (Matrix.kroneckerMap (· * ·) (Matrix.replicateCol (Fin 1) x)
    (1 : Matrix (Fin r) (Fin r) 𝕜)).submatrix id (fun u => (0,u))
private theorem weighted_rank (x : Fin n → 𝕜)
    (P : Matrix (Fin n × Fin r) (Fin n × Fin r) 𝕜) :
    weighted ((fun x => Matrix.vecMulVec x (star x)) x) P = Matrix.conjTranspose (columnEmbed (r := r) x) * P * columnEmbed (r := r) x := by
  ext u v
  simp only [weighted, Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply,
    Pi.star_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, columnEmbed, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Matrix.replicateCol_apply, Matrix.one_apply, id_eq, mul_ite, mul_one, mul_zero,
    Fintype.sum_prod_type, apply_ite, star_zero, Finset.sum_mul, Finset.mul_sum]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
private theorem weighted_sum {I : Type} [Fintype I]
    (M : I → Matrix (Fin n) (Fin n) 𝕜)
    (P : Matrix (Fin n × Fin r) (Fin n × Fin r) 𝕜) :
    weighted (∑ j, M j) P = ∑ j, weighted (M j) P := by
  ext u v
  simp [weighted, Matrix.sum_mul, Matrix.trace_sum, Matrix.sum_apply]
theorem weighted_psd (M : Matrix (Fin n) (Fin n) 𝕜)
    (P : Matrix (Fin n × Fin r) (Fin n × Fin r) 𝕜)
    (hM : M.PosSemidef) (hP : P.PosSemidef) : (weighted M P).PosSemidef := by
  obtain ⟨x, rfl⟩ := psd_rank_sum M hM
  rw [weighted_sum]
  apply Matrix.posSemidef_sum
  intro j _
  rw [weighted_rank]
  exact hP.conjTranspose_mul_mul_same _
def HasPrepare (Phi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜) : Prop :=
  ∃ (k : ℕ) (M : Fin k → Matrix (Fin n) (Fin n) 𝕜)
    (N : Fin k → Matrix (Fin m) (Fin m) 𝕜),
    (∀ j, (M j).PosSemidef ∧ (N j).PosSemidef) ∧
    ∀ A, Phi A = ∑ j, Matrix.trace (M j * A) • N j
theorem prepare_eb (Phi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜) (hPhi : HasPrepare Phi) : IsEB Phi := by
  obtain ⟨k, M, N, hMN, hPhi⟩ := hPhi
  intro r P hP
  have he : (MatrixMap.kron Phi (LinearMap.id : MatrixMap (Fin r) (Fin r) _)) P = ∑ j, (Matrix.kroneckerMap (· * ·)) (N j) (weighted (M j) P) := by
    ext a b
    simp only [kron_id_apply, hPhi, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.kroneckerMap_apply, weighted]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  rw [he]
  apply sep_sum
  intro j
  exact sep_psd_product _ _ (hMN j).2 (weighted_psd _ _ (hMN j).1 hP)
private theorem sum_rotate {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    (f : I → J → K → 𝕜) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ j, ∑ i, f i j k := by
  calc
    _ = ∑ i, ∑ k, ∑ j, f i j k := Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ k, ∑ i, ∑ j, f i j k := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun k _ => Finset.sum_comm)
private theorem separable_choi_prepare (Phi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜) (hC : ((MatrixMap.choi_matrix Phi).submatrix Prod.swap Prod.swap) ∈ SEP 𝕜 n m) :
    HasPrepare Phi := by
  obtain ⟨k, x, y, hC⟩ := hC
  refine ⟨k, (fun j => (fun x => Matrix.vecMulVec x (star x)) (star (x j))), (fun j => (fun x => Matrix.vecMulVec x (star x)) (y j)),
    (fun j => ⟨Matrix.posSemidef_vecMulVec_self_star _,
      Matrix.posSemidef_vecMulVec_self_star _⟩), ?_⟩
  intro A
  ext a b
  have hc (i j : Fin n) : Phi (Matrix.single i j 1) a b =
      ∑ t, (x t i * star (x t j)) * (y t a * star (y t b)) := by
    have h := congrFun (congrFun hC (i, a)) (j, b)
    simpa [MatrixMap.choi_matrix, Matrix.submatrix_apply, Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.vecMulVec_apply] using h
  rw [map_expand]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hc, Finset.mul_sum,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, star_star, Finset.sum_mul]
  rw [sum_rotate]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring
private theorem eb_of_choi (Phi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜) (hC : ((MatrixMap.choi_matrix Phi).submatrix Prod.swap Prod.swap) ∈ SEP 𝕜 n m) : IsEB Phi :=
  prepare_eb Phi (separable_choi_prepare Phi hC)
private theorem eb_iff_choi (Phi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜) : IsEB Phi ↔ ((MatrixMap.choi_matrix Phi).submatrix Prod.swap Prod.swap) ∈ SEP 𝕜 n m :=
  ⟨choi_of_eb Phi, eb_of_choi Phi⟩
private theorem sep_complex_of_real {X : Matrix (Fin n × Fin m) (Fin n × Fin m) ℝ}
    (hX : X ∈ SEP ℝ n m) : X.map Complex.ofReal ∈ SEP ℂ n m := by
  obtain ⟨k,x,y,rfl⟩ := hX
  refine ⟨k, (fun t i => (x t i : ℂ)), (fun t i => (y t i : ℂ)), ?_⟩
  ext a b
  simp [Matrix.map_apply, Matrix.sum_apply, Matrix.kroneckerMap_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, ← Complex.ofReal_sum, ← Complex.ofReal_mul]
private theorem pair_real_average (x z y w : ℂ) :
    (x * star z * (y * star w)).re + (z * star x * (y * star w)).re =
    2 * (x.re * z.re + x.im * z.im) * (y.re * w.re + y.im * w.im) := by
  simp [Complex.star_def, Complex.mul_re, Complex.mul_im]
  ring
private theorem sep_real_of_complex_ipt (X : Matrix (Fin n × Fin m) (Fin n × Fin m) ℝ)
    (hC : X.map Complex.ofReal ∈ SEP ℂ n m) (hT : ptFirst X = X) :
    X ∈ SEP ℝ n m := by
  obtain ⟨k,x,y,hC⟩ := hC
  have hAvg (a b : Fin n × Fin m) :
      X a b = ∑ t, ((x t a.1).re * (x t b.1).re + (x t a.1).im * (x t b.1).im) *
        ((y t a.2).re * (y t b.2).re + (y t a.2).im * (y t b.2).im) := by
    have h1 := congrArg Complex.re (congrFun (congrFun hC a) b)
    have h2 := congrArg Complex.re (congrFun (congrFun hC (b.1,a.2)) (a.1,b.2))
    have ht := congrFun (congrFun hT a) b
    change X (b.1,a.2) (a.1,b.2) = X a b at ht
    simp only [Matrix.map_apply, Complex.ofReal_re, Matrix.sum_apply, Complex.re_sum,
      Matrix.kroneckerMap_apply, Matrix.vecMulVec_apply, Pi.star_apply] at h1 h2
    rw [ht] at h2
    have he : 2 * X a b = 2 * (∑ t,
        ((x t a.1).re * (x t b.1).re + (x t a.1).im * (x t b.1).im) *
        ((y t a.2).re * (y t b.2).re + (y t a.2).im * (y t b.2).im)) := by
      calc
        _ = X a b + X a b := by ring
        _ = _ := by
          nth_rw 1 [h1]
          rw [h2, ← Finset.sum_add_distrib, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t _
          simpa only [mul_assoc] using pair_real_average (x t a.1) (x t b.1)
            (y t a.2) (y t b.2)
    linarith
  have hs := sep_of_family
    (fun t : Fin k × Fin 2 × Fin 2 => fun i => (if t.2.1 = 0 then (x t.1 i).re else (x t.1 i).im))
    (fun t => fun j => (if t.2.2 = 0 then (y t.1 j).re else (y t.1 j).im))
  convert hs using 1
  ext a b
  rw [hAvg]
  simp only [Matrix.sum_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.kroneckerMap_apply, Matrix.vecMulVec_apply, Pi.star_apply, star_trivial,
    Fin.zero_eta, Fin.isValue, ↓reduceIte, one_ne_zero]
  apply Finset.sum_congr rfl
  intro t _
  ring
private theorem sep_psd {𝕜 : Type} [RCLike 𝕜]
    {X : Matrix (Fin n × Fin m) (Fin n × Fin m) 𝕜} (hX : X ∈ SEP 𝕜 n m) :
    X.PosSemidef := by
  obtain ⟨k,x,y,rfl⟩ := hX
  apply Matrix.posSemidef_sum
  intro j _
  exact (Matrix.posSemidef_vecMulVec_self_star (x j)).kronecker
    (Matrix.posSemidef_vecMulVec_self_star (y j))
private theorem sep_real_ipt {X : Matrix (Fin n × Fin m) (Fin n × Fin m) ℝ}
    (hX : X ∈ SEP ℝ n m) : ptFirst X = X := by
  obtain ⟨k,x,y,rfl⟩ := hX
  ext a b
  simp only [ptFirst, Matrix.sum_apply, Matrix.kroneckerMap_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro j _
  ring
private def CSEP (n m : ℕ) : Set (Matrix (Fin n × Fin m) (Fin n × Fin m) ℝ) :=
  {X | X.map Complex.ofReal ∈ SEP ℂ n m ∧ X.PosSemidef}
private def IPTState (n m : ℕ) : Set (Matrix (Fin n × Fin m) (Fin n × Fin m) ℝ) :=
  {X | X.PosSemidef ∧ ptFirst X = X}
private theorem csep_inter_ipt : CSEP n m ∩ IPTState n m = SEP ℝ n m := by
  ext X
  constructor
  · intro h
    exact sep_real_of_complex_ipt X h.1.1 h.2.2
  · intro h
    exact ⟨⟨sep_complex_of_real h, sep_psd h⟩, ⟨sep_psd h, sep_real_ipt h⟩⟩
private theorem choi_tmap (Phi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜) :
    ((MatrixMap.choi_matrix (Phi ∘ₗ (Matrix.transposeLinearEquiv (Fin n) (Fin n) 𝕜 𝕜).toLinearMap)).submatrix Prod.swap Prod.swap) = ptFirst (((MatrixMap.choi_matrix Phi).submatrix Prod.swap Prod.swap)) := by
  ext a b
  change Phi (Matrix.single a.1 b.1 (1 : 𝕜))ᵀ a.2 b.2 = _
  simp [Matrix.transpose_single, MatrixMap.choi_matrix, Matrix.submatrix_apply, ptFirst]
private theorem ipt_input {Phi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜} (hPhi : IsIPT Phi) :
    Phi ∘ₗ (Matrix.transposeLinearEquiv (Fin n) (Fin n) 𝕜 𝕜).toLinearMap = Phi :=
  MatrixMap.choi_matrix_inj (by
    have he := congrArg (fun C => C.submatrix Prod.swap Prod.swap) ((choi_tmap Phi).trans hPhi.2)
    ext ⟨a,u⟩ ⟨b,v⟩
    exact congrFun (congrFun he (a,u)) (b,v))
private theorem ipt_comp {Phi : Matrix (Fin m) (Fin m) 𝕜 →ₗ[𝕜] Matrix (Fin p) (Fin p) 𝕜} {Psi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜}
    (hPhi : MatrixMap.IsCompletelyPositive Phi) (hPsi : IsIPT Psi) : IsIPT (Phi ∘ₗ Psi) := by
  refine ⟨cp_comp hPhi hPsi.1, ?_⟩
  rw [← choi_tmap, LinearMap.comp_assoc, ipt_input hPsi]
private def complexify (Phi : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ :=
  MatrixMap.of_choi_matrix ((MatrixMap.choi_matrix Phi).map Complex.ofReal)
private theorem complexify_real (Phi : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    complexify Phi (A.map Complex.ofReal) = (Phi A).map Complex.ofReal := by
  ext a b
  have he := congrFun (congrFun (map_expand Phi A) a) b
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at he
  simp [complexify, MatrixMap.of_choi_matrix, MatrixMap.choi_matrix, he, Matrix.map_apply, ← Complex.ofReal_sum, ← Complex.ofReal_mul]
private theorem complexify_choi (Phi : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ) :
    ((MatrixMap.choi_matrix (complexify Phi)).submatrix Prod.swap Prod.swap) = (((MatrixMap.choi_matrix Phi).submatrix Prod.swap Prod.swap)).map Complex.ofReal := by
  ext a b
  have he : (Matrix.single a.1 b.1 (1 : ℝ)).map Complex.ofReal =
      Matrix.single a.1 b.1 (1 : ℂ) := by
    ext i j
    simp only [Matrix.single, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  change complexify Phi (Matrix.single a.1 b.1 1) a.2 b.2 = _
  rw [← he, complexify_real]
  rfl
private theorem real_psd_cast {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (hA : A.PosSemidef) : (A.map Complex.ofReal).PosSemidef :=
  D5.S3.Weil.Probability.FiniteGaussianSchoenberg.ofReal_posSemidef A hA
private theorem real_part_psd {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.PosSemidef) : (A.map Complex.re).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    have he := congrArg Complex.re (congrFun (congrFun hA.isHermitian i) j)
    simpa [Matrix.conjTranspose_apply, Matrix.map_apply] using he
  · intro x
    have hp := hA.re_dotProduct_nonneg (fun i => (x i : ℂ))
    simpa [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply,
      Complex.mul_re, Complex.mul_im] using hp
private theorem complexify_cp {Phi : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ} (hPhi : MatrixMap.IsCompletelyPositive Phi) : MatrixMap.IsCompletelyPositive (complexify Phi) := by
  apply (MatrixMap.choi_PSD_iff_CP_map _).mpr
  apply (Matrix.posSemidef_submatrix_equiv (Equiv.prodComm _ _)).mp
  change ((MatrixMap.choi_matrix (complexify Phi)).submatrix Prod.swap Prod.swap).PosSemidef
  rw [complexify_choi]
  exact real_psd_cast _ ((choi_psd_of_cp Phi hPhi))
private theorem complexify_ipt {Phi : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ} (hPhi : IsIPT Phi) : IsIPT (complexify Phi) := by
  refine ⟨complexify_cp hPhi.1, ?_⟩
  rw [complexify_choi]
  have he : ptFirst ((((MatrixMap.choi_matrix Phi).submatrix Prod.swap Prod.swap)).map Complex.ofReal) =
      (ptFirst (((MatrixMap.choi_matrix Phi).submatrix Prod.swap Prod.swap))).map Complex.ofReal := rfl
  rw [he, hPhi.2]
private theorem complexify_comp (Phi : Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] Matrix (Fin p) (Fin p) ℝ) (Psi : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ) :
    complexify (Phi ∘ₗ Psi) = complexify Phi ∘ₗ complexify Psi := by
  apply MatrixMap.choi_matrix_inj
  ext ⟨a,u⟩ ⟨b,v⟩
  let a := (u,a)
  let b := (v,b)
  have he : (Matrix.single a.1 b.1 (1 : ℝ)).map Complex.ofReal =
      Matrix.single a.1 b.1 (1 : ℂ) := by
    ext i j
    simp only [Matrix.single, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  simp only [MatrixMap.choi_matrix, Matrix.submatrix_apply, LinearMap.comp_apply]
  rw [← he, complexify_real, complexify_real, complexify_real]
  rfl
private theorem complexify_eb {Phi : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ} (hPhi : IsEB Phi) : IsEB (complexify Phi) := by
  apply (eb_iff_choi _).mpr
  rw [complexify_choi]
  exact sep_complex_of_real ((eb_iff_choi _).mp hPhi)
private theorem eb_real_of_complexify {Phi : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ} (hPhi : IsIPT Phi)
    (hEB : IsEB (complexify Phi)) : IsEB Phi := by
  apply (eb_iff_choi _).mpr
  rw [← csep_inter_ipt]
  refine ⟨⟨?_, (choi_psd_of_cp Phi hPhi.1)⟩, ⟨(choi_psd_of_cp Phi hPhi.1), hPhi.2⟩⟩
  rw [← complexify_choi]
  exact (eb_iff_choi _).mp hEB
private theorem ipt2c_ipt2r (h : IPT2 ℂ) : IPT2 ℝ := by
  intro n Phi hPhi
  apply eb_real_of_complexify (ipt_comp hPhi.1 hPhi)
  rw [complexify_comp]
  exact h n _ (complexify_ipt hPhi)
private def embedFlag (n : ℕ) (v : Fin 2 → ℂ) : Matrix (Fin (2 * n)) (Fin n) ℂ :=
  (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin n) (Fin n) ℂ)
    (Matrix.replicateCol (Fin 1) v)).submatrix
    ((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm) (fun i => (i,0))
private theorem sum_flag (f : Fin (2 * n) → ℂ) :
    ∑ a, f a = ∑ i : Fin n, ∑ u : Fin 2, f ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)).symm (i,u)) := by
  rw [← (((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)).symm.sum_comp f, Fintype.sum_prod_type]
private theorem embed_compress (v : Fin 2 → ℂ) (X : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) (i j : Fin n) :
    ((embedFlag n v)ᴴ * X * embedFlag n v) i j =
    ∑ u : Fin 2, ∑ w : Fin 2, star (v u) *
      X ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)).symm (i,u)) ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)).symm (j,w)) * v w := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [sum_flag]
  simp_rw [sum_flag]
  simp [embedFlag, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Matrix.replicateCol_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul, apply_ite, ite_mul, mul_ite, Finset.sum_mul]
  ring
private theorem embed_put (v : Fin 2 → ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (a b : Fin (2 * n)) :
    (embedFlag n v * A * (embedFlag n v)ᴴ) a b =
    A (((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm) a).1 (((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm) b).1 *
      v (((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm) a).2 * star (v (((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm) b).2) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, embedFlag, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Matrix.replicateCol_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul, apply_ite,
    ite_mul, mul_ite, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm]
private def bp (n : ℕ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  (1/2 : ℂ) • MatrixMap.of_kraus
    (fun _ : Fin 1 => (embedFlag n (![1, Complex.I] : Fin 2 → ℂ))ᴴ)
    (fun _ : Fin 1 => (embedFlag n (![1, Complex.I] : Fin 2 → ℂ))ᴴ)
private theorem bp_apply (X : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) (i j : Fin n) :
    bp n X i j = (1/2 : ℂ) *
    (X ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)).symm (i,0)) ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)).symm (j,0)) +
     Complex.I * X ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)).symm (i,0)) ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)).symm (j,1)) -
     Complex.I * X ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)).symm (i,1)) ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)).symm (j,0)) +
     X ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)).symm (i,1)) ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)).symm (j,1))) := by
  simp only [bp, MatrixMap.of_kraus, Fin.sum_univ_one]
  change (1/2 : ℂ) *
    ((embedFlag n (![1, Complex.I] : Fin 2 → ℂ))ᴴ * X * ((embedFlag n (![1, Complex.I] : Fin 2 → ℂ))ᴴ)ᴴ) i j = _
  rw [Matrix.conjTranspose_conjTranspose, embed_compress]
  simp [Fin.sum_univ_two]
  ring_nf
  simp [Complex.I_sq]
private def bm (n : ℕ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  (1/2 : ℂ) • MatrixMap.of_kraus
    (fun _ : Fin 1 => (embedFlag n (![1, -Complex.I] : Fin 2 → ℂ))ᴴ)
    (fun _ : Fin 1 => (embedFlag n (![1, -Complex.I] : Fin 2 → ℂ))ᴴ)
private theorem bm_apply (X : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) (i j : Fin n) :
    bm n X i j = (1/2 : ℂ) *
    (X ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)).symm (i,0)) ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)).symm (j,0)) -
     Complex.I * X ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)).symm (i,0)) ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)).symm (j,1)) +
     Complex.I * X ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)).symm (i,1)) ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)).symm (j,0)) +
     X ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)).symm (i,1)) ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)).symm (j,1))) := by
  simp only [bm, MatrixMap.of_kraus, Fin.sum_univ_one]
  change (1/2 : ℂ) *
    ((embedFlag n (![1, -Complex.I] : Fin 2 → ℂ))ᴴ * X * ((embedFlag n (![1, -Complex.I] : Fin 2 → ℂ))ᴴ)ᴴ) i j = _
  rw [Matrix.conjTranspose_conjTranspose, embed_compress]
  simp [Fin.sum_univ_two]
  ring_nf
  simp [Complex.I_sq]
private def ee (n : ℕ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ := bp n + (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℂ ℂ).toLinearMap ∘ₗ bm n
private def pp : Matrix (Fin 2) (Fin 2) ℂ :=
  (1/2 : ℂ) • Matrix.vecMulVec (![1, Complex.I] : Fin 2 → ℂ) (star (![1, Complex.I] : Fin 2 → ℂ))
private def pm : Matrix (Fin 2) (Fin 2) ℂ :=
  (1/2 : ℂ) • Matrix.vecMulVec (![1, -Complex.I] : Fin 2 → ℂ) (star (![1, -Complex.I] : Fin 2 → ℂ))
private def put (n : ℕ) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ where
  toFun A := (Matrix.kroneckerMap (· * ·) A P).submatrix
    ((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)
    ((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)
  map_add' A B := by ext a b; simp [Matrix.kroneckerMap_apply]; ring
  map_smul' c A := by ext a b; simp [Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]; ring
private def dd (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ := put n pp + put n pm ∘ₗ (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℂ ℂ).toLinearMap
private def gamma (Phi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ →ₗ[ℂ] Matrix (Fin (2*m)) (Fin (2*m)) ℂ :=
  (1/2 : ℂ) • (dd m ∘ₗ Phi ∘ₗ ee n)
private theorem bp_dd (A : Matrix (Fin n) (Fin n) ℂ) : bp n (dd n A) = A := by
  ext i j
  apply Complex.ext <;>
    simp [bp_apply, dd, put, Matrix.kroneckerMap_apply, pp, pm, Matrix.transposeLinearEquiv,
      Complex.mul_re, Complex.mul_im] <;> ring
private theorem bm_dd (A : Matrix (Fin n) (Fin n) ℂ) : bm n (dd n A) = Aᵀ := by
  ext i j
  apply Complex.ext <;>
    simp [bm_apply, dd, put, Matrix.kroneckerMap_apply, pp, pm, Matrix.transposeLinearEquiv,
      Complex.mul_re, Complex.mul_im] <;> ring
private theorem ee_dd (A : Matrix (Fin n) (Fin n) ℂ) : ee n (dd n A) = (2 : ℂ) • A := by
  change bp n (dd n A) + (bm n (dd n A))ᵀ = _
  rw [bp_dd, bm_dd, Matrix.transpose_transpose]
  exact (two_smul ℂ A).symm
private theorem bp_tau (X : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) : bp n Xᵀ = (bm n X)ᵀ := by
  ext i j
  simp [bp_apply, bm_apply, Matrix.transpose_apply]
  ring
private theorem ee_tau (X : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) : ee n Xᵀ = ee n X := by
  have hm := congrArg Matrix.transpose (bp_tau (X := Xᵀ))
  simp only [Matrix.transpose_transpose] at hm
  change bp n Xᵀ + (bm n Xᵀ)ᵀ = bp n X + (bm n X)ᵀ
  rw [bp_tau, ← hm]
  exact add_comm _ _
private theorem tau_dd (A : Matrix (Fin n) (Fin n) ℂ) : (dd n A)ᵀ = dd n A := by
  ext a b
  change A ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)) b).1 ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)) a).1 *
      pp ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)) b).2 ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)) a).2 +
    A ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)) a).1 ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)) b).1 *
      pm ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)) b).2 ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)) a).2 =
    A ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)) a).1 ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)) b).1 *
      pp ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)) a).2 ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)) b).2 +
    A ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)) b).1 ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)) a).1 *
      pm ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)) a).2 ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)) b).2
  have hP : ppᵀ = pm := by ext i j; fin_cases i <;> fin_cases j <;> simp [pp,pm]
  have hM : pmᵀ = pp := by ext i j; fin_cases i <;> fin_cases j <;> simp [pp,pm]
  have h1 := congrFun (congrFun hP ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)) a).2) ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)) b).2
  have h2 := congrFun (congrFun hM ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)) a).2) ((((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm)) b).2
  simp only [Matrix.transpose_apply] at h1 h2
  rw [h1,h2]
  ring
private theorem gamma_comp (Psi : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ) (Phi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    gamma Psi ∘ₗ gamma Phi = gamma (Psi ∘ₗ Phi) := by
  ext A a b
  simp only [gamma, LinearMap.comp_apply, LinearMap.smul_apply, map_smul, ee_dd,
    smul_smul]
  norm_num
private theorem conj_cp (C : Matrix (Fin m) (Fin n) ℂ) :
    MatrixMap.IsCompletelyPositive (MatrixMap.of_kraus (fun _ : Fin 1 => C) (fun _ : Fin 1 => C)) :=
  MatrixMap.of_kraus_isCompletelyPositive _
private theorem cp_half {Phi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ} (hPhi : MatrixMap.IsCompletelyPositive Phi) : MatrixMap.IsCompletelyPositive ((1/2 : ℂ) • Phi) := by
  intro r P hP
  have he : MatrixMap.kron ((1/2 : ℂ) • Phi) (LinearMap.id : MatrixMap (Fin r) (Fin r) ℂ) P =
      (1/2 : ℂ) • MatrixMap.kron Phi LinearMap.id P := by
    ext a b
    simp only [kron_id_apply, LinearMap.smul_apply, Matrix.smul_apply]
  rw [he]
  have hc : (0 : ℂ) ≤ (1/2 : ℂ) := by
    have he : (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) := by norm_num
    rw [he]
    exact Complex.zero_le_real.mpr (by norm_num)
  exact (hPhi r hP).smul hc
private theorem put_pp_conj : put n pp = (1/2 : ℂ) • MatrixMap.of_kraus (fun _ : Fin 1 => embedFlag n (![1, Complex.I] : Fin 2 → ℂ)) (fun _ : Fin 1 => embedFlag n (![1, Complex.I] : Fin 2 → ℂ)) := by
  ext A a b
  simp only [MatrixMap.of_kraus, Fin.sum_univ_one]
  change A (((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm) a).1 (((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm) b).1 * pp (((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm) a).2 (((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm) b).2 =
    (1/2 : ℂ) * (embedFlag n (![1, Complex.I] : Fin 2 → ℂ) * A * (embedFlag n (![1, Complex.I] : Fin 2 → ℂ))ᴴ) a b
  rw [embed_put]
  have he : pp = (1/2 : ℂ) • (fun x => Matrix.vecMulVec x (star x)) (![1, Complex.I] : Fin 2 → ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pp, Complex.star_def] <;> ring
  rw [he]
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul]
  ring
private theorem put_pm_conj : put n pm = (1/2 : ℂ) • MatrixMap.of_kraus (fun _ : Fin 1 => embedFlag n (![1, -Complex.I] : Fin 2 → ℂ)) (fun _ : Fin 1 => embedFlag n (![1, -Complex.I] : Fin 2 → ℂ)) := by
  ext A a b
  simp only [MatrixMap.of_kraus, Fin.sum_univ_one]
  change A (((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm) a).1 (((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm) b).1 * pm (((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm) a).2 (((finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm) b).2 =
    (1/2 : ℂ) * (embedFlag n (![1, -Complex.I] : Fin 2 → ℂ) * A * (embedFlag n (![1, -Complex.I] : Fin 2 → ℂ))ᴴ) a b
  rw [embed_put]
  have he : pm = (1/2 : ℂ) • (fun x => Matrix.vecMulVec x (star x)) (![1, -Complex.I] : Fin 2 → ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pm, Complex.star_def] <;> ring
  rw [he]
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul]
  ring
private theorem bp_cp : MatrixMap.IsCompletelyPositive (bp n) := by unfold bp; exact cp_half (conj_cp _)
private theorem bm_cp : MatrixMap.IsCompletelyPositive (bm n) := by unfold bm; exact cp_half (conj_cp _)
private theorem put_pp_cp : MatrixMap.IsCompletelyPositive (put n pp) := by rw [put_pp_conj]; exact cp_half (conj_cp _)
private theorem put_pm_cp : MatrixMap.IsCompletelyPositive (put n pm) := by rw [put_pm_conj]; exact cp_half (conj_cp _)
theorem cp_double_tau {Phi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ} (hPhi : MatrixMap.IsCompletelyPositive Phi) :
    MatrixMap.IsCompletelyPositive ((Matrix.transposeLinearEquiv (Fin m) (Fin m) ℂ ℂ).toLinearMap ∘ₗ Phi ∘ₗ (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℂ ℂ).toLinearMap) := by
  intro r P hP
  have he : (MatrixMap.kron ((Matrix.transposeLinearEquiv (Fin m) (Fin m) ℂ ℂ).toLinearMap ∘ₗ Phi ∘ₗ (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℂ ℂ).toLinearMap) (LinearMap.id : MatrixMap (Fin r) (Fin r) _)) P = ((MatrixMap.kron Phi (LinearMap.id : MatrixMap (Fin r) (Fin r) _)) Pᵀ)ᵀ := by
    ext ⟨a,u⟩ ⟨b,v⟩
    change MatrixMap.kron _ LinearMap.id P (a,u) (b,v) = MatrixMap.kron Phi LinearMap.id Pᵀ (b,v) (a,u)
    rw [kron_id_apply, kron_id_apply]
    rfl
  rw [he]
  exact (hPhi r hP.transpose).transpose
private theorem ppt_input_cp {Phi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ} (hPhi : IsPPT Phi) :
    MatrixMap.IsCompletelyPositive (Phi ∘ₗ (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℂ ℂ).toLinearMap) := by
  apply (MatrixMap.choi_PSD_iff_CP_map _).mpr
  apply (Matrix.posSemidef_submatrix_equiv (Equiv.prodComm _ _)).mp
  change ((MatrixMap.choi_matrix (Phi ∘ₗ (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℂ ℂ).toLinearMap)).submatrix Prod.swap Prod.swap).PosSemidef
  rw [choi_tmap]
  exact hPhi.2
private theorem gamma_four (Phi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    gamma Phi = (1/2 : ℂ) •
      ((put m pp ∘ₗ Phi ∘ₗ bp n) +
       (put m pp ∘ₗ (Phi ∘ₗ (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℂ ℂ).toLinearMap) ∘ₗ bm n) +
       (put m pm ∘ₗ ((Matrix.transposeLinearEquiv (Fin m) (Fin m) ℂ ℂ).toLinearMap ∘ₗ Phi) ∘ₗ bp n) +
       (put m pm ∘ₗ ((Matrix.transposeLinearEquiv (Fin m) (Fin m) ℂ ℂ).toLinearMap ∘ₗ Phi ∘ₗ (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℂ ℂ).toLinearMap) ∘ₗ bm n)) := by
  ext X a b
  simp [gamma, dd, ee, map_add, LinearMap.add_apply, LinearMap.comp_apply]
  ring
private theorem gamma_cp {Phi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ} (hPhi : IsPPT Phi) : MatrixMap.IsCompletelyPositive (gamma Phi) := by
  have hIn := ppt_input_cp hPhi
  have hOut : MatrixMap.IsCompletelyPositive ((Matrix.transposeLinearEquiv (Fin m) (Fin m) ℂ ℂ).toLinearMap ∘ₗ Phi) := by
    have he : (Matrix.transposeLinearEquiv (Fin m) (Fin m) ℂ ℂ).toLinearMap ∘ₗ (Phi ∘ₗ (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℂ ℂ).toLinearMap) ∘ₗ (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℂ ℂ).toLinearMap = (Matrix.transposeLinearEquiv (Fin m) (Fin m) ℂ ℂ).toLinearMap ∘ₗ Phi := by
      ext X a b
      rfl
    rw [← he]
    exact cp_double_tau hIn
  rw [gamma_four]
  apply cp_half
  apply MatrixMap.IsCompletelyPositive.add
  · apply MatrixMap.IsCompletelyPositive.add
    · apply MatrixMap.IsCompletelyPositive.add
      · exact cp_comp put_pp_cp (cp_comp hPhi.1 bp_cp)
      · exact cp_comp put_pp_cp (cp_comp hIn bm_cp)
    · exact cp_comp put_pm_cp (cp_comp hOut bp_cp)
  · exact cp_comp put_pm_cp (cp_comp (cp_double_tau hPhi.1) bm_cp)
private theorem gamma_input (Phi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) (X : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) : gamma Phi Xᵀ = gamma Phi X := by
  simp only [gamma, LinearMap.smul_apply, LinearMap.comp_apply, ee_tau]
private theorem gamma_output (Phi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) (X : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) : (gamma Phi X)ᵀ = gamma Phi X := by
  simp only [gamma, LinearMap.smul_apply, LinearMap.comp_apply, Matrix.transpose_smul, tau_dd]
private theorem gamma_ipt {Phi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ} (hPhi : IsPPT Phi) : IsIPT (gamma Phi) := by
  refine ⟨gamma_cp hPhi, ?_⟩
  ext a b
  change gamma Phi (Matrix.single b.1 a.1 1) a.2 b.2 = gamma Phi (Matrix.single a.1 b.1 1) a.2 b.2
  have he := gamma_input Phi (Matrix.single a.1 b.1 1)
  simpa [Matrix.transpose_single] using congrFun (congrFun he a.2) b.2
private def restrict (Phi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ where
  toFun A := (Phi (A.map Complex.ofReal)).map Complex.re
  map_add' A B := by
    have he : (A+B).map Complex.ofReal = A.map Complex.ofReal + B.map Complex.ofReal := by
      ext i j
      simp
    ext a b
    simp [he, map_add]
  map_smul' c A := by
    have he : (c • A).map Complex.ofReal = (c : ℂ) • A.map Complex.ofReal := by
      ext i j
      simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    ext a b
    simp [he, map_smul, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Complex.mul_re]
private theorem restrict_choi (Phi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    ((MatrixMap.choi_matrix (restrict Phi)).submatrix Prod.swap Prod.swap) = (((MatrixMap.choi_matrix Phi).submatrix Prod.swap Prod.swap)).map Complex.re := by
  ext a b
  have he : (Matrix.single a.1 b.1 (1 : ℝ)).map Complex.ofReal =
      Matrix.single a.1 b.1 (1 : ℂ) := by
    ext i j
    simp only [Matrix.single, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  change (Phi ((Matrix.single a.1 b.1 (1 : ℝ)).map Complex.ofReal) a.2 b.2).re = _
  rw [he]
  rfl
private theorem restrict_cp {Phi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ} (hPhi : MatrixMap.IsCompletelyPositive Phi) : MatrixMap.IsCompletelyPositive (restrict Phi) := by
  apply (MatrixMap.choi_PSD_iff_CP_map _).mpr
  apply (Matrix.posSemidef_submatrix_equiv (Equiv.prodComm _ _)).mp
  change ((MatrixMap.choi_matrix (restrict Phi)).submatrix Prod.swap Prod.swap).PosSemidef
  rw [restrict_choi]
  exact real_part_psd _ ((choi_psd_of_cp Phi hPhi))
private theorem restrict_ipt {Phi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ} (hPhi : IsIPT Phi) : IsIPT (restrict Phi) := by
  refine ⟨restrict_cp hPhi.1, ?_⟩
  rw [restrict_choi]
  have he : ptFirst ((((MatrixMap.choi_matrix Phi).submatrix Prod.swap Prod.swap)).map Complex.re) = (ptFirst (((MatrixMap.choi_matrix Phi).submatrix Prod.swap Prod.swap))).map Complex.re := rfl
  rw [he,hPhi.2]
private theorem choi_real_bisymm (Phi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (hI : ∀ X, Phi Xᵀ = Phi X) (hO : ∀ X, (Phi X)ᵀ = Phi X) :
    ((((MatrixMap.choi_matrix Phi).submatrix Prod.swap Prod.swap)).map Complex.re).map Complex.ofReal = ((MatrixMap.choi_matrix Phi).submatrix Prod.swap Prod.swap) := by
  ext a b
  let A : Matrix (Fin n) (Fin n) ℂ := Matrix.single a.1 b.1 1
  let B : Matrix (Fin n) (Fin n) ℂ := Matrix.single b.1 a.1 1
  have ht : Aᵀ = B := by simp [A,B,Matrix.transpose_single]
  have hi := congrFun (congrFun (hI A) a.2) b.2
  rw [ht] at hi
  have ho := congrFun (congrFun (hO B) a.2) b.2
  have hs : Phi B b.2 a.2 = Phi A a.2 b.2 := ho.trans hi
  have hh := congrFun (congrFun ((choi_psd_of_cp Phi hPhi)).isHermitian a) b
  change star (Phi B b.2 a.2) = Phi A a.2 b.2 at hh
  rw [hs] at hh
  have hz : (Phi A a.2 b.2).im = 0 := by
    have he := congrArg Complex.im hh
    simp only [Complex.star_def, Complex.conj_im] at he
    linarith
  apply Complex.ext
  · rfl
  · simpa [Matrix.map_apply, MatrixMap.choi_matrix, Matrix.submatrix_apply, A] using hz.symm
private theorem complexify_restrict_bisymm (Phi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) (hPhi : MatrixMap.IsCompletelyPositive Phi)
    (hI : ∀ X, Phi Xᵀ = Phi X) (hO : ∀ X, (Phi X)ᵀ = Phi X) :
    complexify (restrict Phi) = Phi := by
  apply MatrixMap.choi_matrix_inj
  have he := congrArg (fun C => C.submatrix Prod.swap Prod.swap)
    ((complexify_choi (restrict Phi)).trans ((congrArg (fun C => C.map Complex.ofReal) (restrict_choi Phi)).trans (choi_real_bisymm Phi hPhi hI hO)))
  ext ⟨a,u⟩ ⟨b,v⟩
  exact congrFun (congrFun he (a,u)) (b,v)
private theorem gamma_real_complexification {Phi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ} (hPhi : IsPPT Phi) :
    complexify (restrict (gamma Phi)) = gamma Phi :=
  complexify_restrict_bisymm _ (gamma_cp hPhi) (gamma_input Phi) (gamma_output Phi)
private theorem gamma_real_ipt {Phi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ} (hPhi : IsPPT Phi) :
    IsIPT (restrict (gamma Phi)) := restrict_ipt (gamma_ipt hPhi)
private theorem conj_dual (C : Matrix (Fin m) (Fin n) ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin m) (Fin m) ℂ) :
    Matrix.trace ((C * M * Cᴴ) * X) = Matrix.trace (M * (Cᴴ * X * C)) := by
  calc
    _ = Matrix.trace ((C * M) * (Cᴴ * X)) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace ((Cᴴ * X) * (C * M)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((Cᴴ * X * C) * M) := by simp only [Matrix.mul_assoc]
    _ = _ := Matrix.trace_mul_comm _ _
private theorem put_pp_dual (M : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) :
    Matrix.trace (put n pp M * X) = Matrix.trace (M * bp n X) := by
  rw [put_pp_conj]
  unfold bp
  simp only [LinearMap.smul_apply, MatrixMap.of_kraus, Fin.sum_univ_one, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.conjTranspose_conjTranspose]
  congr 1
  exact conj_dual _ _ _
private theorem put_pm_dual (M : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) :
    Matrix.trace (put n pm M * X) = Matrix.trace (M * bm n X) := by
  rw [put_pm_conj]
  unfold bm
  simp only [LinearMap.smul_apply, MatrixMap.of_kraus, Fin.sum_univ_one, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.conjTranspose_conjTranspose]
  congr 1
  exact conj_dual _ _ _
private theorem trace_transpose_pair (M A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (M * Aᵀ) = Matrix.trace (Mᵀ * A) := by
  simpa only [Matrix.transpose_transpose] using Matrix.trace_transpose_mul Mᵀ A
private theorem ee_dd_dual (M : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) :
    Matrix.trace (M * ee n X) = Matrix.trace (dd n M * X) := by
  change Matrix.trace (M * (bp n X + (bm n X)ᵀ)) =
    Matrix.trace ((put n pp M + put n pm Mᵀ) * X)
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, Matrix.trace_add,
    trace_transpose_pair, put_pp_dual, put_pm_dual]
private theorem ee_put_pp (A : Matrix (Fin n) (Fin n) ℂ) : ee n (put n pp A) = A := by
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro M
  rw [ee_dd_dual]
  calc
    _ = Matrix.trace (put n pp A * dd n M) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (A * bp n (dd n M)) := put_pp_dual _ _
    _ = Matrix.trace (A * M) := by rw [bp_dd]
    _ = _ := Matrix.trace_mul_comm _ _
private theorem recovery (Phi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    bp n ∘ₗ gamma Phi ∘ₗ gamma Phi ∘ₗ put n pp = (1/2 : ℂ) • (Phi ∘ₗ Phi) := by
  ext A a b
  have hg : gamma Phi (gamma Phi (put n pp A)) =
      gamma (Phi ∘ₗ Phi) (put n pp A) :=
    congrArg (fun F => F (put n pp A)) (gamma_comp Phi Phi)
  change bp n (gamma Phi (gamma Phi (put n pp A))) a b = _
  rw [hg]
  simp only [LinearMap.comp_apply, gamma, LinearMap.smul_apply, map_smul, ee_put_pp, bp_dd]
private theorem cp_id : MatrixMap.IsCompletelyPositive (LinearMap.id : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) := by
  intro r P hP
  convert hP using 1
  ext a b
  simp only [kron_id_apply, LinearMap.id_apply]
private theorem cp_twice {Phi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ} (hPhi : MatrixMap.IsCompletelyPositive Phi) : MatrixMap.IsCompletelyPositive ((2 : ℂ) • Phi) := by
  intro r P hP
  have he : MatrixMap.kron ((2 : ℂ) • Phi) (LinearMap.id : MatrixMap (Fin r) (Fin r) ℂ) P =
      (2 : ℂ) • MatrixMap.kron Phi LinearMap.id P := by
    ext a b
    simp only [kron_id_apply, LinearMap.smul_apply, Matrix.smul_apply]
  rw [he]
  exact (hPhi r hP).smul (by exact_mod_cast (show (0 : ℝ) ≤ 2 by norm_num))
private theorem reflect_eb_square (Phi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (h : IsEB (gamma Phi ∘ₗ gamma Phi)) :
    IsEB (Phi ∘ₗ Phi) := by
  have hb := eb_post bp_cp (eb_pre h put_pp_cp)
  have hr : IsEB ((1/2 : ℂ) • (Phi ∘ₗ Phi)) := by
    have he : bp n ∘ₗ ((gamma Phi ∘ₗ gamma Phi) ∘ₗ put n pp) =
        (1/2 : ℂ) • (Phi ∘ₗ Phi) := by
      simpa only [LinearMap.comp_assoc] using recovery Phi
    rw [he] at hb
    exact hb
  have hs := eb_post (cp_twice (cp_id (n := n))) hr
  have he : ((2 : ℂ) • (LinearMap.id : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)) ∘ₗ
      ((1/2 : ℂ) • (Phi ∘ₗ Phi)) = Phi ∘ₗ Phi := by
    ext A a b
    simp
  rw [he] at hs
  exact hs
private theorem ipt2c_ppt2c (h : IPT2 ℂ) : PPT2C := by
  intro n Phi hPhi
  exact reflect_eb_square Phi (h (2 * n) (gamma Phi) (gamma_ipt hPhi))
private theorem ipt2r_ppt2c (h : IPT2 ℝ) : PPT2C := by
  intro n Phi hPhi
  have hb := h (2 * n) (restrict (gamma Phi)) (gamma_real_ipt hPhi)
  have hc := complexify_eb hb
  rw [complexify_comp, gamma_real_complexification hPhi] at hc
  exact reflect_eb_square Phi hc
theorem result : claim :=
  ⟨⟨ppt2c_ipt2c, ipt2c_ppt2c⟩,
   ⟨ipt2c_ipt2r, fun h => ppt2c_ipt2c (ipt2r_ppt2c h)⟩⟩
end D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence
