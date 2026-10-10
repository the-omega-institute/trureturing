/- GID: D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The Choi spectrum of unital product-unitary-equivariant maps in every dimension. -/

/- Judgement:
   Each declaration below belongs to
   admission_basis: open-problem-resolution (#14200; Proved).
   Definitions have proof_shape: not-applicable; escape_witness: null:
   depol; compl; phi; claim; omega; kmat; dmat; qmat; base; e0; uvec; smat; tmat;
   rmat; sector; tri; rd; key; fval; vk.
   Every theorem has proof_shape: bind-only; escape_witness: null, and each helper, the
   public omega, kmat, dmat, qmat, choi_reindex and omega_dot_omega included, is consumed on
   the proof path of result:
   choi_apply -> choi_reindex; depol_single -> depol_single_eq_dmat, compl_single;
   compl_single -> compl_single_eq_qmat;
   kron_single, depol_single_eq_dmat, compl_single_eq_qmat -> choi_reindex;
   omega_base -> e0_dot_omega, omega_dot_e0, rmat_diag;
   e0_dot_omega -> e0_dot_uvec, conj_kmat; omega_dot_e0, omega_dot_omega -> omega_dot_uvec;
   e0_dot_e0 -> e0_dot_uvec; e0_dot_uvec -> smat_mul_tmat, tmat_mul_smat;
   omega_dot_uvec -> conj_kmat; tmat_mul_smat -> conj_dmat; conj_kmat, conj_dmat -> conj_qmat;
   conj_dmat, conj_qmat -> conj_sector; conj_sector, smat_mul_tmat -> charpoly_sector;
   dmat_apply, rmat_of_ne, tri_apply -> tri_blockTriangular, tri_offdiag;
   dmat_apply, rmat_diag, tri_apply -> tri_diag; rmat_apply -> rmat_of_ne, rmat_diag;
   tri_diag, tri_offdiag, rd_key -> block_eq; tri_blockTriangular, block_eq -> charpoly_tri;
   card_ne_base, card_key -> card_key_values;
   choi_reindex, charpoly_sector, charpoly_tri, card_key_values -> result.
   Direct frozen dependencies (GID; statement_id):
   D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap;
     sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7
   D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.kron;
     sha256:6bbbe42180d7cde8ee171b8a1aeeb16449194862345f2042d95ec7c0b2055471
   D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.kron_def;
     sha256:0a066df1b1de64e4fda175d1ac776d744674a6465abc8a7f13b12f185ce29405
   computational_content: none for every declaration: the statements concern arbitrary
   dimensions and complex parameters, with no bounded enumeration, checker, numerical
   reduction or certified fixed instance.
-/

import D5.S3.Quantum.Foundation.FiniteKrausChannel

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix Polynomial
open scoped BigOperators Kronecker
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf

namespace D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum

/-- The map sending `X` to `(tr X / n) • 1` on `n × n` complex matrices. -/
def depol (n : ℕ) : MatrixMap (Fin n) (Fin n) ℂ where
  toFun X := (X.trace / n) • (1 : Matrix (Fin n) (Fin n) ℂ)
  map_add' X Y := by rw [trace_add, add_div, add_smul]
  map_smul' c X := by
    rw [trace_smul, RingHom.id_apply, smul_smul, smul_eq_mul, mul_div_assoc]

/-- The complementary map `X ↦ X - (tr X / n) • 1`. -/
def compl (n : ℕ) : MatrixMap (Fin n) (Fin n) ℂ := LinearMap.id - depol n

/-- The unital map with parameters `λ₀₁, λ₁₀, λ₁₁` on the two isotypic components
`depol ⊗ compl`, `compl ⊗ depol`, `compl ⊗ compl` and weight one on `depol ⊗ depol`. -/
def phi (n₁ n₂ : ℕ) (l₀₁ l₁₀ l₁₁ : ℂ) : MatrixMap (Fin n₁ × Fin n₂) (Fin n₁ × Fin n₂) ℂ :=
  MatrixMap.kron (depol n₁) (depol n₂) + l₀₁ • MatrixMap.kron (depol n₁) (compl n₂) +
    l₁₀ • MatrixMap.kron (compl n₁) (depol n₂) + l₁₁ • MatrixMap.kron (compl n₁) (compl n₂)

/-- The characteristic polynomial of the Choi matrix of `phi` has the four roots of the
small-dimension formulas with multiplicities `1`, `n₁² - 1`, `n₂² - 1`, `(n₁² - 1)(n₂² - 1)`. -/
def claim : Prop :=
  ∀ n₁ n₂ : ℕ, 1 ≤ n₁ → 1 ≤ n₂ → ∀ l₀₁ l₁₀ l₁₁ : ℂ,
    (∑ p : Fin n₁ × Fin n₂, ∑ q : Fin n₁ × Fin n₂,
        Matrix.single p q (1 : ℂ) ⊗ₖ phi n₁ n₂ l₀₁ l₁₀ l₁₁ (Matrix.single p q 1)).charpoly =
      (X - C ((1 + ((n₂ : ℂ) ^ 2 - 1) * l₀₁ + ((n₁ : ℂ) ^ 2 - 1) * l₁₀ +
          ((n₁ : ℂ) ^ 2 - 1) * ((n₂ : ℂ) ^ 2 - 1) * l₁₁) / ((n₁ : ℂ) * n₂))) *
      (X - C ((1 + ((n₂ : ℂ) ^ 2 - 1) * l₀₁ - l₁₀ - ((n₂ : ℂ) ^ 2 - 1) * l₁₁) /
          ((n₁ : ℂ) * n₂))) ^ (n₁ ^ 2 - 1) *
      (X - C ((1 - l₀₁ + ((n₁ : ℂ) ^ 2 - 1) * l₁₀ - ((n₁ : ℂ) ^ 2 - 1) * l₁₁) /
          ((n₁ : ℂ) * n₂))) ^ (n₂ ^ 2 - 1) *
      (X - C ((1 - l₀₁ - l₁₀ + l₁₁) / ((n₁ : ℂ) * n₂))) ^ ((n₁ ^ 2 - 1) * (n₂ ^ 2 - 1))

private theorem choi_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (Φ : MatrixMap ι ι ℂ)
    (p r q s : ι) :
    (∑ p' : ι, ∑ q' : ι, Matrix.single p' q' (1 : ℂ) ⊗ₖ Φ (Matrix.single p' q' 1)) (p, r) (q, s) =
      Φ (Matrix.single p q 1) r s := by
  simp only [Matrix.sum_apply, kroneckerMap_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single p (by intro b _ hb; simp [hb]) (by simp)]
  rw [Finset.sum_eq_single q (by intro b _ hb; simp [hb]) (by simp)]
  simp

private theorem depol_single (n : ℕ) (i j a b : Fin n) :
    depol n (Matrix.single i j 1) a b = if i = j ∧ a = b then 1 / (n : ℂ) else 0 := by
  simp only [depol, LinearMap.coe_mk, AddHom.coe_mk, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    by_cases hab : a = b <;> simp [hab, trace_single_eq_same]
  · simp [hij, trace_single_eq_of_ne i j (1 : ℂ) hij]

private theorem compl_single (n : ℕ) (i j a b : Fin n) :
    compl n (Matrix.single i j 1) a b =
      (if i = a ∧ j = b then 1 else 0) - (if i = j ∧ a = b then 1 / (n : ℂ) else 0) := by
  simp only [compl, LinearMap.sub_apply, LinearMap.id_apply, Matrix.sub_apply, depol_single,
    Matrix.single_apply]

private theorem kron_single (n₁ n₂ : ℕ) (M₁ : MatrixMap (Fin n₁) (Fin n₁) ℂ)
    (M₂ : MatrixMap (Fin n₂) (Fin n₂) ℂ) (i j : Fin n₁) (k l : Fin n₂) (a b : Fin n₁)
    (c d : Fin n₂) :
    MatrixMap.kron M₁ M₂ (Matrix.single (i, k) (j, l) 1) (a, c) (b, d) =
      M₁ (Matrix.single i j 1) a b * M₂ (Matrix.single k l 1) c d := by
  rw [MatrixMap.kron_def]
  simp only [Matrix.single_apply, Prod.mk.injEq]
  rw [Finset.sum_eq_single i (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  rw [Finset.sum_eq_single j (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  rw [Finset.sum_eq_single k (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  rw [Finset.sum_eq_single l (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp

/-- The vector with entry one on the pairs `(i, i)` and zero elsewhere. -/
def omega (n : ℕ) : Fin n × Fin n → ℂ := fun x => if x.1 = x.2 then 1 else 0

/-- The rank-one matrix `omega omegaᵀ`, the Choi matrix of the identity map. -/
def kmat (n : ℕ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  vecMulVec (omega n) (omega n)

/-- The Choi matrix of `depol n`. -/
def dmat (n : ℕ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  (1 / (n : ℂ)) • (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)

/-- The Choi matrix of `compl n`. -/
def qmat (n : ℕ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ := kmat n - dmat n

private theorem depol_single_eq_dmat (n : ℕ) (i j a b : Fin n) :
    depol n (Matrix.single i j 1) a b = dmat n (i, a) (j, b) := by
  rw [depol_single]
  simp only [dmat, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq, smul_eq_mul]
  by_cases hij : i = j <;> by_cases hab : a = b <;> simp [hij, hab]

private theorem compl_single_eq_qmat (n : ℕ) (i j a b : Fin n) :
    compl n (Matrix.single i j 1) a b = qmat n (i, a) (j, b) := by
  rw [compl_single, ← depol_single, depol_single_eq_dmat]
  simp only [qmat, kmat, omega, Matrix.sub_apply, vecMulVec_apply]
  by_cases hia : i = a <;> by_cases hjb : j = b <;> simp [hia, hjb]

/-- After grouping the indices by factor, the Choi matrix of `phi` is the weighted sum of
Kronecker products of `dmat` and `qmat`. -/
theorem choi_reindex (n₁ n₂ : ℕ) (l₀₁ l₁₀ l₁₁ : ℂ) :
    reindex (Equiv.prodProdProdComm (Fin n₁) (Fin n₂) (Fin n₁) (Fin n₂))
        (Equiv.prodProdProdComm (Fin n₁) (Fin n₂) (Fin n₁) (Fin n₂))
        (∑ p : Fin n₁ × Fin n₂, ∑ q : Fin n₁ × Fin n₂,
          Matrix.single p q (1 : ℂ) ⊗ₖ phi n₁ n₂ l₀₁ l₁₀ l₁₁ (Matrix.single p q 1)) =
      dmat n₁ ⊗ₖ dmat n₂ + l₀₁ • (dmat n₁ ⊗ₖ qmat n₂) + l₁₀ • (qmat n₁ ⊗ₖ dmat n₂) +
        l₁₁ • (qmat n₁ ⊗ₖ qmat n₂) := by
  ext ⟨⟨i, i'⟩, ⟨k, k'⟩⟩ ⟨⟨j, j'⟩, ⟨l, l'⟩⟩
  simp only [reindex_apply, submatrix_apply, Equiv.prodProdProdComm_symm,
    Equiv.prodProdProdComm_apply, choi_apply]
  simp only [phi, LinearMap.add_apply, LinearMap.smul_apply, Matrix.add_apply,
    Matrix.smul_apply, kron_single, depol_single_eq_dmat, compl_single_eq_qmat,
    kroneckerMap_apply, smul_eq_mul]

/-- The distinguished index `(0, 0)`. -/
private def base {n : ℕ} (hn : 1 ≤ n) : Fin n × Fin n := (⟨0, hn⟩, ⟨0, hn⟩)

private def e0 {n : ℕ} (hn : 1 ≤ n) : Fin n × Fin n → ℂ := Pi.single (base hn) 1

private def uvec {n : ℕ} (hn : 1 ≤ n) : Fin n × Fin n → ℂ := omega n - e0 hn

/-- The shear `1 + u e₀ᵀ` sending `e₀` to `omega`. -/
private def smat {n : ℕ} (hn : 1 ≤ n) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  1 + vecMulVec (uvec hn) (e0 hn)

/-- The inverse shear `1 - u e₀ᵀ`. -/
private def tmat {n : ℕ} (hn : 1 ≤ n) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  1 - vecMulVec (uvec hn) (e0 hn)

/-- The conjugate of `kmat`: only the row of the base index is nonzero. -/
private def rmat {n : ℕ} (hn : 1 ≤ n) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  vecMulVec (e0 hn) (omega n + ((n : ℂ) - 1) • e0 hn)

private theorem omega_base {n : ℕ} (hn : 1 ≤ n) : omega n (base hn) = 1 := by
  simp [omega, base]

private theorem e0_dot_omega {n : ℕ} (hn : 1 ≤ n) : e0 hn ⬝ᵥ omega n = 1 := by
  rw [e0, single_dotProduct, one_mul, omega_base]

private theorem omega_dot_e0 {n : ℕ} (hn : 1 ≤ n) : omega n ⬝ᵥ e0 hn = 1 := by
  rw [e0, dotProduct_single, mul_one, omega_base]

private theorem e0_dot_e0 {n : ℕ} (hn : 1 ≤ n) : e0 hn ⬝ᵥ e0 hn = 1 := by
  rw [e0, single_dotProduct, one_mul, Pi.single_eq_same]

/-- `ω ⬝ ω = n`. -/
theorem omega_dot_omega (n : ℕ) : omega n ⬝ᵥ omega n = n := by
  simp only [dotProduct, omega, Fintype.sum_prod_type, mul_ite, mul_one, mul_zero]
  simp

private theorem e0_dot_uvec {n : ℕ} (hn : 1 ≤ n) : e0 hn ⬝ᵥ uvec hn = 0 := by
  rw [uvec, dotProduct_sub, e0_dot_omega, e0_dot_e0, sub_self]

private theorem omega_dot_uvec {n : ℕ} (hn : 1 ≤ n) : omega n ⬝ᵥ uvec hn = (n : ℂ) - 1 := by
  rw [uvec, dotProduct_sub, omega_dot_omega, omega_dot_e0]

private theorem smat_mul_tmat {n : ℕ} (hn : 1 ≤ n) : smat hn * tmat hn = 1 := by
  rw [smat, tmat, add_mul, one_mul, mul_sub, mul_one, vecMulVec_mul_vecMulVec, e0_dot_uvec,
    zero_smul, vecMulVec_zero, sub_zero, sub_add_cancel]

private theorem tmat_mul_smat {n : ℕ} (hn : 1 ≤ n) : tmat hn * smat hn = 1 := by
  rw [smat, tmat, sub_mul, one_mul, mul_add, mul_one, vecMulVec_mul_vecMulVec, e0_dot_uvec,
    zero_smul, vecMulVec_zero, add_zero, add_sub_cancel_right]

private theorem conj_kmat {n : ℕ} (hn : 1 ≤ n) : tmat hn * kmat n * smat hn = rmat hn := by
  have h1 : tmat hn * kmat n = vecMulVec (e0 hn) (omega n) := by
    rw [tmat, kmat, sub_mul, one_mul, vecMulVec_mul_vecMulVec, e0_dot_omega, one_smul, uvec,
      ← sub_vecMulVec, sub_sub_cancel]
  rw [h1, smat, mul_add, mul_one, vecMulVec_mul_vecMulVec, omega_dot_uvec, rmat, vecMulVec_add]

private theorem conj_dmat {n : ℕ} (hn : 1 ≤ n) : tmat hn * dmat n * smat hn = dmat n := by
  rw [dmat, Matrix.mul_smul, mul_one, Matrix.smul_mul, tmat_mul_smat]

private theorem conj_qmat {n : ℕ} (hn : 1 ≤ n) :
    tmat hn * qmat n * smat hn = rmat hn - dmat n := by
  rw [qmat, Matrix.mul_sub, Matrix.sub_mul, conj_kmat, conj_dmat]

/-- The reindexed Choi matrix in sector form. -/
private def sector (n₁ n₂ : ℕ) (l₀₁ l₁₀ l₁₁ : ℂ) :
    Matrix ((Fin n₁ × Fin n₁) × (Fin n₂ × Fin n₂)) ((Fin n₁ × Fin n₁) × (Fin n₂ × Fin n₂)) ℂ :=
  dmat n₁ ⊗ₖ dmat n₂ + l₀₁ • (dmat n₁ ⊗ₖ qmat n₂) + l₁₀ • (qmat n₁ ⊗ₖ dmat n₂) +
    l₁₁ • (qmat n₁ ⊗ₖ qmat n₂)

/-- The sector form after the shear conjugation on both factors. -/
private def tri {n₁ n₂ : ℕ} (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂) (l₀₁ l₁₀ l₁₁ : ℂ) :
    Matrix ((Fin n₁ × Fin n₁) × (Fin n₂ × Fin n₂)) ((Fin n₁ × Fin n₁) × (Fin n₂ × Fin n₂)) ℂ :=
  dmat n₁ ⊗ₖ dmat n₂ + l₀₁ • (dmat n₁ ⊗ₖ (rmat hn₂ - dmat n₂)) +
    l₁₀ • ((rmat hn₁ - dmat n₁) ⊗ₖ dmat n₂) +
    l₁₁ • ((rmat hn₁ - dmat n₁) ⊗ₖ (rmat hn₂ - dmat n₂))

private theorem conj_sector {n₁ n₂ : ℕ} (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂) (l₀₁ l₁₀ l₁₁ : ℂ) :
    (tmat hn₁ ⊗ₖ tmat hn₂) * sector n₁ n₂ l₀₁ l₁₀ l₁₁ * (smat hn₁ ⊗ₖ smat hn₂) =
      tri hn₁ hn₂ l₀₁ l₁₀ l₁₁ := by
  simp only [sector, tri, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    ← mul_kronecker_mul, conj_dmat, conj_qmat]

private theorem charpoly_sector {n₁ n₂ : ℕ} (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂) (l₀₁ l₁₀ l₁₁ : ℂ) :
    (sector n₁ n₂ l₀₁ l₁₀ l₁₁).charpoly = (tri hn₁ hn₂ l₀₁ l₁₀ l₁₁).charpoly := by
  rw [← conj_sector hn₁ hn₂, charpoly_mul_comm, ← Matrix.mul_assoc, ← mul_kronecker_mul,
    smat_mul_tmat, smat_mul_tmat, one_kronecker_one, Matrix.one_mul]

private theorem dmat_apply (n : ℕ) (x x' : Fin n × Fin n) :
    dmat n x x' = if x = x' then 1 / (n : ℂ) else 0 := by
  simp [dmat, Matrix.one_apply]

private theorem rmat_apply {n : ℕ} (hn : 1 ≤ n) (x x' : Fin n × Fin n) :
    rmat hn x x' = if x = base hn then
      omega n x' + ((n : ℂ) - 1) * (if x' = base hn then 1 else 0) else 0 := by
  simp only [rmat, vecMulVec_apply, e0, Pi.single_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  split_ifs <;> simp

private theorem rmat_of_ne {n : ℕ} (hn : 1 ≤ n) {x : Fin n × Fin n} (hx : x ≠ base hn)
    (x' : Fin n × Fin n) : rmat hn x x' = 0 := by
  rw [rmat_apply, if_neg hx]

/-- The diagonal of `rmat`: `n` at the base index and zero elsewhere. -/
private def rd {n : ℕ} (hn : 1 ≤ n) (x : Fin n × Fin n) : ℂ := if x = base hn then n else 0

private theorem rmat_diag {n : ℕ} (hn : 1 ≤ n) (x : Fin n × Fin n) : rmat hn x x = rd hn x := by
  rw [rmat_apply, rd]
  split_ifs with hx
  · subst hx
    rw [omega_base]
    ring
  · rfl

private theorem tri_apply {n₁ n₂ : ℕ} (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂) (l₀₁ l₁₀ l₁₁ : ℂ)
    (x x' : Fin n₁ × Fin n₁) (y y' : Fin n₂ × Fin n₂) :
    tri hn₁ hn₂ l₀₁ l₁₀ l₁₁ (x, y) (x', y') =
      dmat n₁ x x' * dmat n₂ y y' + l₀₁ * (dmat n₁ x x' * (rmat hn₂ y y' - dmat n₂ y y')) +
        l₁₀ * ((rmat hn₁ x x' - dmat n₁ x x') * dmat n₂ y y') +
        l₁₁ * ((rmat hn₁ x x' - dmat n₁ x x') * (rmat hn₂ y y' - dmat n₂ y y')) := by
  simp [tri, kroneckerMap_apply]

/-- Two-level block index: base or not on each factor. -/
private def key {n₁ n₂ : ℕ} (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂)
    (z : (Fin n₁ × Fin n₁) × (Fin n₂ × Fin n₂)) : ℕ :=
  2 * (if z.1 = base hn₁ then 0 else 1) + (if z.2 = base hn₂ then 0 else 1)

private theorem tri_blockTriangular {n₁ n₂ : ℕ} (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂)
    (l₀₁ l₁₀ l₁₁ : ℂ) : (tri hn₁ hn₂ l₀₁ l₁₀ l₁₁).BlockTriangular (key hn₁ hn₂) := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  simp only [key] at h
  rw [tri_apply]
  by_cases hx : x = base hn₁ <;> by_cases hx' : x' = base hn₁ <;>
    by_cases hy : y = base hn₂ <;> by_cases hy' : y' = base hn₂ <;>
    simp only [hx, hx', hy, hy', if_true, if_false] at h <;> (try omega)
  all_goals first
    | (have hxx : x ≠ x' := by rintro rfl; exact hx hx'
       simp [dmat_apply, hxx, rmat_of_ne hn₁ hx])
    | (have hyy : y ≠ y' := by rintro rfl; exact hy hy'
       simp [dmat_apply, hyy, rmat_of_ne hn₂ hy])

/-- The value of a diagonal entry with conjugated diagonal entries `r₁`, `r₂`. -/
private def fval (n₁ n₂ : ℕ) (l₀₁ l₁₀ l₁₁ r₁ r₂ : ℂ) : ℂ :=
  1 / (n₁ : ℂ) * (1 / n₂) + l₀₁ * (1 / (n₁ : ℂ) * (r₂ - 1 / n₂)) +
    l₁₀ * ((r₁ - 1 / n₁) * (1 / n₂)) + l₁₁ * ((r₁ - 1 / n₁) * (r₂ - 1 / n₂))

private theorem tri_diag {n₁ n₂ : ℕ} (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂) (l₀₁ l₁₀ l₁₁ : ℂ)
    (x : Fin n₁ × Fin n₁) (y : Fin n₂ × Fin n₂) :
    tri hn₁ hn₂ l₀₁ l₁₀ l₁₁ (x, y) (x, y) = fval n₁ n₂ l₀₁ l₁₀ l₁₁ (rd hn₁ x) (rd hn₂ y) := by
  rw [tri_apply, rmat_diag, rmat_diag, dmat_apply, dmat_apply, if_pos rfl, if_pos rfl, fval]

private theorem tri_offdiag {n₁ n₂ : ℕ} (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂) (l₀₁ l₁₀ l₁₁ : ℂ)
    (x x' : Fin n₁ × Fin n₁) (y y' : Fin n₂ × Fin n₂)
    (h : key hn₁ hn₂ (x, y) = key hn₁ hn₂ (x', y')) (hne : (x, y) ≠ (x', y')) :
    tri hn₁ hn₂ l₀₁ l₁₀ l₁₁ (x, y) (x', y') = 0 := by
  rw [tri_apply]
  simp only [key] at h
  by_cases hxx : x = x'
  · subst hxx
    have hyy : y ≠ y' := fun h' => hne (by rw [h'])
    have hy : y ≠ base hn₂ := by
      intro hyb
      apply hyy
      by_cases hy' : y' = base hn₂
      · rw [hyb, hy']
      · simp only [hyb, hy', if_true, if_false] at h
        omega
    simp [dmat_apply, hyy, rmat_of_ne hn₂ hy]
  · have hx : x ≠ base hn₁ := by
      intro hxb
      by_cases hx' : x' = base hn₁
      · exact hxx (hxb.trans hx'.symm)
      · simp only [hxb, hx', if_true, if_false] at h
        split_ifs at h <;> omega
    simp [dmat_apply, hxx, rmat_of_ne hn₁ hx]

/-- The common value on block `k`. -/
private def vk (n₁ n₂ : ℕ) (l₀₁ l₁₀ l₁₁ : ℂ) (k : ℕ) : ℂ :=
  fval n₁ n₂ l₀₁ l₁₀ l₁₁ (if k < 2 then (n₁ : ℂ) else 0) (if k % 2 = 0 then (n₂ : ℂ) else 0)

private theorem rd_key {n₁ n₂ : ℕ} (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂)
    (z : (Fin n₁ × Fin n₁) × (Fin n₂ × Fin n₂)) :
    rd hn₁ z.1 = (if key hn₁ hn₂ z < 2 then (n₁ : ℂ) else 0) ∧
      rd hn₂ z.2 = (if key hn₁ hn₂ z % 2 = 0 then (n₂ : ℂ) else 0) := by
  simp only [rd, key]
  by_cases hx : z.1 = base hn₁ <;> by_cases hy : z.2 = base hn₂ <;> simp [hx, hy]

private theorem block_eq {n₁ n₂ : ℕ} (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂) (l₀₁ l₁₀ l₁₁ : ℂ) (k : ℕ) :
    (tri hn₁ hn₂ l₀₁ l₁₀ l₁₁).toSquareBlock (key hn₁ hn₂) k =
      diagonal (fun _ => vk n₁ n₂ l₀₁ l₁₀ l₁₁ k) := by
  ext ⟨⟨x, y⟩, hi⟩ ⟨⟨x', y'⟩, hj⟩
  rw [toSquareBlock_def, of_apply, diagonal_apply]
  by_cases hij : ((⟨(x, y), hi⟩ : {a // key hn₁ hn₂ a = k}) = ⟨(x', y'), hj⟩)
  · rw [if_pos hij]
    have hxy : (x, y) = (x', y') := congrArg Subtype.val hij
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ hxy
    rw [tri_diag, vk]
    obtain ⟨h₁, h₂⟩ := rd_key hn₁ hn₂ (x, y)
    rw [hi] at h₁ h₂
    rw [h₁, h₂]
  · rw [if_neg hij]
    exact tri_offdiag hn₁ hn₂ l₀₁ l₁₀ l₁₁ x x' y y' (hi.trans hj.symm)
      (fun h => hij (Subtype.ext h))

private theorem charpoly_tri {n₁ n₂ : ℕ} (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂) (l₀₁ l₁₀ l₁₁ : ℂ) :
    (tri hn₁ hn₂ l₀₁ l₁₀ l₁₁).charpoly =
      (X - C (vk n₁ n₂ l₀₁ l₁₀ l₁₁ 0)) ^ Fintype.card {z // key hn₁ hn₂ z = 0} *
      (X - C (vk n₁ n₂ l₀₁ l₁₀ l₁₁ 1)) ^ Fintype.card {z // key hn₁ hn₂ z = 1} *
      (X - C (vk n₁ n₂ l₀₁ l₁₀ l₁₁ 2)) ^ Fintype.card {z // key hn₁ hn₂ z = 2} *
      (X - C (vk n₁ n₂ l₀₁ l₁₀ l₁₁ 3)) ^ Fintype.card {z // key hn₁ hn₂ z = 3} := by
  rw [(tri_blockTriangular hn₁ hn₂ l₀₁ l₁₀ l₁₁).charpoly]
  have himg : Finset.image (key hn₁ hn₂) Finset.univ ⊆ Finset.range 4 := by
    intro k hk
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hk
    simp only [Finset.mem_range, key]
    split_ifs <;> omega
  rw [Finset.prod_subset himg (by
    intro k _ hk
    have : IsEmpty {z // key hn₁ hn₂ z = k} :=
      ⟨fun ⟨z, hz⟩ => hk (Finset.mem_image.mpr ⟨z, Finset.mem_univ _, hz⟩)⟩
    exact charpoly_isEmpty)]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, block_eq,
    charpoly_diagonal, Finset.prod_const, Finset.card_univ]

private theorem card_ne_base {n : ℕ} (hn : 1 ≤ n) :
    Fintype.card {x : Fin n × Fin n // x ≠ base hn} = n ^ 2 - 1 := by
  rw [Fintype.card_subtype_compl (· = base hn), Fintype.card_subtype_eq, Fintype.card_prod,
    Fintype.card_fin, sq]

private theorem card_key {n₁ n₂ : ℕ} (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂) (k : ℕ)
    (P : Fin n₁ × Fin n₁ → Prop) (Q : Fin n₂ × Fin n₂ → Prop) [DecidablePred P]
    [DecidablePred Q] (hPQ : ∀ z, key hn₁ hn₂ z = k ↔ P z.1 ∧ Q z.2) :
    Fintype.card {z // key hn₁ hn₂ z = k} = Fintype.card {x // P x} * Fintype.card {y // Q y} := by
  rw [Fintype.card_congr (Equiv.subtypeEquivRight hPQ),
    Fintype.card_congr Equiv.subtypeProdEquivProd, Fintype.card_prod]

private theorem card_key_values {n₁ n₂ : ℕ} (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂) :
    Fintype.card {z // key hn₁ hn₂ z = 0} = 1 ∧
      Fintype.card {z // key hn₁ hn₂ z = 1} = n₂ ^ 2 - 1 ∧
      Fintype.card {z // key hn₁ hn₂ z = 2} = n₁ ^ 2 - 1 ∧
      Fintype.card {z // key hn₁ hn₂ z = 3} = (n₁ ^ 2 - 1) * (n₂ ^ 2 - 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [card_key hn₁ hn₂ 0 (· = base hn₁) (· = base hn₂) (fun z => by
      simp only [key]; by_cases hx : z.1 = base hn₁ <;> by_cases hy : z.2 = base hn₂ <;>
        simp [hx, hy]), Fintype.card_subtype_eq, Fintype.card_subtype_eq]
  · rw [card_key hn₁ hn₂ 1 (· = base hn₁) (· ≠ base hn₂) (fun z => by
      simp only [key]; by_cases hx : z.1 = base hn₁ <;> by_cases hy : z.2 = base hn₂ <;>
        simp [hx, hy]), Fintype.card_subtype_eq, card_ne_base, one_mul]
  · rw [card_key hn₁ hn₂ 2 (· ≠ base hn₁) (· = base hn₂) (fun z => by
      simp only [key]; by_cases hx : z.1 = base hn₁ <;> by_cases hy : z.2 = base hn₂ <;>
        simp [hx, hy]), card_ne_base, Fintype.card_subtype_eq, mul_one]
  · rw [card_key hn₁ hn₂ 3 (· ≠ base hn₁) (· ≠ base hn₂) (fun z => by
      simp only [key]; by_cases hx : z.1 = base hn₁ <;> by_cases hy : z.2 = base hn₂ <;>
        simp [hx, hy]), card_ne_base, card_ne_base]

/-- García-Velo–Ibort, Remark V.2: the Choi spectrum of the unital
`U(n₁) ⊗ U(n₂)`-equivariant maps is given by the four formulas of Lemma V.8 in every
dimension. -/
theorem result : claim := by
  intro n₁ n₂ hn₁ hn₂ l₀₁ l₁₀ l₁₁
  rw [← charpoly_reindex (Equiv.prodProdProdComm (Fin n₁) (Fin n₂) (Fin n₁) (Fin n₂)),
    choi_reindex]
  change (sector n₁ n₂ l₀₁ l₁₀ l₁₁).charpoly = _
  obtain ⟨c₀, c₁, c₂, c₃⟩ := card_key_values hn₁ hn₂
  rw [charpoly_sector hn₁ hn₂, charpoly_tri, c₀, c₁, c₂, c₃]
  have h₁ : (n₁ : ℂ) ≠ 0 := by exact_mod_cast (show n₁ ≠ 0 by omega)
  have h₂ : (n₂ : ℂ) ≠ 0 := by exact_mod_cast (show n₂ ≠ 0 by omega)
  have v₀ : vk n₁ n₂ l₀₁ l₁₀ l₁₁ 0 = (1 + ((n₂ : ℂ) ^ 2 - 1) * l₀₁ + ((n₁ : ℂ) ^ 2 - 1) * l₁₀ +
      ((n₁ : ℂ) ^ 2 - 1) * ((n₂ : ℂ) ^ 2 - 1) * l₁₁) / ((n₁ : ℂ) * n₂) := by
    simp only [vk, fval]
    norm_num
    field_simp
  have v₁ : vk n₁ n₂ l₀₁ l₁₀ l₁₁ 1 = (1 - l₀₁ + ((n₁ : ℂ) ^ 2 - 1) * l₁₀ -
      ((n₁ : ℂ) ^ 2 - 1) * l₁₁) / ((n₁ : ℂ) * n₂) := by
    simp only [vk, fval]
    norm_num
    field_simp
    ring
  have v₂ : vk n₁ n₂ l₀₁ l₁₀ l₁₁ 2 = (1 + ((n₂ : ℂ) ^ 2 - 1) * l₀₁ - l₁₀ -
      ((n₂ : ℂ) ^ 2 - 1) * l₁₁) / ((n₁ : ℂ) * n₂) := by
    simp only [vk, fval]
    norm_num
    field_simp
    ring
  have v₃ : vk n₁ n₂ l₀₁ l₁₀ l₁₁ 3 = (1 - l₀₁ - l₁₀ + l₁₁) / ((n₁ : ℂ) * n₂) := by
    simp only [vk, fval]
    norm_num
    field_simp
    ring
  rw [v₀, v₁, v₂, v₃, pow_one]
  ring

end D5.S3.Quantum.QuantumChannels.ProductUnitaryChoiSpectrum
