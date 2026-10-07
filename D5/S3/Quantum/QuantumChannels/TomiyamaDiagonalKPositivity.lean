/- GID: D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The k-positive region of the diagonal-perturbed Tomiyama family. -/

/- Judgement:
   Each declaration below belongs to
   admission_basis: open-problem-resolution (#13894; Proved).
   Definitions have proof_shape: not-applicable; escape_witness: null:
   phi; KPositive; quadrilateral; claim; q; fourierRows; coordinateRows.
   Per-theorem proof_shape and escape_witness:
   kron_phi_apply: bind-only; null (kron_def and entry normalization).
   kron_phi_rankone_form: bind-only; null (finite-sum normalization).
   kpositive_q: bind-only; null (the rank-one PSD quadratic-form test).
   kron_phi_hermitian: bind-only; null (entrywise conjugation).
   kpositive_iff_q: bind-only; null (PSD factorization and finite sums).
   fourierRows_gram: bind-only; null (Mathlib additive-character orthogonality).
   fourierRows_diagonal: bind-only; null (unit modulus and finite sums).
   fourier_boundary: bind-only; null (the Fourier test and trace identities).
   offdiagonal_boundary: bind-only; null (the matrix-unit test).
   coordinate_boundary: bind-only; null (the coordinate-projection test).
   ranktwo_boundary: bind-only; null (the two-coordinate signed test).
   trace_rank_bound: bind-only; null (orthonormal basis and Cauchy-Schwarz).
   halfplanes_mem_quadrilateral: bind-only; null (barycentric coordinates).
   quadrilateral_kpositive: bind-only; null (the vertex bounds and convexity).
   result: bind-only; null (the four necessary bounds and vertex sufficiency).
   Every helper has a live consumer:
   q -> kron_phi_rankone_form, kpositive_iff_q, boundary and vertex proofs;
   kron_phi_apply -> kron_phi_rankone_form, kron_phi_hermitian;
   kron_phi_rankone_form -> kpositive_q, kpositive_iff_q;
   kpositive_q -> kpositive_iff_q and all four boundary proofs;
   kron_phi_hermitian -> kpositive_iff_q;
   kpositive_iff_q -> quadrilateral_kpositive;
   fourierRows -> fourierRows_gram, fourierRows_diagonal, fourier_boundary;
   fourierRows_gram, fourierRows_diagonal -> fourier_boundary;
   coordinateRows -> coordinate_boundary;
   trace_rank_bound -> quadrilateral_kpositive;
   all four boundary proofs, halfplanes_mem_quadrilateral,
   quadrilateral_kpositive -> result.
   Row-entry sums use explicit unfolding or pointwise equalities, and denominator
   conditions use positivity or linear arithmetic. Generated helpers are consumed
   in the transitive constant closure of result.
   Direct frozen dependencies (GID; statement_id):
   D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap;
     sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7
   D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.kron;
     sha256:6bbbe42180d7cde8ee171b8a1aeeb16449194862345f2042d95ec7c0b2055471
   D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.kron_def;
     sha256:0a066df1b1de64e4fda175d1ac776d744674a6465abc8a7f13b12f185ce29405
   D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.IsPositive;
     sha256:f17d83cade270607ed26a249661ca93167b5a57d01906f355672261f7aaa0cb6
   computational_content: none for every declaration: the definitions and proofs
   concern arbitrary dimensions, matrices and real parameters, with no bounded
   enumeration, checker, numerical reduction or certified fixed instance.
-/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

set_option autoImplicit false
set_option relaxedAutoImplicit false
-- Use the repository instance-synthesis depth for the column-space and basis types.
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf

namespace D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity

/-- The identity, trace-to-identity, and diagonal maps with their real coefficients. -/
def phi (d : ℕ) (α β : ℝ) : MatrixMap (Fin d) (Fin d) ℂ where
  toFun X := ((1 - α - β : ℝ) : ℂ) • X +
    ((α / (d : ℝ) : ℝ) : ℂ) • (trace X • (1 : Matrix (Fin d) (Fin d) ℂ)) +
    (β : ℂ) • diagonal (fun i => X i i)
  map_add' X Y := by
    simp only [trace_add, add_smul, smul_add, Matrix.add_apply, ← diagonal_add]
    abel
  map_smul' c X := by
    ext i j
    simp only [RingHom.id_apply, trace_smul, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.diagonal_apply]
    split_ifs <;> ring

/-- Positivity after tensoring on the left with the identity on k by k matrices. -/
def KPositive (k d : ℕ) (Φ : MatrixMap (Fin d) (Fin d) ℂ) : Prop :=
  (MatrixMap.kron (LinearMap.id : MatrixMap (Fin k) (Fin k) ℂ) Φ).IsPositive

/-- The convex hull of the four parameter vertices. All divisions are real. -/
def quadrilateral (d k : ℕ) : Set (ℝ × ℝ) :=
  convexHull ℝ {(0, 0), (0, (d : ℝ) / ((d : ℝ) - 1)),
    ((d : ℝ) / ((d : ℝ) - 1), -1 / ((d : ℝ) - 1)),
    ((k : ℝ) * (d : ℝ) / ((k : ℝ) * (d : ℝ) - 1), 0)}

/-- Conjecture 2.4 in the preregistered range 2 ≤ k ≤ d. -/
def claim : Prop :=
  ∀ d k : ℕ, 2 ≤ k → k ≤ d → ∀ α β : ℝ,
    KPositive k d (phi d α β) ↔ (α, β) ∈ quadrilateral d k

private def q {d : ℕ} (α β : ℝ) (X : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  α / (d : ℝ) * (∑ i, ∑ j, Complex.normSq (X i j)) +
    β * (∑ i, Complex.normSq (X i i)) +
    (1 - α - β) * Complex.normSq (trace X)

private theorem kron_phi_apply (k d : ℕ) (α β : ℝ)
    (Y : Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ)
    (a b : Fin k) (i j : Fin d) :
    MatrixMap.kron (LinearMap.id : MatrixMap (Fin k) (Fin k) ℂ) (phi d α β) Y
        (a, i) (b, j) =
      ((1 - α - β : ℝ) : ℂ) * Y (a, i) (b, j) +
      ((α / (d : ℝ) : ℝ) : ℂ) * (if i = j then ∑ l, Y (a, l) (b, l) else 0) +
      (β : ℂ) * (if i = j then Y (a, i) (b, i) else 0) := by
  classical
  have ht (l m : Fin d) : trace (Matrix.single l m (1 : ℂ)) =
      if l = m then 1 else 0 := by
    by_cases h : l = m <;> simp [h]
  have hid (p r : Fin k) :
      (LinearMap.id : MatrixMap (Fin k) (Fin k) ℂ) (Matrix.single p r 1) a b =
        if p = a then if r = b then 1 else 0 else 0 := by
    simp only [LinearMap.id_apply, Matrix.single_apply, ite_and]
  rw [MatrixMap.kron_def]
  simp only [hid,
    ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change (∑ l, ∑ m, (phi d α β) (Matrix.single l m 1) i j * Y (a, l) (b, m)) = _
  unfold phi
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Matrix.diagonal_apply,
    ht]
  by_cases hij : i = j
  · subst j
    simp only [if_true, Matrix.single_apply, ite_and, add_mul, ite_mul, one_mul,
      zero_mul, mul_ite, mul_zero, Finset.sum_add_distrib,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.sum_ite_eq, Finset.mem_univ, Finset.mul_sum]
    ring
  · simp only [hij, if_false, Matrix.single_apply, ite_and, ite_mul,
      mul_one, zero_mul, mul_ite, mul_zero, add_zero,
      Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem kron_phi_rankone_form (k d : ℕ) (α β : ℝ)
    (U W : Matrix (Fin k) (Fin d) ℂ) :
    star (fun p : Fin k × Fin d => U p.1 p.2) ⬝ᵥ
      (MatrixMap.kron (LinearMap.id : MatrixMap (Fin k) (Fin k) ℂ) (phi d α β)
        (vecMulVec (fun p => W p.1 p.2) (star (fun p => W p.1 p.2))) *ᵥ
          (fun p => U p.1 p.2)) = (q α β (Uᴴ * W) : ℂ) := by
  classical
  let X := Uᴴ * W
  have hx (i j : Fin d) : X i j = ∑ a, star (U a i) * W a j := rfl
  have hn (i j : Fin d) : (Complex.normSq (X i j) : ℂ) =
      ∑ a, ∑ b, (star (U a i) * W a j) * (star (W b j) * U b i) := by
    rw [← Complex.mul_conj]
    change X i j * star (X i j) = _
    simp only [hx, star_sum, star_mul, star_star,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  have ht : (Complex.normSq (trace X) : ℂ) =
      ∑ a, ∑ i, ∑ b, ∑ j,
        (star (U a i) * W a i) * (star (W b j) * U b j) := by
    rw [← Complex.mul_conj]
    change trace X * star (trace X) = _
    simp only [trace, diag_apply, hx, star_sum, star_mul,
      star_star, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_lhs =>
      enter [2, b]
      rw [Finset.sum_comm]
      enter [2, i]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs =>
      enter [2, i]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  have hf : (∑ i, ∑ j, (Complex.normSq (X i j) : ℂ)) =
      ∑ a, ∑ i, ∑ b, ∑ j,
        (star (U a i) * W a j) * (star (W b j) * U b i) := by
    simp only [hn]
    conv_lhs =>
      enter [2, i]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  have hd : (∑ i, (Complex.normSq (X i i) : ℂ)) =
      ∑ a, ∑ i, ∑ b,
        (star (U a i) * W a i) * (star (W b i) * U b i) := by
    simp only [hn]
    rw [Finset.sum_comm]
  change _ = (q α β X : ℂ)
  simp only [q, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sum,
    hf, hd, ht]
  simp only [dotProduct, mulVec, Fintype.sum_prod_type, Pi.star_apply,
    kron_phi_apply, vecMulVec_apply, mul_add, add_mul, Finset.mul_sum,
    Finset.sum_add_distrib]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  simp only [mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
  ring

private theorem kpositive_q (k d : ℕ) (α β : ℝ)
    (h : KPositive k d (phi d α β)) (U W : Matrix (Fin k) (Fin d) ℂ) :
    0 ≤ q α β (Uᴴ * W) := by
  have hp := h (posSemidef_vecMulVec_self_star (fun p : Fin k × Fin d => W p.1 p.2))
  have hz := hp.dotProduct_mulVec_nonneg (fun p : Fin k × Fin d => U p.1 p.2)
  rw [kron_phi_rankone_form] at hz
  exact_mod_cast hz

private theorem kron_phi_hermitian (k d : ℕ) (α β : ℝ)
    (Y : Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ) (hY : Y.IsHermitian) :
    (MatrixMap.kron (LinearMap.id : MatrixMap (Fin k) (Fin k) ℂ)
      (phi d α β) Y).IsHermitian := by
  classical
  apply IsHermitian.ext
  rintro ⟨a, i⟩ ⟨b, j⟩
  have he (p r : Fin k × Fin d) : star (Y r p) = Y p r :=
    (IsHermitian.ext_iff.mp hY) p r
  simp only [kron_phi_apply, star_add, star_mul,
    RCLike.star_def, Complex.conj_ofReal]
  rw [← RCLike.star_def]
  by_cases hij : i = j
  · subst j
    simp only [if_true, star_sum, he, mul_comm]
  · simp only [hij, Ne.symm hij, if_false, mul_zero, add_zero,
      star_zero, he, mul_comm]

private theorem kpositive_iff_q (k d : ℕ) (α β : ℝ) :
    KPositive k d (phi d α β) ↔
      ∀ U W : Matrix (Fin k) (Fin d) ℂ, 0 ≤ q α β (Uᴴ * W) := by
  classical
  refine ⟨fun h U W => kpositive_q k d α β h U W, ?_⟩
  intro h Y hY
  obtain ⟨B, hB⟩ : ∃ B, Y = Bᴴ * B := by
    exact CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY.nonneg
  have hsum : Y = ∑ r : Fin k × Fin d,
      vecMulVec (fun p => star (B r p)) (star (fun p => star (B r p))) := by
    rw [hB]
    ext p r
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      vecMulVec_apply, Pi.star_apply, star_star]
  rw [hsum, map_sum]
  apply posSemidef_sum
  intro r _
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · apply kron_phi_hermitian
    exact (posSemidef_vecMulVec_self_star _).isHermitian
  · intro u
    let U : Matrix (Fin k) (Fin d) ℂ := fun a i => u (a, i)
    let W : Matrix (Fin k) (Fin d) ℂ := fun a i => star (B r (a, i))
    change 0 ≤ star (fun p : Fin k × Fin d => U p.1 p.2) ⬝ᵥ
      (MatrixMap.kron (LinearMap.id : MatrixMap (Fin k) (Fin k) ℂ) (phi d α β)
        (vecMulVec (fun p => W p.1 p.2) (star (fun p => W p.1 p.2))) *ᵥ
          (fun p => U p.1 p.2))
    rw [kron_phi_rankone_form]
    exact_mod_cast h U W

private def fourierRows (k d : ℕ) [NeZero d] (hkd : k ≤ d) :
    Matrix (Fin k) (Fin d) ℂ := fun a i =>
  ZMod.stdAddChar ((ZMod.finEquiv d i) * (ZMod.finEquiv d (Fin.castLE hkd a)))

private theorem fourierRows_gram (k d : ℕ) [NeZero d] (hkd : k ≤ d) :
    fourierRows k d hkd * (fourierRows k d hkd)ᴴ =
      (d : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) := by
  classical
  let e := ZMod.finEquiv d
  let ψ : AddChar (ZMod d) ℂ := ZMod.stdAddChar
  ext a b
  change (∑ i : Fin d, ψ (e i * e (Fin.castLE hkd a)) *
    star (ψ (e i * e (Fin.castLE hkd b)))) = _
  have hm (i : Fin d) : ψ (e i * e (Fin.castLE hkd a)) *
      star (ψ (e i * e (Fin.castLE hkd b))) =
      ψ (e i * (e (Fin.castLE hkd a) - e (Fin.castLE hkd b))) := by
    rw [RCLike.star_def, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp only [hm]
  rw [Fintype.sum_equiv e.toEquiv
    (fun i => ψ (e i * (e (Fin.castLE hkd a) - e (Fin.castLE hkd b))))
    (fun x => ψ (x * (e (Fin.castLE hkd a) - e (Fin.castLE hkd b)))) (fun _ => rfl)]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar d)]
  have he : e (Fin.castLE hkd a) - e (Fin.castLE hkd b) = 0 ↔ a = b := by
    rw [sub_eq_zero, e.injective.eq_iff]
    exact (Fin.castLE_injective hkd).eq_iff
  simp only [he, ZMod.card, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Nat.cast_ite, Nat.cast_zero]

private theorem fourierRows_diagonal (k d : ℕ) [NeZero d] (hkd : k ≤ d)
    (i : Fin d) : ((fourierRows k d hkd)ᴴ * fourierRows k d hkd) i i = (k : ℂ) := by
  have hn (a : Fin k) : star (fourierRows k d hkd a i) *
      fourierRows k d hkd a i = 1 := by
    rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, fourierRows, AddChar.norm_apply, one_pow,
      Complex.ofReal_one]
  change (∑ a : Fin k, star (fourierRows k d hkd a i) * fourierRows k d hkd a i) = _
  calc
    _ = ∑ _ : Fin k, (1 : ℂ) := Finset.sum_congr rfl fun a _ => hn a
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]

private theorem fourier_boundary (k d : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d)
    (α β : ℝ) (h : KPositive k d (phi d α β)) :
    ((k : ℝ) * d - 1) * α + (k : ℝ) * (d - 1) * β ≤ (k : ℝ) * d := by
  have hd : 0 < d := by omega
  have : NeZero d := ⟨by omega⟩
  let W := fourierRows k d hkd
  let X := Wᴴ * W
  have hg : W * Wᴴ = (d : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) :=
    fourierRows_gram k d hkd
  have hx : Xᴴ = X := isHermitian_conjTranspose_mul_self W
  have hxx : Xᴴ * X = (d : ℂ) • X := by
    rw [hx]
    change Wᴴ * W * (Wᴴ * W) = _
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc W, hg,
      Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]
  have ht : trace X = (d : ℂ) * k := by
    change trace (Wᴴ * W) = _
    rw [trace_mul_comm, hg, trace_smul, trace_one, Fintype.card_fin]
    rfl
  have hf : (∑ i, ∑ j, Complex.normSq (X i j)) = (k : ℝ) * d ^ 2 := by
    have hv := star_vec_dotProduct_vec X X
    rw [hxx, trace_smul, ht] at hv
    simp only [smul_eq_mul] at hv
    have he : ((∑ i, ∑ j, Complex.normSq (X i j) : ℝ) : ℂ) =
        (d : ℂ) * ((d : ℂ) * k) := by
      rw [← hv]
      simp only [dotProduct, Matrix.vec, Fintype.sum_prod_type, Pi.star_apply,
        Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self, RCLike.star_def]
      rw [Finset.sum_comm]
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast,
      pow_two, mul_comm, mul_left_comm, mul_assoc] using he
  have hdiag : (∑ i, Complex.normSq (X i i)) = (d : ℝ) * k ^ 2 := by
    calc
      _ = ∑ _ : Fin d, Complex.normSq (k : ℂ) :=
        Finset.sum_congr rfl fun i _ => congrArg Complex.normSq (fourierRows_diagonal k d hkd i)
      _ = _ := by
        simp only [Complex.normSq_natCast, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        ring
  have htr : Complex.normSq (trace X) = ((d : ℝ) * k) ^ 2 := by
    rw [ht, Complex.normSq_mul, Complex.normSq_natCast, Complex.normSq_natCast]
    ring
  have hq := kpositive_q k d α β h W W
  change 0 ≤ q α β X at hq
  rw [q, hf, hdiag, htr] at hq
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hkr : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have he : α / (d : ℝ) * ((k : ℝ) * d ^ 2) +
      β * ((d : ℝ) * k ^ 2) + (1 - α - β) * ((d : ℝ) * k) ^ 2 =
      (k : ℝ) * d * ((k : ℝ) * d - ((k : ℝ) * d - 1) * α -
        (k : ℝ) * (d - 1) * β) := by
    field_simp
    ring
  rw [he] at hq
  have := (mul_nonneg_iff_of_pos_left (mul_pos hkr hdr)).mp hq
  linarith

private theorem offdiagonal_boundary (k d : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d)
    (α β : ℝ) (h : KPositive k d (phi d α β)) : 0 ≤ α := by
  classical
  let a : Fin k := ⟨0, by omega⟩
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by intro he; have := congrArg Fin.val he; norm_num [i, j] at this
  have hz := kpositive_q k d α β h (Matrix.single a i 1) (Matrix.single a j 1)
  simp only [conjTranspose_single, star_one, single_mul_single_same, one_mul] at hz
  have hf : (∑ p, ∑ r, Complex.normSq (Matrix.single i j (1 : ℂ) p r)) = 1 := by
    simp only [Matrix.single_apply, ite_and, apply_ite Complex.normSq,
      Complex.normSq_one, Complex.normSq_zero, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hd : (∑ p, Complex.normSq (Matrix.single i j (1 : ℂ) p p)) = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    have hn : ¬(i = p ∧ j = p) := by rintro ⟨hi, hj⟩; exact hij (hi.trans hj.symm)
    simp only [Matrix.single_apply, if_neg hn, Complex.normSq_zero]
  rw [q, hf, hd, trace_single_eq_of_ne i j 1 hij] at hz
  simp only [Complex.normSq_zero, mul_zero, add_zero, mul_one] at hz
  have hdp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  simpa only [zero_mul] using (le_div_iff₀ hdp).mp hz

private def coordinateRows (k d : ℕ) (hkd : k ≤ d) : Matrix (Fin k) (Fin d) ℂ :=
  fun a i => if Fin.castLE hkd a = i then 1 else 0

private theorem coordinate_boundary (k d : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d)
    (α β : ℝ) (h : KPositive k d (phi d α β)) :
    ((k : ℝ) * d - 1) * α + (d : ℝ) * (k - 1) * β ≤ (k : ℝ) * d := by
  classical
  let W := coordinateRows k d hkd
  let X := Wᴴ * W
  have hg : W * Wᴴ = (1 : Matrix (Fin k) (Fin k) ℂ) := by
    ext a b
    unfold W coordinateRows
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    by_cases hab : a = b
    · subst b
      simp only [apply_ite star, star_one, star_zero, ite_mul, mul_ite,
        one_mul, zero_mul, mul_zero, if_true, Finset.sum_ite_eq, Finset.mem_univ,
        Matrix.one_apply_eq]
    · have hne : Fin.castLE hkd a ≠ Fin.castLE hkd b :=
        fun he => hab (Fin.castLE_injective hkd he)
      rw [Matrix.one_apply_ne hab]
      apply Finset.sum_eq_zero
      intro i _
      by_cases hai : Fin.castLE hkd a = i
      · have hbi : Fin.castLE hkd b ≠ i := fun he => hne (hai.trans he.symm)
        simp only [hai, hbi, if_true, if_false, star_zero, mul_zero]
      · simp only [hai, if_false, zero_mul]
  have ht : trace X = (k : ℂ) := by
    change trace (Wᴴ * W) = _
    rw [trace_mul_comm, hg, trace_one, Fintype.card_fin]
  have hx : Xᴴ * X = X := by
    rw [(isHermitian_conjTranspose_mul_self W).eq]
    change Wᴴ * W * (Wᴴ * W) = _
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc W, hg, Matrix.one_mul]
  have hf : (∑ i, ∑ j, Complex.normSq (X i j)) = (k : ℝ) := by
    have hv := star_vec_dotProduct_vec X X
    rw [hx, ht] at hv
    apply Complex.ofReal_injective
    rw [Complex.ofReal_natCast, ← hv]
    simp only [dotProduct, Matrix.vec, Fintype.sum_prod_type, Pi.star_apply,
      Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self, RCLike.star_def]
    rw [Finset.sum_comm]
  have hz (i j : Fin d) (hij : i ≠ j) : X i j = 0 := by
    change ∑ a : Fin k, star (W a i) * W a j = 0
    unfold W coordinateRows
    apply Finset.sum_eq_zero
    intro a _
    by_cases hai : Fin.castLE hkd a = i
    · have haj : Fin.castLE hkd a ≠ j := fun he => hij (hai.symm.trans he)
      simp only [hai, hij, if_true, if_false, mul_zero]
    · simp only [hai, if_false, star_zero, zero_mul]
  have hdiag : (∑ i, Complex.normSq (X i i)) = (k : ℝ) := by
    rw [← hf]
    apply Finset.sum_congr rfl
    intro i _
    symm
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [hz i j hji.symm, Complex.normSq_zero]
    · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
  have hq := kpositive_q k d α β h W W
  change 0 ≤ q α β X at hq
  rw [q, hf, hdiag, ht, Complex.normSq_natCast] at hq
  have hD : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hK : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have he : α / (d : ℝ) * k + β * k + (1 - α - β) * ((k : ℝ) * k) =
      (k : ℝ) / d * ((k : ℝ) * d - ((k : ℝ) * d - 1) * α -
        (d : ℝ) * (k - 1) * β) := by field_simp; ring
  rw [he] at hq
  have := (mul_nonneg_iff_of_pos_left (div_pos hK hD)).mp hq
  linarith

private theorem ranktwo_boundary (k d : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d)
    (α β : ℝ) (h : KPositive k d (phi d α β)) : 0 ≤ α + (d : ℝ) * β := by
  classical
  let a : Fin k := ⟨0, by omega⟩
  let b : Fin k := ⟨1, by omega⟩
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hab : a ≠ b := by intro he; have := congrArg Fin.val he; norm_num [a, b] at this
  have hij : i ≠ j := by intro he; have := congrArg Fin.val he; norm_num [i, j] at this
  let U : Matrix (Fin k) (Fin d) ℂ := Matrix.single a i 1 + Matrix.single b j 1
  let W : Matrix (Fin k) (Fin d) ℂ := Matrix.single a i 1 - Matrix.single b j 1
  let v : Fin d → ℂ := fun p => if i = p then 1 else if j = p then -1 else 0
  have hx : Uᴴ * W = diagonal v := by
    simp only [U, W, conjTranspose_add, conjTranspose_single, star_one,
      Matrix.add_mul, Matrix.mul_sub, single_mul_single_same,
      single_mul_single_of_ne _ _ _ _ hab, single_mul_single_of_ne _ _ _ _ hab.symm,
      one_mul, add_zero, zero_add]
    ext p r
    by_cases hpr : p = r
    · subst r
      by_cases hip : i = p
      · have hjp : j ≠ p := fun he => hij (hip.trans he.symm)
        simp [v, hip, hjp]
      · by_cases hjp : j = p <;> simp [v, hip, hjp]
    · have hipr : ¬(i = p ∧ i = r) := fun he => hpr (he.1.symm.trans he.2)
      have hjpr : ¬(j = p ∧ j = r) := fun he => hpr (he.1.symm.trans he.2)
      simp only [Matrix.sub_apply, Matrix.single_apply, if_neg hipr, if_neg hjpr,
        sub_self, Matrix.diagonal_apply, if_neg hpr]
  have hd : (∑ p, Complex.normSq (v p)) = 2 := by
    have hn (p : Fin d) : Complex.normSq (v p) =
        (if i = p then 1 else 0) + (if j = p then 1 else 0) := by
      by_cases hip : i = p
      · have hjp : j ≠ p := fun he => hij (hip.trans he.symm)
        simp [v, hip, hjp]
      · by_cases hjp : j = p <;> simp [v, hip, hjp]
    simp only [hn, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    norm_num
  have hf : (∑ p, ∑ r, Complex.normSq (diagonal v p r)) = 2 := by
    simp only [Matrix.diagonal_apply, apply_ite Complex.normSq, Complex.normSq_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, hd]
  have ht : trace (diagonal v) = 0 := by
    rw [trace_diagonal]
    have hv (p : Fin d) : v p = (if i = p then 1 else 0) - (if j = p then 1 else 0) := by
      by_cases hip : i = p
      · have hjp : j ≠ p := fun he => hij (hip.trans he.symm)
        simp [v, hip, hjp]
      · by_cases hjp : j = p <;> simp [v, hip, hjp]
    simp only [hv, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, sub_self]
  have hq := kpositive_q k d α β h U W
  simp only [hx, q, hf, diagonal_apply_eq, hd, ht, Complex.normSq_zero,
    mul_zero, add_zero] at hq
  have hD : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hh : 0 ≤ α / (d : ℝ) + β := by linarith
  have := mul_nonneg hh hD.le
  rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hD)] at this
  nlinarith

private theorem trace_rank_bound (k d : ℕ) (U W : Matrix (Fin k) (Fin d) ℂ) :
    Complex.normSq (trace (Uᴴ * W)) ≤
      (k : ℝ) * ∑ i, ∑ j, Complex.normSq ((Uᴴ * W) i j) := by
  classical
  let E := EuclideanSpace ℂ (Fin d)
  let L := Matrix.toEuclideanLin Uᴴ
  let S := LinearMap.range L
  let b := stdOrthonormalBasis ℂ S
  let X := Uᴴ * W
  let col (i : Fin d) : S := ⟨WithLp.toLp 2 (fun j => X j i), by
    refine ⟨WithLp.toLp 2 (fun a => W a i), ?_⟩
    rfl⟩
  let c (s : Fin (Module.finrank ℂ S)) (i : Fin d) : ℂ := inner ℂ (b s) (col i)
  let t (s : Fin (Module.finrank ℂ S)) : ℂ := ∑ i, c s i * (b s : E) i
  have hx (i : Fin d) : X i i = ∑ s, c s i * (b s : E) i := by
    have he := congrArg (fun v : S => (v : E) i) (b.sum_repr (col i))
    simpa only [Submodule.coe_sum, Submodule.coe_smul, WithLp.ofLp_sum, Finset.sum_apply,
      PiLp.smul_apply, smul_eq_mul, b.repr_apply_apply] using he.symm
  have ht : trace X = ∑ s, t s := by
    simp only [trace, diag_apply, hx, t]
    rw [Finset.sum_comm]
  have hb (s : Fin (Module.finrank ℂ S)) : ∑ i, ‖(b s : E) i‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq]
    change ‖b s‖ ^ 2 = 1
    rw [b.orthonormal.norm_eq_one, one_pow]
  have hc (i : Fin d) : ∑ s, ‖c s i‖ ^ 2 = ∑ j, ‖X j i‖ ^ 2 := by
    rw [b.sum_sq_norm_inner_right]
    change ‖(col i : E)‖ ^ 2 = _
    rw [EuclideanSpace.norm_sq_eq]
  have hts (s : Fin (Module.finrank ℂ S)) : ‖t s‖ ^ 2 ≤ ∑ i, ‖c s i‖ ^ 2 := by
    have hn : ‖t s‖ ≤ ∑ i, ‖c s i‖ * ‖(b s : E) i‖ := by
      simpa only [t, norm_mul] using norm_sum_le (Finset.univ)
        (fun i => c s i * (b s : E) i)
    have hs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d))
      (fun i => ‖c s i‖) (fun i => ‖(b s : E) i‖)
    rw [hb, mul_one] at hs
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hs
  have hn : ‖trace X‖ ≤ ∑ s, ‖t s‖ := by rw [ht]; exact norm_sum_le _ _
  have hs : (∑ s, ‖t s‖) ^ 2 ≤
      (Module.finrank ℂ S : ℝ) * ∑ s, ‖t s‖ ^ 2 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun s => ‖t s‖))
  have hf : (∑ s, ‖t s‖ ^ 2) ≤ ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
    calc
      _ ≤ ∑ s, ∑ i, ‖c s i‖ ^ 2 := Finset.sum_le_sum fun s _ => hts s
      _ = _ := by rw [Finset.sum_comm]; simp only [hc]; rw [Finset.sum_comm]
  have hr : Module.finrank ℂ S ≤ k := by
    exact (LinearMap.finrank_range_le L).trans (by simp)
  have hrr : (Module.finrank ℂ S : ℝ) ≤ k := by exact_mod_cast hr
  rw [Complex.normSq_eq_norm_sq]
  change ‖trace X‖ ^ 2 ≤ _
  simp only [Complex.normSq_eq_norm_sq]
  calc
    ‖trace X‖ ^ 2 ≤ (∑ s, ‖t s‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ ≤ _ := hs
    _ ≤ (Module.finrank ℂ S : ℝ) * (∑ i, ∑ j, ‖X i j‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right hrr (by positivity)

private theorem halfplanes_mem_quadrilateral (d k : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d)
    (α β : ℝ) (hα : 0 ≤ α) (hdiag : 0 ≤ α + (d : ℝ) * β)
    (hneg : ((k : ℝ) * d - 1) * α + (d : ℝ) * (k - 1) * β ≤ (k : ℝ) * d)
    (hpos : ((k : ℝ) * d - 1) * α + (k : ℝ) * (d - 1) * β ≤ (k : ℝ) * d) :
    (α, β) ∈ quadrilateral d k := by
  have hd : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  have hkr : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hD : (0 : ℝ) < d := by linarith
  have hT : (0 : ℝ) < (k : ℝ) * d := mul_pos (by linarith) hD
  have hTm : (0 : ℝ) < (k : ℝ) * d - 1 := by nlinarith
  let S : Set (ℝ × ℝ) := {(0, 0), (0, (d : ℝ) / (d - 1)),
    ((d : ℝ) / (d - 1), -1 / ((d : ℝ) - 1)),
    ((k : ℝ) * d / ((k : ℝ) * d - 1), 0)}
  change (α, β) ∈ convexHull ℝ S
  by_cases hβ : 0 ≤ β
  · let a : ℝ := β * (d - 1) / d
    let c : ℝ := α * ((k : ℝ) * d - 1) / ((k : ℝ) * d)
    let w : Fin 3 → ℝ := ![1 - a - c, a, c]
    let z : Fin 3 → ℝ × ℝ := ![(0, 0), (0, (d : ℝ) / (d - 1)),
      ((k : ℝ) * d / ((k : ℝ) * d - 1), 0)]
    have ha : 0 ≤ a := div_nonneg (mul_nonneg hβ (by linarith)) hD.le
    have hc : 0 ≤ c := div_nonneg (mul_nonneg hα hTm.le) hT.le
    have he : (1 - a - c) * ((k : ℝ) * d) =
        (k : ℝ) * d - ((k : ℝ) * d - 1) * α - (k : ℝ) * (d - 1) * β := by
      dsimp [a, c]
      field_simp (disch := first | positivity | linarith)
      ring
    have ho : 0 ≤ 1 - a - c := by nlinarith
    have hw : ∀ r ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ w r := by
      intro r _
      fin_cases r <;> exact (by assumption)
    have hs : ∑ r : Fin 3, w r = 1 := by simp [w, Fin.sum_univ_three]; ring
    have hz : ∀ r ∈ (Finset.univ : Finset (Fin 3)), z r ∈ convexHull ℝ S := by
      intro r _
      apply subset_convexHull
      fin_cases r <;> simp [z, S]
    have hm := (convex_convexHull ℝ S).sum_mem hw hs hz
    have heq : (∑ r : Fin 3, w r • z r) = (α, β) := by
      ext <;> simp [w, z, a, c, Fin.sum_univ_three, smul_eq_mul]
      · field_simp (disch := first | positivity | linarith)
      · field_simp (disch := first | positivity | linarith)
    rw [heq] at hm
    exact hm
  · have hβ' : β ≤ 0 := le_of_not_ge hβ
    let a : ℝ := -β * (d - 1)
    let c : ℝ := (α + (d : ℝ) * β) * ((k : ℝ) * d - 1) / ((k : ℝ) * d)
    let w : Fin 3 → ℝ := ![1 - a - c, a, c]
    let z : Fin 3 → ℝ × ℝ := ![(0, 0),
      ((d : ℝ) / (d - 1), -1 / ((d : ℝ) - 1)),
      ((k : ℝ) * d / ((k : ℝ) * d - 1), 0)]
    have ha : 0 ≤ a := mul_nonneg (neg_nonneg.mpr hβ') (by linarith)
    have hc : 0 ≤ c := div_nonneg (mul_nonneg hdiag hTm.le) hT.le
    have he : (1 - a - c) * ((k : ℝ) * d) =
        (k : ℝ) * d - ((k : ℝ) * d - 1) * α - (d : ℝ) * (k - 1) * β := by
      dsimp [a, c]
      field_simp (disch := first | positivity | linarith)
      ring
    have ho : 0 ≤ 1 - a - c := by nlinarith
    have hw : ∀ r ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ w r := by
      intro r _
      fin_cases r <;> exact (by assumption)
    have hs : ∑ r : Fin 3, w r = 1 := by simp [w, Fin.sum_univ_three]; ring
    have hz : ∀ r ∈ (Finset.univ : Finset (Fin 3)), z r ∈ convexHull ℝ S := by
      intro r _
      apply subset_convexHull
      fin_cases r <;> simp [z, S]
    have hm := (convex_convexHull ℝ S).sum_mem hw hs hz
    have hc' : c * ((k : ℝ) * d / ((k : ℝ) * d - 1)) = α + (d : ℝ) * β := by
      dsimp [c]
      rw [mul_div_assoc, mul_assoc, div_mul_div_cancel₀ (ne_of_gt hT),
        div_self (ne_of_gt hTm), mul_one]
    have heq : (∑ r : Fin 3, w r • z r) = (α, β) := by
      ext <;> simp only [Fin.sum_univ_three, w, z, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul, mul_zero, zero_add, add_zero]
      · rw [hc']
        dsimp [a]
        field_simp (disch := first | positivity | linarith)
        ring
      · dsimp [a]
        field_simp (disch := first | positivity | linarith)
    rw [heq] at hm
    exact hm

private theorem quadrilateral_kpositive (d k : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d)
    (α β : ℝ) (h : (α, β) ∈ quadrilateral d k) : KPositive k d (phi d α β) := by
  classical
  let C : Set (ℝ × ℝ) := {p | ∀ U W : Matrix (Fin k) (Fin d) ℂ,
    0 ≤ q p.1 p.2 (Uᴴ * W)}
  have hc : Convex ℝ C := by
    intro x hx y hy a b ha hb hab U W
    change 0 ≤ q (a * x.1 + b * y.1) (a * x.2 + b * y.2) (Uᴴ * W)
    have he : q (a * x.1 + b * y.1) (a * x.2 + b * y.2) (Uᴴ * W) =
        a * q x.1 x.2 (Uᴴ * W) + b * q y.1 y.2 (Uᴴ * W) := by
      dsimp [q]
      linear_combination -(Complex.normSq (trace (Uᴴ * W))) * hab
    rw [he]
    exact add_nonneg (mul_nonneg ha (hx U W)) (mul_nonneg hb (hy U W))
  have hd : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  have hD : (0 : ℝ) < d := by linarith
  have hK : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hT : (0 : ℝ) < (k : ℝ) * d - 1 := by nlinarith
  have hv : {(0, 0), (0, (d : ℝ) / (d - 1)),
      ((d : ℝ) / (d - 1), -1 / ((d : ℝ) - 1)),
      ((k : ℝ) * d / ((k : ℝ) * d - 1), 0)} ⊆ C := by
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> intro U W
    · simp only [q, zero_div, zero_mul, sub_zero, one_mul, zero_add]
      exact Complex.normSq_nonneg _
    · let X := Uᴴ * W
      have hcs : Complex.normSq (trace X) ≤ (d : ℝ) * ∑ i, Complex.normSq (X i i) := by
        have hn : ‖trace X‖ ≤ ∑ i, ‖X i i‖ := norm_sum_le _ _
        have hs : (∑ i, ‖X i i‖) ^ 2 ≤ (d : ℝ) * ∑ i, ‖X i i‖ ^ 2 := by
          simpa only [Finset.card_univ, Fintype.card_fin] using
            (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖X i i‖))
        simp only [Complex.normSq_eq_norm_sq]
        exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hs
      change 0 ≤ q 0 ((d : ℝ) / (d - 1)) X
      have he : q 0 ((d : ℝ) / (d - 1)) X =
          ((d : ℝ) * (∑ i, Complex.normSq (X i i)) - Complex.normSq (trace X)) / (d - 1) := by
        dsimp [q]
        field_simp (disch := first | positivity | linarith)
        ring
      rw [he]
      exact div_nonneg (sub_nonneg.mpr hcs) (sub_pos.mpr hd).le
    · let X := Uᴴ * W
      have hf : (∑ i, Complex.normSq (X i i)) ≤ ∑ i, ∑ j, Complex.normSq (X i j) := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (X i j))
          (Finset.mem_univ i)
      change 0 ≤ q ((d : ℝ) / (d - 1)) (-1 / ((d : ℝ) - 1)) X
      have he : q ((d : ℝ) / (d - 1)) (-1 / ((d : ℝ) - 1)) X =
          ((∑ i, ∑ j, Complex.normSq (X i j)) - (∑ i, Complex.normSq (X i i))) / (d - 1) := by
        dsimp [q]
        field_simp (disch := first | positivity | linarith)
        ring
      rw [he]
      exact div_nonneg (sub_nonneg.mpr hf) (sub_pos.mpr hd).le
    · let X := Uᴴ * W
      have hf := trace_rank_bound k d U W
      change 0 ≤ q ((k : ℝ) * d / ((k : ℝ) * d - 1)) 0 X
      have he : q ((k : ℝ) * d / ((k : ℝ) * d - 1)) 0 X =
          ((k : ℝ) * (∑ i, ∑ j, Complex.normSq (X i j)) - Complex.normSq (trace X)) /
            ((k : ℝ) * d - 1) := by
        dsimp [q]
        field_simp (disch := first | positivity | linarith)
        ring
      rw [he]
      exact div_nonneg (sub_nonneg.mpr hf) hT.le
  exact (kpositive_iff_q k d α β).mpr ((convexHull_min hv hc) h)

/-- The k-positive region is exactly the four-vertex convex hull for 2 ≤ k ≤ d. -/
theorem result : claim := by
  intro d k hk hkd α β
  constructor
  · intro h
    exact halfplanes_mem_quadrilateral d k hk hkd α β
      (offdiagonal_boundary k d hk hkd α β h) (ranktwo_boundary k d hk hkd α β h)
      (coordinate_boundary k d hk hkd α β h) (fourier_boundary k d hk hkd α β h)
  · exact quadrilateral_kpositive d k hk hkd α β

end D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity
