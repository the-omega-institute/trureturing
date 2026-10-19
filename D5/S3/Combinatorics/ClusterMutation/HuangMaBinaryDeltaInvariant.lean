/- GID: D5/S3/Combinatorics/ClusterMutation/HuangMaBinaryDeltaInvariant
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ClusterMutation/HuangMaBinaryDeltaInvariant
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: A fixed positive skew-symmetrizer permits at most two delta residues. -/

/-
result
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#18784; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/18988
The public definitions reproduce the source's symmetrizer, symmetrization and binary claim.
The private rational determinant-square step applies the frozen symplectic-basis theorem.

Frozen dependencies (declaration statement_id; not module pins):
  D5/S3/QuadraticForms/SymplecticBasis.IsSymplecticBasis:
    sha256:43b0425e1471d88988cc2eaa21cd6fd2571e07cbacc060e6c04701c369265b96
  D5/S3/QuadraticForms/SymplecticBasis.IsSymplecticBasis.inl_inl:
    sha256:4d2ba2bdc4218d991cf6a116372e1804cc2157d0c0f5c0942868a7fe6071d4d5
  D5/S3/QuadraticForms/SymplecticBasis.IsSymplecticBasis.inl_inr_of_ne:
    sha256:4e9ed78a69faeff861137c52eda4f1d00bfe7fdccc32cbb947d60e18767deca0
  D5/S3/QuadraticForms/SymplecticBasis.IsSymplecticBasis.inl_inr_self:
    sha256:ad925510dd3b027c9315f6166495d9798fd594a3062ae7bf0687d697877c6bc3
  D5/S3/QuadraticForms/SymplecticBasis.IsSymplecticBasis.inr_inr:
    sha256:a0ffa5aa9c57e2d1ba5a3fd2ebefb64a163ecea506bb4d94d51d4c3e3cfde934
  D5/S3/QuadraticForms/SymplecticBasis.exists_isSymplecticBasis:
    sha256:856da0a7b5b6aa1db96a53c7ea0ff9d139d01f99b195080d626ae9499e853543

Declarations (all escape_witness values are none; definitions have no proof term):
  IsSkewSymmetrizer: proof_shape: definition; consumers: claim, diag_zero, companion_balance, det_companion, det_skew_odd, companion_mod_two, companion_det_mod_two, odd_binary, companion_weighted, companion_prod_inv, skew_prod_inv, companion_congruence, weighted_det_square, result; frozen dependencies: none.
  symmetrization: proof_shape: definition; consumers: claim, companion_balance, det_companion, odd_binary, result; frozen dependencies: none.
  claim: proof_shape: definition; consumers: result (statement); frozen dependencies: none.
  companion: proof_shape: definition; consumers: companion_balance, det_companion, companion_mod_two, companion_det_mod_two, odd_binary, companion_weighted, companion_prod_inv, involution_companion, companion_congruence, result; frozen dependencies: none.
  diag_zero: proof_shape: bind-only; consumers: companion_mod_two, companion_congruence; frozen dependencies: none.
  sqrt_balance: proof_shape: bind-only; consumers: companion_balance; frozen dependencies: none.
  companion_balance: proof_shape: bind-only; consumers: det_companion; frozen dependencies: none.
  det_companion: proof_shape: bind-only; consumers: odd_binary, result; frozen dependencies: none.
  det_skew_odd: proof_shape: bind-only; consumers: odd_binary; frozen dependencies: none.
  companion_mod_two: proof_shape: bind-only; consumers: companion_det_mod_two, companion_congruence; frozen dependencies: none.
  companion_det_mod_two: proof_shape: bind-only; consumers: odd_binary; frozen dependencies: none.
  zmod_four_even: proof_shape: bind-only; consumers: odd_binary, companion_congruence; frozen dependencies: none.
  odd_binary: proof_shape: bind-only; consumers: result; frozen dependencies: none.
  involution_product: proof_shape: bind-only; consumers: involution_card, involution_companion; frozen dependencies: none.
  involution_card: proof_shape: bind-only; consumers: involution_companion; frozen dependencies: none.
  companion_weighted: proof_shape: bind-only; consumers: companion_prod_inv; frozen dependencies: none.
  weighted_prod_reverse: proof_shape: bind-only; consumers: companion_prod_inv; frozen dependencies: none.
  companion_prod_inv: proof_shape: bind-only; consumers: companion_congruence; frozen dependencies: none.
  skew_prod_inv: proof_shape: bind-only; consumers: companion_congruence; frozen dependencies: none.
  involution_companion: proof_shape: bind-only; consumers: companion_congruence; frozen dependencies: none.
  companion_congruence: proof_shape: bind-only; consumers: result; frozen dependencies: none.
  alternating_det_square: proof_shape: bind-only; consumers: weighted_det_square; frozen dependencies: symplectic-basis declarations above.
  weighted_det_square: proof_shape: bind-only; consumers: result; frozen dependencies: symplectic-basis declarations above.
  square_weight_cancel: proof_shape: bind-only; consumers: weighted_square_residues; frozen dependencies: none.
  nonzero_square_residues: proof_shape: bind-only; consumers: weighted_square_residues; frozen dependencies: none.
  weighted_square_residues: proof_shape: bind-only; consumers: result; frozen dependencies: none.
  result: proof_shape: bind-only; consumers: settling result; frozen dependencies: symplectic-basis declarations above.
-/
import D5.S3.QuadraticForms.SymplecticBasis
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false

namespace D5.S3.Combinatorics.ClusterMutation.HuangMaBinaryDeltaInvariant

open Matrix

/-- "B is called skew-symmetrizable if there exists a diagonal matrix D = diag(d₁, …, dₙ) with positive
integers dᵢ such that DB is skew-symmetric. Such a matrix D is called a skew-symmetrizer of B." -/
def IsSkewSymmetrizer {n : ℕ} (d : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i, 0 < d i) ∧ ∀ i j, (d i : ℤ) * B i j = -((d j : ℤ) * B j i)

/-- The symmetrization `S(B)` (Huang–Ma, following [FWZ16, Definition 2.7.8]): `sᵢᵢ = 2`,
`sᵢⱼ = sgn(bᵢⱼ) √|bᵢⱼ bⱼᵢ|` for `i < j`, and `sᵢⱼ = sgn(bⱼᵢ) √|bᵢⱼ bⱼᵢ|` for `i > j`. -/
noncomputable def symmetrization {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    if i = j then 2
    else if i < j then (Int.sign (B i j) : ℝ) * Real.sqrt |((B i j : ℤ) : ℝ) * (B j i : ℝ)|
    else (Int.sign (B j i) : ℝ) * Real.sqrt |((B i j : ℤ) : ℝ) * (B j i : ℝ)|

/-- Huang–Ma, Remark 2.7: "We also conjecture that for any fixed n and any choice of skew-symmetrizer
d₁, …, dₙ, the invariant δ is binary", where δ(B) := det(S(B)) (mod 4) (Definition 1.3; det(S(B)) ∈ ℤ
by Lemma 1.2). Binary: at most two residues occur. -/
def claim : Prop :=
  ∀ (n : ℕ) (d : Fin n → ℕ), (∀ i, 0 < d i) →
    ∃ r₁ r₂ : ZMod 4, ∀ B : Matrix (Fin n) (Fin n) ℤ, IsSkewSymmetrizer d B →
      ∃ k : ℤ, (symmetrization B).det = k ∧ ((k : ZMod 4) = r₁ ∨ (k : ZMod 4) = r₂)

end D5.S3.Combinatorics.ClusterMutation.HuangMaBinaryDeltaInvariant

namespace D5.S3.Combinatorics.ClusterMutation.HuangMaBinaryDeltaInvariant
open Matrix Finset
set_option maxRecDepth 2048

private def companion {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i = j then 2 else if i < j then B i j else -B i j

private theorem diag_zero {n : ℕ} {d : Fin n → ℕ} {B : Matrix (Fin n) (Fin n) ℤ}
    (h : IsSkewSymmetrizer d B) (i : Fin n) : B i i = 0 := by
  have hi : (d i : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (h.1 i))
  have hh := h.2 i i
  have hz : (d i : ℤ) * B i i = 0 := CharZero.eq_neg_self_iff.mp hh
  exact (mul_eq_zero.mp hz).resolve_left hi

private theorem sqrt_balance (a b : ℤ) (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x * (a : ℝ) = -(y * (b : ℝ))) :
    Real.sqrt x * (a : ℝ) = (Int.sign a : ℝ) * Real.sqrt |(a : ℝ) * (b : ℝ)| * Real.sqrt y := by
  have he : x * (a : ℝ)^2 = -(y * ((a : ℝ) * (b : ℝ))) := by
    have hh := congrArg (fun z : ℝ => z * (a : ℝ)) h
    nlinarith only [hh]
  have hp : (a : ℝ) * (b : ℝ) ≤ 0 := by
    have hh : y * ((a : ℝ) * (b : ℝ)) ≤ 0 := by
      nlinarith [mul_nonneg hx.le (sq_nonneg (a : ℝ))]
    exact nonpos_of_mul_nonpos_right hh hy
  have hs : Real.sqrt x * |(a : ℝ)| = Real.sqrt |(a : ℝ) * (b : ℝ)| * Real.sqrt y := by
    calc
      _ = Real.sqrt (x * (a : ℝ)^2) := by rw [Real.sqrt_mul hx.le, Real.sqrt_sq_eq_abs]
      _ = Real.sqrt (|(a : ℝ) * (b : ℝ)| * y) := by
        congr 1
        rw [abs_of_nonpos hp]
        nlinarith only [he]
      _ = _ := Real.sqrt_mul (abs_nonneg _) _
  have hsign : (Int.sign a : ℝ) * |(a : ℝ)| = (a : ℝ) := by
    exact_mod_cast Int.sign_mul_abs a
  calc
    _ = Real.sqrt x * ((Int.sign a : ℝ) * |(a : ℝ)|) := by rw [hsign]
    _ = _ := by rw [mul_left_comm, hs]; ring

private theorem companion_balance {n : ℕ} {d : Fin n → ℕ} {B : Matrix (Fin n) (Fin n) ℤ}
    (h : IsSkewSymmetrizer d B) (i j : Fin n) :
    Real.sqrt (d i) * ((companion B i j : ℤ) : ℝ) = symmetrization B i j * Real.sqrt (d j) := by
  have hd (k : Fin n) : (0 : ℝ) < (d k : ℝ) := by exact_mod_cast h.1 k
  have hh (k l : Fin n) : (d k : ℝ) * (B k l : ℝ) = -((d l : ℝ) * (B l k : ℝ)) := by
    exact_mod_cast h.2 k l
  by_cases hij : i = j
  · subst j
    simp [companion, symmetrization]
    ring
  · by_cases hlt : i < j
    · simpa [companion, symmetrization, hij, hlt] using sqrt_balance (B i j) (B j i) (d i) (d j) (hd i) (hd j) (hh i j)
    · have hswap := sqrt_balance (B j i) (B i j) (d j) (d i) (hd j) (hd i) (hh j i)
      have hsq := Real.sq_sqrt (hd i).le
      have hsq' := Real.sq_sqrt (hd j).le
      simp only [companion, symmetrization, ite_eq_right hij, ite_eq_right hlt, Int.cast_neg]
      have hr := hh i j
      apply mul_right_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (hd i)))
      calc
        _ = -( (d i : ℝ) * (B i j : ℝ)) := by
          calc
            _ = -(Real.sqrt (d i) ^ 2 * (B i j : ℝ)) := by ring
            _ = _ := by rw [hsq]
        _ = (d j : ℝ) * (B j i : ℝ) := by linarith only [hr]
        _ = (Real.sqrt (d j) * (B j i : ℝ)) * Real.sqrt (d j) := by
          calc
            _ = Real.sqrt (d j) ^ 2 * (B j i : ℝ) := by rw [hsq']
            _ = _ := by ring
        _ = _ := by rw [hswap, mul_comm (B j i : ℝ) (B i j : ℝ)]; ring


private theorem det_companion {n : ℕ} {d : Fin n → ℕ} {B : Matrix (Fin n) (Fin n) ℤ}
    (h : IsSkewSymmetrizer d B) :
    (symmetrization B).det = ((companion B).det : ℝ) := by
  let D : Matrix (Fin n) (Fin n) ℝ := diagonal (fun i => Real.sqrt (d i))
  have hmat : D * (companion B).map (Int.castRingHom ℝ) = symmetrization B * D := by
    ext i j
    simpa [D, diagonal_mul, mul_diagonal] using companion_balance h i j
  have hd : D.det ≠ 0 := by
    simp only [D, det_diagonal]
    exact prod_ne_zero_iff.mpr (fun i _ => ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast h.1 i)))
  have hh := congrArg Matrix.det hmat
  rw [det_mul, det_mul] at hh
  have hc := (Int.castRingHom ℝ).map_det (companion B)
  change ((companion B).det : ℝ) = ((companion B).map (Int.castRingHom ℝ)).det at hc
  rw [← hc] at hh
  exact (mul_left_cancel₀ hd (hh.trans (mul_comm _ _))).symm

private theorem det_skew_odd {n : ℕ} {d : Fin n → ℕ} {B : Matrix (Fin n) (Fin n) ℤ}
    (h : IsSkewSymmetrizer d B) (hn : Odd n) : B.det = 0 := by
  let D : Matrix (Fin n) (Fin n) ℤ := diagonal (fun i => (d i : ℤ))
  have ht : (D * B)ᵀ = -(D * B) := by
    ext i j
    simpa [D, diagonal_mul] using h.2 j i
  have hh := Matrix.det_transpose (D * B)
  rw [ht, Matrix.det_neg, Fintype.card_fin, hn.neg_one_pow] at hh
  have hz : (D * B).det = 0 := CharZero.neg_eq_self_iff.mp (by simpa only [neg_one_mul] using hh)
  rw [Matrix.det_mul] at hz
  have hd : D.det ≠ 0 := by
    simp only [D, det_diagonal]
    exact prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast Nat.ne_of_gt (h.1 i))
  exact (mul_eq_zero.mp hz).resolve_left hd

private theorem companion_mod_two {n : ℕ} {d : Fin n → ℕ} {B : Matrix (Fin n) (Fin n) ℤ}
    (h : IsSkewSymmetrizer d B) :
    (companion B).map (Int.castRingHom (ZMod 2)) = B.map (Int.castRingHom (ZMod 2)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [companion, diag_zero h]
    decide +kernel
  · simp only [Matrix.map_apply, companion, ite_eq_right hij]
    split_ifs <;> simp

private theorem companion_det_mod_two {n : ℕ} {d : Fin n → ℕ} {B : Matrix (Fin n) (Fin n) ℤ}
    (h : IsSkewSymmetrizer d B) :
    ((companion B).det : ZMod 2) = (B.det : ZMod 2) := by
  rw [Int.cast_det, Int.cast_det]
  exact congrArg Matrix.det (companion_mod_two h)

private theorem zmod_four_even (k : ℤ) (h : (k : ZMod 2) = 0) :
    (k : ZMod 4) = 0 ∨ (k : ZMod 4) = 2 := by
  obtain ⟨j, rfl⟩ := ZMod.intCast_eq_zero_iff_even.mp h
  push_cast
  generalize (j : ZMod 4) = j'
  fin_cases j' <;> decide +kernel

private theorem odd_binary {n : ℕ} {d : Fin n → ℕ} {B : Matrix (Fin n) (Fin n) ℤ}
    (h : IsSkewSymmetrizer d B) (hn : Odd n) :
    ∃ k : ℤ, (symmetrization B).det = k ∧ ((k : ZMod 4) = 0 ∨ (k : ZMod 4) = 2) := by
  refine ⟨(companion B).det, det_companion h, zmod_four_even _ ?_⟩
  rw [companion_det_mod_two h, det_skew_odd h hn, Int.cast_zero]

private theorem involution_product {n : ℕ} {R : Type*} [CommMonoid R]
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ i, σ (σ i) = i) (f : Fin n → R) :
    (∏ i, f i) = (∏ i with σ i = i, f i) * (∏ i with i < σ i, f i * f (σ i)) := by
  let F := univ.filter (fun i => σ i = i)
  let L := univ.filter (fun i => i < σ i)
  let U := univ.filter (fun i => σ i < i)
  have hU : (∏ i ∈ U, f i) = ∏ i ∈ L, f (σ i) := by
    apply Finset.prod_bij (fun i _ => σ i)
    · intro i hi
      simp only [U, mem_filter, mem_univ, true_and] at hi
      simp [L, hσ, hi]
    · intro i hi j hj hij
      exact σ.injective hij
    · intro j hj
      refine ⟨σ j, ?_, hσ j⟩
      simpa [L, U, hσ] using hj
    · intro i hi
      rw [hσ]
  have hFL : Disjoint F L := by
    apply disjoint_left.mpr
    intro i hi hj
    simp only [F, L, mem_filter, mem_univ, true_and] at hi hj
    omega
  have hFU : Disjoint (F ∪ L) U := by
    apply disjoint_left.mpr
    intro i hi hj
    simp only [F, L, U, mem_union, mem_filter, mem_univ, true_and] at hi hj
    omega
  have hall : F ∪ L ∪ U = univ := by
    ext i
    simp only [F, L, U, mem_union, mem_filter, mem_univ, true_and, iff_true]
    omega
  calc
    _ = ∏ i ∈ F ∪ L ∪ U, f i := by rw [hall]
    _ = ((∏ i ∈ F, f i) * ∏ i ∈ L, f i) * ∏ i ∈ U, f i := by rw [Finset.prod_union hFU, Finset.prod_union hFL]
    _ = _ := by rw [hU, mul_assoc, ← Finset.prod_mul_distrib]

private theorem involution_card {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ i, σ (σ i) = i) :
    n = (univ.filter (fun i => σ i = i)).card + 2 * (univ.filter (fun i => i < σ i)).card := by
  simpa [Nat.mul_comm] using congrArg Multiplicative.toAdd
    (involution_product σ hσ (fun _ => Multiplicative.ofAdd (1 : ℕ)))

private theorem companion_weighted {n : ℕ} {d : Fin n → ℕ} {B : Matrix (Fin n) (Fin n) ℤ}
    (h : IsSkewSymmetrizer d B) (i j : Fin n) :
    (d i : ℤ) * companion B i j = (d j : ℤ) * companion B j i := by
  by_cases hij : i = j
  · subst j; rfl
  · by_cases hlt : i < j
    · simpa [companion, hij, Ne.symm hij, hlt, not_lt.mpr hlt.le] using h.2 i j
    · have hgt : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
      simpa [companion, hij, Ne.symm hij, hlt, hgt] using congrArg Neg.neg (h.2 i j)

private theorem weighted_prod_reverse {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℤ)
    (hd : (∏ i, d i) ≠ 0) (h : ∀ i j, d i * M i j = d j * M j i)
    (σ : Equiv.Perm (Fin n)) : (∏ i, M (σ i) i) = ∏ i, M i (σ i) := by
  have hp : (∏ i, d (σ i)) * (∏ i, M (σ i) i) = (∏ i, d i) * (∏ i, M i (σ i)) := by
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    exact prod_congr rfl (fun i _ => h (σ i) i)
  rw [Equiv.prod_comp σ] at hp
  exact mul_left_cancel₀ hd hp

private theorem companion_prod_inv {n : ℕ} {d : Fin n → ℕ} {B : Matrix (Fin n) (Fin n) ℤ}
    (h : IsSkewSymmetrizer d B) (σ : Equiv.Perm (Fin n)) :
    (∏ i, companion B (σ⁻¹ i) i) = ∏ i, companion B (σ i) i := by
  have hd : (∏ i, (d i : ℤ)) ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast Nat.ne_of_gt (h.1 i))
  have hp := weighted_prod_reverse (companion B) (fun i => (d i : ℤ)) hd (companion_weighted h) σ
  calc
    _ = ∏ i, companion B i (σ i) := by
      simpa using (Equiv.prod_comp σ (fun i => companion B (σ⁻¹ i) i)).symm
    _ = _ := hp.symm

private theorem skew_prod_inv {n : ℕ} {d : Fin n → ℕ} {B : Matrix (Fin n) (Fin n) ℤ}
    (h : IsSkewSymmetrizer d B) (σ : Equiv.Perm (Fin n)) :
    (∏ i, B (σ⁻¹ i) i) = (-1 : ℤ)^n * ∏ i, B (σ i) i := by
  have hd : (∏ i, (d i : ℤ)) ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast Nat.ne_of_gt (h.1 i))
  have hp : (∏ i, (d (σ i) : ℤ)) * (∏ i, B (σ i) i) =
      (∏ i, (d i : ℤ)) * ((-1 : ℤ)^n * ∏ i, B i (σ i)) := by
    rw [← prod_mul_distrib]
    calc
      _ = ∏ i, -((d i : ℤ) * B i (σ i)) := prod_congr rfl (fun i _ => h.2 (σ i) i)
      _ = _ := by rw [prod_neg, card_univ, Fintype.card_fin, prod_mul_distrib]; ring
  rw [Equiv.prod_comp σ (fun i => (d i : ℤ))] at hp
  have he := mul_left_cancel₀ hd hp
  have hn : (-1 : ℤ)^n * (-1 : ℤ)^n = 1 := pow_mul_pow_eq_one n rfl
  calc
    _ = ∏ i, B i (σ i) := by simpa using (Equiv.prod_comp σ (fun i => B (σ⁻¹ i) i)).symm
    _ = (-1 : ℤ)^n * ∏ i, B (σ i) i := by rw [he]; rw [← mul_assoc, hn, one_mul]


private theorem involution_companion {n : ℕ} (m : ℕ) (hn : n = 2*m)
    (B : Matrix (Fin n) (Fin n) ℤ) (hb : ∀ i, B i i = 0)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ i, σ (σ i) = i) :
    (∏ i, (companion B (σ i) i : ZMod 4)) =
      (-1 : ZMod 4)^m * ∏ i, (B (σ i) i : ZMod 4) := by
  let F := univ.filter (fun i => σ i = i)
  let L := univ.filter (fun i => i < σ i)
  let P : ZMod 4 := ∏ i ∈ L, (B (σ i) i : ZMod 4) * (B i (σ i) : ZMod 4)
  have hcard : n = F.card + 2 * L.card := involution_card σ hσ
  have hfixedA : (∏ i ∈ F, (companion B (σ i) i : ZMod 4)) = (2 : ZMod 4)^F.card := by
    calc
      _ = ∏ i ∈ F, (2 : ZMod 4) := by
        apply prod_congr rfl
        intro i hi
        have he : σ i = i := (mem_filter.mp hi).2
        simp [he, companion]
      _ = _ := by simp
  have hpairA : (∏ i ∈ L, (companion B (σ i) i : ZMod 4) * (companion B (σ (σ i)) (σ i) : ZMod 4)) =
      (-1 : ZMod 4)^L.card * P := by
    calc
      _ = ∏ i ∈ L, (-1 : ZMod 4) * ((B (σ i) i : ZMod 4) * (B i (σ i) : ZMod 4)) := by
        apply prod_congr rfl
        intro i hi
        have hlt : i < σ i := (mem_filter.mp hi).2
        have hne : σ i ≠ i := Ne.symm (ne_of_lt hlt)
        simp [companion, hσ, hne, Ne.symm hne, hlt, not_lt.mpr hlt.le]
      _ = _ := by rw [prod_mul_distrib]; simp [P]
  have hfixedB : (∏ i ∈ F, (B (σ i) i : ZMod 4)) = (0 : ZMod 4)^F.card := by
    calc
      _ = ∏ i ∈ F, (0 : ZMod 4) := by
        apply prod_congr rfl
        intro i hi
        rw [(mem_filter.mp hi).2, hb i, Int.cast_zero]
      _ = _ := by simp
  have hA := involution_product σ hσ (fun i => (companion B (σ i) i : ZMod 4))
  have hB := involution_product σ hσ (fun i => (B (σ i) i : ZMod 4))
  change (∏ i, (companion B (σ i) i : ZMod 4)) =
    (∏ i ∈ F, (companion B (σ i) i : ZMod 4)) *
    (∏ i ∈ L, (companion B (σ i) i : ZMod 4) * (companion B (σ (σ i)) (σ i) : ZMod 4)) at hA
  rw [hfixedA, hpairA] at hA
  change (∏ i, (B (σ i) i : ZMod 4)) = (∏ i ∈ F, (B (σ i) i : ZMod 4)) *
    (∏ i ∈ L, (B (σ i) i : ZMod 4) * (B (σ (σ i)) (σ i) : ZMod 4)) at hB
  simp only [hσ] at hB
  rw [hfixedB] at hB
  change (∏ i, (B (σ i) i : ZMod 4)) = (0 : ZMod 4)^F.card * P at hB
  rw [hA, hB]
  by_cases hz : F.card = 0
  · have hl : L.card = m := by omega
    simp [hz, hl]
  · have hf : 2 ≤ F.card := by omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hf
    have hfour : (2 : ZMod 4)^2 = 0 := (ZMod.val_eq_zero ((2 : ZMod 4)^2)).mp rfl
    rw [hk, pow_add, hfour]
    simp

private theorem companion_congruence {n : ℕ} {d : Fin n → ℕ} {B : Matrix (Fin n) (Fin n) ℤ}
    (m : ℕ) (hn : n = 2*m) (h : IsSkewSymmetrizer d B) :
    ((companion B).det : ZMod 4) = (-1 : ZMod 4)^m * (B.det : ZMod 4) := by
  classical
  let f : Equiv.Perm (Fin n) → ℤ := fun σ =>
    (Equiv.Perm.sign σ : ℤ) * ((∏ i, companion B (σ i) i) - (-1 : ℤ)^m * ∏ i, B (σ i) i)
  have heven : (-1 : ℤ)^n = 1 := Even.neg_one_pow (even_iff_exists_two_mul.mpr ⟨m, hn⟩)
  have hfinv (σ : Equiv.Perm (Fin n)) : f σ⁻¹ = f σ := by
    simp only [f, Equiv.Perm.sign_inv, companion_prod_inv h σ, skew_prod_inv h σ, heven, one_mul]
  have hf2 (σ : Equiv.Perm (Fin n)) : (f σ : ZMod 2) = 0 := by
    have hp : ∀ i, ((companion B (σ i) i : ℤ) : ZMod 2) = (B (σ i) i : ZMod 2) := by
      intro i
      exact congrFun (congrFun (companion_mod_two h) (σ i)) i
    dsimp [f]
    push_cast
    rw [CharTwo.neg_one_eq_one]
    simp only [one_pow, one_mul]
    rw [prod_congr rfl (fun i _ => hp i), sub_self, mul_zero]
  have hself (σ : Equiv.Perm (Fin n)) : (f σ : ZMod 4) + (f σ : ZMod 4) = 0 := by
    rcases zmod_four_even (f σ) (hf2 σ) with hz | hz
    · rw [hz]; simp
    · rw [hz]; decide +kernel
  have hfixed (σ : Equiv.Perm (Fin n)) (hi : σ⁻¹ = σ) : (f σ : ZMod 4) = 0 := by
    have hσ : ∀ i, σ (σ i) = i := by
      intro i
      calc
        _ = σ⁻¹ (σ i) := by rw [hi]
        _ = i := σ.symm_apply_apply i
    have hp := involution_companion m hn B (diag_zero h) σ hσ
    dsimp [f]
    push_cast
    rw [hp, sub_self, mul_zero]
  have hsum : (∑ σ : Equiv.Perm (Fin n), (f σ : ZMod 4)) = 0 := by
    apply Finset.sum_involution (fun σ _ => σ⁻¹)
    · intro σ _
      rw [hfinv]
      exact hself σ
    · intro σ _ hne heq
      exact hne (hfixed σ heq)
    · intro σ _; exact inv_inv σ
    · intro σ _; exact mem_univ _
  have hdet : (∑ σ : Equiv.Perm (Fin n), f σ) = (companion B).det - (-1 : ℤ)^m * B.det := by
    rw [Matrix.det_apply', Matrix.det_apply', Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply sum_congr rfl
    intro σ _
    dsimp [f]
    ring
  have hh : (((companion B).det - (-1 : ℤ)^m * B.det : ℤ) : ZMod 4) = 0 := by
    rw [← hdet, Int.cast_sum]
    exact hsum
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] at hh
  exact sub_eq_zero.mp hh


private theorem alternating_det_square (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ)
    (hM : ∀ i j, M i j = -M j i) : IsSquare M.det := by
  classical
  by_cases hz : M.det = 0
  · exact ⟨0, by simp [hz]⟩
  let F := M.toBilin'
  have hsk (x y : Fin n → ℚ) : F x y = -F y x := by
    simp only [F, Matrix.toBilin'_apply, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hM j i]
    ring
  have hAlt : F.IsAlt := fun x => CharZero.eq_neg_self_iff.mp (hsk x x)
  obtain ⟨m, e, he⟩ :=
    D5.S3.QuadraticForms.SymplecticBasis.exists_isSymplecticBasis hAlt
      (LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' M hz)
  let G : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℚ := fromBlocks 0 1 (-1) 0
  have hG : F.toMatrix e = G := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simpa [G, LinearMap.BilinForm.toMatrix_apply] using he.inl_inl i j
    · by_cases hij : i = j
      · subst j; simpa [G, LinearMap.BilinForm.toMatrix_apply] using he.inl_inr_self i
      · simpa [G, LinearMap.BilinForm.toMatrix_apply, Matrix.one_apply, hij] using he.inl_inr_of_ne i j hij
    · rw [LinearMap.BilinForm.toMatrix_apply, ← hAlt.neg_eq]
      by_cases hij : j = i
      · subst j; simp [G, he.inl_inr_self]
      · simp [G, he.inl_inr_of_ne j i hij, Ne.symm hij]
    · simpa [G, LinearMap.BilinForm.toMatrix_apply] using he.inr_inr i j
  have hdetG : G.det = 1 := by
    simpa only [G, Matrix.J, Matrix.fromBlocks_neg, neg_zero, neg_neg] using
      SymplecticGroup.det_eq_one
        (SymplecticGroup.neg_mem (SymplecticGroup.J_mem (Fin m) ℚ))
  let e0 := Pi.basisFun ℚ (Fin n)
  let σ := e.indexEquiv e0
  let b := e0.reindex σ.symm
  have hb : F.toMatrix b = M.submatrix σ σ := by
    ext i j
    simp [b, e0, F, LinearMap.BilinForm.toMatrix_apply, Module.Basis.reindex_apply,
      Pi.basisFun_apply, Matrix.toBilin'_single]
  have ht := congrArg Matrix.det (F.toMatrix_mul_basis_toMatrix b e)
  rw [hG, hdetG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    hb, Matrix.det_submatrix_equiv_self] at ht
  have hp : (b.toMatrix e).det ≠ 0 := right_ne_zero_of_mul_eq_one ht
  refine ⟨(b.toMatrix e).det⁻¹, ?_⟩
  field_simp
  nlinarith only [ht]

private theorem weighted_det_square {n : ℕ} {d : Fin n → ℕ} {B : Matrix (Fin n) (Fin n) ℤ}
    (h : IsSkewSymmetrizer d B) : IsSquare ((∏ i, (d i : ℤ)) * B.det) := by
  let D : Matrix (Fin n) (Fin n) ℤ := diagonal (fun i => (d i : ℤ))
  have ht : ∀ i j, ((D * B).map (Int.castRingHom ℚ)) i j = -((D * B).map (Int.castRingHom ℚ)) j i := by
    intro i j
    simp only [Matrix.map_apply, Matrix.diagonal_mul, D]
    simpa only [map_neg] using congrArg (Int.castRingHom ℚ) (h.2 i j)
  have hs := alternating_det_square n ((D * B).map (Int.castRingHom ℚ)) ht
  apply Rat.isSquare_intCast_iff.mp
  have hd : (D * B).det = (∏ i, (d i : ℤ)) * B.det := by rw [Matrix.det_mul, Matrix.det_diagonal]
  rw [← hd, Int.cast_det]
  exact hs


private theorem square_weight_cancel (a b c : ℤ) (ha : a ≠ 0)
    (hb : IsSquare (a * b)) (hc : IsSquare (a * c)) : IsSquare (b * c) := by
  apply Rat.isSquare_intCast_iff.mp
  obtain ⟨x, hx⟩ := hb
  obtain ⟨y, hy⟩ := hc
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hx' : (a : ℚ) * b = (x : ℚ) * x := by exact_mod_cast hx
  have hy' : (a : ℚ) * c = (y : ℚ) * y := by exact_mod_cast hy
  refine ⟨(x : ℚ) * y / a, ?_⟩
  push_cast
  field_simp [ha']
  nlinarith only [congrArg₂ (fun u v : ℚ => u * v) hx' hy']

private theorem nonzero_square_residues (a b : ZMod 4)
    (ha : a ≠ 0) (hb : b ≠ 0) (h : IsSquare (a * b)) : a = b := by
  revert a b
  change ∀ a b : ZMod 4, a ≠ 0 → b ≠ 0 → (∃ x, a * b = x * x) → a = b
  decide +kernel

private theorem weighted_square_residues (a : ℤ) (ha : a ≠ 0) :
    ∃ r : ZMod 4, ∀ q : ℤ, IsSquare (a * q) → (q : ZMod 4) = 0 ∨ (q : ZMod 4) = r := by
  classical
  by_cases hh : ∃ q : ℤ, IsSquare (a * q) ∧ (q : ZMod 4) ≠ 0
  · obtain ⟨q₀, hq₀, hq₀'⟩ := hh
    refine ⟨q₀, fun q hq => ?_⟩
    by_cases hz : (q : ZMod 4) = 0
    · exact Or.inl hz
    · right
      apply nonzero_square_residues _ _ hz hq₀'
      obtain ⟨x, hx⟩ := square_weight_cancel a q q₀ ha hq hq₀
      refine ⟨(x : ZMod 4), ?_⟩
      simpa only [Int.cast_mul] using congrArg (fun z : ℤ => (z : ZMod 4)) hx
  · refine ⟨0, fun q hq => Or.inl ?_⟩
    by_contra hn
    exact hh ⟨q, hq, hn⟩


theorem result : D5.S3.Combinatorics.ClusterMutation.HuangMaBinaryDeltaInvariant.claim := by
  intro n d hd
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨m, hm⟩ := hn
    have hnm : n = 2*m := by omega
    let Δ : ℤ := ∏ i, (d i : ℤ)
    have hΔ : Δ ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast Nat.ne_of_gt (hd i))
    obtain ⟨r, hr⟩ := weighted_square_residues Δ hΔ
    refine ⟨0, (-1 : ZMod 4)^m * r, fun B hB => ⟨(companion B).det, det_companion hB, ?_⟩⟩
    rw [companion_congruence m hnm hB]
    rcases hr B.det (weighted_det_square hB) with hz | hz
    · left; rw [hz, mul_zero]
    · right; rw [hz]
  · exact ⟨0, 2, fun B hB => odd_binary hB hn⟩

end D5.S3.Combinatorics.ClusterMutation.HuangMaBinaryDeltaInvariant
