/- GID: D5/S3/Quantum/Entanglement/AbsoluteSeparability/AhiableKothakondaWinterEq31
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsoluteSeparability/AhiableKothakondaWinterEq31
   mirror-E: none(waiver:formal-unit-only)
   anchors: []
   utility: none
   digest: Ahiable--Kothakonda--Winter Eq. (31) implies absolute separability. -/

import D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays

open scoped BigOperators ComplexOrder MatrixOrder Kronecker ComplexConjugate
open Matrix Finset
open D5.S3.Resource.CompositeCones
open D5.S3.Resource.EntanglementWitness

namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.AhiableKothakondaWinterEq31

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The linear spectral condition (31) of Theorem 6.2 is sufficient for
absolute separability, as asked in Section 7 of Ahiable--Kothakonda--Winter.
For every pair of natural dimensions `2 ≤ m ≤ n`, let `ρ` be a positive
semidefinite trace-one matrix on `ℂ^m ⊗ ℂ^n`, and put `D = m*n`.
Its eigenvalues `λ₁ ≥ ⋯ ≥ λ_D ≥ 0` are `Matrix.IsHermitian.eigenvalues₀`,
in decreasing `Fin` order by `Matrix.IsHermitian.eigenvalues₀_antitone`.
The source hypothesis is exactly `2λ_D + ∑_{k=1}^{m-1} λ_{D-k} ≥ ∑_{k=1}^{m-1} λ_k`.
Here `lamb i` is `λ_{i+1}`, so the lower-tail zero-based index is `D-k.val-2`.
The conclusion quantifies every global unitary `U` and asserts that `UρU†`
is a finite sum of Kronecker products of positive semidefinite factors,
namely `separableCone (U * ρ * star U)`. No eigenbasis is assumed. -/
def claim : Prop :=
  ∀ m n : ℕ, ∀ (_hm : 2 ≤ m) (_hmn : m ≤ n),
    ∀ ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      ∀ hρ : ρ.PosSemidef, ρ.trace = 1 →
      (let D := m * n
       let hD : m ≤ D := Nat.le_mul_of_pos_right m (by omega)
       let lamb : Fin D → ℝ := fun i =>
         hρ.isHermitian.eigenvalues₀ (Fin.cast (by simp [D]) i)
       2 * lamb ⟨D - 1, by omega⟩ +
           ∑ k : Fin (m - 1), lamb ⟨D - k.val - 2, by omega⟩ ≥
         ∑ k : Fin (m - 1), lamb ⟨k.val, by omega⟩) →
      ∀ U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
        U ∈ Matrix.unitaryGroup (Fin m × Fin n) ℂ →
          separableCone (U * ρ * star U)

set_option maxHeartbeats 2000000 in
-- The spectral projection construction and its finite-sum identities elaborate together.
theorem result : claim := by
  unfold claim
  intro m n hm hmn ρ hρ htr hcond U hU
  classical
  have hmD : m ≤ m * n := Nat.le_mul_of_pos_right m (by omega)
  have telescope {M : Type} [AddCommGroup M] [Module ℝ M]
      (l : ℕ → ℝ) (r : ℕ → M) (d : ℕ) :
      ∑ i ∈ range d, l i • r i =
        l (d - 1) • (∑ i ∈ range d, r i) +
          ∑ i ∈ range (d - 1), (l i - l (i + 1)) •
            (∑ j ∈ range (i + 1), r j) := by
    rw [Finset.sum_range_by_parts]
    rw [sub_eq_add_neg]
    congr 1
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← neg_smul, neg_sub]
  have weighted_abel (D : ℕ) (hD : 2 * m - 1 ≤ D) (l : ℕ → ℝ) :
      (∑ i ∈ range (D - 1),
        ((min (i + 1) (min (m - 1) (D - (i + 1) - 1)) : ℕ) : ℝ) *
          (l i - l (i + 1))) =
      (∑ i ∈ range (m - 1), l i) -
        ∑ i ∈ range (m - 1), l (D - i - 2) := by
    let a : ℕ → ℝ := fun k => (min k (min (m - 1) (D - k - 1)) : ℕ)
    have a0 : a 0 = 0 := by simp [a]
    have aD : a D = 0 := by simp [a]
    have aD1 : a (D - 1) = 0 := by simp [a, show D - (D - 1) = 1 by omega]
    have da (i : ℕ) (hi : i < D - 1) :
        a (i + 1) - a i =
          if i < m - 1 then 1 else if D - m ≤ i then -1 else 0 := by
      by_cases hlo : i < m - 1
      · have h₀ : min i (min (m - 1) (D - i - 1)) = i := by omega
        have h₁ : min (i + 1) (min (m - 1) (D - (i + 1) - 1)) = i + 1 := by omega
        dsimp only [a]
        rw [h₀, h₁]
        simp [hlo]
      · by_cases hhi : D - m ≤ i
        · have h₀ : min i (min (m - 1) (D - i - 1)) = D - i - 1 := by omega
          have h₁ : min (i + 1) (min (m - 1) (D - (i + 1) - 1)) =
              D - (i + 1) - 1 := by omega
          have hstep : D - i - 1 = (D - (i + 1) - 1) + 1 := by omega
          dsimp only [a]
          rw [h₀, h₁, hstep]
          simp [hlo, hhi]
        · have h₀ : min i (min (m - 1) (D - i - 1)) = m - 1 := by omega
          have h₁ : min (i + 1) (min (m - 1) (D - (i + 1) - 1)) = m - 1 := by omega
          dsimp only [a]
          rw [h₀, h₁]
          simp [hlo, hhi]
    have hs : (∑ i ∈ range D, l i * (a (i + 1) - a i)) =
        ∑ i ∈ range (D - 1), a (i + 1) * (l i - l (i + 1)) := by
      have h := Finset.sum_range_by_parts l (fun i => a (i + 1) - a i) D
      simp only [Finset.sum_range_sub, a0, sub_zero, aD, smul_eq_mul, mul_zero,
        zero_sub, ← Finset.sum_neg_distrib] at h
      rw [h]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hlast : l (D - 1) * (a (D - 1 + 1) - a (D - 1)) = 0 := by
      rw [show D - 1 + 1 = D by omega, aD, aD1]
      ring
    have hmain : (∑ i ∈ range (D - 1), l i * (a (i + 1) - a i)) =
        (∑ i ∈ range (m - 1), l i) - ∑ i ∈ Ico (D - m) (D - 1), l i := by
      rw [← Finset.sum_range_add_sum_Ico (fun i => l i * (a (i + 1) - a i))
        (show m - 1 ≤ D - 1 by omega)]
      rw [← Finset.sum_Ico_consecutive (fun i => l i * (a (i + 1) - a i))
        (show m - 1 ≤ D - m by omega) (show D - m ≤ D - 1 by omega)]
      have hlo : (∑ i ∈ range (m - 1), l i * (a (i + 1) - a i)) =
          ∑ i ∈ range (m - 1), l i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [da i (by have := Finset.mem_range.mp hi; omega),
          if_pos (Finset.mem_range.mp hi), mul_one]
      have hmid : (∑ i ∈ Ico (m - 1) (D - m), l i * (a (i + 1) - a i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        obtain ⟨hi₀, hi₁⟩ := Finset.mem_Ico.mp hi
        rw [da i (by omega), if_neg (by omega), if_neg (by omega), mul_zero]
      have hhi : (∑ i ∈ Ico (D - m) (D - 1), l i * (a (i + 1) - a i)) =
          -(∑ i ∈ Ico (D - m) (D - 1), l i) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        obtain ⟨hi₀, hi₁⟩ := Finset.mem_Ico.mp hi
        rw [da i hi₁, if_neg (by omega), if_pos hi₀]
        ring
      rw [hlo, hmid, hhi]
      ring
    have htail : (∑ i ∈ range (m - 1), l (D - i - 2)) =
        ∑ i ∈ Ico (D - m) (D - 1), l i := by
      have h := Finset.sum_Ico_reflect l 0 (m := m - 1) (n := D - 2) (by omega)
      simpa only [Nat.Ico_zero_eq_range, show D - 2 + 1 = D - 1 by omega,
        show D - 1 - (m - 1) = D - m by omega, Nat.sub_zero,
        Nat.sub_sub, Nat.add_comm] using h
    rw [← hs, show D = (D - 1) + 1 by omega, Finset.sum_range_succ, hlast, add_zero]
    rw [hmain, show D - 1 + 1 = D by omega, htail]
  have reflection_bound {ι : Type} [Fintype ι] [DecidableEq ι]
      (P : Matrix ι ι ℂ) (hP : P.IsHermitian) (hPP : P * P = P) :
      ∀ x : ι → ℂ,
        ‖WithLp.toLp 2 (((2 : ℂ) • P - 1) *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖ := by
    let H : Matrix ι ι ℂ := (2 : ℂ) • P - 1
    have hH : H.IsHermitian := by
      change Hᴴ = H
      simp [H, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hP.eq]
    have hHH : Hᴴ * H = 1 := by
      rw [hH.eq]
      dsimp [H]
      noncomm_ring [hPP]
      module
    intro x
    have hs : ‖WithLp.toLp 2 (H *ᵥ x)‖ ^ 2 = ‖WithLp.toLp 2 x‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
      simp only [EuclideanSpace.inner_eq_star_dotProduct]
      rw [dotProduct_comm (H *ᵥ x), Matrix.star_mulVec, Matrix.dotProduct_mulVec,
        Matrix.vecMul_vecMul, hHH, Matrix.vecMul_one, dotProduct_comm]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs.le
  have ray_separable (k : ℕ) (hk : k + 2 ≤ m * n)
      (P : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
      (hP : P.IsHermitian) (hPP : P * P = P) (hPtr : trace P = (k : ℂ))
      (v : Fin k → Fin m × Fin n → ℂ)
      (hv : ∀ i, ∑ x, ‖v i x‖ ^ 2 = 1)
      (hsum : P = ∑ i, vecMulVec (v i) (star (v i))) :
      separableCone
        (((min k (min (m - 1) (m * n - k - 1)) : ℕ) : ℂ) • 1 + (2 : ℂ) • P) := by
    by_cases hlow : k ≤ min (m - 1) (m * n - k - 1)
    · rw [min_eq_left hlow]
      have hsep : separableCone
          (∑ i : Fin k, (1 + (2 : ℂ) • vecMulVec (v i) (star (v i)))) := by
        exact ContractionBlocks.separableCone_sum _ (fun i =>
          LowRankRays.separableCone_one_add_two_rankOne (m := m) (n := n) (v i) (hv i))
      convert hsep using 1
      rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← hsum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      congr 1
      ext x y
      simp [Matrix.smul_apply, Matrix.one_apply]
    · rw [min_eq_right (le_of_not_ge hlow)]
      by_cases hmid : m - 1 ≤ m * n - k - 1
      · rw [min_eq_left hmid]
        have hH : ((2 : ℂ) • P - 1).IsHermitian := by
          change ((2 : ℂ) • P - 1)ᴴ = _
          simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hP.eq]
        have hsep := ContractionBlocks.separableCone_scalar_add_of_opNorm_le_one
          (m := m) (n := n) ((2 : ℂ) • P - 1) hH
          (reflection_bound (ι := Fin m × Fin n) P hP hPP)
        convert hsep using 1
        have hcast : ((m - 1 : ℕ) : ℂ) = (m : ℂ) - 1 := by
          simp only [Nat.cast_sub (show 1 ≤ m by omega), Nat.cast_one]
        rw [hcast]
        module
      · rw [min_eq_right (le_of_not_ge hmid)]
        let Q : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ := 1 - P
        have hQ : Q.IsHermitian := (Matrix.isHermitian_one).sub hP
        have hQQ : Q * Q = Q := by
          dsimp [Q]
          noncomm_ring [hPP]
        let ell : ℝ := (m * n - k : ℕ)
        have htQ : trace Q = (ell : ℂ) := by
          simp only [Q, Matrix.trace_sub, Matrix.trace_one, Fintype.card_prod,
            Fintype.card_fin, hPtr]
          dsimp [ell]
          push_cast [Nat.cast_sub (show k ≤ m * n by omega)]
          ring
        have hell : 1 ≤ ell := by
          dsimp [ell]
          exact_mod_cast (show 1 ≤ m * n - k by omega)
        have hsep := GurvitsBarnumBall.separableCone_scaled_one_sub_two_projection
          Q hQ hQQ ell htQ hell
        convert hsep using 1
        have hcast : ((m * n - k - 1 : ℕ) : ℂ) = (ell : ℂ) - 1 := by
          dsimp [ell]
          push_cast [Nat.cast_sub (show 1 ≤ m * n - k by omega)]
          rfl
        rw [hcast]
        dsimp [Q]
        module
  let I := Fin m × Fin n
  let D := m * n
  have hc : Fintype.card I = D := by simp [I, D]
  let f : Fin (Fintype.card I) ≃ I := Fintype.equivOfCardEq (Fintype.card_fin _)
  let e : Fin D ≃ I := (finCongr hc.symm).trans f
  let lamb : Fin D → ℝ := fun i => hρ.isHermitian.eigenvalues₀ (Fin.cast hc.symm i)
  have hlamb : Antitone lamb := by
    intro i j hij
    exact hρ.isHermitian.eigenvalues₀_antitone
      (show Fin.cast hc.symm i ≤ Fin.cast hc.symm j from hij)
  have hlamb_nonneg (i : Fin D) : 0 ≤ lamb i := by
    have h := hρ.eigenvalues_nonneg (e i)
    simpa [lamb, e, f, Matrix.IsHermitian.eigenvalues] using h
  let W : Matrix I I ℂ := U * hρ.isHermitian.eigenvectorUnitary
  have hW : W ∈ Matrix.unitaryGroup I ℂ :=
    mul_mem hU hρ.isHermitian.eigenvectorUnitary.property
  have hWleft : Wᴴ * W = 1 := Matrix.mem_unitaryGroup_iff'.mp hW
  have hWright : W * Wᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hW
  let v : Fin D → I → ℂ := fun i x => W x (e i)
  have hvinner (i j : Fin D) :
      star (v i) ⬝ᵥ v j = if i = j then 1 else 0 := by
    have h := congrArg (fun M => M (e i) (e j)) hWleft
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, v, dotProduct,
      Matrix.one_apply, e.injective.eq_iff] using h
  have hvnorm (i : Fin D) : ∑ x, ‖v i x‖ ^ 2 = 1 := by
    have h := congrArg Complex.re (hvinner i i)
    simpa [dotProduct, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow] using h
  let R : ℕ → Matrix I I ℂ := fun i =>
    if hi : i < D then vecMulVec (v ⟨i, hi⟩) (star (v ⟨i, hi⟩)) else 0
  let P : ℕ → Matrix I I ℂ := fun k => ∑ i ∈ range k, R i
  let l : ℕ → ℝ := fun i => if hi : i < D then lamb ⟨i, hi⟩ else 0
  have hRherm (i : ℕ) : (R i).IsHermitian := by
    dsimp only [R]
    split_ifs
    · exact (Matrix.posSemidef_vecMulVec_self_star _).isHermitian
    · exact Matrix.isHermitian_zero
  have hPherm (k : ℕ) : (P k).IsHermitian := by
    change (P k)ᴴ = P k
    dsimp only [P]
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl (fun i _ => (hRherm i).eq)
  have hRmul (i j : ℕ) (hi : i < D) (hj : j < D) :
      R i * R j = if i = j then R i else 0 := by
    simp only [R, dif_pos hi, dif_pos hj, Matrix.vecMulVec_mul_vecMulVec,
      hvinner, Fin.mk.injEq]
    split_ifs with hij
    · subst j
      simp
    · simp
  have hPmul (k : ℕ) (hk : k ≤ D) : P k * P k = P k := by
    dsimp only [P]
    rw [Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Matrix.mul_sum]
    have hr : (∑ j ∈ range k, R i * R j) = ∑ j ∈ range k, if i = j then R i else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hRmul i j (by have := Finset.mem_range.mp hi; omega)
        (by have := Finset.mem_range.mp hj; omega)
    rw [hr]
    simp [hi]
  have hRtrace (i : ℕ) (hi : i < D) : trace (R i) = 1 := by
    simp only [R, dif_pos hi]
    have h := hvinner ⟨i, hi⟩ ⟨i, hi⟩
    simpa [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, dotProduct,
      Pi.star_apply, mul_comm] using h
  have hPtrace (k : ℕ) (hk : k ≤ D) : trace (P k) = (k : ℂ) := by
    dsimp only [P]
    rw [Matrix.trace_sum]
    calc
      (∑ i ∈ range k, trace (R i)) = ∑ _i ∈ range k, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hRtrace i (by have := Finset.mem_range.mp hi; omega)
      _ = (k : ℂ) := by simp
  have hPsum (k : ℕ) (hk : k ≤ D) :
      P k = ∑ i : Fin k, vecMulVec (v (Fin.castLE hk i)) (star (v (Fin.castLE hk i))) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [R, dif_pos (show i < D by have := Finset.mem_range.mp hi; omega),
      dif_pos (Finset.mem_range.mp hi)]
    rfl
  have hPD : P D = 1 := by
    rw [hPsum D le_rfl]
    ext x y
    have h := congrArg (fun M => M x y) hWright
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at h
    rw [← e.sum_comp (fun i => W x i * star (W y i))] at h
    simpa [Matrix.sum_apply, Matrix.vecMulVec_apply, v] using h
  have hspec : U * ρ * star U = ∑ i ∈ range D, l i • R i := by
    have hρspec : ρ = ∑ i : I, hρ.isHermitian.eigenvalues i •
        vecMulVec (WithLp.ofLp (hρ.isHermitian.eigenvectorBasis i))
          (star (WithLp.ofLp (hρ.isHermitian.eigenvectorBasis i))) := by
      ext x y
      conv_lhs => rw [hρ.isHermitian.spectral_theorem,
        Unitary.conjStarAlgAut_apply, Matrix.mul_apply]
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec,
        Complex.real_smul]
      apply Finset.sum_congr rfl
      intro i _
      simp [Matrix.mul_diagonal, Matrix.IsHermitian.eigenvectorUnitary_apply]
      ring
    rw [hρspec, Matrix.mul_sum, Matrix.sum_mul]
    rw [← e.sum_comp]
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hiD : i < D := Finset.mem_range.mp hi
    simp only [l, R, dif_pos hiD, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    congr 1
    · simp [lamb, e, f, Matrix.IsHermitian.eigenvalues]
    · have hvU : U *ᵥ (WithLp.ofLp (hρ.isHermitian.eigenvectorBasis (e ⟨i, hiD⟩))) =
          v ⟨i, hiD⟩ := by
        funext x
        simp [v, W, Matrix.mul_apply, Matrix.mulVec, dotProduct,
          Matrix.IsHermitian.eigenvectorUnitary_apply]
      rw [Matrix.star_eq_conjTranspose U, ← Matrix.star_mulVec, hvU]
  have hdim : 2 * m - 1 ≤ D := by
    dsimp [D]
    have h := Nat.mul_le_mul_left m (show 2 ≤ n by omega)
    omega
  have htel : U * ρ * star U = l (D - 1) • (1 : Matrix I I ℂ) +
      ∑ i ∈ range (D - 1), (l i - l (i + 1)) • P (i + 1) := by
    rw [hspec]
    have h := telescope l R D
    change (∑ i ∈ range D, l i • R i) = l (D - 1) • P D +
      ∑ i ∈ range (D - 1), (l i - l (i + 1)) • P (i + 1) at h
    rw [hPD] at h
    exact h
  have habel := weighted_abel D hdim l
  let a : ℕ → ℝ := fun k => (min k (min (m - 1) (D - k - 1)) : ℕ)
  let delta : ℕ → ℝ := fun i => l i - l (i + 1)
  let budget : ℝ := ∑ i ∈ range (D - 2), a (i + 1) * delta i
  have haD1 : a (D - 1) = 0 := by
    simp [a, show D - (D - 1) = 1 by omega]
  have hbudget_id : budget =
      (∑ i ∈ range (m - 1), l i) - ∑ i ∈ range (m - 1), l (D - i - 2) := by
    change (∑ i ∈ range (D - 2), a (i + 1) * delta i) = _
    change (∑ i ∈ range (D - 1), a (i + 1) * delta i) = _ at habel
    rw [show D - 1 = (D - 2) + 1 by omega, Finset.sum_range_succ,
      show D - 2 + 1 = D - 1 by omega, haD1, zero_mul, add_zero] at habel
    exact habel
  have htop : (∑ i ∈ range (m - 1), l i) =
      ∑ i : Fin (m - 1), lamb ⟨i.val, by omega⟩ := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [l, dif_pos (show i < D by have := Finset.mem_range.mp hi; omega),
      dif_pos (Finset.mem_range.mp hi)]
  have htail : (∑ i ∈ range (m - 1), l (D - i - 2)) =
      ∑ i : Fin (m - 1), lamb ⟨D - i.val - 2, by omega⟩ := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [l, dif_pos (show D - i - 2 < D by omega),
      dif_pos (Finset.mem_range.mp hi)]
  have hbudget : budget ≤ 2 * l (D - 1) := by
    rw [hbudget_id, htop, htail]
    change (∑ i : Fin (m - 1), lamb ⟨i.val, by omega⟩) ≤
      2 * lamb ⟨D - 1, by omega⟩ +
        ∑ i : Fin (m - 1), lamb ⟨D - i.val - 2, by omega⟩ at hcond
    simp only [l, dif_pos (show D - 1 < D by omega)]
    linarith
  have hdelta (i : ℕ) (hi : i < D - 1) : 0 ≤ delta i := by
    dsimp only [delta, l]
    rw [dif_pos (show i < D by omega), dif_pos (show i + 1 < D by omega)]
    exact sub_nonneg.mpr (hlamb
      (show (⟨i, by omega⟩ : Fin D) ≤ ⟨i + 1, by omega⟩ from Nat.le_succ i))
  have hidentity : separableCone (1 : Matrix I I ℂ) := by
    refine ⟨1, fun _ => 1, fun _ => 1,
      fun _ => ⟨Matrix.PosSemidef.one, Matrix.PosSemidef.one⟩, ?_⟩
    simp
  have hterminal : separableCone (P (D - 1)) := by
    have hsplit : P (D - 1) + R (D - 1) = 1 := by
      have h : P D = P (D - 1) + R (D - 1) := by
        change (∑ i ∈ range D, R i) = _
        rw [show D = (D - 1) + 1 by omega, Finset.sum_range_succ]
        rfl
      rw [← h, hPD]
    have hp : P (D - 1) = 1 - vecMulVec (v ⟨D - 1, by omega⟩)
        (star (v ⟨D - 1, by omega⟩)) := by
      have h := eq_sub_of_add_eq hsplit
      simpa only [R, dif_pos (show D - 1 < D by omega)] using h
    rw [hp]
    exact GurvitsBarnumBall.separableCone_one_sub_rankOne _ (hvnorm _)
  have hray (i : ℕ) (hi : i < D - 2) :
      separableCone ((a (i + 1) : ℂ) • 1 + (2 : ℂ) • P (i + 1)) := by
    have hk : i + 1 ≤ D := by omega
    exact ray_separable (i + 1) (by dsimp [D] at hi ⊢; omega)
      (P (i + 1)) (hPherm _) (hPmul _ hk) (hPtrace _ hk)
      (fun j => v (Fin.castLE hk j)) (fun j => hvnorm _) (hPsum _ hk)
  have hdecomp : U * ρ * star U =
      (l (D - 1) - budget / 2) • (1 : Matrix I I ℂ) +
      delta (D - 2) • P (D - 1) +
      ∑ i ∈ range (D - 2), (delta i / 2) •
        ((a (i + 1) : ℂ) • 1 + (2 : ℂ) • P (i + 1)) := by
    rw [htel]
    change l (D - 1) • (1 : Matrix I I ℂ) +
      (∑ i ∈ range (D - 1), delta i • P (i + 1)) = _
    rw [show D - 1 = (D - 2) + 1 by omega, Finset.sum_range_succ,
      show D - 2 + 1 = D - 1 by omega]
    have hterm (i : ℕ) : (delta i / 2) •
        ((a (i + 1) : ℂ) • (1 : Matrix I I ℂ) + (2 : ℂ) • P (i + 1)) =
        (a (i + 1) * delta i / 2) • (1 : Matrix I I ℂ) + delta i • P (i + 1) := by
      ext x y
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul,
        Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
      ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    have hsum : (∑ i ∈ range (D - 2), (a (i + 1) * delta i / 2) • (1 : Matrix I I ℂ)) =
        (budget / 2) • (1 : Matrix I I ℂ) := by
      rw [← Finset.sum_smul, ← Finset.sum_div]
    rw [hsum]
    module
  rw [hdecomp]
  apply separableCone_add
  · exact separableCone_add
      (separableCone_smul (by linarith : 0 ≤ l (D - 1) - budget / 2) hidentity)
      (separableCone_smul (hdelta _ (by omega)) hterminal)
  · have hsum (s : Finset ℕ) (hs : ∀ i ∈ s, i < D - 2) :
        separableCone (∑ i ∈ s, (delta i / 2) •
          ((a (i + 1) : ℂ) • 1 + (2 : ℂ) • P (i + 1))) := by
      induction s using Finset.induction_on with
      | empty => simpa using (separableCone_zero (m := m) (n := n))
      | @insert i s his ih =>
          rw [Finset.sum_insert his]
          exact separableCone_add
            (separableCone_smul (div_nonneg (hdelta _ (by have := hs i (by simp); omega))
              (by norm_num)) (hray _ (hs i (by simp))))
            (ih (fun j hj => hs j (by simp [hj])))
    exact hsum _ (fun i hi => Finset.mem_range.mp hi)

#print axioms result

end
end D5.S3.Quantum.Entanglement.AbsoluteSeparability.AhiableKothakondaWinterEq31
