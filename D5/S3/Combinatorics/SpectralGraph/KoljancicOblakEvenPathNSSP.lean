/- GID: D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPathNSSP
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPathNSSP
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact support and unrestricted commutants for even looped paths. -/

import D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath
import D5.S3.Quantum.Matrix.GibbsStochasticSimpleSpectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Exact-support synthesis for the full even double-path event. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPathNSSP

open Polynomial Matrix
open D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence
open D5.S3.Quantum.Matrix.GibbsStochasticSimpleSpectrum

open scoped Matrix.Norms.Elementwise

private def spectralTangent {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ)
    (T : (Fin n → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun v := fun i => (Uᵀ * T v * U) i i
  map_add' v w := by ext i; simp [mul_add, add_mul]
  map_smul' c v := by ext i; simp [Matrix.mul_smul, Matrix.smul_mul]

private lemma diagonal_commutant {n : ℕ} (lam : Fin n → ℝ)
    (hlam : Function.Injective lam) (Y : Matrix (Fin n) (Fin n) ℝ)
    (h : diagonal lam * Y = Y * diagonal lam) :
    Y = diagonal (fun i => Y i i) := by
  ext i j
  by_cases hij : i = j
  · subst j; simp
  · have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) h
    simp only [diagonal_mul, mul_diagonal] at he
    have hn : lam i - lam j ≠ 0 := sub_ne_zero.mpr (fun he => hij (hlam he))
    have hz : (lam i - lam j) * Y i j = 0 := by nlinarith [he]
    simpa [diagonal_apply_ne _ hij] using (mul_eq_zero.mp hz).resolve_left hn

private lemma spectral_tangent_nssp {n : ℕ}
    (A U : Matrix (Fin n) (Fin n) ℝ) (lam : Fin n → ℝ)
    (T : (Fin n → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ)
    (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1)
    (hA : Uᵀ * A * U = diagonal lam) (hlam : Function.Injective lam)
    (hT : ∀ v i j, A i j = 0 → T v i j = 0)
    (hinj : Function.Injective (spectralTangent U T)) : HasNSSP A := by
  classical
  intro X hentry hcomm
  have hc : A * Xᵀ = Xᵀ * A := sub_eq_zero.mp hcomm
  let Y := Uᵀ * Xᵀ * U
  have hdiag : diagonal lam * Y = Y * diagonal lam := by
    rw [← hA]
    dsimp [Y]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᵀ, hU', one_mul]
    rw [← Matrix.mul_assoc A Xᵀ, hc]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᵀ, hU', one_mul]
  have hY := diagonal_commutant lam hlam Y hdiag
  obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective.mp hinj) (fun i => Y i i)
  have hz (v : Fin n → ℝ) : trace (Xᵀ * T v) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    change ∑ j, X j i * T v j i = 0
    apply Finset.sum_eq_zero
    intro j _
    by_cases ha : A j i = 0
    · rw [hT v j i ha, mul_zero]
    · rw [(mul_eq_zero.mp (hentry j i)).resolve_left ha, zero_mul]
  have hp : trace (Y * (Uᵀ * T v * U)) = 0 := by
    dsimp [Y]
    calc
      trace (Uᵀ * Xᵀ * U * (Uᵀ * T v * U)) =
          trace (Uᵀ * (Xᵀ * T v) * U) := by
        congr 1
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc U Uᵀ, hU', one_mul]
      _ = trace (U * Uᵀ * (Xᵀ * T v)) := trace_mul_cycle _ _ _
      _ = 0 := by rw [hU', one_mul]; exact hz v
  have hs : ∑ i, Y i i * Y i i = 0 := by
    rw [hY] at hp
    have hv' (i) : (Uᵀ * T v * U) i i = Y i i := congrFun hv i
    simpa only [trace, diag_apply, diagonal_mul, hv'] using hp
  have hy0 : Y = 0 := by
    rw [hY]
    have hd : ∀ i, Y i i = 0 := by
      simpa using (Finset.sum_mul_self_eq_zero_iff Finset.univ (fun i => Y i i)).mp
        (by simpa using hs)
    simp [hd]
  have hx : Xᵀ = 0 := by
    have he := congrArg (fun M => U * M * Uᵀ) hy0
    dsimp [Y] at he
    simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc U Uᵀ, hU', one_mul,
      Matrix.mul_zero, Matrix.zero_mul, mul_one] using he
  exact transpose_injective (by simpa using hx)

private lemma det_diagonal_derivative_zero {n : ℕ} (d : Fin n → ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : ∀ i, B i i = 0) :
    HasDerivAt (fun t : ℝ => (diagonal d + t • B).det) 0 0 := by
  classical
  let f : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin n → ℝ) ℝ :=
    ⟨detRowAlternating.toMultilinearMap, continuous_id.matrix_det⟩
  have hg : HasDerivAt (fun t : ℝ => diagonal d + t • B) B 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const B).const_add (diagonal d))
  have hf := (f.hasFDerivAt (diagonal d)).comp_hasDerivAt_of_eq (0 : ℝ) hg (by simp)
  have hz : f.linearDeriv (diagonal d) B = 0 := by
    rw [ContinuousMultilinearMap.linearDeriv_apply]
    apply Finset.sum_eq_zero
    intro i _
    change (updateRow (diagonal d) i (B i)).det = 0
    apply det_eq_zero_of_column_eq_zero i
    intro j
    by_cases hji : j = i
    · subst j; simpa using hB i
    · simp [updateRow, Function.update_of_ne hji, diagonal_apply_ne _ hji]
  rw [hz] at hf
  convert hf using 1
  funext t
  rfl

private lemma charpoly_derivative_zero_of_spectral_diagonal_zero {n : ℕ}
    (A U B : Matrix (Fin n) (Fin n) ℝ) (lam : Fin n → ℝ)
    (hU : U * Uᵀ = 1) (hA : Uᵀ * A * U = diagonal lam)
    (hB : ∀ i, (Uᵀ * B * U) i i = 0) (x : ℝ) :
    HasDerivAt (fun t : ℝ => ((A + t • B).charpoly).eval x) 0 0 := by
  have H := det_diagonal_derivative_zero (fun i => x - lam i)
    (-(Uᵀ * B * U)) (by intro i; simp [hB i])
  refine H.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have he : (Uᵀ * (A + t • B) * U).charpoly = (A + t • B).charpoly := by
    rw [charpoly_mul_comm, ← Matrix.mul_assoc, hU, one_mul]
  change ((A + t • B).charpoly).eval x = _
  rw [← he, eval_charpoly]
  congr 1
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hA]
  ext i j
  by_cases hij : i = j
  · subst j; simp [Matrix.scalar, diagonal_apply]; ring
  · simp [Matrix.scalar, diagonal_apply_ne _ hij, hij]


private def leftDirection {r s : ℕ} (v : Fin (s + 1 + r) → ℝ) (k : ℕ) : ℝ :=
  if h : k < r then v ⟨k, by omega⟩ else 0

private def rightDirection {r s : ℕ} (v : Fin (s + 1 + r) → ℝ) (k : ℕ) : ℝ :=
  if h : k < s then v ⟨r + 1 + k, by omega⟩ else 0

private def joinedTangent (r s : ℕ) :
    (Fin (s + 1 + r) → ℝ) →ₗ[ℝ]
      Matrix (Fin (s + 1 + r)) (Fin (s + 1 + r)) ℝ where
  toFun v := joinedPath (leftDirection v) (rightDirection v) (v ⟨r, by omega⟩) r s
  map_add' v w := by
    ext i j
    simp only [joinedPath, leftDirection, rightDirection, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> simp_all
  map_smul' c v := by
    ext i j
    simp only [joinedPath, leftDirection, rightDirection, Pi.smul_apply, Matrix.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp_all

private lemma joinedPath_affine (bL bR : ℕ → ℝ) (a : ℝ) (r s : ℕ)
    (v : Fin (s + 1 + r) → ℝ) (t : ℝ) :
    joinedPath (fun k => bL k + t * leftDirection v k)
      (fun k => bR k + t * rightDirection v k) (a + t * v ⟨r, by omega⟩) r s =
      joinedPath bL bR a r s + t • joinedTangent r s v := by
  ext i j
  simp only [joinedPath, joinedTangent, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> ring

private lemma joined_path_nssp_of_diagonalization (bL bR : ℕ → ℝ) (a : ℝ) (r s : ℕ)
    (ha : a ≠ 0) (hodd : Odd (r + s))
    (hL : ∀ k < r, bL k ≠ 0) (hR : ∀ k < s, bR k ≠ 0)
    (hcop : IsCoprime (continuant (fun k => bL k ^ 2) r)
      (continuant (fun k => bR k ^ 2) s))
    (U : Matrix (Fin (s + 1 + r)) (Fin (s + 1 + r)) ℝ)
    (lam : Fin (s + 1 + r) → ℝ)
    (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1)
    (hA : Uᵀ * joinedPath bL bR a r s * U = diagonal lam)
    (hlam : Function.Injective lam) : HasNSSP (joinedPath bL bR a r s) := by
  classical
  apply spectral_tangent_nssp _ U lam (joinedTangent r s) hU hU' hA hlam
  · intro v i j hz
    change joinedPath (leftDirection v) (rightDirection v) (v ⟨r, by omega⟩) r s i j = 0
    simp only [joinedPath] at hz ⊢
    split_ifs at hz ⊢ <;> try assumption <;> try rfl
    all_goals
      first
      | exact False.elim (ha hz)
      | exact False.elim (hL _ (by assumption) hz)
      | by_cases hk : s + r - 1 - i.val < s
        · exact False.elim (hR _ hk hz)
        · simp [rightDirection, hk]
      | by_cases hk : s + r - 1 - j.val < s
        · exact False.elim (hR _ hk hz)
        · simp [rightDirection, hk]
  · have kernel (v : Fin (s + 1 + r) → ℝ)
        (hv : spectralTangent U (joinedTangent r s) v = 0) : v = 0 := by
      have hvar : joinedVariation (fun k => bL k ^ 2) (fun k => bR k ^ 2)
          (fun k => 2 * bL k * leftDirection v k)
          (fun k => 2 * bR k * rightDirection v k) a (v ⟨r, by omega⟩) r s = 0 := by
        apply Polynomial.funext
        intro x
        have H := joined_path_charpoly_derivative bL bR (leftDirection v)
          (rightDirection v) a (v ⟨r, by omega⟩) r s x
        simp_rw [joinedPath_affine] at H
        have H0 := charpoly_derivative_zero_of_spectral_diagonal_zero
          (joinedPath bL bR a r s) U (joinedTangent r s v) lam hU' hA
          (fun i => congrFun hv i) x
        simpa using H.unique H0
      have hz : (deformedJoinedContinuant (fun k => bL k ^ 2) (fun k => bR k ^ 2)
          (fun k => 2 * bL k * leftDirection v k)
          (fun k => 2 * bR k * rightDirection v k) a (v ⟨r, by omega⟩) r s).coeff 1 = 0 := by
        rw [joined_linearization, hvar]
      obtain ⟨hc, hl, hr⟩ := joined_variation_injective _ _ _ _ _ _ r s ha hodd
        (fun k hk => pow_ne_zero _ (hL k hk)) (fun k hk => pow_ne_zero _ (hR k hk)) hcop hz
      have dl (k : ℕ) (hk : k < r) : leftDirection v k = 0 := by
        exact (mul_eq_zero.mp (hl k hk)).resolve_left
          (mul_ne_zero (by norm_num) (hL k hk))
      have dr (k : ℕ) (hk : k < s) : rightDirection v k = 0 := by
        exact (mul_eq_zero.mp (hr k hk)).resolve_left
          (mul_ne_zero (by norm_num) (hR k hk))
      ext i
      by_cases hil : i.val < r
      · simpa [leftDirection, hil] using dl i.val hil
      · by_cases hic : i.val = r
        · have hi : i = ⟨r, by omega⟩ := Fin.ext hic
          simpa [hi] using hc
        · have hir : i.val - (r + 1) < s := by omega
          have hi : (⟨r + 1 + (i.val - (r + 1)), by omega⟩ : Fin (s + 1 + r)) = i :=
            Fin.ext (by simp only [Fin.val_mk]; omega)
          simpa [rightDirection, hir, hi] using dr (i.val - (r + 1)) hir
    intro v w hvw
    apply sub_eq_zero.mp
    apply kernel
    rw [map_sub, hvw, sub_self]


private lemma joined_simple (bL bR : ℕ → ℝ) (a : ℝ) (r s : ℕ)
    (hL : ∀ k < r, bL k ≠ 0) (hR : ∀ k < s, bR k ≠ 0) :
    HasSimpleEigenvalues (joinedPath bL bR a r s) := by
  classical
  let d : Fin (s + r + 1) → ℝ := fun i => if i.val = r then a else 0
  let e : Fin (s + r + 1) → ℝ := fun i =>
    if i.val < r then bL i.val else bR (s + r - 1 - i.val)
  have he (t : Fin (s + r)) : e t.castSucc ≠ 0 := by
    dsimp [e]
    split_ifs with h
    · exact hL _ h
    · exact hR _ (by omega)
  have H := jacobi_simple (s + r) d e he
  have hj : jacobiMatrix (s + r) d e =
      (fun i j : Fin (s + r + 1) =>
        if i = j then (if i.val = r then a else 0)
        else if i.val + 1 = j.val then e i
        else if j.val + 1 = i.val then e j else 0) := by
    ext i j
    simp only [jacobiMatrix, Matrix.add_apply, diagonal_apply, upperBand, transpose_apply]
    by_cases h : i = j
    · subst j
      have hn : ¬ i.val + 1 = i.val := by omega
      simp [hn, d]
    · by_cases hu : i.val + 1 = j.val
      · have hl : ¬ j.val + 1 = i.val := by omega
        simp [h, hu, hl]
      · by_cases hl : j.val + 1 = i.val
        · simp [h, hu, hl]
        · simp [h, hu, hl]
  rw [hj] at H
  have transport (N : ℕ) (hN : N = s + r + 1) :
      HasSimpleEigenvalues (fun i j : Fin N =>
        if i = j then (if i.val = r then a else 0)
        else if i.val + 1 = j.val then
          (if i.val < r then bL i.val else bR (s + r - 1 - i.val))
        else if j.val + 1 = i.val then
          (if j.val < r then bL j.val else bR (s + r - 1 - j.val)) else 0) := by
    subst N
    exact H
  exact transport (s + 1 + r) (by omega)

private lemma joined_diagonalization (bL bR : ℕ → ℝ) (a : ℝ) (r s : ℕ)
    (hL : ∀ k < r, bL k ≠ 0) (hR : ∀ k < s, bR k ≠ 0) :
    ∃ (U : Matrix (Fin (s + 1 + r)) (Fin (s + 1 + r)) ℝ)
      (lam : Fin (s + 1 + r) → ℝ),
      Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧
      Uᵀ * joinedPath bL bR a r s * U = diagonal lam ∧ Function.Injective lam := by
  classical
  let A := joinedPath bL bR a r s
  have hA : A.IsHermitian := by
    change Aᵀ = A
    ext i j
    dsimp [A, joinedPath, transpose]
    by_cases h : i = j
    · subst j; rfl
    · have hv : i.val ≠ j.val := fun h' => h (Fin.ext h')
      by_cases hu : i.val + 1 = j.val
      · have hl : ¬ j.val + 1 = i.val := by omega
        simp [h, Ne.symm h, hu, hl]
      · by_cases hl : j.val + 1 = i.val
        · simp [h, Ne.symm h, hu, hl]
        · simp [h, Ne.symm h, hu, hl]
  have H := joined_simple bL bR a r s hL hR
  change ((A.map (algebraMap ℝ ℂ)).charpoly.roots).Nodup at H
  rw [charpoly_map, hA.splits_charpoly.roots_map_of_injective (algebraMap ℝ ℂ).injective] at H
  have HR := Multiset.Nodup.of_map (algebraMap ℝ ℂ) H
  rw [hA.roots_charpoly_eq_eigenvalues] at HR
  have hinj : Function.Injective hA.eigenvalues := by
    intro i j hij
    exact Multiset.inj_on_of_nodup_map HR i (by simp) j (by simp) (by simpa using hij)
  let U := hA.eigenvectorUnitary
  refine ⟨U, hA.eigenvalues, ?_, ?_, ?_, hinj⟩
  · simpa only [Unitary.coe_star, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] using Unitary.coe_star_mul_self U
  · simpa only [Unitary.coe_star, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] using Unitary.coe_mul_star_self U
  · simpa only [Unitary.conjStarAlgAut_star_apply, Unitary.coe_star, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, Function.id_comp]
      using hA.conjStarAlgAut_star_eigenvectorUnitary

private lemma joined_nssp (bL bR : ℕ → ℝ) (a : ℝ) (r s : ℕ)
    (ha : a ≠ 0) (hodd : Odd (r + s))
    (hL : ∀ k < r, bL k ≠ 0) (hR : ∀ k < s, bR k ≠ 0)
    (hcop : IsCoprime (continuant (fun k => bL k ^ 2) r)
      (continuant (fun k => bR k ^ 2) s)) : HasNSSP (joinedPath bL bR a r s) := by
  obtain ⟨U, lam, hU, hU', hA, hi⟩ := joined_diagonalization bL bR a r s hL hR
  exact joined_path_nssp_of_diagonalization bL bR a r s ha hodd hL hR hcop U lam hU hU' hA hi

private lemma singleton_support (bL bR : ℕ → ℝ) (a : ℝ) (r s : ℕ)
    (ha : a ≠ 0) (hL : ∀ k < r, bL k ≠ 0) (hR : ∀ k < s, bR k ≠ 0)
    (i j : Fin (s + 1 + r)) :
    joinedPath bL bR a r s i j ≠ 0 ↔ pathPattern {⟨r, by omega⟩} i j := by
  classical
  simp only [pathPattern, Finset.mem_singleton, joinedPath]
  by_cases hij : i = j
  · subst j
    have hn : ¬ i.val + 1 = i.val := by omega
    by_cases hi : i.val = r <;> simp [hi, hn, ha, Fin.ext_iff]
  · by_cases hu : i.val + 1 = j.val
    · have hl : ¬ j.val + 1 = i.val := by omega
      by_cases h : i.val < r
      · simp [hij, hu, hl, h, hL _ h]
      · have h' : s + r - 1 - i.val < s := by omega
        simp [hij, hu, hl, h, hR _ h']
    · by_cases hl : j.val + 1 = i.val
      · by_cases h : j.val < r
        · simp [hij, hu, hl, h, hL _ h]
        · have h' : s + r - 1 - j.val < s := by omega
          simp [hij, hu, hl, h, hR _ h']
      · simp [hij, hu, hl]

private lemma singleton_witness (r s : ℕ) (hodd : Odd (r + s)) :
    ∃ A : Matrix (Fin (s + 1 + r)) (Fin (s + 1 + r)) ℝ,
      (∀ i j, A i j ≠ 0 ↔ pathPattern {⟨r, by omega⟩} i j) ∧ HasNSSP A := by
  obtain ⟨qL, qR, hpL, hpR, hc⟩ := coprime_positive_branches r s hodd
  let bL := fun k => Real.sqrt (qL k)
  let bR := fun k => Real.sqrt (qR k)
  have hL (k : ℕ) (_ : k < r) : bL k ≠ 0 := (Real.sqrt_pos.mpr (hpL k)).ne'
  have hR (k : ℕ) (_ : k < s) : bR k ≠ 0 := (Real.sqrt_pos.mpr (hpR k)).ne'
  have hsL : (fun k => bL k ^ 2) = qL := by
    funext k; exact Real.sq_sqrt (hpL k).le
  have hsR : (fun k => bR k ^ 2) = qR := by
    funext k; exact Real.sq_sqrt (hpR k).le
  refine ⟨joinedPath bL bR 1 r s, ?_, ?_⟩
  · exact singleton_support bL bR 1 r s one_ne_zero hL hR
  · apply joined_nssp bL bR 1 r s one_ne_zero hodd hL hR
    simpa only [hsL, hsR] using hc


private def nsspTest {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ]
      (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) where
  toFun X := (fun i j => A i j * X i j, A * Xᵀ - Xᵀ * A)
  map_add' X Y := by
    apply Prod.ext
    · ext i j; exact mul_add _ _ _
    · change A * (X + Y)ᵀ - (X + Y)ᵀ * A =
        (A * Xᵀ - Xᵀ * A) + (A * Yᵀ - Yᵀ * A)
      simp only [transpose_add, Matrix.mul_add, Matrix.add_mul]
      abel
  map_smul' c X := by
    apply Prod.ext
    · ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, Prod.smul_fst, RingHom.id_apply]
      ring
    · simp [transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]

private def nsspFamily (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ]
      (Matrix (Fin n) (Fin n) ℝ →L[ℝ]
        (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)) where
  toFun A := (nsspTest A).toContinuousLinearMap
  map_add' A B := by
    apply ContinuousLinearMap.ext
    intro X
    change nsspTest (A + B) X = nsspTest A X + nsspTest B X
    apply Prod.ext
    · ext i j; exact add_mul _ _ _
    · change (A + B) * Xᵀ - Xᵀ * (A + B) =
        (A * Xᵀ - Xᵀ * A) + (B * Xᵀ - Xᵀ * B)
      simp only [Matrix.add_mul, Matrix.mul_add]
      abel
  map_smul' c A := by
    apply ContinuousLinearMap.ext
    intro X
    change nsspTest (c • A) X = c • nsspTest A X
    apply Prod.ext
    · ext i j
      simp only [nsspTest, LinearMap.coe_mk, AddHom.coe_mk, Prod.smul_fst,
        Matrix.smul_apply, smul_eq_mul]
      ring
    · change (c • A) * Xᵀ - Xᵀ * (c • A) = c • (A * Xᵀ - Xᵀ * A)
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub]

private lemma nssp_open (n : ℕ) :
    IsOpen {A : Matrix (Fin n) (Fin n) ℝ | HasNSSP A} := by
  have hs : {A : Matrix (Fin n) (Fin n) ℝ | HasNSSP A} =
      nsspFamily n ⁻¹' {f | Function.Injective f} := by
    ext A
    change HasNSSP A ↔ Function.Injective (nsspTest A)
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    constructor
    · intro H X HX
      have hp := congrArg Prod.fst HX
      have hc := congrArg Prod.snd HX
      exact H X (fun i j => congrFun (congrFun hp i) j) hc
    · intro H X hp hc
      apply H X
      apply Prod.ext
      · ext i j; exact hp i j
      · exact hc
  rw [hs]
  exact ContinuousLinearMap.isOpen_injective.preimage
    (nsspFamily n).continuous_of_finiteDimensional

private lemma loop_enlargement {n : ℕ} (L : Finset (Fin n)) (l : Fin n) (hl : l ∈ L)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hs : ∀ i j, A i j ≠ 0 ↔ pathPattern {l} i j) (ha : HasNSSP A) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, B i j ≠ 0 ↔ pathPattern L i j) ∧ HasNSSP B := by
  classical
  let D : Matrix (Fin n) (Fin n) ℝ := diagonal (fun i => if i ∈ L ∧ i ≠ l then 1 else 0)
  let B : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t => A + t • D
  have hc : Continuous B := continuous_const.add (continuous_id.smul continuous_const)
  have hB0 : B 0 = A := by simp only [B, zero_smul, add_zero]
  have htend : Filter.Tendsto B (nhds 0) (nhds A) := by
    simpa only [hB0] using (hc.continuousAt : ContinuousAt B 0).tendsto
  have hevent : ∀ᶠ t in nhds (0 : ℝ), HasNSSP (B t) :=
    htend.eventually ((nssp_open n).mem_nhds ha)
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hevent
  have htpos : 0 < eps / 2 := half_pos heps
  have hnssp : HasNSSP (B (eps / 2)) := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos htpos]
    exact half_lt_self heps
  refine ⟨B (eps / 2), ?_, hnssp⟩
  intro i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i = l
    · subst i
      have hn : A l l ≠ 0 := (hs l l).mpr (Or.inr (Or.inr ⟨rfl, by simp⟩))
      simp [B, D, hn, pathPattern, hl]
    · have hz : A i i = 0 := by
        by_contra hne
        have H := (hs i i).mp hne
        simp [pathPattern, hi] at H
      by_cases hm : i ∈ L
      · simp [B, D, hz, hi, hm, pathPattern, htpos.ne']
      · simp [B, D, hz, hi, hm, pathPattern]
  · have hb : B (eps / 2) i j = A i j := by
      simp [B, D, diagonal_apply_ne _ hij]
    rw [hb]
    simpa only [pathPattern, hij, false_and, or_false] using hs i j

private lemma singleton_at {n : ℕ} (hn : 0 < n) (heven : Even n) (l : Fin n) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, A i j ≠ 0 ↔ pathPattern {l} i j) ∧ HasNSSP A := by
  let r := l.val
  let s := n - 1 - r
  have hnum : s + 1 + r = n := by dsimp [s, r]; omega
  have hodd : Odd (r + s) := by
    apply Nat.odd_iff.mpr
    have he := Nat.even_iff.mp heven
    omega
  have transport (N : ℕ) (hN : N = s + 1 + r) (k : Fin N) (hk : k.val = r) :
      ∃ A : Matrix (Fin N) (Fin N) ℝ,
        (∀ i j, A i j ≠ 0 ↔ pathPattern {k} i j) ∧ HasNSSP A := by
    subst N
    have hloop : (⟨r, by omega⟩ : Fin (s + 1 + r)) = k := Fin.ext hk.symm
    simpa only [hloop] using singleton_witness r s hodd
  exact transport n hnum.symm l rfl

/-- The full existential event, with unrestricted real test matrices. -/
theorem result : D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath.claim := by
  intro n hn heven L hL
  obtain ⟨l, hl⟩ := hL
  obtain ⟨A, hs, ha⟩ := singleton_at hn heven l
  exact loop_enlargement L l hl A hs ha


end D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPathNSSP
