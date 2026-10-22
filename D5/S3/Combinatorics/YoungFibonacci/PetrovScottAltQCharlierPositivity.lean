/- GID: D5/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity
   generality: I
   mirror-B: D5/B/S3/Combinatorics/YoungFibonacci/PetrovScottAltQCharlierPositivity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Alternative q-Charlier Fibonacci positivity at rho = q = 1/4. -/

/-
result:
  proof_shape: content
  escape_witness: tri_det_pos (positive weighted tridiagonal determinant in every size)
  admission_basis: open-problem-resolution (#18756; Proved)
Direct frozen dependencies: none (all declarations; only pinned Mathlib imports).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19808
The public recursion writes the source shift as fun k => u (k + offset),
without redeclaring the existing sequence-shift operation.
The proof uses continuous strict diagonal dominance and induction on arbitrary words.
Utility none: no bounded enumeration, checker, numerical reduction or finite-instance
certificate is delivered; all dimensions and word lengths are unbounded.
Declaration classification (consumers extracted from compiled terms):
det_pos_of_dominant: proof_shape: content; escape_witness: det_pos_of_dominant; consumers: tri_det_pos.
paramT: declaration_kind: definition; consumers: paramT_bounds, paramT_bounds, paramT_lower, paramT_lower, tt, tt_bound, tt_decay, tt_nonneg, x_normal, y_normal.
tt: declaration_kind: definition; consumers: A_pos, B_pos, tt_all_bound, tt_all_bound, tt_bound, tt_decay, tt_decay, tt_nonneg, tt_pos, tt_pos, x_normal, x_normal, y_normal, y_normal.
cc: declaration_kind: definition; consumers: A_pos, B_pos, cc_pos, cc_pos, x_normal, x_normal, y_normal, y_normal.
paramT_bounds: proof_shape: bind-only; escape_witness: none; consumers: tt_bound, tt_decay, tt_nonneg.
paramT_lower: proof_shape: bind-only; escape_witness: none; consumers: tt_decay, tt_pos.
tt_nonneg: proof_shape: bind-only; escape_witness: none; consumers: A_pos, B_pos.
tt_bound: proof_shape: bind-only; escape_witness: none; consumers: tt_all_bound.
tt_pos: proof_shape: bind-only; escape_witness: none; consumers: A_pos, B_pos.
tt_decay: proof_shape: bind-only; escape_witness: none; consumers: A_pos, B_pos.
cc_pos: proof_shape: bind-only; escape_witness: none; consumers: A_pos, B_pos.
fin_sum_spike_le: proof_shape: bind-only; escape_witness: none; consumers: tri_det_pos.
scaleVec: declaration_kind: definition; consumers: tri_det_pos.
tri: declaration_kind: definition; consumers: A_pos, B_pos, tri_det_pos, tri_det_pos.
tri_det_pos: proof_shape: content; escape_witness: tri_det_pos; consumers: A_pos, B_pos.
x_closed: proof_shape: bind-only; escape_witness: none; consumers: x_normal.
y_closed: proof_shape: bind-only; escape_witness: none; consumers: y_normal.
x_normal: proof_shape: bind-only; escape_witness: none; consumers: A_pos, B_pos.
y_normal: proof_shape: bind-only; escape_witness: none; consumers: A_pos, B_pos.
tt_all_bound: proof_shape: bind-only; escape_witness: none; consumers: B_pos.
A_pos: proof_shape: content; escape_witness: A_pos; consumers: sAux_pos.
B_pos: proof_shape: content; escape_witness: B_pos; consumers: sAux_pos.
sAux_pos: proof_shape: content; escape_witness: sAux_pos; consumers: result.
-/

import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false

namespace D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity

/-- `A_ℓ(x⃗ | y⃗)`: the determinant of the `ℓ × ℓ` tridiagonal matrix with diagonal `x_1, …, x_ℓ`,
superdiagonal `y_1, …, y_{ℓ-1}` and subdiagonal `1` (`A_0 = 1`). Sequences are indexed from `1`. -/
noncomputable def A (x y : ℕ → ℝ) (ℓ : ℕ) : ℝ :=
  Matrix.det (Matrix.of fun i j : Fin ℓ =>
    if (i : ℕ) = j then x (i + 1)
    else if (j : ℕ) = i + 1 then y (i + 1)
    else if (i : ℕ) = j + 1 then 1 else 0)

/-- `B_k(x⃗ | y⃗)`: the determinant of the `(k+1) × (k+1)` tridiagonal matrix with first row
`(y_1, x_1 y_2, 0, …)`, then diagonal `x_3, x_4, …`, superdiagonal `y_3, y_4, …` and subdiagonal `1`. -/
noncomputable def B (x y : ℕ → ℝ) (k : ℕ) : ℝ :=
  Matrix.det (Matrix.of fun i j : Fin (k + 1) =>
    if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then y 1
    else if (i : ℕ) = 0 ∧ (j : ℕ) = 1 then x 1 * y 2
    else if (i : ℕ) = j then x (i + 2)
    else if (j : ℕ) = i + 1 then y (i + 2)
    else if (i : ℕ) = j + 1 then 1 else 0)

/-- Definition 2.5 with `k` leading letters `1` already read: `s_{1^k} = A_k` and
`s_{1^k 2 u} = B_k(x⃗ + |u| | y⃗ + |u|) · s_u`, for words over `{1, 2}` with `|u|` the sum of the letters. -/
noncomputable def sAux (x y : ℕ → ℝ) : ℕ → List ℕ → ℝ
  | k, [] => A x y k
  | k, 1 :: w => sAux x y (k + 1) w
  | k, _ :: u => B (fun k => x (k + u.sum)) (fun k => y (k + u.sum)) k * sAux x y 0 u

/-- The biserial clone Schur function `s_w(x⃗ | y⃗)`. -/
noncomputable def s (x y : ℕ → ℝ) (w : List ℕ) : ℝ := sAux x y 0 w

/-- Definition 4.1: `(x⃗, y⃗)` is Fibonacci positive if `s_w(x⃗ | y⃗) > 0` for every Fibonacci word `w`. -/
def FibonacciPositive (x y : ℕ → ℝ) : Prop :=
  ∀ w : List ℕ, (∀ a ∈ w, a = 1 ∨ a = 2) → 0 < s x y w

/-- The alternative `q`-Charlier specialization, `x_k` for `k ≥ 1`. -/
noncomputable def xAQC (ρ q : ℝ) (k : ℕ) : ℝ :=
  q ^ ((k : ℤ) - 1) * (1 + ρ * q ^ ((k : ℤ) - 2) + ρ * q ^ ((k : ℤ) - 1) - ρ * q ^ (2 * (k : ℤ) - 2)) /
    ((1 + ρ * q ^ (2 * (k : ℤ) - 3)) * (1 + ρ * q ^ (2 * (k : ℤ) - 1)))

/-- The alternative `q`-Charlier specialization, `y_k` for `k ≥ 1`. -/
noncomputable def yAQC (ρ q : ℝ) (k : ℕ) : ℝ :=
  ρ * q ^ (3 * (k : ℤ) - 2) * (1 - q ^ (k : ℤ)) * (1 + ρ * q ^ ((k : ℤ) - 1)) /
    ((1 + ρ * q ^ (2 * (k : ℤ))) * (1 + ρ * q ^ (2 * (k : ℤ) - 1)) ^ 2 * (1 + ρ * q ^ (2 * (k : ℤ) - 2)))

/-- Petrov–Scott, Forum Math. Sigma 14 (2026) e15, Conjecture 6.3 ("There exist values of ρ and q for which the
following specialization (which we call the alternative q-Charlier) is Fibonacci positive"). -/
def claim : Prop := ∃ ρ q : ℝ, FibonacciPositive (xAQC ρ q) (yAQC ρ q)

end D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity

namespace D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity

private theorem det_pos_of_dominant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hd : ∀ i, 0 < M i i)
    (h : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖M i j‖ < M i i) : 0 < M.det := by
  let H (t : ℝ) : Matrix ι ι ℝ := fun i j => if i = j then M i i else t * M i j
  have hzero : H 0 = Matrix.diagonal (fun i => M i i) := by
    ext i j
    by_cases hij : i = j <;> simp [H, hij]
  have hone : H 1 = M := by
    ext i j
    by_cases hij : i = j <;> simp [H, hij]
  have hn (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : (H t).det ≠ 0 := by
    apply det_ne_zero_of_sum_row_lt_diag
    intro i
    have he : ∑ j ∈ Finset.univ.erase i, ‖H t i j‖ =
        t * ∑ j ∈ Finset.univ.erase i, ‖M i j‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hji : i ≠ j := (Finset.mem_erase.mp hj).1.symm
      simp [H, hji, norm_mul, Real.norm_of_nonneg ht.1]
    rw [he]
    have hh : ‖H t i i‖ = M i i := by simp [H, Real.norm_of_nonneg (hd i).le]
    rw [hh]
    exact (mul_le_of_le_one_left (Finset.sum_nonneg fun _ _ => norm_nonneg _) ht.2).trans_lt (h i)
  have hc : Continuous (fun t => (H t).det) := by
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    dsimp [H]
    split_ifs <;> fun_prop
  have hz : 0 < (H 0).det := by
    rw [hzero, Matrix.det_diagonal]
    exact Finset.prod_pos fun i _ => hd i
  by_contra hnpos
  have h1 : (H 1).det ≤ 0 := by simpa [hone] using le_of_not_gt hnpos
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1)
    hc.continuousOn (show (0:ℝ) ∈ Set.Icc ((H 1).det) ((H 0).det) from ⟨h1, hz.le⟩)
  exact hn t ht he

private noncomputable def paramT (z : ℝ) : ℝ :=
  z * (1-z) * (1+z^2/16) / ((1+z/4)*(1+z^2))
private noncomputable def tt (k : ℕ) : ℝ := paramT ((4⁻¹:ℝ)^k)
private noncomputable def cc (k : ℕ) : ℝ :=
  4 * ((4⁻¹:ℝ)^k) * (1+((4⁻¹:ℝ)^k)) /
    ((1+((4⁻¹:ℝ)^k)^2)*(1+4*((4⁻¹:ℝ)^k)^2))

private theorem paramT_bounds (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ paramT z ∧ paramT z ≤ z := by
  have hsub : 0 ≤ 1-z := sub_nonneg.mpr hz1
  have hsq : 0 ≤ z^2 := sq_nonneg z
  have hd : 0 < (1+z/4)*(1+z^2) := by positivity
  constructor
  · exact div_nonneg (by positivity) hd.le
  · rw [paramT, div_le_iff₀ hd]
    have hh : (1-z)*(1+z^2/16) ≤ (1+z/4)*(1+z^2) := by
      calc
        (1-z)*(1+z^2/16) ≤ 1*(1+z^2) :=
          mul_le_mul (by linarith) (by nlinarith) (by positivity) (by norm_num)
        _ ≤ (1+z/4)*(1+z^2) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hh hz]

private theorem paramT_lower (z : ℝ) (hz : 0 ≤ z) (hzq : z ≤ 4⁻¹) :
    z/2 ≤ paramT z := by
  have hsub : 0 ≤ 1-z := by linarith
  have hsq : 0 ≤ z^2 := sq_nonneg z
  have hsqbound : z^2 ≤ 1/16 := by nlinarith
  have hd : 0 < (1+z/4)*(1+z^2) := by positivity
  have hdb : (1+z/4)*(1+z^2) ≤ 3/2 := by
    have h := mul_le_mul (show 1+z/4 ≤ (17/16:ℝ) by linarith)
      (show 1+z^2 ≤ (17/16:ℝ) by linarith) (by positivity : 0 ≤ 1+z^2)
      (by norm_num : (0:ℝ) ≤ 17/16)
    norm_num at h
    linarith
  have hn : z*(3/4) ≤ z*(1-z)*(1+z^2/16) := by
    have h1 : z*(3/4) ≤ z*(1-z) := by nlinarith
    have h2 : z*(1-z) ≤ z*(1-z)*(1+z^2/16) := by
      nlinarith [mul_nonneg (show 0 ≤ z*(1-z) by positivity) hsq]
    exact h1.trans h2
  rw [paramT, le_div_iff₀ hd]
  nlinarith [mul_le_mul_of_nonneg_left hdb (show 0 ≤ z/2 by positivity)]

private theorem tt_nonneg (k : ℕ) : 0 ≤ tt k :=
  (paramT_bounds _ (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))).1

private theorem tt_bound (k : ℕ) (hk : 1 ≤ k) : tt k ≤ 4⁻¹ := by
  have hp : (4⁻¹:ℝ)^k ≤ 4⁻¹ := by
    simpa using pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 4⁻¹)
      (by norm_num : (4⁻¹:ℝ) ≤ 1) hk
  exact (paramT_bounds _ (by positivity) (by linarith)).2.trans hp

private theorem tt_pos (k : ℕ) (hk : 1 ≤ k) : 0 < tt k := by
  have hp : (4⁻¹:ℝ)^k ≤ 4⁻¹ := by
    simpa using pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 4⁻¹)
      (by norm_num : (4⁻¹:ℝ) ≤ 1) hk
  exact (half_pos (pow_pos (by norm_num : (0:ℝ) < 4⁻¹) k)).trans_le
    (paramT_lower _ (by positivity) hp)

private theorem tt_decay (k : ℕ) (hk : 1 ≤ k) : tt (k+1) ≤ tt k / 2 := by
  have hp : (4⁻¹:ℝ)^k ≤ 4⁻¹ := by
    simpa using pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 4⁻¹)
      (by norm_num : (4⁻¹:ℝ) ≤ 1) hk
  have hl := paramT_lower _ (by positivity : 0 ≤ (4⁻¹:ℝ)^k) hp
  have hu := (paramT_bounds ((4⁻¹:ℝ)^(k+1)) (by positivity)
    (pow_le_one₀ (by norm_num) (by norm_num))).2
  dsimp [tt]
  rw [pow_succ] at hu
  rw [pow_succ]
  linarith

private theorem cc_pos (k : ℕ) : 0 < cc k := by
  unfold cc
  positivity

private theorem fin_sum_spike_le (n a : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (s : Finset (Fin n)) : (∑ j ∈ s, if (j:ℕ) = a then u else 0) ≤ u := by
  classical
  by_cases ha : a < n
  · let j : Fin n := ⟨a, ha⟩
    have he (i : Fin n) : ((i:ℕ) = a) ↔ i = j := by exact Iff.symm Fin.eq_mk_iff_val_eq
    simp_rw [he]
    simp only [Finset.sum_ite_eq']
    split_ifs <;> linarith
  · have he (j : Fin n) : (j:ℕ) ≠ a := by omega
    simp [he, hu]

private noncomputable def scaleVec (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | k+1 => scaleVec c k / c (k+1)

private noncomputable def tri (c d e : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if (i:ℕ) = j then c i * d i
    else if (j:ℕ) = i+1 then c i * c (i+1) * e i
    else if (i:ℕ) = j+1 then 1 else 0

private theorem tri_det_pos (c d e : ℕ → ℝ) (n : ℕ)
    (hc : ∀ k, 0 < c k) (he : ∀ k, 0 ≤ e k)
    (hd : ∀ k, (if k=0 then 0 else 1) + e k < d k) : 0 < (tri c d e n).det := by
  classical
  let v := scaleVec c
  have hv (k : ℕ) : 0 < v k := by
    induction k with
    | zero => norm_num [v, scaleVec]
    | succ k ih => exact div_pos ih (hc _)
  have hvstep (k : ℕ) : c (k+1) * v (k+1) = v k := by
    dsimp [v, scaleVec]
    exact mul_div_cancel₀ _ (ne_of_gt (hc (k+1)))
  let M := tri c d e n * Matrix.diagonal (fun i : Fin n => v i)
  have hM (i j : Fin n) : M i j = tri c d e n i j * v j := by
    exact Matrix.mul_diagonal (fun i : Fin n => v i) (tri c d e n) i j
  have hdiag (i : Fin n) : M i i = c i * v i * d i := by
    rw [hM]
    simp only [tri]
    exact mul_right_comm (c i) (d i) (v i)
  have hpos : 0 < M.det := by
    apply det_pos_of_dominant
    · intro i
      rw [hdiag]
      have hi := hd i
      have hei := he i
      have hdi : 0 < d i := by split_ifs at hi <;> linarith
      exact mul_pos (mul_pos (hc _) (hv _)) hdi
    · intro i
      let L := if (i:ℕ)=0 then (0:ℝ) else c i * v i
      let U := c i * v i * e i
      have hL : 0 ≤ L := by
        dsimp [L]
        split_ifs
        · norm_num
        · exact (mul_pos (hc _) (hv _)).le
      have hU : 0 ≤ U := mul_nonneg (mul_pos (hc _) (hv _)).le (he _)
      have hentry (j : Fin n) (hj : j ∈ Finset.univ.erase i) :
          ‖M i j‖ ≤ (if (j:ℕ)=i+1 then U else 0) +
            (if (j:ℕ)=i-1 then L else 0) := by
        have hji : (i:ℕ) ≠ (j:ℕ) := by
          intro hh
          exact (Finset.mem_erase.mp hj).1 (Fin.ext hh.symm)
        rw [hM]
        by_cases hs : (j:ℕ)=i+1
        · have hs' : v j = v (i+1) := congrArg v hs
          simp only [tri, ite_eq_right hji, ite_eq_left hs, hs']
          have hval : c i * c (i+1) * e i * v (i+1) = U := by
            dsimp [U]
            calc
              _ = c i * e i * (c (i+1) * v (i+1)) := by
                simpa only [mul_assoc] using mul_mul_mul_comm (c i) (c (i+1)) (e i) (v (i+1))
              _ = c i * e i * v i := by rw [hvstep]
              _ = _ := by exact mul_right_comm (c i) (e i) (v i)
          rw [hval, Real.norm_of_nonneg hU]
          split_ifs <;> linarith
        · by_cases hp : (i:ℕ)=j+1
          · have hip : (i:ℕ) ≠ 0 := by omega
            have hjp : (j:ℕ)=i-1 := Nat.eq_sub_of_add_eq hp.symm
            have hvp : v j = c i * v i := by
              simpa [hp] using (hvstep j).symm
            simp only [tri, ite_eq_right hji, ite_eq_right hs, ite_eq_left hp, one_mul, ite_eq_left hjp,
              zero_add]
            rw [hvp, Real.norm_of_nonneg (mul_pos (hc _) (hv _)).le]
            simp only [L, ite_eq_right hip]
            exact le_rfl
          · simp only [tri, ite_eq_right hji, ite_eq_right hs, ite_eq_right hp, zero_mul, norm_zero]
            split_ifs <;> linarith
      have hsum : ∑ j ∈ Finset.univ.erase i, ‖M i j‖ ≤ U+L := by
        calc
          _ ≤ ∑ j ∈ Finset.univ.erase i,
              ((if (j:ℕ)=i+1 then U else 0) + (if (j:ℕ)=i-1 then L else 0)) :=
            Finset.sum_le_sum hentry
          _ = (∑ j ∈ Finset.univ.erase i, if (j:ℕ)=i+1 then U else 0) +
              (∑ j ∈ Finset.univ.erase i, if (j:ℕ)=i-1 then L else 0) := Finset.sum_add_distrib
          _ ≤ U+L := add_le_add (fin_sum_spike_le _ _ _ hU _) (fin_sum_spike_le _ _ _ hL _)
      rw [hdiag]
      apply hsum.trans_lt
      have hdi := mul_lt_mul_of_pos_left (hd i) (mul_pos (hc i) (hv i))
      dsimp [U, L]
      split_ifs at * <;> nlinarith
  have hdv : 0 < (Matrix.diagonal (fun i : Fin n => v i)).det := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_pos fun i _ => hv _
  dsimp [M] at hpos
  rw [Matrix.det_mul] at hpos
  exact (mul_pos_iff_of_pos_right hdv).mp hpos

private theorem x_closed (k : ℕ) :
    xAQC (4⁻¹) (4⁻¹) k =
      4*((4⁻¹:ℝ)^k)*(1+5*((4⁻¹:ℝ)^k)-4*((4⁻¹:ℝ)^k)^2) /
      ((1+16*((4⁻¹:ℝ)^k)^2)*(1+((4⁻¹:ℝ)^k)^2)) := by
  have h2 : (4⁻¹:ℝ)^(2*(k:ℤ)) = ((4⁻¹:ℝ)^k)^2 := by
    rw [mul_comm (2:ℤ), zpow_mul]
    simp
  unfold xAQC
  simp only [zpow_sub₀ (by norm_num : (4⁻¹:ℝ) ≠ 0), h2, zpow_natCast]
  norm_num
  field_simp (disch := positivity)
  ring

private theorem y_closed (k : ℕ) :
    yAQC (4⁻¹) (4⁻¹) k =
      4*((4⁻¹:ℝ)^k)^3*(1-((4⁻¹:ℝ)^k))*(1+((4⁻¹:ℝ)^k)) /
      ((1+((4⁻¹:ℝ)^k)^2/4)*(1+((4⁻¹:ℝ)^k)^2)^2*(1+4*((4⁻¹:ℝ)^k)^2)) := by
  have h2 : (4⁻¹:ℝ)^(2*(k:ℤ)) = ((4⁻¹:ℝ)^k)^2 := by
    rw [mul_comm (2:ℤ), zpow_mul]
    simp
  have h3 : (4⁻¹:ℝ)^(3*(k:ℤ)) = ((4⁻¹:ℝ)^k)^3 := by
    rw [mul_comm (3:ℤ), zpow_mul]
    simp
  unfold yAQC
  simp only [zpow_sub₀ (by norm_num : (4⁻¹:ℝ) ≠ 0), h2, h3, zpow_natCast]
  norm_num
  field_simp (disch := positivity)
  ring

private theorem x_normal (k : ℕ) :
    xAQC (4⁻¹) (4⁻¹) (k+1) = cc (k+1)*(1+tt k) := by
  rw [x_closed]
  unfold cc tt paramT
  rw [pow_succ]
  field_simp (disch := positivity)
  ring

private theorem y_normal (k : ℕ) :
    yAQC (4⁻¹) (4⁻¹) k = cc k * cc (k+1) * tt k := by
  rw [y_closed]
  unfold cc tt paramT
  rw [pow_succ]
  field_simp (disch := positivity)
  ring

private theorem tt_all_bound (k : ℕ) : tt k ≤ 4⁻¹ := by
  cases k with
  | zero => norm_num [tt, paramT]
  | succ k => exact tt_bound _ (by omega)

private theorem A_pos (n : ℕ) :
    0 < A (xAQC (4⁻¹) (4⁻¹)) (yAQC (4⁻¹) (4⁻¹)) n := by
  let c := fun i => cc (i+1)
  let d := fun i => 1+tt i
  let e := fun i => tt (i+1)
  have hdet := tri_det_pos c d e n
    (fun _ => cc_pos _) (fun _ => tt_nonneg _)
    (by
      intro i
      dsimp [d, e]
      by_cases hi : i=0
      · subst i
        norm_num [tt, paramT]
      · rw [ite_eq_right hi]
        have ht := tt_decay i (by omega)
        have hp := tt_pos i (by omega)
        linarith)
  have hm : (Matrix.of fun i j : Fin n =>
    if (i:ℕ) = j then xAQC (4⁻¹) (4⁻¹) (i+1)
    else if (j:ℕ) = i+1 then yAQC (4⁻¹) (4⁻¹) (i+1)
    else if (i:ℕ) = j+1 then 1 else 0) = tri c d e n := by
    ext i j
    simp only [Matrix.of_apply, tri]
    split_ifs <;> simp [c, d, e, x_normal, y_normal, Nat.add_assoc]
  simpa only [A, hm] using hdet

private theorem B_pos (m n : ℕ) :
    0 < B (fun k => xAQC (4⁻¹) (4⁻¹) (k + m)) (fun k => yAQC (4⁻¹) (4⁻¹) (k + m)) n := by
  let c := fun i => if i=0 then cc (m+1)*cc (m+2) else cc (m+i+2)
  let d := fun i => if i=0 then tt (m+1) else 1+tt (m+i+1)
  let e := fun i => if i=0 then (1+tt m)*tt (m+2) else tt (m+i+2)
  have hc : ∀ k, 0 < c k := by
    intro k
    dsimp [c]
    split_ifs
    · exact mul_pos (cc_pos _) (cc_pos _)
    · exact cc_pos _
  have he : ∀ k, 0 ≤ e k := by
    intro k
    dsimp [e]
    split_ifs
    · exact mul_nonneg (by linarith [tt_nonneg m]) (tt_nonneg _)
    · exact tt_nonneg _
  have hd : ∀ k, (if k=0 then 0 else 1)+e k < d k := by
    intro k
    by_cases hk : k=0
    · subst k
      simp only [e, d, ite_eq_left rfl, ite_true, zero_add]
      have hb := tt_all_bound m
      have hn := tt_nonneg m
      have hp := tt_pos (m+1) (by omega)
      have hdec := tt_decay (m+1) (by omega)
      have hnp := tt_nonneg (m+2)
      have heq : (m+1)+1 = m+2 := Nat.add_left_inj.mpr rfl
      rw [heq] at hdec
      nlinarith [mul_nonneg (show 0 ≤ 4⁻¹-tt m by linarith) hnp]
    · simp only [e, d, ite_eq_right hk]
      have hdec := tt_decay (m+k+1) (by omega)
      have hp := tt_pos (m+k+1) (by omega)
      have heq : (m+k+1)+1 = m+k+2 := Nat.add_right_comm (m + k) 1 1
      rw [heq] at hdec
      linarith
  have hdet := tri_det_pos c d e (n+1) hc he hd
  have hm : (Matrix.of fun i j : Fin (n+1) =>
    if (i:ℕ) = 0 ∧ (j:ℕ) = 0 then yAQC (4⁻¹) (4⁻¹) (1 + m)
    else if (i:ℕ) = 0 ∧ (j:ℕ) = 1 then xAQC (4⁻¹) (4⁻¹) (1 + m) * yAQC (4⁻¹) (4⁻¹) (2 + m)
    else if (i:ℕ) = j then xAQC (4⁻¹) (4⁻¹) ((i+2) + m)
    else if (j:ℕ) = i+1 then yAQC (4⁻¹) (4⁻¹) ((i+2) + m)
    else if (i:ℕ) = j+1 then 1 else 0) = tri c d e (n+1) := by
    ext i j
    simp only [Matrix.of_apply, tri]
    by_cases hi : (i:ℕ)=0
    · by_cases hj : (j:ℕ)=0
      · simp [hi, hj, c, d, y_normal, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      · by_cases hj1 : (j:ℕ)=1
        · simp [hi, hj1, c, e, y_normal, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          have hx := x_normal m
          rw [hx]
          ring
        · simp [hi, hj, hj1, Ne.symm hj]
    · have hi1 : (i:ℕ)+1 ≠ 0 := Ne.symm (Nat.zero_ne_add_one (i : ℕ))
      simp only [hi, false_and, ite_false]
      by_cases hij : (i:ℕ)=(j:ℕ)
      · simp only [ite_eq_left hij, c, d, ite_eq_right hi]
        simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using x_normal (m+i+1)
      · by_cases hs : (j:ℕ)=i+1
        · simp only [ite_eq_right hij, ite_eq_left hs, c, e, ite_eq_right hi, ite_eq_right hi1]
          simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using y_normal (m+i+2)
        · simp only [ite_eq_right hij, ite_eq_right hs]
  simpa only [B, hm] using hdet

private theorem sAux_pos (w : List ℕ) (k : ℕ) :
    0 < sAux (xAQC (4⁻¹) (4⁻¹)) (yAQC (4⁻¹) (4⁻¹)) k w := by
  induction w generalizing k with
  | nil => exact A_pos k
  | cons a w ih =>
    by_cases ha : a=1
    · subst a
      simpa only [sAux] using ih (k+1)
    · simpa only [sAux, ite_eq_right ha] using mul_pos (B_pos w.sum k) (ih 0)

theorem result : D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity.claim := by
  refine ⟨4⁻¹, 4⁻¹, ?_⟩
  intro w hw
  exact sAux_pos w 0



end D5.S3.Combinatorics.YoungFibonacci.PetrovScottAltQCharlierPositivity
