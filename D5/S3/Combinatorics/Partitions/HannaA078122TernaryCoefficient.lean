/- GID: D5/S3/Combinatorics/Partitions/HannaA078122TernaryCoefficient
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/HannaA078122TernaryCoefficient
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna's full ternary matrix coefficient formula via scaled convolution. -/

/-
result: proof_shape: content (scaled convolution and strong row induction).
escape_witness: none.
admission_basis: open-problem-resolution (#23570; Proved).
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/26165.

The first-column condition M(n,0)=1 is the one used by both source programs
and the displayed matrix; the NAME's first-row condition is inconsistent
with lower triangularity. The source formulas are retained in IsSourceMatrix,
partitionSeries and claim. Finite views use Matrix.submatrix directly.

Declaration classification (same-delivery proofs expanded; frozen dependencies: none):
IsSourceMatrix: proof_shape: bind-only; consumers: claim, Mstar_source, source_unique.
partitionSeries: proof_shape: bind-only; consumers: claim, rel, F, A_zero, coeff_A_zero, coeff_A_zero_all, coeff_rel, fdiff, formula_Mstar.
claim: proof_shape: bind-only; consumers: result.
rel: proof_shape: bind-only; consumers: coeff_rel.
F: proof_shape: bind-only; consumers: fdiff, convolution, F_one, G_cast, formula_Mstar.
A_zero: proof_shape: bind-only; consumers: coeff_A_zero.
coeff_A_zero: proof_shape: bind-only; consumers: fdiff.
coeff_A_zero_all: proof_shape: bind-only; consumers: fdiff, F_one.
coeff_rel: proof_shape: bind-only; consumers: fdiff.
fdiff: proof_shape: bind-only; consumers: convolution, G_cast.
sum_succ_decomp: proof_shape: bind-only; consumers: convolution.
convolution: proof_shape: content; consumers: G_convolution.
F_one: proof_shape: bind-only; consumers: G_one.
G: proof_shape: bind-only; consumers: G_cast, G_one, G_convolution, EN, CN_diag, EN_sum, source_unique.
G_cast: proof_shape: content; consumers: G_one, G_convolution, formula_Mstar.
G_one: proof_shape: content; consumers: CN_col0, source_unique.
G_convolution: proof_shape: content; consumers: EN_sum.
EN: proof_shape: bind-only; consumers: CN_lower, CN_col0, CN_diag, EN_sum, CN_mul, CN_shift, Mstar_source, source_unique, formula_Mstar, result.
CN_lower: proof_shape: bind-only; consumers: Mstar_source.
CN_col0: proof_shape: content; consumers: Mstar_source.
CN_diag: proof_shape: bind-only; consumers: Mstar_source.
EN_sum: proof_shape: content; consumers: CN_mul.
CN_mul: proof_shape: content; consumers: CN_shift.
CN_shift: proof_shape: content; consumers: Mstar_source, source_unique.
Mstar_source: proof_shape: content; consumers: result.
source_unique: proof_shape: content; consumers: result.
formula_Mstar: proof_shape: content; consumers: result.
result: proof_shape: content; consumers: settling conclusion.
-/

import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown

open scoped BigOperators

namespace D5.S3.Combinatorics.Partitions.HannaA078122TernaryCoefficient

def IsSourceMatrix (M : Matrix ℕ ℕ ℕ) : Prop :=
  M.IsLowerTriangular ∧
    (∀ n : ℕ, M n 0 = 1) ∧
    (∀ n : ℕ, M n n = 1) ∧
    ∀ (m : ℕ) (i j : Fin (m + 1)),
      ((M.submatrix (fun a : Fin (m + 1) => a.val)
        (fun a : Fin (m + 1) => a.val)) ^ 3) i j = M (i.val + 1) (j.val + 1)

/-- The formal expansion of 1/Product_{j=0..d}(1-x^(3^j)).
Every exponent 3^j is positive, so the denominator has constant term 1. -/

noncomputable def partitionSeries (d : ℕ) : PowerSeries ℚ :=
  (∏ j ∈ Finset.range (d + 1),
    ((1 : PowerSeries ℚ) - PowerSeries.X ^ (3 ^ j)))⁻¹

/-- The full second FORMULA conjecture, with existence of the implicitly
specified source matrix. Natural subtraction is used only when k < n,
so both subtractions agree with the source's integer exponents. -/

def claim : Prop :=
  (∃ M : Matrix ℕ ℕ ℕ, IsSourceMatrix M) ∧
    ∀ M : Matrix ℕ ℕ ℕ, IsSourceMatrix M →
      ∀ (n k : ℕ), 0 < n → k < n →
        (M n k : ℚ) =
          PowerSeries.coeff (3 ^ n - 3 ^ (n - k)) (partitionSeries (n - k))

private theorem rel (d : ℕ) :
    ((1 : PowerSeries ℚ) - PowerSeries.X ^ (3 ^ (d+1))) * partitionSeries (d+1) = partitionSeries d := by
  rw [partitionSeries, partitionSeries, Finset.prod_range_succ]
  let P : PowerSeries ℚ := ∏ j ∈ Finset.range (d + 1), ((1 : PowerSeries ℚ) - PowerSeries.X ^ (3 ^ j))
  let Q : PowerSeries ℚ := (1 : PowerSeries ℚ) - PowerSeries.X ^ (3 ^ (d+1))
  have hQ : PowerSeries.constantCoeff Q ≠ 0 := by simp [Q]
  change Q * (P * Q)⁻¹ = P⁻¹
  rw [PowerSeries.mul_inv_rev]
  rw [← mul_assoc, PowerSeries.mul_inv_cancel Q hQ, one_mul]

private noncomputable def F (d t : ℕ) : ℚ :=
  if d = 0 then 1 else if t = 0 then 0 else PowerSeries.coeff (3^d * (t-1)) (partitionSeries d)

private theorem A_zero : partitionSeries 0 = PowerSeries.mk (1 : ℕ → ℚ) := by
  let Q : PowerSeries ℚ := (1 : PowerSeries ℚ) - PowerSeries.X
  have hQ : PowerSeries.constantCoeff Q ≠ 0 := by simp [Q]
  have hinv : Q⁻¹ * Q = 1 := PowerSeries.inv_mul_cancel Q hQ
  have hprod : PowerSeries.mk (1 : ℕ → ℚ) * Q = 1 := by
    simpa [Q] using (PowerSeries.mk_one_mul_one_sub_eq_one ℚ)
  have hEq : partitionSeries 0 = Q⁻¹ := by
    simp [partitionSeries, Q]
  rw [hEq]
  calc
    Q⁻¹ = Q⁻¹ * 1 := by rw [mul_one]
    _ = Q⁻¹ * (PowerSeries.mk (1 : ℕ → ℚ) * Q) := by rw [hprod]
    _ = (Q⁻¹ * Q) * PowerSeries.mk (1 : ℕ → ℚ) := by ac_rfl
    _ = PowerSeries.mk (1 : ℕ → ℚ) := by rw [hinv, one_mul]

private theorem coeff_A_zero (n : ℕ) : PowerSeries.coeff n (partitionSeries 0) = 1 := by
  rw [A_zero]
  simp

private theorem coeff_A_zero_all (d : ℕ) : PowerSeries.coeff 0 (partitionSeries d) = 1 := by
  simp [partitionSeries, PowerSeries.coeff_zero_eq_constantCoeff]

private theorem coeff_rel (d t : ℕ) (hd : 0 < d) (ht : 0 < t) :
    PowerSeries.coeff (3^d * t) (partitionSeries d) - PowerSeries.coeff (3^d * (t-1)) (partitionSeries d) =
      PowerSeries.coeff (3^d * t) (partitionSeries (d-1)) := by
  have hd' : d - 1 + 1 = d := by exact Nat.sub_add_cancel hd
  have h := congrArg (PowerSeries.coeff (3^d * t)) (rel (d-1))
  simp only [hd'] at h
  rw [sub_mul] at h
  simp only [one_mul] at h
  rw [map_sub, PowerSeries.coeff_X_pow_mul'] at h
  have hpow : 3^d ≤ 3^d * t := by exact Nat.le_mul_of_pos_right (3 ^ d) ht
  simp only [ite_eq_left hpow] at h
  have hidx : 3^d * t - 3^d = 3^d * (t - 1) := by exact Eq.symm (Nat.mul_sub_one (3 ^ d) t)
  rw [hidx] at h
  exact h

private theorem fdiff (d : ℕ) (hd : 0 < d) (t : ℕ) : F d (t+1) = F d t + F (d-1) (3*t+1) := by
  have h0 := coeff_A_zero_all
  have hleft : F d (t+1) = PowerSeries.coeff (3^d * t) (partitionSeries d) := by
    simp [F, hd.ne']
  by_cases ht : t = 0
  · subst t
    rw [hleft]
    by_cases he : d = 1
    · subst d
      simp [F, h0]
    · have hd1 : 0 < d - 1 := by omega
      simp [F, hd.ne', hd1.ne', h0]
  · have ht' : 0 < t := Nat.pos_of_ne_zero ht
    have hmid : F d t = PowerSeries.coeff (3^d * (t-1)) (partitionSeries d) := by
      simp [F, hd.ne', ht]
    by_cases he : d = 1
    · subst d
      have hr : F 0 (3*t+1) = 1 := by exact Rat.add_left_cancel (F 1 (t + 1)) (congrFun (congrArg HAdd.hAdd hleft) (F 0 (3 * t + 1)))
      rw [hleft, hmid, hr]
      have h := coeff_rel 1 t (by omega) ht'
      have hi : 3^1 * t = 3 * t := by exact (Nat.mul_left_inj ht).mpr rfl
      have hi' : 3^1 * (t-1) = 3 * (t-1) := by exact Nat.add_zero ((3 ^ 1).mul (t - 1))
      rw [hi, hi'] at h
      simp only [Nat.sub_self] at h
      have ha : PowerSeries.coeff (3*t) (partitionSeries 0) = 1 := coeff_A_zero (3*t)
      norm_num at hleft hmid h ⊢
      linarith
    · have hd1 : 0 < d - 1 := by omega
      have hright : F (d-1) (3*t+1) = PowerSeries.coeff (3^d*t) (partitionSeries (d-1)) := by
        simp [F, hd1.ne']
        have hp : 3^d = 3^(d-1) * 3 := by exact Eq.symm (Nat.pow_pred_mul hd)
        rw [hp]
        ring
      rw [hleft, hmid, hright]
      linarith [coeff_rel d t hd ht']

private theorem sum_succ_decomp (n : ℕ) (g : ℕ → ℚ) :
    (∑ h ∈ Finset.range (n+1), g h) = g 0 + ∑ j ∈ Finset.range n, g (j+1) := by
  simpa [add_comm] using (Finset.sum_range_succ' g n)

private theorem convolution (d r u : ℕ) :
    F d (r+u) = ∑ h ∈ Finset.range (d+1), F (d-h) (3^h*r) * F h u := by
  induction d generalizing r u with
  | zero => simp [F]
  | succ d ih =>
    induction u with
    | zero =>
      simp only [Nat.add_zero]
      rw [Finset.sum_eq_single 0]
      · simp [F]
      · intro b hb hb0
        have hb' : b ≠ 0 := by exact Ne.symm (Ne.intro (id (Ne.symm hb0)))
        simp [F, hb']
      · simp
    | succ u ihu =>
      have hl := fdiff (d+1) (by omega) (r+u)
      have ho := ih (3*r) (3*u+1)
      have hs (v : ℕ) :
          (∑ h ∈ Finset.range (d+2), F (d+1-h) (3^h*r) * F h v) =
            F (d+1) r +
            ∑ j ∈ Finset.range (d+1), F (d-j) (3^(j+1)*r) * F (j+1) v := by
        rw [sum_succ_decomp]
        simp only [Nat.sub_zero, pow_zero, one_mul]
        have hF0 : F 0 v = 1 := by exact Rat.ext rfl rfl
        rw [hF0, mul_one]
        apply congrArg (fun z => F (d+1) r + z)
        apply Finset.sum_congr rfl
        intro j hj
        congr 2
        omega
      have hinc :
          (∑ j ∈ Finset.range (d+1), F (d-j) (3^(j+1)*r) * F (j+1) (u+1)) =
            (∑ j ∈ Finset.range (d+1), F (d-j) (3^(j+1)*r) * F (j+1) u) +
            (∑ j ∈ Finset.range (d+1), F (d-j) (3^(j+1)*r) * F j (3*u+1)) := by
        calc
          _ = ∑ j ∈ Finset.range (d+1),
                F (d-j) (3^(j+1)*r) *
                  (F (j+1) u + F j (3*u+1)) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [fdiff (j+1) (by omega) u]
            have hjidx : j + 1 - 1 = j := by exact Nat.add_sub_self_right j 1
            rw [hjidx]
          _ = _ := by
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib]
      have houter' :
          F d (3*r + (3*u+1)) =
            ∑ j ∈ Finset.range (d+1), F (d-j) (3^(j+1)*r) * F j (3*u+1) := by
        rw [ho]
        apply Finset.sum_congr rfl
        intro j hj
        congr 2
        ring
      rw [show r + (u+1) = (r+u)+1 by omega, hl, ihu, hs (u+1), hinc, hs u]
      have hdarg : d + 1 - 1 = d := by exact Nat.add_sub_self_right d 1
      have harg : 3 * (r + u) + 1 = 3*r + (3*u+1) := by ring
      rw [hdarg, harg, houter']
      ring

private theorem F_one (d : ℕ) : F d 1 = 1 := by
  by_cases hd : d = 0
  · simp [F, hd]
  · simp [F, hd, coeff_A_zero_all]

private def G : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _+1, 0 => 0
  | d+1, t+1 => G (d+1) t + G d (3*t+1)

private theorem G_cast (d t : ℕ) : (G d t : ℚ) = F d t := by
  induction d generalizing t with
  | zero => simp [G, F]
  | succ d ih =>
    induction t with
    | zero => simp [G, F]
    | succ t iht =>
      simp only [G, Nat.cast_add]
      change (G (d+1) t : ℚ) + (G d (3*t+1) : ℚ) = F (d+1) (t+1)
      rw [fdiff (d+1) (by omega) t]
      rw [ih, iht]
      simp only [Nat.add_sub_cancel]

private theorem G_one (d : ℕ) : G d 1 = 1 := by
  apply Nat.cast_injective (R := ℚ)
  rw [G_cast, F_one]
  norm_num

private theorem G_convolution (d r u : ℕ) :
    G d (r+u) = ∑ h ∈ Finset.range (d+1), G (d-h) (3^h*r) * G h u := by
  apply Nat.cast_injective (R := ℚ)
  simp only [Nat.cast_sum, Nat.cast_mul]
  change (G d (r+u) : ℚ) =
    ∑ h ∈ Finset.range (d+1), (G (d-h) (3^h*r) : ℚ) * (G h u : ℚ)
  simpa only [G_cast] using (convolution d r u)

private def EN (s : ℕ) : Matrix ℕ ℕ ℕ :=
  fun n k => if k ≤ n then G (n-k) (s*3^k) else 0

private theorem CN_lower : Matrix.IsLowerTriangular (fun i j => EN 1 i j) := by
  intro i j hij
  have hlt : i < j := hij
  simp only [EN]
  split_ifs with h
  · omega
  · rfl

private theorem CN_col0 (n : ℕ) : EN 1 n 0 = 1 := by
  simp only [EN, Nat.zero_le, Nat.mul_one, pow_zero, ite_eq_left]
  simpa using (G_one n)

private theorem CN_diag (n : ℕ) : EN 1 n n = 1 := by
  simp [EN, G]

private theorem EN_sum (m s t n k : ℕ) (hn : n ≤ m) (hk : k ≤ n) :
    (∑ i ∈ Finset.range (m+1), EN s n i * EN t i k) =
      G (n-k) ((s+t) * 3^k) := by
  let S : Finset ℕ := Finset.Ico k (n+1)
  have hsub : S ⊆ Finset.range (m+1) := by
    simpa only [S, Finset.range_eq_Ico] using
      (Finset.Ico_subset_Ico (Nat.zero_le k) (Nat.add_le_add_right hn 1))
  have hz : ∀ i ∈ Finset.range (m+1), i ∉ S → EN s n i * EN t i k = 0 := by
    intro i hi hnot
    by_cases hik : k ≤ i
    · have hni : ¬ i ≤ n := by
        intro hle
        apply hnot
        simp only [S, Finset.mem_Ico]
        exact ⟨hik, by omega⟩
      simp [EN, hni]
    · simp [EN, hik]
  rw [← Finset.sum_subset hsub hz]
  rw [Finset.sum_Ico_eq_sum_range]
  have hconv := G_convolution (n-k) (s*3^k) (t*3^k)
  rw [show n + 1 - k = (n-k)+1 by omega]
  have hconv' :
      G (n-k) ((s+t)*3^k) =
        ∑ h ∈ Finset.range ((n-k)+1), G (n-k-h) (3^h*(s*3^k)) * G h (t*3^k) := by
    simpa [Nat.add_mul] using hconv
  rw [hconv']
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < (n-k)+1 := by exact List.mem_range.mp hj
  have hjle : j ≤ n-k := by exact Nat.le_of_lt_succ hjlt
  have hkj : k+j ≤ n := by exact (Nat.le_sub_iff_add_le' hk).mp hjle
  have hkk : k ≤ k+j := by exact Nat.le_add_right k j
  simp only [EN, ite_eq_left hkj, ite_eq_left hkk]
  have hidx1 : n - (k+j) = n-k-j := by exact Nat.sub_add_eq n k j
  have hidx2 : (k+j)-k = j := by exact Nat.add_sub_self_left k j
  rw [hidx1, hidx2]
  have hp : 3 ^ j * (s * 3 ^ k) = s * 3 ^ (k+j) := by
    rw [pow_add]
    ring
  rw [hp]

private theorem CN_mul (m s t : ℕ) : ((EN s).submatrix (fun a : Fin (m+1) => a.val) (fun a : Fin (m+1) => a.val)) * ((EN t).submatrix (fun a : Fin (m+1) => a.val) (fun a : Fin (m+1) => a.val)) = ((EN (s+t)).submatrix (fun a : Fin (m+1) => a.val) (fun a : Fin (m+1) => a.val)) := by
  ext i k
  rw [Matrix.mul_apply]
  change (∑ j : Fin (m+1), EN s i.val j.val * EN t j.val k.val) = EN (s+t) i.val k.val
  have hsum := Fin.sum_univ_eq_sum_range (fun x => EN s i.val x * EN t x k.val) (m+1)
  rw [hsum]
  by_cases hik : k.val ≤ i.val
  · have hE := EN_sum m s t i.val k.val (Fin.is_le i) hik
    rw [hE]
    simp [EN, hik]
  · rw [show EN (s+t) i.val k.val = 0 by simp [EN, hik]]
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hkj : k.val ≤ j
    · have hij : ¬ j ≤ i.val := by omega
      simp only [EN, ite_eq_right hij, zero_mul]
    · simp only [EN, ite_eq_right hkj, mul_zero]

private theorem CN_shift (m : ℕ) (i j : Fin (m+1)) :
    ((((EN 1).submatrix (fun a : Fin (m+1) => a.val) (fun a : Fin (m+1) => a.val)))^3) i j = EN 1 (i.val+1) (j.val+1) := by
  have hc : (((EN 1).submatrix (fun a : Fin (m+1) => a.val) (fun a : Fin (m+1) => a.val)))^3 = ((EN 3).submatrix (fun a : Fin (m+1) => a.val) (fun a : Fin (m+1) => a.val)) := by
    calc
      (((EN 1).submatrix (fun a : Fin (m+1) => a.val) (fun a : Fin (m+1) => a.val)))^3 = (((EN 1).submatrix (fun a : Fin (m+1) => a.val) (fun a : Fin (m+1) => a.val)))^2 * ((EN 1).submatrix (fun a : Fin (m+1) => a.val) (fun a : Fin (m+1) => a.val)) := by rw [pow_succ]
      _ = (((EN 1).submatrix (fun a : Fin (m+1) => a.val) (fun a : Fin (m+1) => a.val)) * ((EN 1).submatrix (fun a : Fin (m+1) => a.val) (fun a : Fin (m+1) => a.val))) * ((EN 1).submatrix (fun a : Fin (m+1) => a.val) (fun a : Fin (m+1) => a.val)) := by rw [pow_two]
      _ = ((EN 3).submatrix (fun a : Fin (m+1) => a.val) (fun a : Fin (m+1) => a.val)) := by rw [CN_mul, CN_mul]
  rw [hc]
  by_cases hij : j.val ≤ i.val
  · have hshift : j.val + 1 ≤ i.val + 1 := by exact Nat.add_le_add_right hij 1
    simp only [Matrix.submatrix_apply, EN, ite_eq_left hij, ite_eq_left hshift]
    have hsub : i.val + 1 - (j.val+1) = i.val-j.val := by exact Nat.add_sub_add_right (↑i) 1 ↑j
    rw [hsub]
    have hp : (3:ℕ) * 3^j.val = 3^(j.val+1) := by exact Eq.symm Nat.pow_succ'
    rw [hp]
    simp
  · have hshift : ¬ j.val+1 ≤ i.val+1 := by omega
    simp only [Matrix.submatrix_apply, EN, ite_eq_right hij, ite_eq_right hshift]

private theorem Mstar_source : IsSourceMatrix (EN 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact CN_lower hij
  · intro n
    exact CN_col0 n
  · intro n
    exact CN_diag n
  · intro m i j
    exact CN_shift m i j

private theorem source_unique (M : Matrix ℕ ℕ ℕ) (hM : IsSourceMatrix M) :
    ∀ n k, M n k = (EN 1) n k := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro k
      by_cases hn0 : n = 0
      · subst n
        by_cases hk : k = 0
        · subst k
          rw [hM.2.1]
          simp [ EN, G]
        · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
          have hz : M 0 k = 0 := hM.1 hkpos
          rw [hz]
          have hnot : ¬ k ≤ 0 := by exact Nat.not_le_of_lt hkpos
          simp [ EN, hnot]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        by_cases hk0 : k = 0
        · subst k
          rw [hM.2.1]
          simpa [ EN] using (G_one n).symm
        · by_cases hnk : n < k
          · have hz : M n k = 0 := hM.1 hnk
            rw [hz]
            simp [ EN, Nat.not_le_of_lt hnk]
          · by_cases hdiag : k = n
            · subst k
              rw [hM.2.2.1]
              simp [ EN, G]
            · have hkupper : k < n := by omega
              let i0 : Fin (n-1+1) := ⟨n-1, by omega⟩
              let j0 : Fin (n-1+1) := ⟨k-1, by omega⟩
              have hblock :
                  M.submatrix (fun a : Fin (n-1+1) => a.val)
                    (fun a : Fin (n-1+1) => a.val) = ((EN 1).submatrix (fun a : Fin ((n-1)+1) => a.val) (fun a : Fin ((n-1)+1) => a.val)) := by
                ext a b
                exact ih a.val (by omega) b.val
              have hs := hM.2.2.2 (n-1) i0 j0
              rw [hblock] at hs
              have hc := CN_shift (n-1) i0 j0
              have hns : n - 1 + 1 = n := by exact Nat.sub_add_cancel hnpos
              have hks : k - 1 + 1 = k := by exact Nat.succ_pred_eq_of_ne_zero hk0
              have hval : M n k = (EN 1) n k := by
                calc
                  M n k = ((((EN 1).submatrix (fun a : Fin ((n-1)+1) => a.val) (fun a : Fin ((n-1)+1) => a.val)))^3) i0 j0 := by
                    simpa [i0, j0, hns, hks] using hs.symm
                  _ = EN 1 n k := by simpa [i0, j0, hns, hks] using hc
                  _ = (EN 1) n k := rfl
              exact hval

private theorem formula_Mstar (n k : ℕ) (hkn : k < n) :
    ((EN 1) n k : ℚ) =
      PowerSeries.coeff (3 ^ n - 3 ^ (n - k)) (partitionSeries (n - k)) := by
  have hkle : k ≤ n := by exact Nat.le_of_succ_le hkn
  have hdnz : n-k ≠ 0 := by exact Nat.sub_ne_zero_iff_lt.mpr hkn
  have hpow : 3 ^ (n-k) * 3^k = 3^n := by exact Nat.pow_sub_mul_pow 3 hkle
  have harg : 3 ^ (n-k) * (3^k - 1) = 3^n - 3^(n-k) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, hpow]
  change (EN 1 n k : ℚ) = _
  simp only [EN, ite_eq_left hkle]
  rw [G_cast]
  simp [F, hdnz, harg]

theorem result : claim := by
  constructor
  · exact ⟨(EN 1), Mstar_source⟩
  · intro M hM n k hn hkn
    have hu := source_unique M hM n k
    rw [hu]
    exact formula_Mstar n k hkn


end D5.S3.Combinatorics.Partitions.HannaA078122TernaryCoefficient
