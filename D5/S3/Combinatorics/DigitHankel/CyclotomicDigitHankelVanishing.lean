/- GID: D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelVanishing
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelVanishing
   mirror-E: none(waiver:cyclotomic-sparse-kernels)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.NonsingularInverse]
   utility: none
   digest: Binary digit block decomposition and cyclotomic sparse-kernel identities. -/

import D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankelDefs
import D5.S3.Combinatorics.DigitHankel.BinaryDigitHankelStructure
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankelVanishing

open CyclotomicDigitHankelDefs
open scoped Matrix

set_option maxHeartbeats 1000000 in
-- Nested range partitions require a larger elaboration budget.
/-- A block kernel and a carry kernel yield a sparse tensor kernel that can be
truncated or padded throughout the interval allowed by its trailing zeros. -/
theorem sparse_kernel_interval (l s z n : ℕ) (t : ℂ) (hs : 0 < s)
    (hz : z < 2 ^ l) (hlo : 2 ^ l * s - z ≤ n) (hhi : n ≤ 2 ^ l * s + z + 1)
    (U V : ℕ → ℂ) (hu : ∀ j, s ≤ j → U j = 0)
    (hv : ∀ j, 2 ^ l - z ≤ j → V j = 0)
    (hu0 : ∃ j < s, U j ≠ 0) (hv0 : ∃ j < 2 ^ l, V j ≠ 0)
    (hvs : (∑ j ∈ Finset.range (2 ^ l), V j) = 0)
    (hvk : ∀ i < 2 ^ l,
      (∑ j ∈ Finset.range (2 ^ l), digitSum (i + j) t * V j) = 0)
    (huk : ∀ i < s, (∑ j ∈ Finset.range s,
      (digitSum (i + j + 1) t - digitSum (i + j) t - 1) * U j) = 0) :
    hankel n t = 0 := by
  classical
  have digit_block (k v u : ℕ) (t : ℂ) (hu : u < 2 ^ k) :
    digitSum (2 ^ k * v + u) t = t ^ k * digitSum v t + digitSum u t := by
    let ev : List ℕ → ℂ := fun xs =>
      ((xs.map (Nat.cast : ℕ → ℂ)).mapIdx fun j e => e * t ^ j).sum
    have ev_append (xs ys : List ℕ) : ev (xs ++ ys) = ev xs + t ^ xs.length * ev ys := by
      dsimp [ev]
      rw [List.map_append, List.mapIdx_append, List.sum_append]
      simp only [List.length_map]
      have hm : ((ys.map (Nat.cast : ℕ → ℂ)).mapIdx
          fun i e => e * t ^ (i + xs.length)) =
          ((ys.map (Nat.cast : ℕ → ℂ)).mapIdx fun i e => e * t ^ i).map
            (fun z => t ^ xs.length * z) := by
        apply List.ext_getElem
        · simp
        · intro i hi hi'
          simp only [List.getElem_map, List.getElem_mapIdx, pow_add]
          ring
      rw [hm]; congr 1
      simpa using List.sum_map_mul_left ((ys.map (Nat.cast : ℕ → ℂ)).mapIdx fun i e => e * t ^ i)
        (fun z => z) (t ^ xs.length)
    have ev_zero (j : ℕ) : ev (List.replicate j 0) = 0 := by
      have hm : (((List.replicate j (0 : ℕ)).map (Nat.cast : ℕ → ℂ)).mapIdx
          fun i e => e * t ^ i) =
          List.replicate j (0 : ℂ) := by
        apply List.ext_getElem <;> simp
      dsimp [ev]; rw [hm]; simp
    by_cases hv : v = 0
    · subst v
      simp [digitSum]
    · have hlength := (Nat.digits_length_le_iff (by omega : 1 < 2) u).2 hu
      have he : (Nat.digits 2 u).length + (k - (Nat.digits 2 u).length) = k := by omega
      have hc := Nat.digits_append_zeroes_append_digits (b := 2)
        (k := k - (Nat.digits 2 u).length) (m := v) (n := u) (by omega) (by omega)
      rw [he] at hc
      rw [show 2 ^ k * v + u = u + 2 ^ k * v by omega]
      unfold digitSum
      rw [← hc]
      change ((List.flatMap (fun e : ℕ => [(e : ℂ)])
          (Nat.digits 2 u ++ List.replicate (k - (Nat.digits 2 u).length) 0 ++
            Nat.digits 2 v)).mapIdx fun j e => e * t ^ j).sum =
        t ^ k * ((List.flatMap (fun e : ℕ => [(e : ℂ)]) (Nat.digits 2 v)).mapIdx
          fun j e => e * t ^ j).sum +
        ((List.flatMap (fun e : ℕ => [(e : ℂ)]) (Nat.digits 2 u)).mapIdx
          fun j e => e * t ^ j).sum
      rw [← List.map_eq_flatMap, ← List.map_eq_flatMap, ← List.map_eq_flatMap]
      change ev ((Nat.digits 2 u ++ List.replicate (k - (Nat.digits 2 u).length) 0) ++
        Nat.digits 2 v) = t ^ k * ev (Nat.digits 2 v) + ev (Nat.digits 2 u)
      rw [ev_append, ev_append, ev_zero]
      simp only [List.length_append, List.length_replicate, he]
      ring
  let P := 2 ^ l
  have hp : 0 < P := by dsimp [P]; positivity
  have hz' : z < P := hz
  change P * s - z ≤ n at hlo
  change n ≤ P * s + z + 1 at hhi
  let W : ℕ → ℂ := fun j => U (j / P) * V (j % P)
  have Wentry (q j : ℕ) (hj : j < P) : W (q * P + j) = U q * V j := by
    have hd : (q * P + j) / P = q := by
      rw [Nat.mul_comm q P, Nat.mul_add_div hp, Nat.div_eq_of_lt hj, Nat.add_zero]
    simp [W, hd, Nat.add_mod, Nat.mod_eq_of_lt hj]
  have Wtail (j : ℕ) (hj : P * s - z ≤ j) : W j = 0 := by
    by_cases hq : s ≤ j / P
    · simp [W, hu _ hq]
    · have hj' : P * s - z ≤ P * (j / P) + j % P := by
        simpa [Nat.div_add_mod] using hj
      have hr : P - z ≤ j % P := by
        have hb : j / P + 1 ≤ s := by omega
        have hmul : P * (j / P + 1) ≤ P * s := Nat.mul_le_mul_left _ hb
        have hm : j % P < P := Nat.mod_lt _ hp
        rw [Nat.mul_add, Nat.mul_one] at hmul
        omega
      simp [W, hv _ hr]
  have partition (f : ℕ → ℂ) :
      (∑ j ∈ Finset.range (P * s), f j * W j) =
        ∑ q ∈ Finset.range s, ∑ j ∈ Finset.range P, f (q * P + j) * (U q * V j) := by
    have block (b : ℕ) : (∑ j ∈ Finset.range (b * P), f j * W j) =
        ∑ q ∈ Finset.range b, ∑ j ∈ Finset.range P, f (q * P + j) * W (q * P + j) := by
      induction b with
      | zero => simp
      | succ b ih =>
          rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    rw [Nat.mul_comm P s, block]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro j hj
    rw [Wentry _ _ (Finset.mem_range.mp hj)]
  have dot_split (q r : ℕ) (hr : r < P) :
      (∑ j ∈ Finset.range P, digitSum (P * q + r + j) t * V j) =
        (∑ j ∈ Finset.range P, digitSum (r + j) t * V j) +
          t ^ l * digitSum q t * (∑ j ∈ Finset.range P, V j) +
          t ^ l * (digitSum (q + 1) t - digitSum q t - 1) *
            (∑ j ∈ Finset.range P, if P ≤ r + j then V j else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < P := Finset.mem_range.mp hj
    by_cases hc : P ≤ r + j
    · have hrem : r + j - P < P := by omega
      have heq : P * q + r + j = P * (q + 1) + (r + j - P) := by
        rw [Nat.mul_add, Nat.mul_one]; omega
      have heq' : r + j = P * 1 + (r + j - P) := by omega
      have hbig := digit_block l (q + 1) (r + j - P) t hrem
      have hsmall := digit_block l 1 (r + j - P) t hrem
      change digitSum (P * (q + 1) + (r + j - P)) t = _ at hbig
      change digitSum (P * 1 + (r + j - P)) t = _ at hsmall
      rw [← heq] at hbig
      rw [← heq'] at hsmall
      have hone : digitSum 1 t = 1 := by
        simp [digitSum]
      rw [hbig, hsmall, hone, if_pos hc]
      ring
    · have hrem : r + j < P := by omega
      rw [show P * q + r + j = P * q + (r + j) by omega,
        digit_block l q (r + j) t hrem, if_neg hc]
      ring
  have Wkernel (i : ℕ) (hi : i < n) :
      (∑ j ∈ Finset.range (P * s), digitSum (i + j) t * W j) = 0 := by
    rw [partition]
    let q := i / P
    let r := i % P
    have hr : r < P := Nat.mod_lt _ hp
    have hiqr : i = P * q + r := by
      dsimp [q, r]; exact (Nat.div_add_mod i P).symm
    have hq : q ≤ s := by
      have hi' : i < P * (s + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
      have := (Nat.div_lt_iff_lt_mul hp).mpr
        (show i < (s + 1) * P by simpa [Nat.mul_comm] using hi')
      dsimp [q]; omega
    have terms (a : ℕ) :
        (∑ j ∈ Finset.range P, digitSum (i + (a * P + j)) t * (U a * V j)) =
          U a * (t ^ l * (digitSum (q + a + 1) t - digitSum (q + a) t - 1) *
            (∑ j ∈ Finset.range P, if P ≤ r + j then V j else 0)) := by
      have idx (j : ℕ) : i + (a * P + j) = P * (q + a) + r + j := by
        rw [hiqr]; ring
      simp_rw [idx, show ∀ j, digitSum (P * (q + a) + r + j) t * (U a * V j) =
        U a * (digitSum (P * (q + a) + r + j) t * V j) by intro j; ring]
      rw [← Finset.mul_sum, dot_split _ _ hr, hvs, hvk _ hr]
      ring
    simp_rw [terms]
    by_cases hqs : q < s
    · have e := huk q hqs
      have rearrange (a : ℕ) :
          U a * (t ^ l * (digitSum (q + a + 1) t - digitSum (q + a) t - 1) *
            (∑ j ∈ Finset.range P, if P ≤ r + j then V j else 0)) =
          t ^ l * (∑ j ∈ Finset.range P, if P ≤ r + j then V j else 0) *
            ((digitSum (q + a + 1) t - digitSum (q + a) t - 1) * U a) := by ring
      simp_rw [rearrange]
      rw [← Finset.mul_sum, e, mul_zero]
    · have hqe : q = s := by omega
      have hrz : r ≤ z := by rw [hiqr, hqe] at hi; omega
      have hc : (∑ j ∈ Finset.range P, if P ≤ r + j then V j else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        split_ifs with h
        · exact hv _ (by omega)
        · rfl
      simp [hc]
  let x : Fin n → ℂ := fun j => W j.val
  have hx : (Matrix.of fun i j : Fin n => digitSum (i + j) t) *ᵥ x = 0 := by
    ext i
    change (∑ j : Fin n, digitSum (i.val + j.val) t * W j.val) = 0
    rw [Fin.sum_univ_eq_sum_range (fun j => digitSum (i.val + j) t * W j) n]
    have he : (∑ j ∈ Finset.range n, digitSum (i.val + j) t * W j) =
        ∑ j ∈ Finset.range (P * s), digitSum (i.val + j) t * W j := by
      by_cases hnP : n ≤ P * s
      · apply Finset.sum_subset (Finset.range_mono hnP)
        intro j hj hjn
        rw [Wtail j (by have := Finset.mem_range.not.mp hjn; omega), mul_zero]
      · symm
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro j hj hjP
        rw [Wtail j (by have := Finset.mem_range.not.mp hjP; omega), mul_zero]
    rw [he]
    exact Wkernel i.val i.isLt
  obtain ⟨a, ha, hUa⟩ := hu0
  obtain ⟨b, hb, hVb⟩ := hv0
  have hb' : b < P - z := by
    by_contra h
    exact hVb (hv b (by omega))
  have hab : a * P + b < n := by
    have hmul := Nat.mul_le_mul_right P (show a + 1 ≤ s by omega)
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm s P] at hmul
    have hps : P ≤ P * s := by
      simpa using Nat.mul_le_mul_left P hs
    omega
  by_contra h
  have he := Matrix.eq_zero_of_mulVec_eq_zero h hx
  have he0 := congrFun he (⟨a * P + b, hab⟩ : Fin n)
  change W (a * P + b) = 0 at he0
  rw [Wentry a b hb] at he0
  exact (mul_ne_zero hUa hVb) he0

/-- In odd dimension the carry matrix is bipartite. Conjugating by the parity
signs reverses its sign, forcing singularity and a nonzero kernel vector. -/
theorem odd_carry_kernel {R : Type*} [Field R] [CharZero R] (f : ℕ → R)
    (hf : ∀ a, f (2 * a + 1) - f (2 * a) = 1) (s : ℕ) (hs : Odd s) :
    ∃ U : Fin s → R, U ≠ 0 ∧ ∀ i : Fin s,
      (∑ j : Fin s, (f (i.val + j.val + 1) - f (i.val + j.val) - 1) * U j) = 0 := by
  classical
  let A : Matrix (Fin s) (Fin s) R := Matrix.of fun i j =>
    f (i.val + j.val + 1) - f (i.val + j.val) - 1
  let sign : Fin s → R := fun i => if i.val % 2 = 0 then 1 else -1
  let D : Matrix (Fin s) (Fin s) R := Matrix.diagonal sign
  have hsign (i : Fin s) : sign i * sign i = 1 := by
    dsimp [sign]; split_ifs <;> ring
  have hDD : D * D = 1 := by
    rw [show D = Matrix.diagonal sign from rfl, Matrix.diagonal_mul_diagonal']
    ext i j
    simp [hsign, Matrix.one_apply]
  have hconj : D * A * D = -A := by
    ext i j
    simp only [D, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.neg_apply]
    by_cases hi : i.val % 2 = 0 <;> by_cases hj : j.val % 2 = 0
    · have he : i.val + j.val = 2 * ((i.val + j.val) / 2) := by omega
      have h := hf ((i.val + j.val) / 2)
      rw [← he] at h
      have ha : A i j = 0 := by dsimp [A]; rw [h]; ring
      simp [ha]
    · simp [sign, hi, hj]
    · simp [sign, hi, hj]
    · have he : i.val + j.val = 2 * ((i.val + j.val) / 2) := by omega
      have h := hf ((i.val + j.val) / 2)
      rw [← he] at h
      have ha : A i j = 0 := by dsimp [A]; rw [h]; ring
      simp [ha]
  have hd : D.det * D.det = 1 := by
    rw [← Matrix.det_mul, hDD, Matrix.det_one]
  have hdet : A.det = 0 := by
    have h := congrArg Matrix.det hconj
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_neg, Fintype.card_fin,
      hs.neg_one_pow] at h
    have h' : A.det = -A.det := by
      calc
        A.det = D.det * A.det * D.det := by rw [mul_right_comm, hd, one_mul]
        _ = -A.det := by simpa using h
    have hz : (2 : R) * A.det = 0 := by
      calc
        (2 : R) * A.det = A.det + A.det := by ring
        _ = -A.det + A.det := congrArg (fun x : R => x + A.det) h'
        _ = 0 := neg_add_cancel _
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  have hnot : ¬Function.Injective A.mulVec := by
    intro h
    have hu := Matrix.mulVec_injective_iff_isUnit.mp h
    have hd' := (Matrix.isUnit_iff_isUnit_det A).mp hu
    rw [hdet] at hd'
    exact not_isUnit_zero hd'
  obtain ⟨v, w, hvw, hne⟩ := Function.not_injective_iff.mp hnot
  refine ⟨v - w, sub_ne_zero.mpr hne, ?_⟩
  have hzero : A *ᵥ (v - w) = 0 := by rw [Matrix.mulVec_sub, hvw, sub_self]
  intro i
  exact congrFun hzero i

set_option maxHeartbeats 1000000 in
-- Nested range partitions require a larger elaboration budget.
/-- The first cyclotomic kernels alternate two adjacent columns in each binary
block. Their length is unbounded and their last block has exactly two nonzero entries. -/
theorem root_base_kernel (d k : ℕ) (hd : 0 < d) (hk : 0 < k)
    (ζ : ℂ) (hζ : ζ ^ d = 1) :
    ∃ V : ℕ → ℂ, V 0 = 1 ∧
      (∀ j, 2 ^ (d + k) - (2 ^ k - 2) ≤ j → V j = 0) ∧
      (∑ j ∈ Finset.range (2 ^ (d + k)), V j) = 0 ∧
      (∀ i < 2 ^ (d + k),
        (∑ j ∈ Finset.range (2 ^ (d + k)), digitSum (i + j) (2 * ζ) * V j) = 0) ∧
      (∀ i ≤ 2 ^ d, (∑ j ∈ Finset.range (2 ^ (d - 1)),
        (digitSum (i + 2 * j + 1) (2 * ζ) - digitSum (i + 2 * j) (2 * ζ) - 1)) = 0) := by
  classical
  have digit_block (k v u : ℕ) (t : ℂ) (hu : u < 2 ^ k) :
    digitSum (2 ^ k * v + u) t = t ^ k * digitSum v t + digitSum u t := by
    let ev : List ℕ → ℂ := fun xs =>
      ((xs.map (Nat.cast : ℕ → ℂ)).mapIdx fun j e => e * t ^ j).sum
    have ev_append (xs ys : List ℕ) : ev (xs ++ ys) = ev xs + t ^ xs.length * ev ys := by
      dsimp [ev]
      rw [List.map_append, List.mapIdx_append, List.sum_append]
      simp only [List.length_map]
      have hm : ((ys.map (Nat.cast : ℕ → ℂ)).mapIdx
          fun i e => e * t ^ (i + xs.length)) =
          ((ys.map (Nat.cast : ℕ → ℂ)).mapIdx fun i e => e * t ^ i).map
            (fun z => t ^ xs.length * z) := by
        apply List.ext_getElem
        · simp
        · intro i hi hi'
          simp only [List.getElem_map, List.getElem_mapIdx, pow_add]
          ring
      rw [hm]; congr 1
      simpa using List.sum_map_mul_left ((ys.map (Nat.cast : ℕ → ℂ)).mapIdx fun i e => e * t ^ i)
        (fun z => z) (t ^ xs.length)
    have ev_zero (j : ℕ) : ev (List.replicate j 0) = 0 := by
      have hm : (((List.replicate j (0 : ℕ)).map (Nat.cast : ℕ → ℂ)).mapIdx
          fun i e => e * t ^ i) =
          List.replicate j (0 : ℂ) := by
        apply List.ext_getElem <;> simp
      dsimp [ev]; rw [hm]; simp
    by_cases hv : v = 0
    · subst v
      simp [digitSum]
    · have hlength := (Nat.digits_length_le_iff (by omega : 1 < 2) u).2 hu
      have he : (Nat.digits 2 u).length + (k - (Nat.digits 2 u).length) = k := by omega
      have hc := Nat.digits_append_zeroes_append_digits (b := 2)
        (k := k - (Nat.digits 2 u).length) (m := v) (n := u) (by omega) (by omega)
      rw [he] at hc
      rw [show 2 ^ k * v + u = u + 2 ^ k * v by omega]
      unfold digitSum
      rw [← hc]
      change ((List.flatMap (fun e : ℕ => [(e : ℂ)])
          (Nat.digits 2 u ++ List.replicate (k - (Nat.digits 2 u).length) 0 ++
            Nat.digits 2 v)).mapIdx fun j e => e * t ^ j).sum =
        t ^ k * ((List.flatMap (fun e : ℕ => [(e : ℂ)]) (Nat.digits 2 v)).mapIdx
          fun j e => e * t ^ j).sum +
        ((List.flatMap (fun e : ℕ => [(e : ℂ)]) (Nat.digits 2 u)).mapIdx
          fun j e => e * t ^ j).sum
      rw [← List.map_eq_flatMap, ← List.map_eq_flatMap, ← List.map_eq_flatMap]
      change ev ((Nat.digits 2 u ++ List.replicate (k - (Nat.digits 2 u).length) 0) ++
        Nat.digits 2 v) = t ^ k * ev (Nat.digits 2 v) + ev (Nat.digits 2 u)
      rw [ev_append, ev_append, ev_zero]
      simp only [List.length_append, List.length_replicate, he]
      ring
  let t := 2 * ζ
  let P := 2 ^ d
  let Q := 2 ^ k
  let M := 2 ^ (d - 1)
  have hp : 0 < P := by dsimp [P]; positivity
  have hq : 2 ≤ Q := by
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hk
  have hqpos : 0 < Q := by omega
  have hP : P = 2 * M := by
    dsimp [P, M]
    calc
      2 ^ d = 2 ^ ((d - 1) + 1) := by congr 1; omega
      _ = 2 * 2 ^ (d - 1) := by rw [pow_succ]; ring
  have hN : 2 ^ (d + k) = P * Q := pow_add 2 d k
  have htpow : t ^ d = (P : ℂ) := by
    dsimp [t, P]
    rw [mul_pow, hζ, mul_one]
    norm_cast
  have even_step (a : ℕ) : digitSum (2 * a) t = t * digitSum a t := by
    have h := digit_block 1 a 0 t (by decide)
    simpa [digitSum] using h
  have odd_step (a : ℕ) : digitSum (2 * a + 1) t = t * digitSum a t + 1 := by
    have h := digit_block 1 a 1 t (by decide)
    simpa [digitSum] using h
  have row_sum (i : ℕ) (hi : i ≤ P) :
      (∑ j ∈ Finset.range M,
        (digitSum (i + 2 * j + 1) t - digitSum (i + 2 * j) t - 1)) = 0 := by
    by_cases he : i % 2 = 0
    · apply Finset.sum_eq_zero
      intro j hj
      have hidx : i + 2 * j = 2 * (i / 2 + j) := by omega
      rw [hidx, odd_step, even_step]
      ring
    · have hidx : ∀ j, i + 2 * j = 2 * (i / 2 + j) + 1 := by intro j; omega
      have hterm (j : ℕ) :
          digitSum (i + 2 * j + 1) t - digitSum (i + 2 * j) t - 1 =
            t * (digitSum (i / 2 + (j + 1)) t - digitSum (i / 2 + j) t) - 2 := by
        rw [hidx j, show 2 * (i / 2 + j) + 1 + 1 = 2 * (i / 2 + (j + 1)) by omega,
          even_step, odd_step]
        ring
      simp_rw [hterm]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_range_sub (fun j => digitSum (i / 2 + j) t)]
      have ha : i / 2 < M := by rw [hP] at hi; omega
      have hb := digit_block (d - 1) 1 (i / 2) t ha
      change digitSum (M * 1 + i / 2) t = _ at hb
      have hone : digitSum 1 t = 1 := by simp [digitSum]
      rw [Nat.mul_one, Nat.add_comm M] at hb
      rw [hb, hone]
      simp only [add_zero, mul_one, add_sub_cancel_right, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      have htt : t * t ^ (d - 1) = (P : ℂ) := by
        rw [← pow_succ', show d - 1 + 1 = d by omega, htpow]
      rw [htt]
      have hc : (P : ℂ) = 2 * (M : ℂ) := by exact_mod_cast hP
      rw [hc]
      ring
  let sign : ℕ → ℂ := fun a => if a % 2 = 0 then 1 else -1
  have sign_sum (f : ℕ → ℂ) :
      (∑ a ∈ Finset.range P, sign a * f a) =
        ∑ a ∈ Finset.range M, (f (2 * a) - f (2 * a + 1)) := by
    have pairs (b : ℕ) : (∑ a ∈ Finset.range (2 * b), sign a * f a) =
        ∑ a ∈ Finset.range b, (f (2 * a) - f (2 * a + 1)) := by
      induction b with
      | zero => simp
      | succ b ih =>
          rw [show 2 * (b + 1) = 2 * b + 2 by omega, Finset.sum_range_add, ih,
            Finset.sum_range_succ]
          simp [Finset.sum_range_succ, sign, Nat.add_mod]
          ring
    rw [hP, pairs]
  have hsignsum : (∑ a ∈ Finset.range P, sign a) = 0 := by
    have h := sign_sum (fun _ => 1)
    simpa using h
  have carry_sum (i : ℕ) (hi : i < P) :
      (∑ a ∈ Finset.range P, sign a *
        (digitSum (i + a + 1) t - digitSum (i + a) t - 1)) = 0 := by
    rw [sign_sum, Finset.sum_sub_distrib]
    have h1 := row_sum i (by omega)
    have h2 := row_sum (i + 1) (by omega)
    have eqidx (a : ℕ) : i + 1 + 2 * a = i + (2 * a + 1) := by omega
    simp_rw [eqidx] at h2
    rw [h1, h2, sub_self]
  let V : ℕ → ℂ := fun j => if j < P * Q then sign (j / Q) *
    (if j % Q = 0 then 1 else if j % Q = 1 then -1 else 0) else 0
  have Ventry (a b : ℕ) (ha : a < P) (hb : b < Q) : V (a * Q + b) =
      sign a * (if b = 0 then 1 else if b = 1 then -1 else 0) := by
    have hdiv : (a * Q + b) / Q = a := by
      rw [Nat.mul_comm a Q, Nat.mul_add_div hqpos, Nat.div_eq_of_lt hb, Nat.add_zero]
    have hm := Nat.mul_le_mul_right Q (show a + 1 ≤ P by omega)
    rw [Nat.add_mul, Nat.one_mul] at hm
    simp [V, show a * Q + b < P * Q by omega, hdiv, Nat.add_mod,
      Nat.mod_eq_of_lt hb]
  have Vsum (f : ℕ → ℂ) :
      (∑ j ∈ Finset.range (P * Q), f j * V j) =
        ∑ a ∈ Finset.range P, sign a * (f (a * Q) - f (a * Q + 1)) := by
    have blocks (b : ℕ) : (∑ j ∈ Finset.range (b * Q), f j * V j) =
        ∑ a ∈ Finset.range b, ∑ j ∈ Finset.range Q, f (a * Q + j) * V (a * Q + j) := by
      induction b with
      | zero => simp
      | succ b ih =>
          rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    rw [blocks]
    apply Finset.sum_congr rfl
    intro a ha
    have hterms : (∑ j ∈ Finset.range Q, f (a * Q + j) * V (a * Q + j)) =
        ∑ j ∈ Finset.range Q, f (a * Q + j) *
          (sign a * (if j = 0 then 1 else if j = 1 then -1 else 0)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Ventry a j (Finset.mem_range.mp ha) (Finset.mem_range.mp hj)]
    rw [hterms]
    have hQ : Q = 2 + (Q - 2) := by omega
    rw [show Finset.range Q = Finset.range (2 + (Q - 2)) by rw [← hQ],
      Finset.sum_range_add]
    have hzsum : (∑ j ∈ Finset.range (Q - 2), f (a * Q + (2 + j)) *
        (sign a * (if 2 + j = 0 then 1 else if 2 + j = 1 then -1 else 0))) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp [show 2 + j ≠ 1 by omega]
    rw [hzsum]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.add_zero]
    simp
    ring
  refine ⟨V, ?_, ?_, ?_, ?_, ?_⟩
  · simp [V, sign, hp, hqpos]
  · intro j hj
    rw [hN] at hj
    have htail : P * Q - (Q - 2) ≤ j := hj
    by_cases hdiv : j / Q < P
    · have he : j = Q * (j / Q) + j % Q := (Nat.div_add_mod j Q).symm
      have hm : j % Q < Q := Nat.mod_lt _ hqpos
      have hmul := Nat.mul_le_mul_left Q (show j / Q + 1 ≤ P by omega)
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm Q P] at hmul
      have hr : 2 ≤ j % Q := by omega
      simp [V, show j % Q ≠ 0 by omega, show j % Q ≠ 1 by omega]
    · have hbig : P ≤ j / Q := by omega
      have hjbig : P * Q ≤ j := (Nat.le_div_iff_mul_le hqpos).mp hbig
      simp [V, show ¬j < P * Q by omega]
  · rw [hN]
    have h := Vsum (fun _ => 1)
    simpa only [one_mul, sub_self, mul_zero, Finset.sum_const_zero] using h
  · intro i hi
    rw [hN] at hi ⊢
    rw [Vsum]
    change (∑ a ∈ Finset.range P, sign a *
      (digitSum (i + a * Q) t - digitSum (i + (a * Q + 1)) t)) = 0
    simp only [← Nat.add_assoc]
    let q := i / Q
    let r := i % Q
    have hr : r < Q := Nat.mod_lt _ hqpos
    have hiqr : i = Q * q + r := (Nat.div_add_mod i Q).symm
    have hqP : q < P := (Nat.div_lt_iff_lt_mul hqpos).mpr hi
    by_cases hboundary : r + 1 = Q
    · have hdiff (a : ℕ) : digitSum (i + a * Q) t - digitSum (i + a * Q + 1) t =
          digitSum r t - t ^ k * (digitSum (q + a + 1) t - digitSum (q + a) t) := by
        have hidx : i + a * Q = Q * (q + a) + r := by rw [hiqr]; ring
        rw [hidx, digit_block k (q + a) r t hr]
        have hidx' : Q * (q + a) + r + 1 = Q * (q + a + 1) + 0 := by
          simp only [Nat.mul_add, Nat.mul_one, Nat.add_zero]; omega
        rw [hidx', digit_block k (q + a + 1) 0 t hqpos]
        try simp [digitSum]
        ring
      simp_rw [hdiff]
      have hc := carry_sum q hqP
      have hcarry : (∑ a ∈ Finset.range P,
          sign a * (digitSum (q + a + 1) t - digitSum (q + a) t)) = 0 := by
        have hrew (a : ℕ) : sign a *
            (digitSum (q + a + 1) t - digitSum (q + a) t - 1) =
              sign a * (digitSum (q + a + 1) t - digitSum (q + a) t) - sign a := by ring
        simp_rw [hrew, Finset.sum_sub_distrib, hsignsum, sub_zero] at hc
        exact hc
      have rearrange (a : ℕ) : sign a *
          (digitSum r t - t ^ k * (digitSum (q + a + 1) t - digitSum (q + a) t)) =
            sign a * digitSum r t -
              t ^ k * (sign a * (digitSum (q + a + 1) t - digitSum (q + a) t)) := by ring
      simp_rw [rearrange]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsignsum, zero_mul,
        ← Finset.mul_sum, hcarry, mul_zero, sub_zero]
    · have hr1 : r + 1 < Q := by omega
      have hdiff (a : ℕ) : digitSum (i + a * Q) t - digitSum (i + a * Q + 1) t =
          digitSum r t - digitSum (r + 1) t := by
        have hidx : i + a * Q = Q * (q + a) + r := by rw [hiqr]; ring
        rw [hidx, digit_block k (q + a) r t hr,
          show Q * (q + a) + r + 1 = Q * (q + a) + (r + 1) by omega,
          digit_block k (q + a) (r + 1) t hr1]
        ring
      simp_rw [hdiff]
      rw [← Finset.sum_mul, hsignsum, zero_mul]
  · exact row_sum

set_option maxHeartbeats 1000000 in
-- Nested range partitions require a larger elaboration budget.
/-- At twice the root order a cancellation of two tensor constructions removes
one more terminal column, giving the improved initial kernel. -/
theorem root_second_kernel (d : ℕ) (hd : 0 < d) (ζ : ℂ) (hζ : ζ ^ d = 1) :
    ∃ V : ℕ → ℂ, V 0 = 1 ∧
      (∀ j, 2 ^ (2 * d) - (2 ^ d - 1) ≤ j → V j = 0) ∧
      (∑ j ∈ Finset.range (2 ^ (2 * d)), V j) = 0 ∧
      (∀ i < 2 ^ (2 * d),
        (∑ j ∈ Finset.range (2 ^ (2 * d)), digitSum (i + j) (2 * ζ) * V j) = 0) := by
  classical
  have digit_block (k v u : ℕ) (t : ℂ) (hu : u < 2 ^ k) :
    digitSum (2 ^ k * v + u) t = t ^ k * digitSum v t + digitSum u t := by
    let ev : List ℕ → ℂ := fun xs =>
      ((xs.map (Nat.cast : ℕ → ℂ)).mapIdx fun j e => e * t ^ j).sum
    have ev_append (xs ys : List ℕ) : ev (xs ++ ys) = ev xs + t ^ xs.length * ev ys := by
      dsimp [ev]
      rw [List.map_append, List.mapIdx_append, List.sum_append]
      simp only [List.length_map]
      have hm : ((ys.map (Nat.cast : ℕ → ℂ)).mapIdx
          fun i e => e * t ^ (i + xs.length)) =
          ((ys.map (Nat.cast : ℕ → ℂ)).mapIdx fun i e => e * t ^ i).map
            (fun z => t ^ xs.length * z) := by
        apply List.ext_getElem
        · simp
        · intro i hi hi'
          simp only [List.getElem_map, List.getElem_mapIdx, pow_add]
          ring
      rw [hm]; congr 1
      simpa using List.sum_map_mul_left ((ys.map (Nat.cast : ℕ → ℂ)).mapIdx fun i e => e * t ^ i)
        (fun z => z) (t ^ xs.length)
    have ev_zero (j : ℕ) : ev (List.replicate j 0) = 0 := by
      have hm : (((List.replicate j (0 : ℕ)).map (Nat.cast : ℕ → ℂ)).mapIdx
          fun i e => e * t ^ i) =
          List.replicate j (0 : ℂ) := by
        apply List.ext_getElem <;> simp
      dsimp [ev]; rw [hm]; simp
    by_cases hv : v = 0
    · subst v
      simp [digitSum]
    · have hlength := (Nat.digits_length_le_iff (by omega : 1 < 2) u).2 hu
      have he : (Nat.digits 2 u).length + (k - (Nat.digits 2 u).length) = k := by omega
      have hc := Nat.digits_append_zeroes_append_digits (b := 2)
        (k := k - (Nat.digits 2 u).length) (m := v) (n := u) (by omega) (by omega)
      rw [he] at hc
      rw [show 2 ^ k * v + u = u + 2 ^ k * v by omega]
      unfold digitSum
      rw [← hc]
      change ((List.flatMap (fun e : ℕ => [(e : ℂ)])
          (Nat.digits 2 u ++ List.replicate (k - (Nat.digits 2 u).length) 0 ++
            Nat.digits 2 v)).mapIdx fun j e => e * t ^ j).sum =
        t ^ k * ((List.flatMap (fun e : ℕ => [(e : ℂ)]) (Nat.digits 2 v)).mapIdx
          fun j e => e * t ^ j).sum +
        ((List.flatMap (fun e : ℕ => [(e : ℂ)]) (Nat.digits 2 u)).mapIdx
          fun j e => e * t ^ j).sum
      rw [← List.map_eq_flatMap, ← List.map_eq_flatMap, ← List.map_eq_flatMap]
      change ev ((Nat.digits 2 u ++ List.replicate (k - (Nat.digits 2 u).length) 0) ++
        Nat.digits 2 v) = t ^ k * ev (Nat.digits 2 v) + ev (Nat.digits 2 u)
      rw [ev_append, ev_append, ev_zero]
      simp only [List.length_append, List.length_replicate, he]
      ring
  let t := 2 * ζ
  let P := 2 ^ d
  let M := 2 ^ (d - 1)
  have hp : 0 < P := by dsimp [P]; positivity
  have hp2 : P ≤ P * P := by simpa using Nat.mul_le_mul_left P hp
  have hP : P = 2 * M := by
    dsimp [P, M]
    calc
      2 ^ d = 2 ^ ((d - 1) + 1) := by congr 1; omega
      _ = 2 * 2 ^ (d - 1) := by rw [pow_succ]; ring
  have hN : 2 ^ (2 * d) = P * P := by
    rw [show 2 * d = d + d by omega, pow_add]
  have htpow : t ^ d = (P : ℂ) := by
    dsimp [t, P]; rw [mul_pow, hζ, mul_one]; norm_cast
  obtain ⟨_, _, _, _, _, row_sum⟩ := root_base_kernel d 1 hd (by decide) ζ hζ
  change ∀ i ≤ P, (∑ j ∈ Finset.range M,
    (digitSum (i + 2 * j + 1) t - digitSum (i + 2 * j) t - 1)) = 0 at row_sum
  let sign : ℕ → ℂ := fun a => if a % 2 = 0 then 1 else -1
  let E : ℕ → ℂ := fun a => if a % 2 = 0 then 1 else 0
  have pairs (f : ℕ → ℂ) : (∑ a ∈ Finset.range P, f a) =
      ∑ a ∈ Finset.range M, (f (2 * a) + f (2 * a + 1)) := by
    have aux (b : ℕ) : (∑ a ∈ Finset.range (2 * b), f a) =
        ∑ a ∈ Finset.range b, (f (2 * a) + f (2 * a + 1)) := by
      induction b with
      | zero => simp
      | succ b ih =>
          rw [show 2 * (b + 1) = 2 * b + 2 by omega, Finset.sum_range_add, ih,
            Finset.sum_range_succ]
          simp [Finset.sum_range_succ]
    rw [hP, aux]
  have sign_sum (f : ℕ → ℂ) :
      (∑ a ∈ Finset.range P, sign a * f a) =
        ∑ a ∈ Finset.range M, (f (2 * a) - f (2 * a + 1)) := by
    rw [pairs]
    apply Finset.sum_congr rfl
    intro a ha
    simp [sign, Nat.add_mod, sub_eq_add_neg]
  have E_sum (f : ℕ → ℂ) : (∑ a ∈ Finset.range P, E a * f a) =
      ∑ a ∈ Finset.range M, f (2 * a) := by
    rw [pairs]
    apply Finset.sum_congr rfl
    intro a ha
    simp [E, Nat.add_mod]
  have hsign : (∑ a ∈ Finset.range P, sign a) = 0 := by
    have h := sign_sum (fun _ => 1); simpa using h
  have hE : (∑ a ∈ Finset.range P, E a) = (M : ℂ) := by
    have h := E_sum (fun _ => 1); simpa using h
  have Ecarry (i : ℕ) (hi : i < P) : (∑ a ∈ Finset.range P, E a *
      (digitSum (i + a + 1) t - digitSum (i + a) t - 1)) = 0 := by
    rw [E_sum]; exact row_sum i (by omega)
  have sign_digit (i : ℕ) (hi : i < P) :
      (∑ a ∈ Finset.range P, sign a * digitSum (i + a) t) = -(M : ℂ) := by
    rw [sign_sum]
    have hr := row_sum i (by omega)
    have ht (a : ℕ) : digitSum (i + 2 * a) t - digitSum (i + (2 * a + 1)) t =
        -(digitSum (i + 2 * a + 1) t - digitSum (i + 2 * a) t - 1) - 1 := by
      rw [Nat.add_assoc]; ring
    simp_rw [ht, Finset.sum_sub_distrib, Finset.sum_neg_distrib, hr]
    simp
  have dot_sign (q r : ℕ) (hr : r < P) :
      (∑ b ∈ Finset.range P, digitSum (P * q + r + b) t * sign b) =
        -(M : ℂ) + t ^ d *
          (digitSum (q + 1) t - digitSum q t - 1) *
            (∑ b ∈ Finset.range P, if P ≤ r + b then sign b else 0) := by
    have split : (∑ b ∈ Finset.range P, digitSum (P * q + r + b) t * sign b) =
        (∑ b ∈ Finset.range P, digitSum (r + b) t * sign b) +
          t ^ d * digitSum q t * (∑ b ∈ Finset.range P, sign b) +
          t ^ d * (digitSum (q + 1) t - digitSum q t - 1) *
            (∑ b ∈ Finset.range P, if P ≤ r + b then sign b else 0) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b hb
      have hb' : b < P := Finset.mem_range.mp hb
      by_cases hc : P ≤ r + b
      · have hrem : r + b - P < P := by omega
        have heq : P * q + r + b = P * (q + 1) + (r + b - P) := by
          rw [Nat.mul_add, Nat.mul_one]; omega
        have heq' : r + b = P * 1 + (r + b - P) := by omega
        have hbig := digit_block d (q + 1) (r + b - P) t hrem
        have hsmall := digit_block d 1 (r + b - P) t hrem
        change digitSum (P * (q + 1) + (r + b - P)) t = _ at hbig
        change digitSum (P * 1 + (r + b - P)) t = _ at hsmall
        rw [← heq] at hbig
        rw [← heq'] at hsmall
        have hone : digitSum 1 t = 1 := by simp [digitSum]
        rw [hbig, hsmall, hone, if_pos hc]; ring
      · have hrem : r + b < P := by omega
        rw [show P * q + r + b = P * q + (r + b) by omega,
          digit_block d q (r + b) t hrem, if_neg hc]; ring
    rw [split, hsign]
    have hlow : (∑ b ∈ Finset.range P, digitSum (r + b) t * sign b) = -(M : ℂ) := by
      simpa [mul_comm] using sign_digit r hr
    rw [hlow]; ring
  let V : ℕ → ℂ := fun j => if j < P * P then
    2 * E (j / P) * sign (j % P) - sign (j / P) * (if j % P = 0 then 1 else 0)
    else 0
  have Ventry (a b : ℕ) (ha : a < P) (hb : b < P) :
      V (a * P + b) = 2 * E a * sign b - sign a * (if b = 0 then 1 else 0) := by
    have hm := Nat.mul_le_mul_right P (show a + 1 ≤ P by omega)
    rw [Nat.add_mul, Nat.one_mul] at hm
    have hdiv : (a * P + b) / P = a := by
      rw [Nat.mul_comm a P, Nat.mul_add_div hp, Nat.div_eq_of_lt hb, Nat.add_zero]
    simp [V, show a * P + b < P * P by omega, hdiv, Nat.add_mod, Nat.mod_eq_of_lt hb]
  have Vsum (f : ℕ → ℂ) : (∑ j ∈ Finset.range (P * P), f j * V j) =
      ∑ a ∈ Finset.range P, (2 * E a *
        (∑ b ∈ Finset.range P, f (a * P + b) * sign b) - sign a * f (a * P)) := by
    have blocks (c : ℕ) : (∑ j ∈ Finset.range (c * P), f j * V j) =
        ∑ a ∈ Finset.range c, ∑ b ∈ Finset.range P, f (a * P + b) * V (a * P + b) := by
      induction c with
      | zero => simp
      | succ c ih =>
          rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    rw [blocks]
    apply Finset.sum_congr rfl
    intro a ha
    have hterm (b : ℕ) (hb : b < P) : f (a * P + b) * V (a * P + b) =
        2 * E a * (f (a * P + b) * sign b) -
          sign a * (if b = 0 then f (a * P + b) else 0) := by
      rw [Ventry a b (Finset.mem_range.mp ha) hb]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun b hb => hterm b (Finset.mem_range.mp hb))]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    simp [hp]
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · norm_num [V, E, sign, hp]
  · intro j hj
    rw [hN] at hj
    by_cases hjP : j < P * P
    · have he : j = P * (j / P) + j % P := (Nat.div_add_mod j P).symm
      have hr : j % P < P := Nat.mod_lt _ hp
      have hdiv : j / P < P := (Nat.div_lt_iff_lt_mul hp).mpr hjP
      have hm' : P * (P - 1) = P * P - P := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      have hlowq : P - 1 ≤ j / P := (Nat.le_div_iff_mul_le hp).mpr (by
        rw [Nat.mul_comm (P - 1) P, hm']; omega)
      have heq : j / P = P - 1 := by omega
      have hrem : 1 ≤ j % P := by rw [heq, hm'] at he; omega
      have hb : j / P = P - 1 ∧ 1 ≤ j % P := ⟨heq, hrem⟩
      have hodd : (j / P) % 2 ≠ 0 := by rw [hb.1]; rw [hP]; omega
      simp [V, E, hjP, hodd, show j % P ≠ 0 by omega]
    · simp [V, hjP]
  · rw [hN]
    have h := Vsum (fun _ => 1)
    simp only [one_mul, mul_one, hsign, mul_zero, zero_sub] at h
    rw [h, Finset.sum_neg_distrib, hsign, neg_zero]
  · intro i hi
    rw [hN] at hi ⊢
    rw [Vsum]
    change (∑ a ∈ Finset.range P, (2 * E a *
      (∑ b ∈ Finset.range P, digitSum (i + (a * P + b)) t * sign b) -
        sign a * digitSum (i + a * P) t)) = 0
    let q := i / P
    let r := i % P
    have hr : r < P := Nat.mod_lt _ hp
    have hq : q < P := (Nat.div_lt_iff_lt_mul hp).mpr hi
    have hiqr : i = P * q + r := (Nat.div_add_mod i P).symm
    have hidx (a b : ℕ) : i + (a * P + b) = P * (q + a) + r + b := by
      rw [hiqr]; ring
    simp_rw [hidx, dot_sign _ _ hr]
    have hleft : (∑ a ∈ Finset.range P,
        2 * E a * (-(M : ℂ) + t ^ d *
          (digitSum (q + a + 1) t - digitSum (q + a) t - 1) *
            (∑ b ∈ Finset.range P, if P ≤ r + b then sign b else 0))) =
              -2 * (M : ℂ) ^ 2 := by
      have rearrange (a : ℕ) : 2 * E a * (-(M : ℂ) + t ^ d *
          (digitSum (q + a + 1) t - digitSum (q + a) t - 1) *
            (∑ b ∈ Finset.range P, if P ≤ r + b then sign b else 0)) =
          (-2 * (M : ℂ)) * E a +
            (2 * t ^ d * (∑ b ∈ Finset.range P, if P ≤ r + b then sign b else 0)) *
              (E a * (digitSum (q + a + 1) t - digitSum (q + a) t - 1)) := by ring
      simp_rw [rearrange]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hE,
        Ecarry _ hq, mul_zero, add_zero]; ring
    have hright : (∑ a ∈ Finset.range P, sign a * digitSum (i + a * P) t) =
        -2 * (M : ℂ) ^ 2 := by
      have idx (a : ℕ) : i + a * P = P * (q + a) + r := by rw [hiqr]; ring
      have blk (a : ℕ) : digitSum (P * (q + a) + r) t =
          t ^ d * digitSum (q + a) t + digitSum r t := digit_block d (q + a) r t hr
      simp_rw [idx, blk, mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsign, zero_mul, add_zero]
      have rearrange (a : ℕ) : sign a * (t ^ d * digitSum (q + a) t) =
          t ^ d * (sign a * digitSum (q + a) t) := by ring
      simp_rw [rearrange]
      rw [← Finset.mul_sum, sign_digit _ hq, htpow]
      have hc : (P : ℂ) = 2 * (M : ℂ) := by exact_mod_cast hP
      rw [hc]; ring
    rw [Finset.sum_sub_distrib, hleft, hright, sub_self]

end D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankelVanishing
