/- GID: D5/S3/Combinatorics/Hankel/SunA006077Arithmetic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hankel/SunA006077Arithmetic
   mirror-E: none(waiver:unbounded-binomial-valuation-proof)
   anchors: []
   utility: none
   digest: Integral normalization and binary parity of the multinomial moments. -/

import D5.S3.Combinatorics.Hankel.SunA006077Binary

/-! Binomial normalization and the powers of two detected by its parity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Hankel.SunA006077

/-- An explicit integral quotient of the positive-index moments by six. -/
def q (r : ℕ) : ℕ := (2*r-1).choose (r-1) * (3*r-1).choose (r-1)

/-- Every positive-index moment has the explicit factor six. -/
theorem c_six (r : ℕ) (hr : 0 < r) : c r = 6 * (q r : ℤ) := by
  unfold c q
  rw [Nat.choose_mul_right (m := 2) hr.ne', Nat.choose_mul_right (m := 3) hr.ne']
  push_cast
  ring

private theorem binary_sum_pos (r : ℕ) (hr : 0 < r) : 0 < (Nat.digits 2 r).sum := by
  have hn : Nat.digits 2 r ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hr.ne'
  exact List.sum_pos_iff_exists_pos_nat.mpr
    ⟨_, List.getLast_mem hn, Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero 2 hr.ne')⟩

private theorem binary_sum_one (r : ℕ) :
    (Nat.digits 2 r).sum = 1 ↔ ∃ k : ℕ, r=2^k := by
  constructor
  · intro h
    have zero_digits (L : List ℕ) (hL : L.sum=0) : Nat.ofDigits 2 L=0 := by
      induction L with
      | nil => rfl
      | cons a L ih =>
        simp only [List.sum_cons] at hL
        have ha : a=0 := by omega
        have ht : L.sum=0 := by omega
        simp [Nat.ofDigits_cons, ha, ih ht]
    have one_digits (L : List ℕ) (hL : L.sum=1) : ∃ k : ℕ, Nat.ofDigits 2 L=2^k := by
      induction L with
      | nil => simp at hL
      | cons a L ih =>
        simp only [List.sum_cons] at hL
        by_cases ha : a=0
        · have ht : L.sum=1 := by omega
          obtain ⟨k, hk⟩ := ih ht
          exact ⟨k+1, by simp [Nat.ofDigits_cons, ha, hk, pow_succ']⟩
        · have ha1 : a=1 := by omega
          have ht : L.sum=0 := by omega
          exact ⟨0, by simp [Nat.ofDigits_cons, ha1, zero_digits L ht]⟩
    obtain ⟨k, hk⟩ := one_digits (Nat.digits 2 r) h
    exact ⟨k, (Nat.ofDigits_digits 2 r).symm.trans hk⟩
  · rintro ⟨k, rfl⟩
    have h := Nat.digits_base_pow_mul (b := 2) (k := k) (by decide) (by decide : 0 < 1)
    simpa using congrArg List.sum h

private theorem central_valuation (r : ℕ) (hr : 0 < r) :
    padicValNat 2 ((2*r).choose r) = (Nat.digits 2 r).sum := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := sub_one_mul_padicValNat_choose_eq_sub_sum_digits'
    (p := 2) (n := r) (k := r)
  have hd := congrArg List.sum (Nat.digits_base_mul (by decide : 1 < 2) hr)
  have he : (Nat.digits 2 (2*r)).sum = (Nat.digits 2 r).sum := by simpa using hd
  rw [show r+r=2*r by omega] at h
  simp only [Nat.reduceSub, one_mul, he] at h
  omega

/-- A normalized coefficient is odd exactly at a positive power of two. -/
theorem q_odd_iff (r : ℕ) (hr : 0 < r) : Odd (q r) ↔ ∃ k : ℕ, r=2^k := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : (2*r).choose r ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hn2 : (3*r).choose r ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hq : q r ≠ 0 := by
    unfold q
    exact mul_ne_zero (Nat.choose_pos (by omega)).ne' (Nat.choose_pos (by omega)).ne'
  have hc : (2*r).choose r * (3*r).choose r = 6*q r := by
    rw [Nat.choose_mul_right (m := 2) hr.ne', Nat.choose_mul_right (m := 3) hr.ne']
    unfold q
    ring
  have hv : padicValNat 2 ((2*r).choose r) + padicValNat 2 ((3*r).choose r) =
      1 + padicValNat 2 (q r) := by
    rw [← padicValNat.mul hn1 hn2, hc, padicValNat.mul (by decide : 6 ≠ 0) hq]
    rw [show (6 : ℕ)=2*3 by decide, padicValNat.mul (by decide : (2 : ℕ) ≠ 0)
      (by decide : (3 : ℕ) ≠ 0), padicValNat_self,
      padicValNat.eq_zero_of_not_dvd (by decide : ¬(2 : ℕ) ∣ 3), add_zero]
  have hodd : Odd (q r) ↔ padicValNat 2 (q r)=0 := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd, padicValNat.eq_zero_iff]
    simp [hq]
  rw [hodd]
  constructor
  · intro h
    have hs := central_valuation r hr
    have hp := binary_sum_pos r hr
    apply (binary_sum_one r).mp
    omega
  · rintro ⟨k, rfl⟩
    have hs := central_valuation (2^k) (by positivity)
    have h1 := (binary_sum_one (2^k)).mpr ⟨k, rfl⟩
    have h2 : (Nat.digits 2 (2*(2^k))).sum=1 := by
      have he := congrArg List.sum
        (Nat.digits_base_mul (by decide : 1 < 2) (by positivity : 0 < 2^k))
      simpa only [List.sum_cons, zero_add, h1] using he
    have h3 : (Nat.digits 2 (3*(2^k))).sum=2 := by
      rw [mul_comm 3]
      have h := Nat.digits_base_pow_mul (b := 2) (k := k) (by decide) (by decide : 0 < 3)
      simpa [show Nat.digits 2 3 = [1,1] by decide] using congrArg List.sum h
    have ht := sub_one_mul_padicValNat_choose_eq_sub_sum_digits'
      (p := 2) (n := 2*(2^k)) (k := 2^k)
    rw [show 2*2^k+2^k=3*2^k by omega] at ht
    simp only [Nat.reduceSub, one_mul, h1, h2, h3] at ht
    omega


open Matrix Finset

/-- The unshifted determinant with all rows except the first divided by six. -/
def d (m : ℕ) : ℤ :=
  (Matrix.of fun i j : Fin (m+1) => if i.val=0 then c j.val else (q (i.val+j.val) : ℤ)).det

/-- The shifted determinant with every row divided by six. -/
def e (m : ℕ) : ℤ :=
  (Matrix.of fun i j : Fin m => (q (i.val+j.val+1) : ℤ)).det

/-- The unshifted row normalization is an exact integral factorization. -/
theorem D_normalization (m : ℕ) : D (m+1)=6^m*d m := by
  let A : Matrix (Fin (m+1)) (Fin (m+1)) ℤ :=
    Matrix.of fun i j => if i.val=0 then c j.val else (q (i.val+j.val) : ℤ)
  let f : Fin (m+1) → ℤ := fun i => if i.val=0 then 1 else 6
  have hm : (Matrix.of fun i j : Fin (m+1) => c (i.val+j.val)) =
      Matrix.of (fun i j => f i * A i j) := by
    ext i j
    by_cases hi : i.val=0
    · have hi0 : i=0 := Fin.ext hi
      simp [f,A,hi0]
    · simp only [Matrix.of_apply,f,A,hi,ite_false]
      exact c_six _ (by omega)
  have hp : (∏ i : Fin (m+1), f i)=(6 : ℤ)^m := by
    rw [Fin.prod_univ_succ]
    simp [f]
  unfold D d
  rw [hm,Matrix.det_mul_column,hp]

/-- The shifted row normalization is an exact integral factorization. -/
theorem E_normalization (m : ℕ) : E m=6^m*e m := by
  have hm : (Matrix.of fun i j : Fin m => c (i.val+j.val+1)) =
      Matrix.of (fun i j : Fin m => (6 : ℤ)*(q (i.val+j.val+1) : ℤ)) := by
    ext i j
    exact c_six _ (by omega)
  unfold E e
  rw [hm]
  have h := Matrix.det_mul_column (fun _ : Fin m => (6 : ℤ))
    (Matrix.of fun i j : Fin m => (q (i.val+j.val+1) : ℤ))
  simpa only [Matrix.of_apply,Finset.prod_const,Fintype.card_fin,Finset.card_univ] using h

private theorem q_mod_two (r : ℕ) (hr : 0 < r) : (q r : ZMod 2)=epsilon r := by
  classical
  by_cases h : ∃ k : ℕ, r=2^k
  · simp only [epsilon,h,ite_true]
    exact ZMod.natCast_eq_one_iff_odd.mpr ((q_odd_iff r hr).mpr h)
  · simp only [epsilon,h,ite_false]
    by_contra hz
    exact h ((q_odd_iff r hr).mp (ZMod.natCast_ne_zero_iff_odd.mp hz))

private theorem c_mod_two (r : ℕ) (hr : 0 < r) : (c r : ZMod 2)=0 := by
  rw [c_six r hr]
  push_cast
  rw [show (6 : ZMod 2)=0 by decide,zero_mul]

/-- Both integral quotient determinants are odd at every size. -/
theorem normalized_odd (m : ℕ) : Odd (d m) ∧ Odd (e m) := by
  have he : (e m : ZMod 2)=S m := by
    unfold e S
    rw [Int.cast_det]
    congr 1
    ext i j
    simp only [Matrix.map_apply,Matrix.of_apply,Int.cast_natCast]
    exact q_mod_two _ (by omega)
  have hd : (d m : ZMod 2)=T m := by
    let M : Matrix (Fin (m+1)) (Fin (m+1)) (ZMod 2) :=
      Matrix.of fun i j => if i.val=0 then (if j.val=0 then 1 else 0)
        else epsilon (i.val+j.val)
    have hm : (d m : ZMod 2)=M.det := by
      unfold d
      rw [Int.cast_det]
      congr 1
      ext i j
      by_cases hi : i.val=0
      · by_cases hj : j.val=0
        · have hi0 : i=0 := Fin.ext hi
          have hj0 : j=0 := Fin.ext hj
          simp [M,hi0,hj0,c]
        · simp only [Matrix.map_apply,Matrix.of_apply,M]
          rw [if_pos hi,if_pos hi,if_neg hj]
          exact c_mod_two j.val (Nat.pos_of_ne_zero hj)
      · simp only [Matrix.map_apply,Matrix.of_apply,hi,ite_false,M,Int.cast_natCast]
        exact q_mod_two _ (by omega)
    rw [hm,Matrix.det_succ_row_zero,sum_eq_single 0]
    · have hminor : M.submatrix Fin.succ Fin.succ =
          Matrix.of (fun i j : Fin m => epsilon (i.val+j.val+2)) := by
        ext i j
        simp only [M,Matrix.submatrix_apply,Matrix.of_apply,Fin.val_succ]
        simp [show i.val+1+(j.val+1)=i.val+j.val+2 by omega]
      simp only [M,Matrix.of_apply,Fin.val_zero,ite_true,pow_zero,one_mul,
        Fin.succAbove_zero,hminor]
      rfl
    · intro j _ hj
      have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
      simp [M,hj]
    · simp
  constructor
  · exact ZMod.intCast_eq_one_iff_odd.mp (hd.trans (rueppel_determinants m).2)
  · exact ZMod.intCast_eq_one_iff_odd.mp (he.trans (rueppel_determinants m).1)

end D5.S3.Combinatorics.Hankel.SunA006077
