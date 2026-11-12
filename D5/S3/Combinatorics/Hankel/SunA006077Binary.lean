/- GID: D5/S3/Combinatorics/Hankel/SunA006077Binary
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hankel/SunA006077Binary
   mirror-E: none(waiver:all-index-binary-determinant-induction)
   anchors: []
   utility: none
   digest: Both shifted Rueppel Hankel determinants equal one in characteristic two. -/

import D5.S3.Combinatorics.Hankel.SunA006077Blocks

/-! The ordinary and once-shifted Rueppel determinants modulo two. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Hankel.SunA006077

open Matrix Finset

/-- The indicator of the positive powers of two, with value zero at zero. -/
def epsilon (n : ℕ) : ZMod 2 := by
  classical
  exact if ∃ k : ℕ, n=2^k then 1 else 0

/-- The ordinary shifted Rueppel determinant. -/
def S (k : ℕ) : ZMod 2 :=
  (Matrix.of fun i j : Fin k => epsilon (i.val+j.val+1)).det

/-- The next shifted Rueppel determinant. -/
def T (k : ℕ) : ZMod 2 :=
  (Matrix.of fun i j : Fin k => epsilon (i.val+j.val+2)).det

private theorem epsilon_even (n : ℕ) : epsilon (2*n) = epsilon n := by
  classical
  have h : (∃ k : ℕ, 2*n=2^k) ↔ ∃ k : ℕ, n=2^k := by
    constructor
    · rintro ⟨k, hk⟩
      cases k with
      | zero => simp at hk
      | succ k => exact ⟨k, by rw [pow_succ'] at hk; omega⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k+1, by rw [pow_succ']⟩
  simp only [epsilon, h]

private theorem epsilon_odd (n : ℕ) : epsilon (2*n+1) = if n=0 then 1 else 0 := by
  classical
  have h : (∃ k : ℕ, 2*n+1=2^k) ↔ n=0 := by
    constructor
    · rintro ⟨k, hk⟩
      cases k with
      | zero => simpa using hk
      | succ k => rw [pow_succ'] at hk; omega
    · rintro rfl
      exact ⟨0, rfl⟩
  simp only [epsilon, h]

private def parityEquiv (N a b : ℕ) (ha : a=(N+1)/2) (hb : b=N/2) :
    Fin a ⊕ Fin b ≃ Fin N :=
  Equiv.ofBijective (fun i => match i with
    | Sum.inl j => ⟨2*j.val, by have := j.isLt; omega⟩
    | Sum.inr j => ⟨2*j.val+1, by have := j.isLt; omega⟩) (by
    constructor
    · intro i j h
      have hv := congrArg Fin.val h
      rcases i with i|i <;> rcases j with j|j <;> dsimp at hv <;>
        (try simp only [Sum.inl.injEq, Sum.inr.injEq, Fin.ext_iff]) <;> omega
    · intro j
      have hj := j.isLt
      by_cases he : j.val%2=0
      · exact ⟨Sum.inl ⟨j.val/2, by omega⟩, Fin.ext (by dsimp; omega)⟩
      · exact ⟨Sum.inr ⟨j.val/2, by omega⟩, Fin.ext (by dsimp; omega)⟩)

private def epsBlock (a b shift : ℕ) : Matrix (Fin a) (Fin b) (ZMod 2) :=
  Matrix.of fun i j => epsilon (i.val+j.val+shift)

private theorem t_blocks (N a b : ℕ) (ha : a=(N+1)/2) (hb : b=N/2) :
    T N = (epsBlock a a 1).det * (epsBlock b b 2).det := by
  let e := parityEquiv N a b ha hb
  have h : (Matrix.of fun i j : Fin N => epsilon (i.val+j.val+2)).submatrix e e =
      fromBlocks (epsBlock a a 1) 0 0 (epsBlock b b 2) := by
    ext i j
    rcases i with i|i <;> rcases j with j|j
    · change epsilon (2*i.val+2*j.val+2) = epsilon (i.val+j.val+1)
      rw [show 2*i.val+2*j.val+2=2*(i.val+j.val+1) by omega, epsilon_even]
    · change epsilon (2*i.val+(2*j.val+1)+2) = 0
      rw [show 2*i.val+(2*j.val+1)+2=2*(i.val+j.val+1)+1 by omega, epsilon_odd]
      simp
    · change epsilon ((2*i.val+1)+2*j.val+2) = 0
      rw [show (2*i.val+1)+2*j.val+2=2*(i.val+j.val+1)+1 by omega, epsilon_odd]
      simp
    · change epsilon ((2*i.val+1)+(2*j.val+1)+2) = epsilon (i.val+j.val+2)
      rw [show (2*i.val+1)+(2*j.val+1)+2=2*(i.val+j.val+2) by omega, epsilon_even]
  unfold T
  rw [← det_submatrix_equiv_self e, h, det_fromBlocks_zero₂₁]

private theorem s_even (k : ℕ) : S (2*k) = (S k)^2 := by
  let e := parityEquiv (2*k) k k (by omega) (by omega)
  let A : Matrix (Fin k) (Fin k) (ZMod 2) :=
    Matrix.of fun i j => if i.val=0 ∧ j.val=0 then 1 else 0
  have h : (Matrix.of fun i j : Fin (2*k) => epsilon (i.val+j.val+1)).submatrix e e =
      fromBlocks A (epsBlock k k 1) (epsBlock k k 1) 0 := by
    ext i j
    rcases i with i|i <;> rcases j with j|j
    · change epsilon (2*i.val+2*j.val+1) = if i.val=0 ∧ j.val=0 then 1 else 0
      rw [show 2*i.val+2*j.val+1=2*(i.val+j.val)+1 by omega, epsilon_odd]
      simp
    · change epsilon (2*i.val+(2*j.val+1)+1) = epsilon (i.val+j.val+1)
      rw [show 2*i.val+(2*j.val+1)+1=2*(i.val+j.val+1) by omega, epsilon_even]
    · change epsilon ((2*i.val+1)+2*j.val+1) = epsilon (i.val+j.val+1)
      rw [show (2*i.val+1)+2*j.val+1=2*(i.val+j.val+1) by omega, epsilon_even]
    · change epsilon ((2*i.val+1)+(2*j.val+1)+1) = 0
      rw [show (2*i.val+1)+(2*j.val+1)+1=2*(i.val+j.val+1)+1 by omega, epsilon_odd]
      simp
  unfold S
  rw [← det_submatrix_equiv_self e, h, cross_block_det]
  simp only [show (-1 : ZMod 2)=1 by decide, one_pow, one_mul]
  simp only [pow_two]
  rfl

private def oddEquiv (k : ℕ) : Fin 1 ⊕ (Fin k ⊕ Fin k) ≃ Fin (2*k+1) :=
  Equiv.ofBijective (fun i => match i with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl j) => ⟨2*j.val+2, by omega⟩
    | Sum.inr (Sum.inr j) => ⟨2*j.val+1, by omega⟩) (by
    constructor
    · intro i j h
      have hv := congrArg Fin.val h
      rcases i with i|(i|i) <;> rcases j with j|(j|j) <;> dsimp at hv <;>
        (try simp only [Sum.inl.injEq, Sum.inr.injEq, Fin.ext_iff]) <;> omega
    · intro j
      by_cases hz : j.val=0
      · exact ⟨Sum.inl 0, Fin.ext hz.symm⟩
      · by_cases he : j.val%2=0
        · exact ⟨Sum.inr (Sum.inl ⟨j.val/2-1, by omega⟩), Fin.ext (by dsimp; omega)⟩
        · exact ⟨Sum.inr (Sum.inr ⟨j.val/2, by omega⟩), Fin.ext (by dsimp; omega)⟩)

private theorem s_odd (k : ℕ) : S (2*k+1) = (T k)^2 := by
  let M := Matrix.of fun i j : Fin (2*k+1) => epsilon (i.val+j.val+1)
  let e := oddEquiv k
  let B : Matrix (Fin k) (Fin k) (ZMod 2) := epsBlock k k 2
  let u : Matrix (Fin 1) (Fin k) (ZMod 2) := Matrix.of fun _ j => epsilon (j.val+1)
  let A : Matrix (Fin 1 ⊕ (Fin k ⊕ Fin k)) (Fin 1 ⊕ (Fin k ⊕ Fin k)) (ZMod 2) :=
    fromBlocks 1 (Matrix.of fun i => Sum.elim (fun _ => 0) (u i))
      (Matrix.of (Sum.elim (fun _ _ => 0) (fun i j => u j i))) (fromBlocks 0 B B 0)
  have hm : M.submatrix e e=A := by
    ext i j
    rcases i with i|(i|i) <;> rcases j with j|(j|j)
    · change epsilon (0+0+1) = (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)) i j
      have hi : i=0 := Subsingleton.elim _ _
      have hj : j=0 := Subsingleton.elim _ _
      have he : ∃ k : ℕ, 1=2^k := ⟨0,rfl⟩
      simp [Matrix.one_apply,hi,hj,epsilon,he]
    · change epsilon (0+(2*j.val+2)+1)=0
      rw [show 0+(2*j.val+2)+1=2*(j.val+1)+1 by omega, epsilon_odd]
      simp
    · change epsilon (0+(2*j.val+1)+1)=epsilon (j.val+1)
      rw [show 0+(2*j.val+1)+1=2*(j.val+1) by omega,epsilon_even]
    · change epsilon ((2*i.val+2)+0+1)=0
      rw [show (2*i.val+2)+0+1=2*(i.val+1)+1 by omega,epsilon_odd]
      simp
    · change epsilon ((2*i.val+2)+(2*j.val+2)+1)=0
      rw [show (2*i.val+2)+(2*j.val+2)+1=2*(i.val+j.val+2)+1 by omega,epsilon_odd]
      simp
    · change epsilon ((2*i.val+2)+(2*j.val+1)+1)=epsilon (i.val+j.val+2)
      rw [show (2*i.val+2)+(2*j.val+1)+1=2*(i.val+j.val+2) by omega,epsilon_even]
    · change epsilon ((2*i.val+1)+0+1)=epsilon (i.val+1)
      rw [show (2*i.val+1)+0+1=2*(i.val+1) by omega,epsilon_even]
    · change epsilon ((2*i.val+1)+(2*j.val+2)+1)=epsilon (i.val+j.val+2)
      rw [show (2*i.val+1)+(2*j.val+2)+1=2*(i.val+j.val+2) by omega,epsilon_even]
    · change epsilon ((2*i.val+1)+(2*j.val+1)+1)=0
      rw [show (2*i.val+1)+(2*j.val+1)+1=2*(i.val+j.val+1)+1 by omega,epsilon_odd]
      simp
  let Q : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) (ZMod 2) := fromBlocks 0 1 1 0
  have hQ : Q.det=1 := by
    have hp : (fromBlocks (1 : Matrix (Fin k) (Fin k) (ZMod 2))
      (1 : Matrix (Fin k) (Fin k) (ZMod 2)) 0 1).det=1 := by simp
    have hh : fromBlocks (1 : Matrix (Fin k) (Fin k) (ZMod 2)) 1 0 1 * Q =
        fromBlocks 1 1 1 0 := by simp [Q,fromBlocks_multiply]
    have hd := congrArg Matrix.det hh
    rw [det_mul,hp,one_mul,det_fromBlocks_one₁₁] at hd
    simpa [det_neg,show (-1 : ZMod 2)=1 by decide] using hd
  let Q' : Matrix (Fin 1 ⊕ (Fin k ⊕ Fin k)) (Fin 1 ⊕ (Fin k ⊕ Fin k)) (ZMod 2) :=
    fromBlocks 1 0 0 Q
  have hQ' : Q'.det=1 := by simp [Q',hQ]
  have hp : (A*Q').submatrix (Equiv.sumAssoc _ _ _) (Equiv.sumAssoc _ _ _) =
      fromBlocks (fromBlocks 1 u 0 B)
        (0 : Matrix (Fin 1 ⊕ Fin k) (Fin k) (ZMod 2))
        (Matrix.of fun i => Sum.elim (fun j => u j i) (fun _ => 0)) B := by
    ext i j
    rcases i with (i|i)|i <;> rcases j with (j|j)|j <;>
      simp [A,Q',Q,Matrix.fromBlocks,Matrix.mul_apply,Matrix.one_apply]
    all_goals intro hj; exact (hj (Subsingleton.elim _ _)).elim
  have hd := congrArg Matrix.det hp
  rw [det_submatrix_equiv_self,det_mul,hQ',mul_one,det_fromBlocks_zero₁₂,
    det_fromBlocks_zero₂₁,det_one,one_mul] at hd
  change M.det = (T k)^2
  rw [← det_submatrix_equiv_self e,hm,hd]
  simp only [pow_two]
  rfl

/-- Both binary determinant families are one for every natural size. -/
theorem rueppel_determinants (n : ℕ) : S n=1 ∧ T n=1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n=0
    · subst n
      simp [S,T]
    · by_cases h1 : n=1
      · subst n
        constructor
        · norm_num [S,Matrix.det_fin_one,epsilon]
          exact ⟨0,rfl⟩
        · norm_num [T,Matrix.det_fin_one,epsilon]
          exact ⟨1,rfl⟩
      · have hn : 2 ≤ n := by omega
        have hk : n/2<n := by omega
        obtain ⟨hs,ht⟩ := ih (n/2) hk
        by_cases he : n%2=0
        · have hN : n=2*(n/2) := by omega
          constructor
          · rw [hN,s_even,hs]; simp
          · rw [hN,t_blocks (2*(n/2)) (n/2) (n/2) (by omega) (by omega)]
            change S (n/2)*T (n/2)=1
            rw [hs,ht]; ring
        · have hN : n=2*(n/2)+1 := by omega
          constructor
          · rw [hN,s_odd,ht]; simp
          · have hk1 : n/2+1<n := by omega
            have hs1 := (ih (n/2+1) hk1).1
            rw [hN,t_blocks (2*(n/2)+1) (n/2+1) (n/2) (by omega) (by omega)]
            change S (n/2+1)*T (n/2)=1
            rw [hs1,ht]; ring

end D5.S3.Combinatorics.Hankel.SunA006077
