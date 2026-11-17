/- GID: D5/S3/Combinatorics/Hankel/SunA006077Blocks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hankel/SunA006077Blocks
   mirror-E: none(waiver:symbolic-residue-block-proof)
   anchors: []
   utility: none
   digest: Residue classes split the sparse Sun moment determinants into three blocks. -/

import D5.S3.Combinatorics.Hankel.SunA006077

/-! Residue blocks for the sparse moments, with simultaneous row and column signs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Hankel.SunA006077

open Finset Matrix

/-- The unshifted multinomial moment determinant, including the empty determinant. -/
def D (k : ℕ) : ℤ := (Matrix.of fun i j : Fin k => c (i.val+j.val)).det

/-- The once-shifted multinomial moment determinant. -/
def E (k : ℕ) : ℤ := (Matrix.of fun i j : Fin k => c (i.val+j.val+1)).det

private def residueEquiv (N a b d : ℕ)
    (ha : a=(N+2)/3) (hb : b=(N+1)/3) (hd : d=N/3) :
    Fin a ⊕ (Fin b ⊕ Fin d) ≃ Fin N :=
  Equiv.ofBijective (fun a => match a with
    | Sum.inl i => ⟨3*i.val, by have := i.isLt; omega⟩
    | Sum.inr (Sum.inl i) => ⟨3*i.val+1, by have := i.isLt; omega⟩
    | Sum.inr (Sum.inr i) => ⟨3*i.val+2, by have := i.isLt; omega⟩) (by
    constructor
    · intro a b h
      have hval := congrArg Fin.val h
      rcases a with i | (i | i) <;> rcases b with j | (j | j) <;>
        dsimp at hval <;> (try simp only [Sum.inl.injEq, Sum.inr.injEq, Fin.ext_iff]) <;> omega
    · intro j
      have hj := j.isLt
      by_cases h0 : j.val % 3 = 0
      · refine ⟨Sum.inl ⟨j.val/3, by omega⟩, ?_⟩
        apply Fin.ext
        dsimp
        omega
      · by_cases h1 : j.val % 3 = 1
        · refine ⟨Sum.inr (Sum.inl ⟨j.val/3, by omega⟩), ?_⟩
          apply Fin.ext
          dsimp
          omega
        · refine ⟨Sum.inr (Sum.inr ⟨j.val/3, by omega⟩), ?_⟩
          apply Fin.ext
          dsimp
          omega)

private theorem swap_block_det {R : Type*} [CommRing R] (k : ℕ) :
    (fromBlocks (0 : Matrix (Fin k) (Fin k) R)
      (1 : Matrix (Fin k) (Fin k) R) (1 : Matrix (Fin k) (Fin k) R) 0).det = (-1 : R)^k := by
  let P : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R := fromBlocks 1 1 0 1
  have hp : P.det = 1 := by simp [P]
  have hprod : P * fromBlocks 0 1 1 0 = fromBlocks 1 1 1 0 := by
    simp [P, fromBlocks_multiply]
  have hd := congrArg Matrix.det hprod
  rw [det_mul, hp, one_mul, det_fromBlocks_one₁₁] at hd
  simpa [Matrix.det_neg] using hd

theorem cross_block_det {R : Type*} [CommRing R] (k : ℕ)
    (A B C : Matrix (Fin k) (Fin k) R) :
    (fromBlocks A B C 0).det = (-1 : R)^k * B.det * C.det := by
  have hp : fromBlocks A B C 0 * fromBlocks 0 1 1 0 = fromBlocks B A 0 C := by
    simp [fromBlocks_multiply]
  have hd := congrArg Matrix.det hp
  rw [det_mul, swap_block_det, det_fromBlocks_zero₂₁] at hd
  have hs : (-1 : R)^k * (-1 : R)^k = 1 := by rw [← mul_pow]; simp
  calc
    (fromBlocks A B C 0).det =
        (-1 : R)^k * ((fromBlocks A B C 0).det * (-1)^k) := by
      rw [mul_left_comm, hs, mul_one]
    _ = (-1 : R)^k * B.det * C.det := by rw [hd]; ring

private def signedSparse (N : ℕ) : Matrix (Fin N) (Fin N) ℤ :=
  Matrix.of fun i j => (-1 : ℤ)^(i.val/3) * sparse (i.val+j.val) * (-1)^(j.val/3)

private theorem signedSparse_det (N : ℕ) : (signedSparse N).det =
    (Matrix.of fun i j : Fin N => sparse (i.val+j.val)).det := by
  let f : Fin N → ℤ := fun i => (-1 : ℤ)^(i.val/3)
  have hs : (∏ i : Fin N, f i) * (∏ i : Fin N, f i) = 1 := by
    rw [← prod_mul_distrib]
    apply prod_eq_one
    intro i _
    dsimp [f]
    rw [← mul_pow]
    simp
  have he : signedSparse N = Matrix.of (fun i j => f j *
      (Matrix.of fun i j : Fin N => f i * sparse (i.val+j.val)) i j) := by
    ext i j
    simp only [signedSparse, f, Matrix.of_apply]
    ring
  have hc := det_mul_column f (Matrix.of fun i j : Fin N => sparse (i.val+j.val))
  simp only [Matrix.of_apply] at hc
  rw [he, det_mul_row, hc, ← mul_assoc, hs, one_mul]

private theorem signed_entry (p q r s : ℕ) (hr : r < 3) (hs : s < 3) :
    (-1 : ℤ)^((3*p+r)/3) * sparse ((3*p+r)+(3*q+s)) *
      (-1)^((3*q+s)/3) =
      if r+s=0 then c (p+q) else if r+s=3 then -c (p+q+1) else 0 := by
  have hp : (3*p+r)/3=p := by omega
  have hq : (3*q+s)/3=q := by omega
  rw [hp, hq]
  by_cases h0 : r+s=0
  · have hdiv : ((3*p+r)+(3*q+s))/3 = p+q := by omega
    have hmod : ((3*p+r)+(3*q+s))%3 = 0 := by omega
    simp only [h0, ite_true, sparse, hmod, hdiv, pow_add]
    have hp2 : (-1 : ℤ)^p * (-1)^p=1 := by rw [← mul_pow]; simp
    have hq2 : (-1 : ℤ)^q * (-1)^q=1 := by rw [← mul_pow]; simp
    calc
      _ = ((-1 : ℤ)^p * (-1)^p) * ((-1)^q * (-1)^q) * c (p+q) := by ring
      _ = c (p+q) := by rw [hp2, hq2]; ring
  · by_cases h3 : r+s=3
    · have hdiv : ((3*p+r)+(3*q+s))/3 = p+q+1 := by omega
      have hmod : ((3*p+r)+(3*q+s))%3 = 0 := by omega
      simp only [h0, h3, ite_false, ite_true, sparse, hmod, hdiv, pow_add, pow_one]
      have hp2 : (-1 : ℤ)^p * (-1)^p=1 := by rw [← mul_pow]; simp
      have hq2 : (-1 : ℤ)^q * (-1)^q=1 := by rw [← mul_pow]; simp
      calc
        _ = -(((-1 : ℤ)^p * (-1)^p) * ((-1)^q * (-1)^q) * c (p+q+1)) := by ring
        _ = -c (p+q+1) := by rw [hp2, hq2]; ring
    · have hmod : ((3*p+r)+(3*q+s))%3 ≠ 0 := by omega
      simp only [sparse, hmod, ite_false, mul_zero, zero_mul, h0, h3]

private def cBlock (a b shift : ℕ) : Matrix (Fin a) (Fin b) ℤ :=
  Matrix.of fun i j => c (i.val+j.val+shift)

private theorem signed_blocks (N a b d : ℕ)
    (ha : a=(N+2)/3) (hb : b=(N+1)/3) (hd : d=N/3) :
    (signedSparse N).submatrix (residueEquiv N a b d ha hb hd)
        (residueEquiv N a b d ha hb hd) =
      fromBlocks (cBlock a a 0) 0 0
        (fromBlocks (0 : Matrix (Fin b) (Fin b) ℤ)
          (-cBlock b d 1) (-cBlock d b 1) 0) := by
  ext a b
  rcases a with i | (i | i) <;> rcases b with j | (j | j)
  · simpa [signedSparse, residueEquiv, Equiv.ofBijective, cBlock, Matrix.submatrix_apply] using
      signed_entry i.val j.val 0 0 (by decide) (by decide)
  · simpa [signedSparse, residueEquiv, Equiv.ofBijective, cBlock, Matrix.submatrix_apply] using
      signed_entry i.val j.val 0 1 (by decide) (by decide)
  · simpa [signedSparse, residueEquiv, Equiv.ofBijective, cBlock, Matrix.submatrix_apply] using
      signed_entry i.val j.val 0 2 (by decide) (by decide)
  · simpa [signedSparse, residueEquiv, Equiv.ofBijective, cBlock, Matrix.submatrix_apply] using
      signed_entry i.val j.val 1 0 (by decide) (by decide)
  · simpa [signedSparse, residueEquiv, Equiv.ofBijective, cBlock, Matrix.submatrix_apply] using
      signed_entry i.val j.val 1 1 (by decide) (by decide)
  · simpa [signedSparse, residueEquiv, Equiv.ofBijective, cBlock, Matrix.submatrix_apply] using
      signed_entry i.val j.val 1 2 (by decide) (by decide)
  · simpa [signedSparse, residueEquiv, Equiv.ofBijective, cBlock, Matrix.submatrix_apply] using
      signed_entry i.val j.val 2 0 (by decide) (by decide)
  · simpa [signedSparse, residueEquiv, Equiv.ofBijective, cBlock, Matrix.submatrix_apply] using
      signed_entry i.val j.val 2 1 (by decide) (by decide)
  · simpa [signedSparse, residueEquiv, Equiv.ofBijective, cBlock, Matrix.submatrix_apply] using
      signed_entry i.val j.val 2 2 (by decide) (by decide)

private theorem determinant_blocks (N a b d : ℕ)
    (ha : a=(N+2)/3) (hb : b=(N+1)/3) (hd : d=N/3) :
    (Matrix.of fun i j : Fin N => sparse (i.val+j.val)).det =
      (cBlock a a 0).det *
        (fromBlocks (0 : Matrix (Fin b) (Fin b) ℤ) (-cBlock b d 1) (-cBlock d b 1) 0).det := by
  rw [← signedSparse_det N,
    ← det_submatrix_equiv_self (residueEquiv N a b d ha hb hd), signed_blocks]
  exact det_fromBlocks_zero₂₁ _ _ _

/-- The determinant in residue zero has one unshifted and two shifted factors. -/
theorem block_zero (m : ℕ) : W (3*m) = (-1 : ℤ)^m * D (m+1) * (E m)^2 := by
  rw [source_hankel_reduction,
    determinant_blocks (3*m+1) (m+1) m m (by omega) (by omega) (by omega)]
  rw [cross_block_det, Matrix.det_neg]
  simp only [Fintype.card_fin, cBlock, Nat.add_zero]
  change D (m+1) * ((-1 : ℤ)^m * ((-1)^m * E m) * ((-1)^m * E m)) = _
  have hs : (-1 : ℤ)^m * (-1)^m=1 := by rw [← mul_pow]; simp
  calc
    _ = (-1 : ℤ)^m * D (m+1) * (E m)^2 * ((-1)^m * (-1)^m) := by ring
    _ = _ := by rw [hs]; ring

/-- The determinant in residue two has equal shifted blocks of size `m+1`. -/
theorem block_two (m : ℕ) :
    W (3*m+2) = (-1 : ℤ)^(m+1) * D (m+1) * (E (m+1))^2 := by
  rw [source_hankel_reduction,
    determinant_blocks (3*m+2+1) (m+1) (m+1) (m+1) (by omega) (by omega) (by omega)]
  rw [cross_block_det, Matrix.det_neg]
  simp only [Fintype.card_fin, cBlock, Nat.add_zero]
  change D (m+1) * ((-1 : ℤ)^(m+1) * ((-1)^(m+1) * E (m+1)) *
    ((-1)^(m+1) * E (m+1))) = _
  have hs : (-1 : ℤ)^(m+1) * (-1)^(m+1)=1 := by rw [← mul_pow]; simp
  calc
    _ = (-1 : ℤ)^(m+1) * D (m+1) * (E (m+1))^2 *
      ((-1)^(m+1) * (-1)^(m+1)) := by ring
    _ = _ := by rw [hs]; ring

/-- The residue-one source determinants vanish at every index. -/
theorem zero_branch (m : ℕ) : W (3*m+1) = 0 := by
  classical
  rw [source_hankel_reduction, Matrix.det_apply]
  apply sum_eq_zero
  intro σ _
  suffices hz : (∏ i : Fin (3*m+1+1), sparse ((σ i).val+i.val)) = 0 by simp [hz]
  by_contra hp
  have entries (i : Fin (3*m+1+1)) : sparse ((σ i).val+i.val) ≠ 0 :=
    (prod_ne_zero_iff.mp hp) i (mem_univ i)
  let embed : Fin (m+1) → Fin (3*m+1+1) := fun i => ⟨3*i.val+1, by omega⟩
  have hres (i : Fin (m+1)) : (σ (embed i)).val % 3 = 2 := by
    have h := entries (embed i)
    by_contra hr
    have hm : ((σ (embed i)).val + (embed i).val) % 3 ≠ 0 := by
      change ((σ (embed i)).val + (3*i.val+1)) % 3 ≠ 0
      omega
    simp [sparse, hm] at h
  let f : Fin (m+1) → Fin m := fun i =>
    ⟨(σ (embed i)).val/3, by have := (σ (embed i)).isLt; have := hres i; omega⟩
  have hinj : Function.Injective f := by
    intro i j h
    have hv := congrArg Fin.val h
    have hri := hres i
    have hrj := hres j
    have hσ : σ (embed i) = σ (embed j) := Fin.ext (by dsimp [f] at hv; omega)
    have he := congrArg Fin.val (σ.injective hσ)
    apply Fin.ext
    dsimp [embed] at he
    omega
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hcard
  omega

end D5.S3.Combinatorics.Hankel.SunA006077
