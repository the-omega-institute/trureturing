/- GID: D5/S3/Quantum/AURICOmega/RationalGramCospectral
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/RationalGramCospectral
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A conic family of cospectral unit Gram matrices with distinct rational dimension bounds. -/

import D5.S3.Quantum.AURICOmega.RationalGramOddPrime
import Mathlib.Data.Nat.Prime.Int
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace D5.S3.Quantum.AURICOmega.RationalGramCospectral

set_option autoImplicit false

open Matrix

local notation "GramMatrix" => Matrix (Fin 4) (Fin 4) ℚ

/-- Unit-diagonal matrix with weight twice the other off-diagonal entries on a matching. -/
def pairedEdges (t : ℚ) : GramMatrix :=
  !![1,t,t,2*t; t,1,2*t,t; t,2*t,1,t; 2*t,t,t,1]

/-- Unit-diagonal matrix with an isolated direction and a constant-weight triangle. -/
def triangleBlock (t : ℚ) : GramMatrix :=
  !![1,0,0,0; 0,1,2*t,2*t; 0,2*t,1,2*t; 0,2*t,2*t,1]

private def spectralDiagonal (t : ℚ) : GramMatrix :=
  diagonal ![1+4*t,1,1-2*t,1-2*t]

private def aBasis : GramMatrix := !![1,1,1,0; 1,-1,0,1; 1,-1,0,-1; 1,1,-1,0]
private def aInv : GramMatrix := !![1/4,1/4,1/4,1/4; 1/4,-1/4,-1/4,1/4;
  1/2,0,0,-1/2; 0,1/2,-1/2,0]

private def bBasis : GramMatrix := !![0,1,0,0; 1,0,1,1; 1,0,-1,1; 1,0,0,-2]
private def bInv : GramMatrix := !![0,1/3,1/3,1/3; 1,0,0,0;
  0,1/2,-1/2,0; 0,1/6,1/6,-1/3]

private theorem aBasis_mul_inv : aBasis * aInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [aBasis, aInv, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

private theorem bBasis_mul_inv : bBasis * bInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bBasis, bInv, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

private theorem paired_eigenbasis (t : ℚ) :
    pairedEdges t * aBasis = aBasis * spectralDiagonal t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pairedEdges, aBasis, spectralDiagonal, Matrix.diagonal_apply, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring

private theorem triangle_eigenbasis (t : ℚ) :
    triangleBlock t * bBasis = bBasis * spectralDiagonal t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [triangleBlock, bBasis, spectralDiagonal, Matrix.diagonal_apply, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring

private theorem simultaneous_similarity :
    ∃ P : GramMatrix, P.det ≠ 0 ∧ ∀ t : ℚ, pairedEdges t * P = P * triangleBlock t := by
  have hb_inv : bInv * bBasis = 1 := mul_eq_one_comm.mp bBasis_mul_inv
  have hP : (aBasis * bInv) * (bBasis * aInv) = 1 := by
    rw [mul_assoc aBasis, ← mul_assoc bInv, hb_inv, one_mul, aBasis_mul_inv]
  refine ⟨aBasis * bInv, Matrix.det_ne_zero_of_right_inverse hP, fun t => ?_⟩
  have hb : spectralDiagonal t * bInv = bInv * triangleBlock t := by
    have h := congrArg (fun X : GramMatrix => bInv * X * bInv) (triangle_eigenbasis t)
    have lhs : bInv * (triangleBlock t * bBasis) * bInv = bInv * triangleBlock t := by
      rw [Matrix.mul_assoc bInv, Matrix.mul_assoc (triangleBlock t),
        bBasis_mul_inv, Matrix.mul_one]
    have rhs : bInv * (bBasis * spectralDiagonal t) * bInv = spectralDiagonal t * bInv := by
      rw [← Matrix.mul_assoc bInv, hb_inv, Matrix.one_mul]
    exact rhs.symm.trans (h.symm.trans lhs)
  rw [← mul_assoc, paired_eigenbasis, mul_assoc, hb, mul_assoc]

private theorem gram_pair_cospectral (t : ℚ) :
    (pairedEdges t).charpoly = (triangleBlock t).charpoly ∧
      (pairedEdges t).charpoly =
        (Polynomial.X - Polynomial.C (1 + 4 * t)) * (Polynomial.X - 1) *
          (Polynomial.X - Polynomial.C (1 - 2 * t)) ^ 2 := by
  have hA := Matrix.charpoly_eq_of_mul_eq_mul
    (Matrix.det_ne_zero_of_right_inverse aBasis_mul_inv) (paired_eigenbasis t)
  have hB := Matrix.charpoly_eq_of_mul_eq_mul
    (Matrix.det_ne_zero_of_right_inverse bBasis_mul_inv) (triangle_eigenbasis t)
  refine ⟨hA.trans hB.symm, hA.trans ?_⟩
  simp [spectralDiagonal, Matrix.charpoly_diagonal, Fin.prod_univ_succ, pow_two, mul_assoc]

/-- An exact rational Gram factorization with the specified number of columns. -/
def RealizableIn (G : GramMatrix) (n : ℕ) : Prop :=
  ∃ X : Matrix (Fin 4) (Fin n) ℚ, X * Xᵀ = G

private theorem fits_congr (G D P Q : GramMatrix) (hpq : P * Q = 1)
    (h : Pᵀ * G * P = D) (n : ℕ) : RealizableIn G n ↔ RealizableIn D n := by
  have hqp : Qᵀ * Pᵀ = 1 := by rw [← Matrix.transpose_mul, hpq, Matrix.transpose_one]
  constructor
  · rintro ⟨X, rfl⟩
    refine ⟨Pᵀ * X, ?_⟩
    rw [← h, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
  · rintro ⟨X, hx⟩
    refine ⟨Qᵀ * X, ?_⟩
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      (Qᵀ * X) * (Xᵀ * Q) = Qᵀ * (X * Xᵀ) * Q := by simp only [Matrix.mul_assoc]
      _ = Qᵀ * (Pᵀ * G * P) * Q := by rw [hx, h]
      _ = (Qᵀ * Pᵀ) * G * (P * Q) := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hqp, hpq, Matrix.one_mul, Matrix.mul_one]

private def aCongr : GramMatrix := !![1/2,1,2,0; -1/2,1,0,2; -1/2,1,0,-2; 1/2,1,-2,0]
private def aCongrInv : GramMatrix := !![1/2,-1/2,-1/2,1/2; 1/4,1/4,1/4,1/4;
  1/4,0,0,-1/4; 0,1/4,-1/4,0]

private theorem aCongr_mul_inv : aCongr * aCongrInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [aCongr, aCongrInv, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

private def bCongr : GramMatrix := !![1,0,0,0; 0,1,-1/3,-2/3; 0,0,8/3,-2/3; 0,0,0,6]
private def bCongrInv : GramMatrix := !![1,0,0,0; 0,1,1/8,1/8; 0,0,3/8,1/24; 0,0,0,1/6]

private theorem first_one_sixteenth_fit (n : ℕ) :
    RealizableIn (pairedEdges (1/16)) n ↔ RealizableIn (diagonal ![1,5,7,7]) n := by
  apply fits_congr _ _ aCongr aCongrInv aCongr_mul_inv _ n
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pairedEdges, aCongr, Matrix.diagonal_apply, Matrix.transpose_apply, Matrix.mul_apply,
      Fin.sum_univ_succ]

private theorem second_one_sixteenth_fit (n : ℕ) :
    RealizableIn (triangleBlock (1/16)) n ↔ RealizableIn (diagonal ![1,1,7,35]) n := by
  apply fits_congr _ _ bCongr bCongrInv _ _ n
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [bCongr, bCongrInv, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [triangleBlock, bCongr, Matrix.diagonal_apply, Matrix.transpose_apply, Matrix.mul_apply,
        Fin.sum_univ_succ]

private theorem modular_ternary_descent
    (p a b c : ℕ) (hp : 1 < p)
    (reduce_yz : ∀ y z : ZMod p, y ^ 2 + b * z ^ 2 = 0 → y = 0 ∧ z = 0)
    (reduce_xd : ∀ x d : ZMod p, a * x ^ 2 = c * d ^ 2 → x = 0 ∧ d = 0)
    (d : ℕ) (hd : 0 < d) (x y z : ℕ) :
    p * a * x ^ 2 + y ^ 2 + b * z ^ 2 ≠ p * c * d ^ 2 := by
  induction d using Nat.strongRecOn generalizing x y z with
  | ind d ih =>
    intro h
    have hp0 : 0 < p := by omega
    have cast_p : (p : ZMod p) = 0 := ZMod.natCast_self p
    have h_yz : (y : ZMod p) ^ 2 + b * (z : ZMod p) ^ 2 = 0 := by
      have hmod := congrArg (fun n : ℕ => (n : ZMod p)) h
      push_cast at hmod
      simpa only [cast_p, zero_mul, zero_add, add_assoc] using hmod
    obtain ⟨y', hy⟩ := (ZMod.natCast_eq_zero_iff y p).mp (reduce_yz _ _ h_yz).1
    obtain ⟨z', hz⟩ := (ZMod.natCast_eq_zero_iff z p).mp (reduce_yz _ _ h_yz).2
    rw [hy, hz] at h
    have hs : p * (a * x ^ 2 + p * y' ^ 2 + p * b * z' ^ 2) = p * (c * d ^ 2) := by
      calc
        _ = p * a * x ^ 2 + (p * y') ^ 2 + b * (p * z') ^ 2 := by ring
        _ = _ := by simpa only [Nat.mul_assoc] using h
    have h' := Nat.eq_of_mul_eq_mul_left hp0 hs
    have h_xd : (a : ZMod p) * (x : ZMod p) ^ 2 = c * (d : ZMod p) ^ 2 := by
      have hmod := congrArg (fun n : ℕ => (n : ZMod p)) h'
      push_cast at hmod
      simpa only [cast_p, zero_mul, add_zero] using hmod
    obtain ⟨x', hx⟩ := (ZMod.natCast_eq_zero_iff x p).mp (reduce_xd _ _ h_xd).1
    obtain ⟨d', hd'⟩ := (ZMod.natCast_eq_zero_iff d p).mp (reduce_xd _ _ h_xd).2
    have dpos : 0 < d' := by
      by_contra! hnonpos
      have : d' = 0 := by omega
      rw [hd', this, Nat.mul_zero] at hd
      omega
    have dlt : d' < d := by
      calc
        d' = 1 * d' := by simp
        _ < p * d' := Nat.mul_lt_mul_of_pos_right hp dpos
        _ = d := hd'.symm
    rw [hx, hd'] at h'
    have hscaled : p * (p * a * x' ^ 2 + y' ^ 2 + b * z' ^ 2) = p * (p * c * d' ^ 2) := by
      calc
        _ = a * (p * x') ^ 2 + p * y' ^ 2 + p * b * z' ^ 2 := by ring
        _ = c * (p * d') ^ 2 := h'
        _ = _ := by ring
    exact ih d' dlt dpos x' y' z' (Nat.eq_of_mul_eq_mul_left hp0 hscaled)

private theorem weighted_ternary_rational_obstruction (a b c : ℕ)
    (integer_obstruction : ∀ (d : ℕ), 0 < d → ∀ x y z : ℕ,
      a * x ^ 2 + y ^ 2 + b * z ^ 2 ≠ c * d ^ 2) (x y z : ℚ) :
    (a : ℚ) * x ^ 2 + y ^ 2 + (b : ℚ) * z ^ 2 ≠ (c : ℚ) := by
  intro equation
  let d := x.den * y.den * z.den
  let A : ℤ := x.num * y.den * z.den
  let B : ℤ := y.num * x.den * z.den
  let C : ℤ := z.num * x.den * y.den
  have dx : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have dy : (y.den : ℚ) ≠ 0 := by exact_mod_cast y.den_ne_zero
  have dz : (z.den : ℚ) ≠ 0 := by exact_mod_cast z.den_ne_zero
  have hd : 0 < d := by
    simpa [d] using Nat.mul_pos (Nat.mul_pos x.den_pos y.den_pos) z.den_pos
  have hx : (A : ℚ) = x * (d : ℚ) := by
    have h : (x.num : ℚ) = x * (x.den : ℚ) := (div_eq_iff dx).mp x.num_div_den
    simp only [A,d,Int.cast_mul,Int.cast_natCast,Nat.cast_mul,h]
    ring
  have hy : (B : ℚ) = y * (d : ℚ) := by
    have h : (y.num : ℚ) = y * (y.den : ℚ) := (div_eq_iff dy).mp y.num_div_den
    simp only [B,d,Int.cast_mul,Int.cast_natCast,Nat.cast_mul,h]
    ring
  have hz : (C : ℚ) = z * (d : ℚ) := by
    have h : (z.num : ℚ) = z * (z.den : ℚ) := (div_eq_iff dz).mp z.num_div_den
    simp only [C,d,Int.cast_mul,Int.cast_natCast,Nat.cast_mul,h]
    ring
  have hq : (a : ℚ) * (A : ℚ) ^ 2 + (B : ℚ) ^ 2 + (b : ℚ) * (C : ℚ) ^ 2 =
      (c : ℚ) * (d : ℚ) ^ 2 := by
    rw [hx, hy, hz]
    linear_combination (d : ℚ) ^ 2 * equation
  have hi : (a : ℤ) * A ^ 2 + B ^ 2 + (b : ℤ) * C ^ 2 =
      (c : ℤ) * (d : ℤ) ^ 2 := by exact_mod_cast hq
  have hn : ((a * A.natAbs ^ 2 + B.natAbs ^ 2 + b * C.natAbs ^ 2 : ℕ) : ℤ) =
      ((c * d ^ 2 : ℕ) : ℤ) := by
    have cast_square (n : ℤ) : (n.natAbs : ℤ) ^ 2 = n ^ 2 := by
      exact_mod_cast (show ((n.natAbs ^ 2 : ℕ) : ℤ) = n ^ 2 by
        simpa only [pow_two] using (Int.natAbs_mul_self (a := n)))
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow] at hi ⊢
    rw [cast_square, cast_square, cast_square]
    exact hi
  exact integer_obstruction d hd _ _ _ (Int.ofNat_inj.mp hn)

private theorem modular_ternary_rational_descent
    (p a b c : ℕ) (hp : 1 < p)
    (reduce_yz : ∀ y z : ZMod p, y ^ 2 + b * z ^ 2 = 0 → y = 0 ∧ z = 0)
    (reduce_xd : ∀ x d : ZMod p, a * x ^ 2 = c * d ^ 2 → x = 0 ∧ d = 0)
    (x y z : ℚ) :
    ((p * a : ℕ) : ℚ) * x ^ 2 + y ^ 2 + (b : ℚ) * z ^ 2 ≠ ((p * c : ℕ) : ℚ) := by
  exact weighted_ternary_rational_obstruction (p * a) b (p * c)
    (modular_ternary_descent p a b c hp reduce_yz reduce_xd) x y z

/-- Finite families with the same Gram data are related by a rational dot-product isometry. -/
private theorem fin_frame_isometry {ι : Type} [Fintype ι] {n : ℕ} (a b : Fin n → ι → ℚ)
    (h : ∀ i j, a i ⬝ᵥ a j = b i ⬝ᵥ b j) :
    ∃ f : (ι → ℚ) → (ι → ℚ),
      (∀ i, f (a i) = b i) ∧ ∀ x y, f x ⬝ᵥ f y = x ⬝ᵥ y := by
  induction n with
  | zero =>
    exact ⟨id, fun i => Fin.elim0 i, fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨f, hfit, hf⟩ :=
      ih (a ∘ Fin.castSucc) (b ∘ Fin.castSucc) (fun i j => h i.castSucc j.castSucc)
    let j := Fin.last n
    obtain ⟨g, hlast, hg, hfix⟩ :=
      RationalGramOddPrime.rational_reflection_with_fixed_vectors (f (a j)) (b j)
        ((hf _ _).trans (h j j))
    refine ⟨g ∘ f, ?_, fun x y => (hg _ _).trans (hf x y)⟩
    intro i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · exact hlast
    have hk : f (a k.castSucc) = b k.castSucc := hfit k
    change g (f (a k.castSucc)) = b k.castSucc
    rw [hk]
    apply hfix
    calc
      _ = f (a j) ⬝ᵥ f (a k.castSucc) := congrArg (fun y => f (a j) ⬝ᵥ y) hk.symm
      _ = _ := (hf _ _).trans (h j k.castSucc)

private theorem no_seven_under_fixed_frame (z : Fin 6 → ℚ)
    (h0 : (![1,0,0,0,0,0] : Fin 6 → ℚ) ⬝ᵥ z = 0)
    (h1 : (![0,2,1,0,0,0] : Fin 6 → ℚ) ⬝ᵥ z = 0)
    (h2 : (![0,1,-2,1,1,0] : Fin 6 → ℚ) ⬝ᵥ z = 0) :
    z ⬝ᵥ z ≠ 7 := by
  intro h
  norm_num [dotProduct, Fin.sum_univ_succ] at h0 h1 h2 h
  have hz2 : z 2 = -2*z 1 := by linear_combination h1
  have hz34 : z 3 + z 4 = -5*z 1 := by linear_combination h2 + 2 * hz2
  apply modular_ternary_rational_descent 7 5 2 2 (by decide) (by decide) (by decide)
    (z 1) (z 3 - z 4) (z 5)
  rw [h0, hz2] at h
  have hs : (z 3 + z 4)^2 = (-5*z 1)^2 := congrArg (· ^ 2) hz34
  linear_combination 2*h - hs

private theorem no_orthogonal_1577 (u v w z : Fin 6 → ℚ)
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 5) (hw : w ⬝ᵥ w = 7) (hz : z ⬝ᵥ z = 7)
    (huv : u ⬝ᵥ v = 0) (huw : u ⬝ᵥ w = 0) (huz : u ⬝ᵥ z = 0)
    (hvw : v ⬝ᵥ w = 0) (hvz : v ⬝ᵥ z = 0) (hwz : w ⬝ᵥ z = 0) : False := by
  let b₀ : Fin 6 → ℚ := ![1,0,0,0,0,0]
  let b₁ : Fin 6 → ℚ := ![0,2,1,0,0,0]
  let b₂ : Fin 6 → ℚ := ![0,1,-2,1,1,0]
  let earlier : Fin 3 → Fin 6 → ℚ := ![u,v,w]
  let standard : Fin 3 → Fin 6 → ℚ := ![b₀,b₁,b₂]
  have hgram (i j : Fin 3) : earlier i ⬝ᵥ earlier j = standard i ⬝ᵥ standard j := by
    have hvu := (dotProduct_comm v u).trans huv
    have hwu := (dotProduct_comm w u).trans huw
    have hwv := (dotProduct_comm w v).trans hvw
    norm_num [dotProduct, Fin.sum_univ_succ] at hu hv hw huv huw hvw hvu hwu hwv
    fin_cases i <;> fin_cases j <;>
      norm_num [earlier, standard, b₀, b₁, b₂, dotProduct, Fin.sum_univ_succ] <;> assumption
  obtain ⟨f, hfit, hf⟩ := fin_frame_isometry earlier standard hgram
  have preserve_left (i : Fin 3) : standard i ⬝ᵥ f z = earlier i ⬝ᵥ z := by
    rw [← hfit i, hf]
  have h0 : b₀ ⬝ᵥ f z = 0 := (preserve_left 0).trans huz
  have h1 : b₁ ⬝ᵥ f z = 0 := (preserve_left 1).trans hvz
  have h2 : b₂ ⬝ᵥ f z = 0 := (preserve_left 2).trans hwz
  exact no_seven_under_fixed_frame (f z) h0 h1 h2 ((hf _ _).trans hz)

private theorem first_one_sixteenth_not_six : ¬ RealizableIn (pairedEdges (1/16)) 6 := by
  intro h
  obtain ⟨X, hX⟩ := (first_one_sixteenth_fit 6).mp h
  have entry (i j : Fin 4) : (X i) ⬝ᵥ (X j) = (diagonal ![1,5,7,7] : GramMatrix) i j :=
    congrFun (congrFun hX i) j
  apply no_orthogonal_1577 (X 0) (X 1) (X 2) (X 3)
  all_goals (first
    | simpa [diagonal_apply] using entry 0 0
    | simpa [diagonal_apply] using entry 1 1
    | simpa [diagonal_apply] using entry 2 2
    | simpa [diagonal_apply] using entry 3 3
    | simpa [diagonal_apply] using entry 0 1
    | simpa [diagonal_apply] using entry 0 2
    | simpa [diagonal_apply] using entry 0 3
    | simpa [diagonal_apply] using entry 1 2
    | simpa [diagonal_apply] using entry 1 3
    | simpa [diagonal_apply] using entry 2 3)

private theorem square_mod_four (n : ℕ) : n ^ 2 % 4 = n % 2 := by
  exact_mod_cast Int.sq_emod_four (n : ℤ)

private theorem square_mod_eight_odd (n : ℕ) (hodd : n % 2 = 1) : n ^ 2 % 8 = 1 := by
  have h : Odd (n : ℤ) := Int.odd_iff.mpr (by exact_mod_cast hodd)
  have hmod : (1 : ℤ) ≡ (n : ℤ) ^ 2 [ZMOD 8] :=
    Int.modEq_of_dvd (Int.eight_dvd_sq_sub_one_of_odd h)
  have hm : (n : ℤ) ^ 2 % 8 = 1 := by simpa [Int.ModEq] using hmod.symm
  exact_mod_cast hm

private theorem square_mod_eight (n : ℕ) : n ^ 2 % 8 = 0 ∨ n ^ 2 % 8 = 1 ∨ n ^ 2 % 8 = 4 := by
  have hs := Nat.pow_mod n 2 8
  rw [hs]
  have h : n % 8 < 8 := Nat.mod_lt _ (by decide)
  interval_cases (n % 8) <;> decide

private theorem weighted_dyadic_descent (a b c : ℕ) (ha : a % 4 = 1) (hb : b % 4 = 1)
    (odd_obstruction : ∀ x y z : ℕ, (a * x ^ 2 + y ^ 2 + b * z ^ 2) % 8 ≠ c % 8)
    (d : ℕ) (hd : 0 < d) : ∀ x y z : ℕ, a * x ^ 2 + y ^ 2 + b * z ^ 2 ≠ c * d ^ 2 := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro x y z equality
    by_cases dodd : d % 2 = 1
    · have residues := congrArg (· % 8) equality
      rw [Nat.mul_mod c, square_mod_eight_odd d dodd, mul_one, Nat.mod_mod] at residues
      exact odd_obstruction x y z residues
    · have de : d % 2 = 0 := by omega
      have residues := congrArg (· % 4) equality
      rw [Nat.add_mod (a * x ^ 2 + y ^ 2), Nat.add_mod (a * x ^ 2),
        Nat.mul_mod a, Nat.mul_mod b, Nat.mul_mod c,
        square_mod_four, square_mod_four, square_mod_four, square_mod_four, ha, hb, de] at residues
      have xe : x = 2 * (x / 2) := by omega
      have ye : y = 2 * (y / 2) := by omega
      have ze : z = 2 * (z / 2) := by omega
      have de' : d = 2 * (d / 2) := by omega
      apply ih (d / 2) (by omega) (by omega) (x / 2) (y / 2) (z / 2)
      have scaled : 4 * (a * (x / 2) ^ 2 + (y / 2) ^ 2 + b * (z / 2) ^ 2) =
          4 * (c * (d / 2) ^ 2) := by
        calc
          _ = a * (2 * (x / 2)) ^ 2 + (2 * (y / 2)) ^ 2 + b * (2 * (z / 2)) ^ 2 := by ring
          _ = c * (2 * (d / 2)) ^ 2 := by rw [← xe, ← ye, ← ze, ← de', equality]
          _ = _ := by ring
      omega

private theorem no_seven_scaled_squares (d : ℕ) (hd : 0 < d) :
    ∀ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 ≠ 7 * d ^ 2 := by
  have odd_obstruction (x y z : ℕ) : (1 * x ^ 2 + y ^ 2 + 1 * z ^ 2) % 8 ≠ 7 % 8 := by
    intro equality
    rw [one_mul, one_mul, Nat.add_mod (x ^ 2 + y ^ 2), Nat.add_mod (x ^ 2)] at equality
    rcases square_mod_eight x with hx | hx | hx <;>
      rcases square_mod_eight y with hy | hy | hy <;>
      rcases square_mod_eight z with hz | hz | hz <;>
      simp [hx, hy, hz] at equality
  simpa using weighted_dyadic_descent 1 1 7 (by decide) (by decide) odd_obstruction d hd

private theorem seven_not_three_rational_squares (x y z : ℚ) :
    x ^ 2 + y ^ 2 + z ^ 2 ≠ 7 := by
  have obstruction (d : ℕ) (hd : 0 < d) (X Y Z : ℕ) :
      1 * X ^ 2 + Y ^ 2 + 1 * Z ^ 2 ≠ 7 * d ^ 2 := by
    simpa using no_seven_scaled_squares d hd X Y Z
  simpa using weighted_ternary_rational_obstruction 1 1 7 obstruction x y z

private theorem no_orthogonal_117_in_five (u v w : Fin 5 → ℚ)
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (hw : w ⬝ᵥ w = 7)
    (huv : u ⬝ᵥ v = 0) (huw : u ⬝ᵥ w = 0) (hvw : v ⬝ᵥ w = 0) : False := by
  let b₀ : Fin 5 → ℚ := ![1,0,0,0,0]
  let b₁ : Fin 5 → ℚ := ![0,1,0,0,0]
  let earlier : Fin 2 → Fin 5 → ℚ := ![u,v]
  let standard : Fin 2 → Fin 5 → ℚ := ![b₀,b₁]
  have hgram (i j : Fin 2) : earlier i ⬝ᵥ earlier j = standard i ⬝ᵥ standard j := by
    have hvu := (dotProduct_comm v u).trans huv
    norm_num [dotProduct, Fin.sum_univ_succ] at hu hv huv hvu
    fin_cases i <;> fin_cases j <;>
      norm_num [earlier, standard, b₀, b₁, dotProduct, Fin.sum_univ_succ] <;> assumption
  obtain ⟨f, hfit, hf⟩ := fin_frame_isometry earlier standard hgram
  let y := f w
  have preserve_left (i : Fin 2) : standard i ⬝ᵥ y = earlier i ⬝ᵥ w := by
    rw [← hfit i, show y = f w from rfl, hf]
  have hy₀ : b₀ ⬝ᵥ y = 0 := (preserve_left 0).trans huw
  have hy₁ : b₁ ⬝ᵥ y = 0 := (preserve_left 1).trans hvw
  have hy_sq : y ⬝ᵥ y = 7 := (hf _ _).trans hw
  norm_num [b₀, b₁, dotProduct, Fin.sum_univ_succ] at hy₀ hy₁ hy_sq
  apply seven_not_three_rational_squares (y 2) (y 3) (y 4)
  rw [hy₀, hy₁] at hy_sq
  linear_combination hy_sq

private theorem second_one_sixteenth_not_five : ¬ RealizableIn (triangleBlock (1/16)) 5 := by
  intro h
  obtain ⟨X, hX⟩ := (second_one_sixteenth_fit 5).mp h
  have entry (i j : Fin 4) : (X i) ⬝ᵥ (X j) = (diagonal ![1,1,7,35] : GramMatrix) i j :=
    congrFun (congrFun hX i) j
  apply no_orthogonal_117_in_five (X 0) (X 1) (X 2)
  all_goals (first
    | simpa [diagonal_apply] using entry 0 0
    | simpa [diagonal_apply] using entry 1 1
    | simpa [diagonal_apply] using entry 2 2
    | simpa [diagonal_apply] using entry 0 1
    | simpa [diagonal_apply] using entry 0 2
    | simpa [diagonal_apply] using entry 1 2)

private theorem fits_mono {G : GramMatrix} {m n : ℕ} (hmn : m ≤ n) (hG : RealizableIn G m) :
    RealizableIn G n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨X, hX⟩ := hG
  refine ⟨fun i => Fin.append (X i) (fun _ => 0), ?_⟩
  ext i j
  have e := congrFun (congrFun hX i) j
  change (∑ l : Fin (m + k), Fin.append (X i) (fun _ => (0 : ℚ)) l *
    Fin.append (X j) (fun _ => (0 : ℚ)) l) = G i j
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_add] using e

private theorem thresholds_at_base (n : ℕ) :
    (RealizableIn (pairedEdges (1/16)) n ↔ 7 ≤ n) ∧ (RealizableIn (triangleBlock (1/16)) n ↔ 6 ≤ n) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h
    by_contra! hn
    exact first_one_sixteenth_not_six (fits_mono (by omega) h)
  · intro hn
    apply fits_mono hn
    apply (first_one_sixteenth_fit 7).mpr
    refine ⟨!![1,0,0,0,0,0,0; 0,2,1,0,0,0,0; 0,1,-2,1,1,0,0; 0,0,0,1,-1,1,2], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.diagonal_apply, Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_succ]
  · intro h
    by_contra! hn
    exact second_one_sixteenth_not_five (fits_mono (by omega) h)
  · intro hn
    apply fits_mono hn
    apply (second_one_sixteenth_fit 6).mpr
    refine ⟨!![1,0,0,0,0,0; 0,1,0,0,0,0; 0,0,2,1,1,1; 0,0,3,-5,-1,0], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.diagonal_apply, Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem decompose_first (t : ℚ) :
    aCongrᵀ * pairedEdges t * aCongr = diagonal ![1,4*(1+4*t),8*(1-2*t),8*(1-2*t)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pairedEdges, aCongr, Matrix.diagonal_apply, Matrix.transpose_apply,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem decompose_second (t : ℚ) :
    bBasisᵀ * triangleBlock t * bBasis = diagonal ![3*(1+4*t),1,2*(1-2*t),6*(1-2*t)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [triangleBlock, bBasis, Matrix.diagonal_apply, Matrix.transpose_apply,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem diag_scaling (e f g : Fin 4 → ℚ) (hn : ∀ i, e i ≠ 0)
    (h : ∀ i, e i ^ 2 * f i = g i) (n : ℕ) :
    RealizableIn (diagonal f) n ↔ RealizableIn (diagonal g) n := by
  apply fits_congr _ _ (diagonal e) (diagonal fun i => (e i)⁻¹) _ _ n
  · rw [diagonal_mul_diagonal, ← diagonal_one]
    congr
    funext i
    exact mul_inv_cancel₀ (hn i)
  · rw [diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr
    funext i
    rw [← h i]
    ring

private theorem first_family_fit (t u v : ℚ) (hu : u ≠ 0) (hv : v ≠ 0)
    (htu : 1+4*t = 5*u^2) (htv : 1-2*t = 7/2*v^2) (n : ℕ) :
    RealizableIn (pairedEdges t) n ↔ RealizableIn (diagonal ![1,5,7,7]) n := by
  refine (fits_congr _ _ aCongr aCongrInv aCongr_mul_inv (decompose_first t) n).trans ?_
  apply diag_scaling ![1,(2*u)⁻¹,(2*v)⁻¹,(2*v)⁻¹]
  · intro i
    fin_cases i <;> simp [hu, hv]
  · intro i
    fin_cases i <;> simp [htu, htv] <;> field_simp <;> ring

private theorem second_family_fit (t u v : ℚ) (hu : u ≠ 0) (hv : v ≠ 0)
    (htu : 1+4*t = 5*u^2) (htv : 1-2*t = 7/2*v^2) (n : ℕ) :
    RealizableIn (triangleBlock t) n ↔ RealizableIn (diagonal ![15,1,7,21]) n := by
  refine (fits_congr _ _ bBasis bInv bBasis_mul_inv (decompose_second t) n).trans ?_
  apply diag_scaling ![u⁻¹,1,v⁻¹,v⁻¹]
  · intro i
    fin_cases i <;> simp [hu, hv]
  · intro i
    fin_cases i <;> simp [htu, htv] <;> field_simp <;> ring

/-- One rational similarity works for the whole family and preserves the displayed
characteristic polynomial. On the conic the coordinate minima are seven and six. -/
theorem spectrum_and_thresholds :
    ((∃ P : GramMatrix, P.det ≠ 0 ∧ ∀ t : ℚ, pairedEdges t * P = P * triangleBlock t) ∧
    ∀ t : ℚ, (pairedEdges t).charpoly = (triangleBlock t).charpoly ∧
      (pairedEdges t).charpoly =
        (Polynomial.X - Polynomial.C (1 + 4 * t)) * (Polynomial.X - 1) *
          (Polynomial.X - Polynomial.C (1 - 2 * t)) ^ 2) ∧
    ∀ (u v : ℚ), 5*u^2 + 7*v^2 = 3 → ∀ n : ℕ,
      let t := (5*u^2-1)/4
      (RealizableIn (pairedEdges t) n ↔ 7 ≤ n) ∧ (RealizableIn (triangleBlock t) n ↔ 6 ≤ n) := by
  refine ⟨⟨simultaneous_similarity, gram_pair_cospectral⟩, ?_⟩
  intro u v h n
  dsimp only
  have hu : u ≠ 0 := by
    intro hz
    have he : v ^ 2 = 3 / 7 := by
      rw [hz] at h
      linear_combination h / 7
    have hs : IsSquare (3 / 7 : ℚ) := ⟨v, by rw [← he, pow_two]⟩
    have hn : (3 / 7 : ℚ).num = 3 :=
      Rat.num_div_eq_of_coprime (a := 3) (b := 7) (by decide) (by decide)
    exact Int.prime_three.not_isSquare (hn ▸ (Rat.isSquare_iff.mp hs).1)
  have hv : v ≠ 0 := by
    intro hz
    have he : u ^ 2 = 3 / 5 := by
      rw [hz] at h
      linear_combination h / 5
    have hs : IsSquare (3 / 5 : ℚ) := ⟨u, by rw [← he, pow_two]⟩
    have hn : (3 / 5 : ℚ).num = 3 :=
      Rat.num_div_eq_of_coprime (a := 3) (b := 5) (by decide) (by decide)
    exact Int.prime_three.not_isSquare (hn ▸ (Rat.isSquare_iff.mp hs).1)
  let t := (5*u^2-1)/4
  have h₁ : 1+4*t = 5*u^2 := by dsimp [t]; ring
  have h₂ : 1-2*t = 7/2*v^2 := by dsimp [t]; linear_combination -h/2
  have bb : RealizableIn (triangleBlock (1/16)) n ↔ RealizableIn (diagonal ![15,1,7,21]) n :=
    second_family_fit (1/16) (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) n
  exact ⟨(first_family_fit t u v hu hv h₁ h₂ n).trans
      ((first_one_sixteenth_fit n).symm.trans (thresholds_at_base n).1),
    (second_family_fit t u v hu hv h₁ h₂ n).trans (bb.symm.trans (thresholds_at_base n).2)⟩

private theorem three_not_five_sq_add_two_sq (x y z : ℚ) :
    5 * x ^ 2 + y ^ 2 + z ^ 2 ≠ 3 := by
  have odd_obstruction (X Y Z : ℕ) : (5 * X ^ 2 + Y ^ 2 + 1 * Z ^ 2) % 8 ≠ 3 % 8 := by
    intro he
    have reduced := congrArg (fun n : ℕ => (n : ZMod 8)) he
    rw [ZMod.natCast_mod, ZMod.natCast_mod] at reduced
    push_cast at reduced
    exact (by decide : ∀ a b c : ZMod 8, 5 * a ^ 2 + b ^ 2 + 1 * c ^ 2 ≠ 3) _ _ _ reduced
  simpa using weighted_ternary_rational_obstruction 5 1 3
    (weighted_dyadic_descent 5 1 3 (by decide) (by decide) odd_obstruction) x y z

private theorem no_orthogonal_1153_in_six (u v w z : Fin 6 → ℚ)
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (hw : w ⬝ᵥ w = 5) (hz : z ⬝ᵥ z = 3)
    (huv : u ⬝ᵥ v = 0) (huw : u ⬝ᵥ w = 0) (huz : u ⬝ᵥ z = 0)
    (hvw : v ⬝ᵥ w = 0) (hvz : v ⬝ᵥ z = 0) (hwz : w ⬝ᵥ z = 0) : False := by
  let b₀ : Fin 6 → ℚ := ![1,0,0,0,0,0]
  let b₁ : Fin 6 → ℚ := ![0,1,0,0,0,0]
  let b₂ : Fin 6 → ℚ := ![0,0,2,1,0,0]
  let earlier : Fin 3 → Fin 6 → ℚ := ![u,v,w]
  let standard : Fin 3 → Fin 6 → ℚ := ![b₀,b₁,b₂]
  have hgram (i j : Fin 3) : earlier i ⬝ᵥ earlier j = standard i ⬝ᵥ standard j := by
    have hvu := (dotProduct_comm v u).trans huv
    have hwu := (dotProduct_comm w u).trans huw
    have hwv := (dotProduct_comm w v).trans hvw
    norm_num [dotProduct, Fin.sum_univ_succ] at hu hv hw huv huw hvw hvu hwu hwv
    fin_cases i <;> fin_cases j <;>
      norm_num [earlier, standard, b₀, b₁, b₂, dotProduct, Fin.sum_univ_succ] <;> assumption
  obtain ⟨f, hfit, hf⟩ := fin_frame_isometry earlier standard hgram
  let y := f z
  have preserve_left (i : Fin 3) : standard i ⬝ᵥ y = earlier i ⬝ᵥ z := by
    rw [← hfit i, show y = f z from rfl, hf]
  have h0 : b₀ ⬝ᵥ y = 0 := (preserve_left 0).trans huz
  have h1 : b₁ ⬝ᵥ y = 0 := (preserve_left 1).trans hvz
  have h2 : b₂ ⬝ᵥ y = 0 := (preserve_left 2).trans hwz
  have hnorm : y ⬝ᵥ y = 3 := (hf _ _).trans hz
  norm_num [b₀, b₁, b₂, dotProduct, Fin.sum_univ_succ] at h0 h1 h2 hnorm
  have h3 : y 3 = -2 * y 2 := by linear_combination h2
  rw [h0, h1, h3] at hnorm
  apply three_not_five_sq_add_two_sq (y 2) (y 4) (y 5)
  linear_combination hnorm

private theorem one_sixth_triangle_not_six : ¬ RealizableIn (triangleBlock (1/6)) 6 := by
  intro h
  have hdiag : RealizableIn (triangleBlock (1/6)) 6 ↔
      RealizableIn (diagonal ![5,1,3,1]) 6 := by
    refine (fits_congr _ _ bBasis bInv bBasis_mul_inv (decompose_second (1/6)) 6).trans ?_
    apply diag_scaling ![1,1,3/2,1/2]
    · intro i
      fin_cases i <;> norm_num
    · intro i
      fin_cases i <;> norm_num
  obtain ⟨X,hX⟩ := hdiag.mp h
  have entry (i j : Fin 4) : X i ⬝ᵥ X j = (diagonal ![5,1,3,1] : Matrix (Fin 4) (Fin 4) ℚ) i j :=
    congrFun (congrFun hX i) j
  apply no_orthogonal_1153_in_six (X 1) (X 3) (X 0) (X 2)
  all_goals (first
    | simpa [diagonal_apply] using entry 0 0
    | simpa [diagonal_apply] using entry 1 1
    | simpa [diagonal_apply] using entry 2 2
    | simpa [diagonal_apply] using entry 3 3
    | simpa [diagonal_apply] using entry 1 3
    | simpa [diagonal_apply] using entry 1 0
    | simpa [diagonal_apply] using entry 1 2
    | simpa [diagonal_apply] using entry 3 0
    | simpa [diagonal_apply] using entry 3 2
    | simpa [diagonal_apply] using entry 0 2)


private theorem one_sixth_matching_not_four : ¬ RealizableIn (pairedEdges (1/6)) 4 := by
  rintro ⟨X, hX⟩
  have h := congrArg Matrix.det hX
  rw [Matrix.det_mul, Matrix.det_transpose] at h
  have hc := spectrum_and_thresholds.1.2 (1/6)
  have hpol := congrArg (Polynomial.eval (0 : ℚ)) hc.2
  have hdet : (pairedEdges (1/6)).det = 20/27 := by
    norm_num [Matrix.eval_charpoly, Matrix.det_neg, Fintype.card_fin] at hpol
    exact hpol
  have hs : IsSquare (20/27 : ℚ) := ⟨X.det, hdet.symm.trans h.symm⟩
  have hn : (20/27 : ℚ).num = 20 := Rat.num_div_eq_of_coprime (a := 20) (b := 27) (by decide) (by decide)
  obtain ⟨n, hn'⟩ := hn ▸ (Rat.isSquare_iff.mp hs).1
  have hmod := congrArg (fun v : ℤ => (v : ZMod 3)) hn'
  push_cast at hmod
  exact (by decide : ∀ n : ZMod 3, (20 : ZMod 3) ≠ n * n) _ hmod

private theorem one_sixth_matching_five : RealizableIn (pairedEdges (1/6)) 5 := by
  refine ⟨!![1/2,0,1/6,5/6,1/6; -1/2,0,-1/2,1/2,1/2;
    -1/2,-2/3,1/6,1/2,-1/6; 1/2,-2/3,-1/2,1/6,1/6], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pairedEdges, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]

private theorem one_sixth_triangle_seven : RealizableIn (triangleBlock (1/6)) 7 := by
  refine ⟨!![1,0,0,0,0,0,0; 0,1/3,2/3,1/3,1/3,1/3,1/3;
    0,1/3,2/3,1/3,-1/3,-1/3,-1/3; 0,-2/3,2/3,1/3,0,0,0], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [triangleBlock, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]

private theorem thresholds_at_one_sixth (n : ℕ) :
    (RealizableIn (pairedEdges (1/6)) n ↔ 5 ≤ n) ∧
    (RealizableIn (triangleBlock (1/6)) n ↔ 7 ≤ n) := by
  constructor
  · refine ⟨fun h => ?_, fun hn => fits_mono hn one_sixth_matching_five⟩
    by_contra hn
    exact one_sixth_matching_not_four (fits_mono (by omega) h)
  · refine ⟨fun h => ?_, fun hn => fits_mono hn one_sixth_triangle_seven⟩
    by_contra hn
    exact one_sixth_triangle_not_six (fits_mono (by omega) h)


private theorem matching_same_square_classes (s t u v : ℚ) (hu : u ≠ 0) (hv : v ≠ 0)
    (h₁ : 1 + 4 * t = (1 + 4 * s) * u ^ 2)
    (h₂ : 1 - 2 * t = (1 - 2 * s) * v ^ 2) (n : ℕ) :
    RealizableIn (pairedEdges t) n ↔ RealizableIn (pairedEdges s) n := by
  refine (fits_congr _ _ aCongr aCongrInv aCongr_mul_inv (decompose_first t) n).trans
    (Iff.trans ?_ (fits_congr _ _ aCongr aCongrInv aCongr_mul_inv (decompose_first s) n).symm)
  apply diag_scaling ![1, u⁻¹, v⁻¹, v⁻¹]
  · intro i
    fin_cases i <;> simp [hu, hv]
  · intro i
    fin_cases i <;> simp [h₁, h₂] <;> field_simp <;> ring

private theorem triangle_same_square_classes (s t u v : ℚ) (hu : u ≠ 0) (hv : v ≠ 0)
    (h₁ : 1 + 4 * t = (1 + 4 * s) * u ^ 2)
    (h₂ : 1 - 2 * t = (1 - 2 * s) * v ^ 2) (n : ℕ) :
    RealizableIn (triangleBlock t) n ↔ RealizableIn (triangleBlock s) n := by
  refine (fits_congr _ _ bBasis bInv bBasis_mul_inv (decompose_second t) n).trans
    (Iff.trans ?_ (fits_congr _ _ bBasis bInv bBasis_mul_inv (decompose_second s) n).symm)
  apply diag_scaling ![u⁻¹, 1, v⁻¹, v⁻¹]
  · intro i
    fin_cases i <;> simp [hu, hv]
  · intro i
    fin_cases i <;> simp [h₁, h₂] <;> field_simp <;> ring

/-- The conic through (1, 1) gives a family with rational coordinate minima five and seven. -/
theorem five_seven_on_conic (u v : ℚ) (hu : u ≠ 0) (h : 5 * u ^ 2 + 4 * v ^ 2 = 9)
    (n : ℕ) :
    let t := (5 * u ^ 2 / 3 - 1) / 4
    (RealizableIn (pairedEdges t) n ↔ 5 ≤ n) ∧
      (RealizableIn (triangleBlock t) n ↔ 7 ≤ n) := by
  have hv : v ≠ 0 := by
    intro hz
    rw [hz] at h
    have hsq : IsSquare (5 : ℚ) := ⟨5 * u / 3, by
      rw [← sq]
      linear_combination -5 / 9 * h⟩
    have hnat : IsSquare (5 : ℕ) := Rat.isSquare_natCast_iff.mp hsq
    exact (Nat.prime_five.not_isSquare hnat)
  let t := (5 * u ^ 2 / 3 - 1) / 4
  have h₁ : 1 + 4 * t = (1 + 4 * (1/6 : ℚ)) * u ^ 2 := by
    dsimp [t]
    ring
  have h₂ : 1 - 2 * t = (1 - 2 * (1/6 : ℚ)) * v ^ 2 := by
    dsimp [t]
    linear_combination -h / 6
  exact ⟨(matching_same_square_classes (1/6) t u v hu hv h₁ h₂ n).trans
      (thresholds_at_one_sixth n).1,
    (triangle_same_square_classes (1/6) t u v hu hv h₁ h₂ n).trans
      (thresholds_at_one_sixth n).2⟩

end D5.S3.Quantum.AURICOmega.RationalGramCospectral
