/- GID: D5/S3/Quantum/AURICOmega/RationalGramOddPrime
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/RationalGramOddPrime
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A rank-four rational unit Gram matrix needs seven rational coordinates by a mod-three obstruction. -/

import D5.S3.Combinatorics.Geometry.EuclideanSimplex.RationalUnitSimplex
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace D5.S3.Quantum.AURICOmega.RationalGramOddPrime

open Matrix
open D5.S3.Combinatorics.Geometry.EuclideanSimplex.RationalUnitSimplex (rational_unit_reflection)

set_option autoImplicit false

private theorem three_divides_of_zmod {x : ℕ} (h : (x : ZMod 3) = 0) : 3 ∣ x :=
  (ZMod.natCast_eq_zero_iff x 3).mp h

private theorem no_scaled_three (d : ℕ) (hd : 0 < d) :
    ∀ x y z : ℕ, 6 * x ^ 2 + y ^ 2 + z ^ 2 ≠ 3 * d ^ 2 := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro x y z h
    -- The first reduction forces both unweighted coordinates to be divisible by three.
    have hf : ∀ a b : ZMod 3, a ^ 2 + b ^ 2 = 0 → a = 0 ∧ b = 0 := by decide
    have h₃ : (3 : ZMod 3) = 0 := by decide
    have h₆ : (6 : ZMod 3) = 0 := by decide
    have hYZ : (y : ZMod 3) ^ 2 + (z : ZMod 3) ^ 2 = 0 := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, h₃, h₆, zero_mul,
        zero_add] using congrArg (fun n : ℕ => (n : ZMod 3)) h
    obtain ⟨y', hy⟩ := three_divides_of_zmod (hf _ _ hYZ).1
    obtain ⟨z', hz⟩ := three_divides_of_zmod (hf _ _ hYZ).2
    rw [hy, hz] at h
    have hs : 3 * (2 * x ^ 2 + 3 * y' ^ 2 + 3 * z' ^ 2) = 3 * d ^ 2 := by
      calc
        _ = 6 * x ^ 2 + (3 * y') ^ 2 + (3 * z') ^ 2 := by ring
        _ = _ := h
    have h' : 2 * x ^ 2 + 3 * y' ^ 2 + 3 * z' ^ 2 = d ^ 2 := by omega
    -- Divide by three, then test the remaining coordinate and denominator.
    have hg : ∀ a b : ZMod 3, 2*a ^ 2 = b ^ 2 → a = 0 ∧ b = 0 := by decide
    have hXD : 2*(x : ZMod 3) ^ 2 = (d : ZMod 3) ^ 2 := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, h₃, zero_mul,
        add_zero] using congrArg (fun n : ℕ => (n : ZMod 3)) h'
    obtain ⟨x', hx⟩ := three_divides_of_zmod (hg _ _ hXD).1
    obtain ⟨d', hd'⟩ := three_divides_of_zmod (hg _ _ hXD).2
    have dpos : 0 < d' := by omega
    have dlt : d' < d := by omega
    apply ih d' dlt dpos x' y' z'
    rw [hx, hd'] at h'
    have hscaled : 3 * (6 * x' ^ 2 + y' ^ 2 + z' ^ 2) = 3 * (3 * d' ^ 2) := by
      calc
        _ = 2*(3*x') ^ 2 + 3 * y' ^ 2 + 3 * z' ^ 2 := by ring
        _ = (3 * d') ^ 2 := h'
        _ = _ := by ring
    omega

private theorem three_not_six_square_add_two_squares (x y z : ℚ) :
    6 * x ^ 2 + y ^ 2 + z ^ 2 ≠ 3 := by
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
  have hq : 6*(A : ℚ) ^ 2 + (B : ℚ) ^ 2 + (C : ℚ) ^ 2 = 3*(d : ℚ) ^ 2 := by
    rw [hx, hy, hz]
    linear_combination (d : ℚ) ^ 2 * equation
  have hi : 6*A ^ 2 + B ^ 2 + C ^ 2 = 3*(d : ℤ) ^ 2 := by exact_mod_cast hq
  have hn : ((6*A.natAbs ^ 2 + B.natAbs ^ 2 + C.natAbs ^ 2 : ℕ) : ℤ) =
      ((3 * d ^ 2 : ℕ) : ℤ) := by
    have cast_square (n : ℤ) : ((n.natAbs ^ 2 : ℕ) : ℤ) = n ^ 2 := by
      simpa only [pow_two] using (Int.natAbs_mul_self (a := n))
    rw [Int.natCast_add, Int.natCast_add, Int.natCast_mul, cast_square, cast_square, cast_square]
    exact_mod_cast hi
  exact no_scaled_three d hd _ _ _ (Int.ofNat_inj.mp hn)

private theorem rational_reflection_with_fixed_vectors {ι : Type} [Fintype ι]
    (a b : ι → ℚ) (hab : a ⬝ᵥ a = b ⬝ᵥ b) :
    ∃ f : (ι → ℚ) → (ι → ℚ), f a = b ∧ (∀ x y, f x ⬝ᵥ f y = x ⬝ᵥ y) ∧
      ∀ x, a ⬝ᵥ x = b ⬝ᵥ x → f x = x := by
  by_cases h : a = b
  · exact ⟨id, h, fun _ _ => rfl, fun _ _ => rfl⟩
  let u := a - b
  let d := u ⬝ᵥ u
  have hd : d ≠ 0 := fun hz => h (sub_eq_zero.mp (dotProduct_self_eq_zero.mp hz))
  let coef := fun x : ι → ℚ => 2 * (u ⬝ᵥ x) / d
  let reflect := fun x : ι → ℚ => x - coef x • u
  have hdouble : d = 2 * (u ⬝ᵥ a) := by
    simp only [d, u, dotProduct_sub, sub_dotProduct, ← hab, dotProduct_comm a b]
    ring
  refine ⟨reflect, ?_, ?_, ?_⟩
  · have hc : coef a = 1 := by
      dsimp only [coef]
      rw [← hdouble, div_self hd]
    rw [show reflect a = a - coef a • u from rfl, hc, one_smul]
    simp [u]
  · intro x y
    change (x - coef x • u) ⬝ᵥ (y - coef y • u) = x ⬝ᵥ y
    simp only [dotProduct_sub, sub_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm x u]
    change x ⬝ᵥ y - coef x * (u ⬝ᵥ y) - coef y * (u ⬝ᵥ x - coef x * d) = x ⬝ᵥ y
    dsimp only [coef]
    field_simp [hd]
    ring
  · intro x hx
    change x - coef x • u = x
    simp [coef, u, sub_dotProduct, hx]

private theorem no_vector_in_six_with_frame
    (v : Fin 6 → ℚ)
    (h₀ : (![1, 0, 0, 0, 0, 0] : Fin 6 → ℚ) ⬝ᵥ v = 0)
    (h₁ : (![0, 1, 1, 0, 0, 0] : Fin 6 → ℚ) ⬝ᵥ v = 0)
    (h₂ : (![0, 1, -1, 1, 0, 0] : Fin 6 → ℚ) ⬝ᵥ v = 0) :
    v ⬝ᵥ v ≠ 3 := by
  intro hv
  norm_num [dotProduct, Fin.sum_univ_succ] at h₀ h₁ h₂ hv
  have c₁ : v 2 = -v 1 := by linear_combination h₁
  have c₂ : v 3 = -2 * v 1 := by linear_combination h₂ + c₁
  exact three_not_six_square_add_two_squares (v 1) (v 4) (v 5) (by
    rw [h₀, c₁, c₂] at hv
    linear_combination hv)

private theorem no_rational_orthogonal_diagonal_1233_in_six
    (u v w z : Fin 6 → ℚ)
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 2) (hw : w ⬝ᵥ w = 3) (hz : z ⬝ᵥ z = 3)
    (huv : u ⬝ᵥ v = 0) (huw : u ⬝ᵥ w = 0) (huz : u ⬝ᵥ z = 0)
    (hvw : v ⬝ᵥ w = 0) (hvz : v ⬝ᵥ z = 0) (hwz : w ⬝ᵥ z = 0) : False := by
  let b₀ : Fin 6 → ℚ := ![1, 0, 0, 0, 0, 0]
  let b₁ : Fin 6 → ℚ := ![0, 1, 1, 0, 0, 0]
  let b₂ : Fin 6 → ℚ := ![0, 1, -1, 1, 0, 0]
  have h₀₀ : b₀ ⬝ᵥ b₀ = 1 := by norm_num [b₀, dotProduct, Fin.sum_univ_succ]
  have h₁₁ : b₁ ⬝ᵥ b₁ = 2 := by norm_num [b₁, dotProduct, Fin.sum_univ_succ]
  have h₂₂ : b₂ ⬝ᵥ b₂ = 3 := by norm_num [b₂, dotProduct, Fin.sum_univ_succ]
  have h₀₁ : b₀ ⬝ᵥ b₁ = 0 := by norm_num [b₀, b₁, dotProduct, Fin.sum_univ_succ]
  have h₀₂ : b₀ ⬝ᵥ b₂ = 0 := by norm_num [b₀, b₂, dotProduct, Fin.sum_univ_succ]
  have h₁₂ : b₁ ⬝ᵥ b₂ = 0 := by norm_num [b₁, b₂, dotProduct, Fin.sum_univ_succ]
  obtain ⟨F, hFu, hF⟩ := rational_unit_reflection u b₀ hu h₀₀
  obtain ⟨G, hGv, hG, hGfix⟩ :=
    rational_reflection_with_fixed_vectors (F v) b₁
      ((hF v v).trans (hv.trans h₁₁.symm))
  have hG₀ : G b₀ = b₀ := hGfix _ (by rw [dotProduct_comm (F v), ← hFu, hF, huv, hFu,
    dotProduct_comm b₁, h₀₁])
  obtain ⟨H, hHw, hH, hHfix⟩ :=
    rational_reflection_with_fixed_vectors (G (F w)) b₂
      ((hG _ _).trans ((hF w w).trans (hw.trans h₂₂.symm)))
  have hH₀ : H b₀ = b₀ := hHfix _ (by
    rw [dotProduct_comm (G (F w)), ← hG₀, hG, ← hFu, hF, huw, hFu, hG₀,
      dotProduct_comm b₂, h₀₂])
  have hH₁ : H b₁ = b₁ := hHfix _ (by
    rw [dotProduct_comm (G (F w)), ← hGv, hG, hF, hvw, hGv, dotProduct_comm b₂, h₁₂])
  let y := H (G (F z))
  have hy₀ : b₀ ⬝ᵥ y = 0 := by
    dsimp only [y]
    rw [← hH₀, hH, ← hG₀, hG, ← hFu, hF, huz]
  have hy₁ : b₁ ⬝ᵥ y = 0 := by
    dsimp only [y]
    rw [← hH₁, hH, ← hGv, hG, hF, hvz]
  have hy₂ : b₂ ⬝ᵥ y = 0 := by
    dsimp only [y]
    rw [← hHw, hH, hG, hF, hwz]
  apply no_vector_in_six_with_frame y hy₀ hy₁ hy₂
  dsimp only [y]
  rw [hH, hG, hF, hz]

/-- The four specified unit vectors have the Gram form isometric to ⟨1, 2, 3, 3⟩. -/
def hasUnitGram {n : ℕ} (a b c d : Fin n → ℚ) : Prop :=
  a ⬝ᵥ a = 1 ∧ b ⬝ᵥ b = 1 ∧ c ⬝ᵥ c = 1 ∧ d ⬝ᵥ d = 1 ∧
  a ⬝ᵥ b = -1 / 3 ∧ a ⬝ᵥ c = -1 / 2 ∧ a ⬝ᵥ d = -1 / 2 ∧
  b ⬝ᵥ c = 1 / 6 ∧ b ⬝ᵥ d = 1 / 6 ∧ c ⬝ᵥ d = 1 / 4

private theorem exact_six_seven :
    (∃ a b c d : Fin 7 → ℚ, hasUnitGram a b c d) ∧
      ¬ (∃ a b c d : Fin 6 → ℚ, hasUnitGram a b c d) := by
  constructor
  · refine ⟨![1, 0, 0, 0, 0, 0, 0], ![-1 / 3, 2 / 3, 2 / 3, 0, 0, 0, 0],
      ![-1 / 2, 1 / 2, -1 / 2, 1 / 2, 0, 0, 0], ![-1 / 2, 0, 0, 0, 1 / 2, 1 / 2, 1 / 2], ?_⟩
    norm_num [hasUnitGram, dotProduct, Fin.sum_univ_succ]
  · rintro ⟨a, b, c, d, haa, hbb, hcc, hdd, hab, hac, had, hbc, hbd, hcd⟩
    let v := (3 / 2 : ℚ) • b + (1 / 2 : ℚ) • a
    let w := (2 : ℚ) • c + a
    let z := (2 : ℚ) • d + a
    have hba : b ⬝ᵥ a = -1 / 3 := (dotProduct_comm b a).trans hab
    have hca : c ⬝ᵥ a = -1 / 2 := (dotProduct_comm c a).trans hac
    have hda : d ⬝ᵥ a = -1 / 2 := (dotProduct_comm d a).trans had
    apply no_rational_orthogonal_diagonal_1233_in_six a v w z haa <;>
      norm_num [v, w, z, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
        smul_eq_mul, haa, hbb, hcc, hdd, hab, hac, had, hbc, hbd, hcd, hba, hca, hda]

private theorem hasUnitGram_mono {m n : ℕ} (hmn : m ≤ n)
    (hm : ∃ a b c d : Fin m → ℚ, hasUnitGram a b c d) :
    ∃ a b c d : Fin n → ℚ, hasUnitGram a b c d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  let pad (u : Fin m → ℚ) : Fin (m + k) → ℚ := Fin.append u (fun _ => 0)
  have hpad (u v : Fin m → ℚ) : pad u ⬝ᵥ pad v = u ⬝ᵥ v := by
    simp [dotProduct, Fin.sum_univ_add, pad]
  obtain ⟨a, b, c, d, h⟩ := hm
  exact ⟨pad a, pad b, pad c, pad d, by simpa only [hasUnitGram, hpad] using h⟩

/-- This rank-four unit Gram matrix requires exactly seven rational coordinates. -/
theorem realizable_iff (n : ℕ) :
    (∃ a b c d : Fin n → ℚ, hasUnitGram a b c d) ↔ 7 ≤ n := by
  constructor
  · intro h
    by_contra! hn
    exact exact_six_seven.2 (hasUnitGram_mono (by omega) h)
  · intro hn
    exact hasUnitGram_mono hn exact_six_seven.1

end D5.S3.Quantum.AURICOmega.RationalGramOddPrime
