/- GID: D5/S3/Arith/CharacterSums/QuadraticCharacterGram
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/QuadraticCharacterGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full quadratic-character correlation and its restricted row Gram identity. -/

import D5.S3.Arith.FiniteFieldQuadraticCharacterSum
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace D5.S3.Arith.CharacterSums.QuadraticCharacterGram

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Correlation of two translates, including the diagonal. -/
theorem correlation (hF : ringChar F ≠ 2) (u v : F) :
    ∑ x : F, quadraticChar F (x - u) * quadraticChar F (x - v) =
      (Fintype.card F : ℤ) * (if u = v then 1 else 0) - 1 := by
  classical
  by_cases huv : u = v
  · subst v
    have hterm (x : F) : quadraticChar F (x - u) * quadraticChar F (x - u) =
        1 - (if x = u then 1 else 0) := by
      by_cases hx : x = u
      · simp [hx, quadraticChar_zero]
      · rw [if_neg hx, sub_zero, ← sq]
        exact quadraticChar_sq_one (sub_ne_zero.mpr hx)
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib]
    simp
  · have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hF
    have hA : ((u - v) / 2) ^ 2 ≠ 0 :=
      pow_ne_zero _ (div_ne_zero (sub_ne_zero.mpr huv) htwo)
    let c : F := (u + v) / 2
    let e : F ≃ F :=
      { toFun := fun x => x - c
        invFun := fun x => x + c
        left_inv := by intro x; simp
        right_inv := by intro x; simp }
    have hpoly (x : F) : (x - u) * (x - v) =
        (e x) ^ 2 - ((u - v) / 2) ^ 2 := by
      dsimp [e, c]
      field_simp [htwo]
      ring
    rw [if_neg huv, mul_zero, zero_sub]
    calc
      (∑ x : F, quadraticChar F (x - u) * quadraticChar F (x - v)) =
          ∑ x : F, quadraticChar F ((e x) ^ 2 - ((u - v) / 2) ^ 2) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [← map_mul, hpoly]
      _ = ∑ x : F, quadraticChar F (x ^ 2 - ((u - v) / 2) ^ 2) :=
        Equiv.sum_comp e (fun x : F => quadraticChar F (x ^ 2 - ((u - v) / 2) ^ 2))
      _ = -1 := FiniteFieldQuadraticCharacterSum.quadraticChar_shift_square_sum hF hA

/-- An even function sums twice over any genuine choice of one element from each nonzero
negation pair. All partition hypotheses are explicit and none is a Gram assumption. -/
theorem sum_even (H : Finset F) (h0 : (0 : F) ∉ H)
    (hd : Disjoint H (H.image fun x => -x))
    (hc : ∀ x : F, x ≠ 0 → x ∈ H ∨ -x ∈ H)
    (f : F → ℤ) (hf : ∀ x, f (-x) = f x) :
    ∑ x : F, f x = f 0 + 2 * ∑ x ∈ H, f x := by
  classical
  have h0i : (0 : F) ∉ H.image (fun x => -x) := by
    rintro h
    obtain ⟨x, hx, hx0⟩ := Finset.mem_image.mp h
    have : x = 0 := neg_eq_zero.mp hx0
    exact h0 (this ▸ hx)
  have hU : insert 0 (H ∪ H.image (fun x => -x)) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · apply Finset.mem_insert_of_mem
      rcases hc x hx with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨-x, h, neg_neg x⟩)
  rw [← hU, Finset.sum_insert (by simpa only [Finset.mem_union, not_or] using And.intro h0 h0i),
    Finset.sum_union hd,
    Finset.sum_image (fun _ _ _ _ h => neg_injective h)]
  simp_rw [hf]
  ring

/-- The restricted row Gram identity used for both signs in the Chen-Sun argument.
The left side is an actual finite sum; the only geometric input is a half-set partition. -/
theorem restricted_gram (hF : ringChar F ≠ 2) (H : Finset F)
    (h0 : (0 : F) ∉ H) (hd : Disjoint H (H.image fun x => -x))
    (hc : ∀ x : F, x ≠ 0 → x ∈ H ∨ -x ∈ H)
    {i j : F} (hi : i ∈ H) (hj : j ∈ H) (t : ℤ) (ht : t = 1 ∨ t = -1) :
    (∑ x ∈ H,
      (quadraticChar F (i + x) + t * quadraticChar F (i - x)) *
      (quadraticChar F (j + x) + t * quadraticChar F (j - x))) =
        (Fintype.card F : ℤ) * (if i = j then 1 else 0) -
          (1 + t * quadraticChar F (-1)) -
            (1 + t) * quadraticChar F i * quadraticChar F j := by
  classical
  let ε : ℤ := quadraticChar F (-1)
  let d : ℤ := (Fintype.card F : ℤ) * (if i = j then 1 else 0)
  let f : F → ℤ := fun x =>
    (quadraticChar F (i + x) + t * quadraticChar F (i - x)) *
    (quadraticChar F (j + x) + t * quadraticChar F (j - x))
  have hij : i ≠ -j := by
    intro h
    exact Finset.disjoint_left.mp hd hi (Finset.mem_image.mpr ⟨j, hj, h.symm⟩)
  have hnij : -i ≠ j := by
    intro h
    apply hij
    exact neg_eq_iff_eq_neg.mp h
  have hε : ε ^ 2 = 1 := quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero)
  have hneg (a x : F) : quadraticChar F (a - x) = ε * quadraticChar F (x - a) := by
    change quadraticChar F (a - x) = quadraticChar F (-1) * quadraticChar F (x - a)
    rw [← map_mul]
    congr 1
    ring
  have hplus (a x : F) : quadraticChar F (a + x) = quadraticChar F (x - -a) := by
    congr 1
    ring
  have hAA : (∑ x : F, quadraticChar F (i + x) * quadraticChar F (j + x)) = d - 1 := by
    simpa only [hplus, neg_inj] using correlation hF (-i) (-j)
  have hBB : (∑ x : F, quadraticChar F (i - x) * quadraticChar F (j - x)) = d - 1 := by
    calc
      _ = ∑ x : F, quadraticChar F (x - i) * quadraticChar F (x - j) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hneg i x, hneg j x]
        calc
          _ = ε ^ 2 * (quadraticChar F (x - i) * quadraticChar F (x - j)) := by ring
          _ = _ := by rw [hε, one_mul]
      _ = d - 1 := correlation hF i j
  have hAB : (∑ x : F, quadraticChar F (i + x) * quadraticChar F (j - x)) = -ε := by
    calc
      _ = ∑ x : F, ε * (quadraticChar F (x - -i) * quadraticChar F (x - j)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hplus i x, hneg j x]
        ring
      _ = ε * ∑ x : F, quadraticChar F (x - -i) * quadraticChar F (x - j) :=
        (Finset.mul_sum _ _ _).symm
      _ = -ε := by rw [correlation hF (-i) j, if_neg hnij]; ring
  have hBA : (∑ x : F, quadraticChar F (i - x) * quadraticChar F (j + x)) = -ε := by
    calc
      _ = ∑ x : F, ε * (quadraticChar F (x - i) * quadraticChar F (x - -j)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hneg i x, hplus j x]
        ring
      _ = ε * ∑ x : F, quadraticChar F (x - i) * quadraticChar F (x - -j) :=
        (Finset.mul_sum _ _ _).symm
      _ = -ε := by rw [correlation hF i (-j), if_neg hij]; ring
  have hfull : (∑ x : F, f x) = 2 * (d - 1) - 2 * t * ε := by
    calc
      _ = ∑ x : F,
          (quadraticChar F (i + x) * quadraticChar F (j + x) +
          t * (quadraticChar F (i + x) * quadraticChar F (j - x)) +
          t * (quadraticChar F (i - x) * quadraticChar F (j + x)) +
          quadraticChar F (i - x) * quadraticChar F (j - x)) := by
        apply Finset.sum_congr rfl
        intro x _
        rcases ht with rfl | rfl <;> dsimp [f] <;> ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hAA, hAB, hBA, hBB]
        ring
  have hzero : f 0 = 2 * (1 + t) * quadraticChar F i * quadraticChar F j := by
    rcases ht with rfl | rfl <;> simp [f] <;> ring
  have heven (x : F) : f (-x) = f x := by
    rcases ht with rfl | rfl <;> dsimp [f] <;>
      simp only [sub_neg_eq_add, ← sub_eq_add_neg] <;> ring
  have hhalf := sum_even H h0 hd hc f heven
  rw [hfull, hzero] at hhalf
  change (∑ x ∈ H, f x) = d - (1 + t * ε) -
    (1 + t) * quadraticChar F i * quadraticChar F j
  linarith

/-- Summing the restricted Gram identity gives the integral energy of the column sums.
This is the common energy identity for the even and odd prime families. -/
theorem restricted_column_energy (hF : ringChar F ≠ 2) (H : Finset F)
    (h0 : (0 : F) ∉ H) (hd : Disjoint H (H.image fun x => -x))
    (hc : ∀ x : F, x ≠ 0 → x ∈ H ∨ -x ∈ H)
    (t : ℤ) (ht : t = 1 ∨ t = -1) :
    (∑ x ∈ H, (H.sum (fun i : F =>
      quadraticChar F (i + x) + t * quadraticChar F (i - x))) ^ 2) =
      (Fintype.card F : ℤ) * H.card -
        (1 + t * quadraticChar F (-1)) * (H.card : ℤ) ^ 2 -
          (1 + t) * (∑ i ∈ H, quadraticChar F i) ^ 2 := by
  classical
  let M (i x : F) : ℤ := quadraticChar F (i + x) + t * quadraticChar F (i - x)
  have hdiag : (∑ i ∈ H, ∑ j ∈ H,
      (Fintype.card F : ℤ) * (if i = j then 1 else 0)) =
        (Fintype.card F : ℤ) * H.card := by
    simp [mul_comm]
  have hconst : (∑ i ∈ H, ∑ _j ∈ H, (1 + t * quadraticChar F (-1))) =
      (1 + t * quadraticChar F (-1)) * (H.card : ℤ) ^ 2 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  have hrank : (∑ i ∈ H, ∑ j ∈ H,
      (1 + t) * quadraticChar F i * quadraticChar F j) =
        (1 + t) * (∑ i ∈ H, quadraticChar F i) ^ 2 := by
    calc
      _ = ∑ i ∈ H, (1 + t) * quadraticChar F i * (∑ j ∈ H, quadraticChar F j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      _ = (1 + t) * (∑ i ∈ H, quadraticChar F i) * (∑ j ∈ H, quadraticChar F j) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ = _ := by ring
  calc
    _ = ∑ x ∈ H, ∑ i ∈ H, ∑ j ∈ H, M i x * M j x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [pow_two]
      change (∑ i ∈ H, M i x) * (∑ j ∈ H, M j x) = _
      exact Finset.sum_mul_sum H H (fun i => M i x) (fun j => M j x)
    _ = ∑ i ∈ H, ∑ x ∈ H, ∑ j ∈ H, M i x * M j x := Finset.sum_comm
    _ = ∑ i ∈ H, ∑ j ∈ H, ∑ x ∈ H, M i x * M j x := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ i ∈ H, ∑ j ∈ H,
        ((Fintype.card F : ℤ) * (if i = j then 1 else 0) -
          (1 + t * quadraticChar F (-1)) -
            (1 + t) * quadraticChar F i * quadraticChar F j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact restricted_gram hF H h0 hd hc hi hj t ht
    _ = _ := by
      simp only [Finset.sum_sub_distrib]
      rw [hdiag, hconst, hrank]

/-- The actual lower half of the nonzero residues, selected by least natural representatives. -/
def primeHalf (p : ℕ) [NeZero p] : Finset (ZMod p) :=
  Finset.univ.filter fun x => 0 < x.val ∧ x.val ≤ (p - 1) / 2

private theorem mem_primeHalf {p : ℕ} [NeZero p] (x : ZMod p) :
    x ∈ primeHalf p ↔ 0 < x.val ∧ x.val ≤ (p - 1) / 2 := by
  simp [primeHalf]

private theorem primeHalf_zero {p : ℕ} [NeZero p] : (0 : ZMod p) ∉ primeHalf p := by
  simp [mem_primeHalf]

private theorem primeHalf_disjoint {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    Disjoint (primeHalf p) ((primeHalf p).image fun x => -x) := by
  apply Finset.disjoint_left.mpr
  intro x hx hxn
  obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hxn
  have hxv := (mem_primeHalf x).mp hx
  have hyv := (mem_primeHalf y).mp hy
  have hy0 : y ≠ 0 := by intro h; simpa [h] using hyv.1
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp)
  have hxyv : x.val = p - y.val := by rw [← hxy, ZMod.neg_val, if_neg hy0]
  omega

private theorem primeHalf_cover {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (x : ZMod p) (hx : x ≠ 0) : x ∈ primeHalf p ∨ -x ∈ primeHalf p := by
  have hv : 0 < x.val := Nat.pos_of_ne_zero ((ZMod.val_eq_zero x).not.mpr hx)
  have hlt := x.val_lt
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp)
  by_cases hh : x.val ≤ (p - 1) / 2
  · exact Or.inl ((mem_primeHalf x).mpr ⟨hv, hh⟩)
  · right
    rw [mem_primeHalf, ZMod.neg_val, if_neg hx]
    omega

/-- Specialization to the genuine lower-half residue set for every odd prime.
No half-set or correlation condition is assumed in this prime statement. -/
theorem prime_restricted_gram (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    {i j : ZMod p} (hi : 0 < i.val ∧ i.val ≤ (p - 1) / 2)
    (hj : 0 < j.val ∧ j.val ≤ (p - 1) / 2) (t : ℤ) (ht : t = 1 ∨ t = -1) :
    (∑ x ∈ primeHalf p,
      (quadraticChar (ZMod p) (i + x) + t * quadraticChar (ZMod p) (i - x)) *
      (quadraticChar (ZMod p) (j + x) + t * quadraticChar (ZMod p) (j - x))) =
        (p : ℤ) * (if i = j then 1 else 0) -
          (1 + t * quadraticChar (ZMod p) (-1)) -
            (1 + t) * quadraticChar (ZMod p) i * quadraticChar (ZMod p) j := by
  simpa only [ZMod.card] using
    restricted_gram ((ZMod.ringChar_zmod_n p).substr hp) (primeHalf p)
      primeHalf_zero (primeHalf_disjoint hp) (primeHalf_cover hp)
      ((mem_primeHalf i).mpr hi) ((mem_primeHalf j).mpr hj) t ht

/-- The residue half-set is precisely the positive interval, with its least representatives. -/
theorem sum_primeHalf (p : ℕ) [Fact p.Prime] (f : ZMod p → ℤ) :
    (∑ x ∈ primeHalf p, f x) =
      ∑ j ∈ Finset.range ((p - 1) / 2), f ((j + 1 : ℕ) : ZMod p) := by
  classical
  have hp0 := (Fact.out : p.Prime).pos
  refine Finset.sum_bij (fun x _ => x.val - 1) ?_ ?_ ?_ ?_
  · intro x hx
    have hx' := (mem_primeHalf x).mp hx
    exact Finset.mem_range.mpr (by omega)
  · intro x hx y hy h
    apply ZMod.val_injective p
    have hx' := (mem_primeHalf x).mp hx
    have hy' := (mem_primeHalf y).mp hy
    omega
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    have hjp : j + 1 < p := by omega
    refine ⟨((j + 1 : ℕ) : ZMod p), ?_, ?_⟩
    · rw [mem_primeHalf, ZMod.val_cast_of_lt hjp]
      omega
    · rw [ZMod.val_cast_of_lt hjp]
      omega
  · intro x hx
    have hx' := (mem_primeHalf x).mp hx
    have heq : x.val - 1 + 1 = x.val := by omega
    rw [heq, ZMod.natCast_zmod_val]

theorem primeHalf_card (p : ℕ) [Fact p.Prime] : (primeHalf p).card = (p - 1) / 2 := by
  have h := sum_primeHalf p (fun _ => 1)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

/-- Pairing the complete zero-sum quadratic character gives cancellation of its half sum. -/
theorem prime_half_character_cancellation (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (1 + quadraticChar (ZMod p) (-1)) *
      (∑ x ∈ primeHalf p, quadraticChar (ZMod p) x) = 0 := by
  classical
  have hF : ringChar (ZMod p) ≠ 2 := (ZMod.ringChar_zmod_n p).substr hp
  rcases quadraticChar_dichotomy (show (-1 : ZMod p) ≠ 0 from neg_ne_zero.mpr one_ne_zero)
    with h | h
  · have heven (x : ZMod p) : quadraticChar (ZMod p) (-x) = quadraticChar (ZMod p) x := by
      rw [neg_eq_neg_one_mul, map_mul, h, one_mul]
    have hs := sum_even (primeHalf p) primeHalf_zero (primeHalf_disjoint hp)
      (primeHalf_cover hp) (quadraticChar (ZMod p)) heven
    rw [quadraticChar_sum_zero hF, quadraticChar_zero, zero_add] at hs
    rw [h]
    linarith
  · rw [h]
    ring

/-- Actual half-residue column energy for every odd prime. Its hypotheses contain
neither an assumed Gram identity nor an assumed norm formula. -/
theorem prime_column_energy (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (t : ℤ) (ht : t = 1 ∨ t = -1) :
    ((primeHalf p).sum (fun x : ZMod p =>
      ((primeHalf p).sum (fun i : ZMod p =>
        quadraticChar (ZMod p) (i + x) + t * quadraticChar (ZMod p) (i - x))) ^ 2)) =
      (p : ℤ) * (((p - 1) / 2 : ℕ) : ℤ) -
        (1 + t * quadraticChar (ZMod p) (-1)) * (((p - 1) / 2 : ℕ) : ℤ) ^ 2 -
          (1 + t) * (∑ i ∈ primeHalf p, quadraticChar (ZMod p) i) ^ 2 := by
  simpa only [ZMod.card, primeHalf_card] using
    restricted_column_energy ((ZMod.ringChar_zmod_n p).substr hp) (primeHalf p)
      primeHalf_zero (primeHalf_disjoint hp) (primeHalf_cover hp) t ht

end D5.S3.Arith.CharacterSums.QuadraticCharacterGram
