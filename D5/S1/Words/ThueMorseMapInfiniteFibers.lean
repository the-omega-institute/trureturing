/- GID: D5/S1/Words/ThueMorseMapInfiniteFibers
   generality: G
   mirror-B: D5/B/S1/Words/ThueMorseMapInfiniteFibers
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: none
   digest: Infinitely many attained global Thue-Morse AP maxima have infinite positive odd fibers. -/

import D5.S1.Words.ThueMorseMapFirstStart
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Choose
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify

namespace D5.S1.Words.ThueMorseMapInfiniteFibers

open D5.S1.Words.Complexity
open D5.S1.Words.ThueMorseDyadic
open D5.S1.Words.ThueMorseMapFirstStart (MAP)

/-- Attainment and universal maximality, over every start and both letters. -/
def ExactMax (d n : Nat) : Prop :=
  (∃ s, MAP d s n) ∧ ∀ s L, MAP d s L → L ≤ n

/-- Joshi–Rust, arXiv:2501.05830v2, §3.2.1 Question 3.7, second clause. -/
def claim : Prop :=
  Set.Infinite {n : Nat | Set.Infinite {d : Nat | 0 < d ∧ Odd d ∧ ExactMax d n}}

private theorem no_triple (b : Nat) :
    ¬ (thueMorse b = thueMorse (b + 1) ∧
       thueMorse (b + 1) = thueMorse (b + 2)) := by
  intro h
  obtain ⟨a, rfl | rfl⟩ := b.even_or_odd'
  · simpa using h.1
  · have hh := h.2
    rw [show 2 * a + 1 + 1 = 2 * (a + 1) by omega,
      show 2 * a + 1 + 2 = 2 * (a + 1) + 1 by omega] at hh
    simp at hh

private theorem seed (m : Nat) (hm : 3 ≤ m) (hodd : Odd m) :
    let M := 2 ^ m
    let c := M ^ 2 + M + 1
    let B := 2 ^ (4 * m + 1)
    let a := c * (M ^ 2 - 1)
    1 < c ∧ Nat.Coprime B c ∧ a + 2 * c < B ∧
      (∀ i < 3, thueMorse (a + i * c) = true) ∧
      (∀ j < M, thueMorse (c * j) = thueMorse j) := by
  dsimp only
  let M := 2 ^ m
  let c := M ^ 2 + M + 1
  change 1 < c ∧ Nat.Coprime (2 ^ (4 * m + 1)) c ∧
    c * (M ^ 2 - 1) + 2 * c < 2 ^ (4 * m + 1) ∧
    (∀ i < 3, thueMorse (c * (M ^ 2 - 1) + i * c) = true) ∧
    (∀ j < M, thueMorse (c * j) = thueMorse j)
  have hM : 8 ≤ M := by
    exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hm)
  have hB : 2 ^ (4 * m + 1) = 2 * M ^ 4 := by
    dsimp [M]
    rw [Nat.pow_add, Nat.mul_comm 4 m, Nat.pow_mul]
    ring
  have hMeven : Even M := by
    exact even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega : m ≠ 0))
  have hcodd : Odd c := by
    dsimp [c]
    exact (hMeven.pow_of_ne_zero (by decide)).add hMeven |>.add_odd (by decide : Odd (1 : Nat))
  have hcop : Nat.Coprime (2 ^ (4 * m + 1)) c := by
    exact (Nat.coprime_two_left.mpr hcodd).pow_left _
  have t1 : thueMorse 1 = true := by decide
  have t2 : thueMorse 2 = true := by decide
  have top : thueMorse (M - 1) = true := by
    dsimp [M]
    rw [top_parity]
    simp [Nat.odd_iff.mp hodd]
  have low : thueMorse (M - 2) = false := by
    obtain ⟨v, hv⟩ := hMeven
    have hp : M - 2 = 2 * (v - 1) := by omega
    have hq : M - 1 = 2 * (v - 1) + 1 := by omega
    rw [hq, thueMorse_two_mul_add_one] at top
    rw [hp, thueMorse_two_mul]
    cases ht : thueMorse (v - 1) <;> simp_all
  have digits (a b e f g : Nat) (hb : b < M) (he : e < M)
      (hf : f < M) (hg : g < M) :
      thueMorse ((((a * M + b) * M + e) * M + f) * M + g) =
        Bool.xor (Bool.xor (Bool.xor (Bool.xor (thueMorse a)
          (thueMorse b)) (thueMorse e)) (thueMorse f)) (thueMorse g) := by
    rw [dyadic_block m _ g hg, dyadic_block m _ f hf,
      dyadic_block m _ e he, dyadic_block m _ b hb]
  have hexp0 : c * (M ^ 2 - 1) =
      (((1 * M + 0) * M + (M - 1)) * M + (M - 2)) * M + (M - 1) := by
    dsimp [c]
    zify [show 1 ≤ M by omega, show 2 ≤ M by omega,
      show 1 ≤ M ^ 2 by nlinarith]
    ring
  have hexp1 : c * (M ^ 2 - 1) + c =
      (((1 * M + 1) * M + 1) * M + 0) * M + 0 := by
    dsimp [c]
    zify [show 1 ≤ M ^ 2 by nlinarith]
    ring
  have hexp2 : c * (M ^ 2 - 1) + 2 * c =
      (((1 * M + 1) * M + 2) * M + 1) * M + 1 := by
    dsimp [c]
    zify [show 1 ≤ M ^ 2 by nlinarith]
    ring
  refine ⟨by dsimp [c]; nlinarith, hcop, ?_, ?_, ?_⟩
  · rw [hB, hexp2]
    nlinarith [Nat.mul_le_mul_right (M ^ 3) hM,
      Nat.mul_le_mul_right (M ^ 2) hM, Nat.mul_le_mul_right M hM]
  · intro i hi
    interval_cases i
    · simp only [Nat.zero_mul, Nat.add_zero]
      rw [hexp0, digits 1 0 (M - 1) (M - 2) (M - 1)
        (by omega) (by omega) (by omega) (by omega)]
      simp [t1, top, low]
    · simp only [Nat.one_mul]
      rw [hexp1, digits 1 1 1 0 0 (by omega) (by omega) (by omega) (by omega)]
      simp [t1]
    · rw [hexp2, digits 1 1 2 1 1 (by omega) (by omega) (by omega) (by omega)]
      simp [t1, t2]
  · intro j hj
    rw [show c * j = (j * M + j) * M + j by dsimp [c]; ring]
    rw [dyadic_block m _ j hj, dyadic_block m _ j hj]
    cases thueMorse j <;> rfl

private theorem every_window (e c a : Nat) (hc : 1 < c)
    (hcop : Nat.Coprime (2 ^ e) c) (ha : a + 2 * c < 2 ^ e)
    (htriple : ∀ i < 3, thueMorse (a + i * c) = true) (u : Nat) :
    ∃ r γ, r + 2 < 2 * 2 ^ e + 2 ∧
      ∀ i < 3, thueMorse (u + c * (r + i)) = γ := by
  let B := 2 ^ e
  have hB : 0 < B := Nat.two_pow_pos e
  let q := u / B + if u % B = 0 then 0 else 1
  have hq : u ≤ q * B ∧ q * B < u + B := by
    have hd := Nat.mod_add_div u B
    rw [Nat.mul_comm B] at hd
    have hr := Nat.mod_lt u hB
    dsimp [q]
    split_ifs <;> simp only [Nat.add_mul, Nat.one_mul, Nat.add_zero] <;> omega
  let f : Fin c → Fin c := fun i =>
    ⟨((q + i.val) * B + a) % c, Nat.mod_lt _ (by omega)⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have he : Nat.ModEq c ((q + i.val) * B + a) ((q + j.val) * B + a) :=
      congrArg Fin.val hij
    have hmul := Nat.ModEq.add_right_cancel' a he
    have hsum := Nat.ModEq.cancel_right_of_coprime hcop.symm hmul
    have hres := Nat.ModEq.add_left_cancel' q hsum
    apply Fin.ext
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hres
  obtain ⟨v, hv⟩ := (Finite.surjective_of_injective hinj)
    ⟨u % c, Nat.mod_lt _ (by omega)⟩
  let p := q + v.val
  let x := p * B + a
  have hmod : x % c = u % c := congrArg Fin.val hv
  have hxlo : u ≤ x := by
    have hp := Nat.mul_le_mul_right B (Nat.le_add_right q v.val)
    dsimp [x, p]
    omega
  have hxhi : x < u + 2 * c * B := by
    have hvB := Nat.mul_le_mul_right B (show v.val + 1 ≤ c by omega)
    have hcB := Nat.mul_le_mul_right B (show c + 1 ≤ 2 * c by omega)
    have he : x = q * B + v.val * B + a := by dsimp [x, p]; ring
    simp only [Nat.add_mul, Nat.one_mul] at hvB hcB
    omega
  obtain ⟨r, hxr⟩ := (Nat.modEq_iff_exists_eq_add hxlo).mp
    (show Nat.ModEq c u x from hmod.symm)
  have hr : r < 2 * B := by
    have hmul' : c * r < c * (2 * B) := by rw [hxr] at hxhi; nlinarith
    exact Nat.lt_of_mul_lt_mul_left hmul'
  refine ⟨r, Bool.xor (thueMorse p) true, by omega, ?_⟩
  intro i hi
  have hir : a + i * c < B := by
    have him := Nat.mul_le_mul_right c (show i ≤ 2 by omega)
    omega
  have he : u + c * (r + i) = p * B + (a + i * c) := by
    have hh : x = p * B + a := rfl
    rw [hxr] at hh
    nlinarith
  rw [he, dyadic_block e _ _ hir, htriple i hi]

private theorem no_shadow (e c a : Nat) (hc : 1 < c)
    (hcop : Nat.Coprime (2 ^ e) c) (ha : a + 2 * c < 2 ^ e)
    (htriple : ∀ i < 3, thueMorse (a + i * c) = true) :
    ∀ u b : Nat, ∀ γ : Bool,
      ¬ (∀ j < 2 * 2 ^ e + 2,
        thueMorse (u + c * j) = Bool.xor γ (thueMorse (b + j))) := by
  intro u b γ h
  obtain ⟨r, δ, hr, ht⟩ := every_window e c a hc hcop ha htriple u
  have h0 := (h r (by omega)).symm.trans (ht 0 (by decide))
  have h1 := (h (r + 1) (by omega)).symm.trans (ht 1 (by decide))
  have h2 := (h (r + 2) (by omega)).symm.trans (ht 2 (by decide))
  apply no_triple (b + r)
  constructor
  · have hh := h0.trans h1.symm
    cases γ <;> simpa [Nat.add_assoc] using hh
  · have hh := h1.trans h2.symm
    cases γ <;> simpa [Nat.add_assoc] using hh

private theorem lifted_bounds (m c U : Nat)
    (hsmall : ∀ j < 2 ^ m, thueMorse (c * j) = thueMorse j)
    (hshadow : ∀ u b : Nat, ∀ γ : Bool,
      ¬ (∀ j < U, thueMorse (u + c * j) = Bool.xor γ (thueMorse (b + j))))
    (k : Nat) (hlarge : 2 * U + 1 ≤ 2 ^ k)
    (hm : 2 ^ m ≤ 2 ^ k) :
    MAP (c * 2 ^ k + 1) 0 (2 ^ m) ∧
      ∀ s L, MAP (c * 2 ^ k + 1) s L → L ≤ 2 * U := by
  let R := 2 ^ k
  have lower : MAP (c * R + 1) 0 (2 ^ m) := by
    intro j hj
    rw [show 0 + j * (c * R + 1) = (c * j) * R + j by ring]
    rw [dyadic_block k _ _ (by omega), hsmall j hj]
    simp
  refine ⟨lower, ?_⟩
  intro s L hmap
  by_contra hL
  have sample (j : Nat) (hj : j < 2 * U + 1) :
      thueMorse (s + j * (c * R + 1)) = thueMorse s := hmap j (by omega)
  let q := s / R
  let r := s % R
  have hr : r < R := Nat.mod_lt _ (Nat.two_pow_pos k)
  have hs : s = q * R + r := by
    have hd := Nat.mod_add_div s R
    rw [Nat.mul_comm R] at hd
    dsimp [q, r]
    omega
  have decode (x y γ : Bool) (h : Bool.xor x y = γ) : x = Bool.xor γ y := by
    cases x <;> cases y <;> cases γ <;> simp_all
  by_cases hlow : r + U ≤ R
  · apply hshadow q r (thueMorse s)
    intro j hj
    have hi : s + j * (c * R + 1) = (q + c * j) * R + (r + j) := by
      rw [hs]
      ring
    have ht := sample j (by omega)
    rw [hi, dyadic_block k _ _ (by omega)] at ht
    exact decode _ _ _ ht
  · let v := R - r
    have hv : r + v = R := by dsimp [v]; omega
    have hvU : v < U := by omega
    apply hshadow (q + c * v + 1) 0 (thueMorse s)
    intro j hj
    have hi : s + (v + j) * (c * R + 1) =
        (q + c * v + 1 + c * j) * R + j := by
      calc
        _ = (q + c * (v + j)) * R + (r + v) + j := by rw [hs]; ring
        _ = _ := by rw [hv]; ring
    have ht := sample (v + j) (by omega)
    rw [hi, dyadic_block k _ _ (by omega)] at ht
    simpa only [Nat.zero_add] using decode _ _ _ ht

private theorem attained (d M C : Nat) (hlower : MAP d 0 M)
    (hbound : ∀ s L, MAP d s L → L ≤ C) :
    ∃ n, M ≤ n ∧ n ≤ C ∧ ExactMax d n := by
  classical
  let S : Set Nat := {L | ∃ s, MAP d s L}
  have hfinite : S.Finite := (Set.finite_Iic C).subset (by
    rintro L ⟨s, hs⟩
    exact hbound s L hs)
  obtain ⟨n, hn, hmax⟩ := Set.exists_max_image S id hfinite ⟨M, 0, hlower⟩
  obtain ⟨s, hs⟩ := hn
  exact ⟨n, hmax M ⟨0, hlower⟩, hbound s n hs,
    ⟨⟨s, hs⟩, fun a L hL => hmax L ⟨a, hL⟩⟩⟩

private theorem family (m : Nat) (hm : 3 ≤ m) (hodd : Odd m) :
    ∃ n, 2 ^ m ≤ n ∧
      Set.Infinite {d : Nat | 0 < d ∧ Odd d ∧ ExactMax d n} := by
  classical
  let M := 2 ^ m
  let c := M ^ 2 + M + 1
  let B := 2 ^ (4 * m + 1)
  let a := c * (M ^ 2 - 1)
  let U := 2 * B + 2
  have hseed := seed m hm hodd
  change 1 < c ∧ Nat.Coprime B c ∧ a + 2 * c < B ∧
    (∀ i < 3, thueMorse (a + i * c) = true) ∧
    (∀ j < M, thueMorse (c * j) = thueMorse j) at hseed
  rcases hseed with ⟨hc, hcop, ha, htriple, hsmall⟩
  have hshadow := no_shadow (4 * m + 1) c a hc hcop ha htriple
  let T := max (2 * U + 1) M
  let d : Nat → Nat := fun i => c * 2 ^ (T + i) + 1
  have maxima (i : Nat) : ∃ n, M ≤ n ∧ n ≤ 2 * U ∧ ExactMax (d i) n := by
    have hp := Nat.lt_two_pow_self (n := T + i)
    have hT0 : 2 * U + 1 ≤ T := Nat.le_max_left _ _
    have hT1 : M ≤ T := Nat.le_max_right _ _
    obtain ⟨hl, hu⟩ := lifted_bounds m c U hsmall hshadow
      (T + i) (by omega) (by omega)
    exact attained (d i) M (2 * U) hl hu
  choose n hnlo hnhi hnmax using maxima
  let f : Nat → Fin (2 * U + 1) := fun i => ⟨n i, by have := hnhi i; omega⟩
  obtain ⟨v, hv⟩ := Finite.exists_infinite_fiber f
  have hfiber : Set.Infinite {i : Nat | f i = v} := Set.infinite_coe_iff.mp hv
  have hinj : Function.Injective d := by
    intro i j hij
    have hp : 2 ^ (T + i) = 2 ^ (T + j) := by dsimp [d] at hij; nlinarith
    have he := Nat.pow_right_injective (by decide : 2 ≤ 2) hp
    omega
  refine ⟨v.val, ?_, (hfiber.image hinj.injOn).mono ?_⟩
  · obtain ⟨i, hi⟩ := hfiber.nonempty
    have he : n i = v.val := congrArg Fin.val hi
    rw [← he]
    exact hnlo i
  · rintro x ⟨i, hi, rfl⟩
    have he : n i = v.val := congrArg Fin.val hi
    refine ⟨by dsimp [d]; omega, ?_, ?_⟩
    · have heven : Even (2 ^ (T + i)) :=
        even_iff_two_dvd.mpr (dvd_pow_self 2 (by dsimp [T, U]; omega : T + i ≠ 0))
      exact (heven.mul_left c).add_odd (by decide : Odd (1 : Nat))
    · rw [← he]
      exact hnmax i

/-- Infinitely many exact global maxima have infinitely many positive odd differences. -/
theorem result : claim := by
  classical
  intro hfinite
  obtain ⟨N, hN⟩ := hfinite.bddAbove
  obtain ⟨n, hnlo, hninf⟩ := family (2 * N + 3) (by omega) ⟨N + 1, by omega⟩
  have hp := Nat.lt_two_pow_self (n := 2 * N + 3)
  have hnupper : n ≤ N := hN hninf
  omega

end D5.S1.Words.ThueMorseMapInfiniteFibers
