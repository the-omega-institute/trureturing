/- GID: D5/S3/Combinatorics/Circle/TwoSmallSource
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/TwoSmallSource
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: Exactly two physical SMALL labels admit a complete native half-strip word. -/
import D5.S3.Combinatorics.Circle.TwoSmallPlacement
import D5.S3.Combinatorics.Circle.AntipodalSourceCompletion
import D5.S1.Words.Compositions.ZeroSumWordCount

/-! # Native completion with exactly two SMALL physical labels -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.TwoSmallSource
open SourceWidth ExpandingSourcePath TwoSmallProfile TwoSmallPlacement
open MixedSuffixEnergy TwoOppositeLargeExchange
open scoped BigOperators

theorem phase_add {k : ℕ} (hk : 0 < k) (o : Fin k) (j : ℕ) :
    phase hk o j = o + (⟨j % k, Nat.mod_lt _ hk⟩ : Fin k) := by
  apply Fin.ext
  simp [phase, Fin.val_add, Nat.add_mod]

theorem filter_rotate {α : Type*} (p : α → Bool) (l : List α) (n : ℕ) :
    (l.rotate n).filter p ~r l.filter p := by
  let r := n % l.length
  have hright : l.filter p = (l.take r).filter p ++ (l.drop r).filter p := by
    rw [← List.filter_append, List.take_append_drop]
  rw [List.rotate_eq_drop_append_take_mod, List.filter_append, hright]
  exact List.isRotated_append

private theorem range_filter_delete (ell m : ℕ) :
    (List.range (ell + m + 2)).filter (fun j => decide (j ≠ 0 ∧ j ≠ ell + 1)) =
      List.range' 1 ell ++ List.range' (ell + 2) m := by
  have h1 : List.range' 1 ell ++ [ell + 1] = List.range' 1 (ell + 1) := by
    simpa only [Nat.add_comm] using (List.range'_1_concat (s := 1) (n := ell)).symm
  have h2 : List.range' 1 (ell + 1) ++ List.range' (ell + 2) m =
      List.range' 1 (ell + 1 + m) := by
    simpa only [show 1 + (ell + 1) = ell + 2 by omega] using
      (List.range'_append_1 (s := 1) (m := ell + 1) (n := m))
  have hinv : [0] ++ List.range' 1 ell ++ [ell + 1] ++ List.range' (ell + 2) m =
      List.range (ell + m + 2) := by
    calc
      [0] ++ List.range' 1 ell ++ [ell + 1] ++ List.range' (ell + 2) m =
          [0] ++ ((List.range' 1 ell ++ [ell + 1]) ++ List.range' (ell + 2) m) := by
            simp only [List.append_assoc]
      _ = [0] ++ List.range' 1 (ell + 1 + m) := by rw [h1, h2]
      _ = List.range (ell + m + 2) := by
        rw [List.range_eq_range', show ell + m + 2 = (ell + 1 + m) + 1 by omega,
          List.range'_succ]
        rfl
  have hmid : (List.range' 1 ell).filter
      (fun j => decide (j ≠ 0 ∧ j ≠ ell + 1)) = List.range' 1 ell := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp only [List.mem_range'] at hx
    rcases hx with ⟨i, hi, rfl⟩
    rw [decide_eq_true_eq]
    constructor <;> omega
  have htail : (List.range' (ell + 2) m).filter
      (fun j => decide (j ≠ 0 ∧ j ≠ ell + 1)) = List.range' (ell + 2) m := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp only [List.mem_range'] at hx
    rcases hx with ⟨i, hi, rfl⟩
    rw [decide_eq_true_eq]
    constructor <;> omega
  rw [← hinv, List.filter_append, List.filter_append, List.filter_append,
    List.filter_cons, List.filter_nil, hmid, htail]
  simp

private theorem short_gap {k : ℕ} (hk : 0 < k) (P : Fin k → Prop)
    (a b : Fin k) (hab : a ≠ b) (hP : ∀ i, P i ↔ i = a ∨ i = b) :
    ∃ o : Fin k, ∃ d : ℕ, 0 < d ∧ d < k ∧ d ≤ k - d ∧
      ∀ j < k, P (phase hk o j) ↔ j = 0 ∨ j = d := by
  letI : NeZero k := ⟨ne_of_gt hk⟩
  have hchar (o z : Fin k) (hp : ∀ i, P i ↔ i = o ∨ i = z) :
      ∀ j < k, P (phase hk o j) ↔ j = 0 ∨ j = (z - o).val := by
    intro j hj
    rw [hp, phase_add]
    have hcast : (⟨j % k, Nat.mod_lt _ hk⟩ : Fin k) = ⟨j, hj⟩ :=
      Fin.ext (Nat.mod_eq_of_lt hj)
    rw [hcast]
    constructor
    · rintro (he | he)
      · left
        have ht : (⟨j, hj⟩ : Fin k) = 0 := by
          apply add_left_cancel (a := o)
          simpa using he
        simpa only [Fin.val_zero] using congrArg Fin.val ht
      · right
        have ht : (⟨j, hj⟩ : Fin k) = z - o := by rw [← he]; abel
        exact congrArg Fin.val ht
    · rintro (rfl | he)
      · left
        have hz : (⟨0, hj⟩ : Fin k) = 0 := Fin.ext (by simp)
        rw [hz, add_zero]
      · right
        have ht : (⟨j, hj⟩ : Fin k) = z - o := Fin.ext he
        rw [ht]; abel
  let d := (b - a).val
  have hd0 : 0 < d := by
    by_contra h
    have he : b - a = 0 := Fin.ext (by dsimp [d] at h; simpa using (show (b - a).val = 0 by omega))
    have he' : b = a := sub_eq_zero.mp he
    exact hab he'.symm
  have hdk : d < k := (b - a).isLt
  by_cases hd : d ≤ k - d
  · exact ⟨a, d, hd0, hdk, hd, hchar a b hP⟩
  · have he : (a - b).val = k - d := by
      have hn : a - b = -(b - a) := by abel
      simp only [hn, Fin.val_neg, if_neg (sub_ne_zero.mpr (Ne.symm hab)), d]
    refine ⟨b, (a - b).val, by omega, (a - b).isLt, by omega, ?_⟩
    exact hchar b a (fun i => by rw [hP]; tauto)

/-- Exactly two SMALL occurrences force a nonzero row. The zero case uses
the existing opposite-rotation owner, rather than reproving cyclic propagation. -/
private theorem no_zero {k : ℕ} (hk : 3 ≤ k) (t : ℕ)
    (htwo : (Finset.univ.filter (fun i : Fin k =>
      |actualSource k t i| < quarter k)).card = 2) :
    ∀ i, actualSource k t i ≠ 0 := by
  classical
  letI : NeZero k := ⟨by omega⟩
  intro i hi
  have hall (j : Fin k) : actualSource k t j = 0 := by
    have hop : actualSource k t i = -actualSource k t i := by rw [hi]; norm_num
    have hh := AntipodalSourceCompletion.opposite_rotation hk t i i hop j
    change actualSource k t (finCycle (i - i) j) = -actualSource k t j at hh
    simp only [sub_self, finCycle_apply, add_zero] at hh
    omega
  have hset : Finset.univ.filter (fun i : Fin k =>
      |actualSource k t i| < quarter k) = Finset.univ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp [hall j, show 0 < quarter k from lt_of_lt_of_le (by norm_num) (source_geometry hk).1]
  rw [hset, Finset.card_univ, Fintype.card_fin] at htwo
  omega

/-- Native two-defect normalization: gaps are physical distances, and every
profile hypothesis is derived from the source and the SMALL inventory. -/
theorem actual_two_gap_profile {k : ℕ} (hk : 3 ≤ k) (t : ℕ)
    (htwo : (Finset.univ.filter (fun i : Fin k =>
      |actualSource k t i| < quarter k)).card = 2) :
    ∃ (o : Fin k) (negative : Bool) (ell m : ℕ),
      k = ell + m + 2 ∧ ell ≤ m ∧ ell % 2 = m % 2 ∧
      let w := fun j => orient negative (actualSource k t (phase (by omega) o j))
      let r := paritySign ell * w (ell + 1)
      0 < w 0 ∧ 0 < r ∧
        3 * w 0 = half k - (-2 : ℤ) ^ m ∧
        3 * r = half k - (-2 : ℤ) ^ ell ∧
        (∀ j ≤ ell, 3 * w (j + 1) =
          paritySign j * modulus k + (2 : ℤ) ^ j * (6 * w 0 - modulus k)) ∧
        (∀ j < k, quarter k ≤ |w j| ↔ j ≠ 0 ∧ j ≠ ell + 1) ∧
        (∀ j ≤ m, 3 * (paritySign ell * w (ell + 1 + (j + 1))) =
          paritySign j * modulus k + (2 : ℤ) ^ j * (6 * r - modulus k)) := by
  classical
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp htwo
  have hp (i : Fin k) : |actualSource k t i| < quarter k ↔ i = a ∨ i = b := by
    have he := Finset.ext_iff.mp hset i
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] using he
  obtain ⟨o, d, hd0, hdk, hdshort, hchar⟩ := short_gap (by omega)
    (fun i => |actualSource k t i| < quarter k) a b hab hp
  let negative := decide (actualSource k t o < 0)
  let w := fun j => orient negative (actualSource k t (phase (by omega) o j))
  let ell := d - 1
  let m := k - d - 1
  have hk' : k = ell + m + 2 := by dsimp [ell, m]; omega
  have hd : ell + 1 = d := by dsimp [ell]; omega
  have hwpos : 0 < w 0 := by
    have hn := no_zero hk t htwo o
    dsimp [w, negative]
    rw [phase_zero]
    by_cases he : actualSource k t o < 0 <;> simp [orient, he] <;> omega
  obtain ⟨hQ, hN, hC, hN0, hodd⟩ := source_geometry hk
  have hwb : ∀ j ≤ ell + m + 2, -(half k) ≤ w j ∧ w j ≤ half k := by
    intro j _
    have hh := centered_bounds hN0 hodd
      ((2 : ℤ) ^ (phase (by omega) o j).val * t)
    change -(half k) ≤ actualSource k t (phase (by omega) o j) ∧
      actualSource k t (phase (by omega) o j) ≤ half k at hh
    dsimp [w]
    cases negative <;> simp only [orient, Bool.false_eq_true, ite_false, ite_true] <;> omega
  have hws : w 0 < quarter k := by
    have hh := (hchar 0 (by omega)).mpr (Or.inl rfl)
    have he : |w 0| = |actualSource k t (phase (by omega) o 0)| := orient_abs _ _
    rw [← he, abs_of_pos hwpos] at hh
    exact hh
  have hwsmall : |w (ell + 1)| < quarter k := by
    have hh := (hchar d hdk).mpr (Or.inr rfl)
    simpa only [w, hd, orient_abs] using hh
  have hwlarge : ∀ j, 0 < j → j < ell + m + 2 → j ≠ ell + 1 →
      quarter k ≤ |w j| := by
    intro j hj hjk hjd
    have hh := hchar j (by omega)
    have hn : ¬|actualSource k t (phase (by omega) o j)| < quarter k := by
      intro hs
      rcases hh.mp hs with h | h <;> omega
    simpa only [w, orient_abs] using le_of_not_gt hn
  have hwstep : ∀ j < ell + m + 2, w (j + 1) = doubleStep (modulus k) (w j) := by
    intro j _
    have hh := phase_step hk t o j
    dsimp [w]
    rw [hh]
    cases negative <;> simp only [orient, Bool.false_eq_true, ite_false, ite_true]
    exact (doubleStep_neg (le_of_lt hN0)).symm
  have hwlarge' : ∀ j < k, quarter k ≤ |w j| ↔ j ≠ 0 ∧ j ≠ ell + 1 := by
    intro j hj
    have hh := hchar j hj
    have hs : |w j| < quarter k ↔ j = 0 ∨ j = ell + 1 := by
      simpa only [w, orient_abs, hd] using hh
    constructor
    · intro h
      constructor
      · intro hj0
        exact (not_lt_of_ge h) (hs.mpr (Or.inl hj0))
      · intro hjd
        exact (not_lt_of_ge h) (hs.mpr (Or.inr hjd))
    · intro h
      have hn : ¬ |w j| < quarter k := by
        intro hs'
        rcases hs.mp hs' with hj0 | hjd
        · exact h.1 hj0
        · exact h.2 hjd
      omega
  have hwclose : w (ell + m + 2) = w 0 := by
    have he : phase (by omega) o (ell + m + 2) = phase (by omega) o 0 := by
      apply Fin.ext
      simp only [phase, ← hk', Nat.add_mod_right, Nat.zero_mod, Nat.add_zero]
    dsimp [w]; rw [he]
  have hpow : quarter k = (2 : ℤ) ^ (ell + m) := by
    unfold quarter
    congr 1
    omega
  obtain ⟨hr, hpar, hs, hrval, hfirst, hsecond⟩ :=
    cyclic_two_gap_classifier ell m (quarter k) (modulus k) (half k) hQ hpow hN hC w
      hwb ⟨hwpos, hws⟩ hwsmall hwlarge hwstep hwclose
  exact ⟨o, negative, ell, m, hk', by dsimp [ell, m]; omega, hpar,
    hwpos, hr, hs, hrval, hfirst, hwlarge', hsecond⟩


private theorem two_even (n : ℕ) : (2 : ℤ) ^ (2 * n) = (4 : ℤ) ^ n := by
  rw [pow_mul]; norm_num
private theorem neg_two_even (n : ℕ) : (-2 : ℤ) ^ (2 * n) = (4 : ℤ) ^ n := by
  rw [pow_mul]; norm_num
private theorem sign_even (n : ℕ) : paritySign (2 * n) = 1 := by simp [paritySign]
private theorem sign_odd (n : ℕ) : paritySign (2 * n + 1) = -1 := by simp [paritySign]

private theorem normalized_placement (ell m : ℕ) (hle : ell ≤ m)
    (hpar : ell % 2 = m % 2) (hsize : 1 ≤ ell + m)
    (N C : ℤ) (hN : N = 4 * (2 : ℤ) ^ (ell + m) - 1)
    (hC : C = 2 * (2 : ℤ) ^ (ell + m) - 1)
    (w : ℕ → ℤ)
    (hs : 3 * w 0 = C - (-2 : ℤ) ^ m)
    (hr : 3 * (paritySign ell * w (ell + 1)) = C - (-2 : ℤ) ^ ell)
    (hfirst : ∀ j ≤ ell, 3 * w (j + 1) =
      paritySign j * N + (2 : ℤ) ^ j * (6 * w 0 - N))
    (hsecond : ∀ j ≤ m, 3 * (paritySign ell * w (ell + 1 + (j + 1))) =
      paritySign j * N + (2 : ℤ) ^ j *
        (6 * (paritySign ell * w (ell + 1)) - N)) :
    ∃ word : List ℕ, word.Perm (List.range (ell + m + 2)) ∧
      InStrip w C 0 word ∧ (word.map w).sum = 0 ∧
      word.filter (fun j => decide (j ≠ 0 ∧ j ≠ ell + 1)) =
        List.range' 1 ell ++ List.range' (ell + 2) m := by
  let p := ell / 2
  let q := m / 2
  by_cases he : ell % 2 = 0
  · have hell : ell = 2 * p := by dsimp [p]; omega
    have hm : m = 2 * q := by dsimp [q]; omega
    let a : ℤ := (4 : ℤ) ^ p
    let b : ℤ := (4 : ℤ) ^ q
    have hpq : p ≤ q := by omega
    have hne : 1 ≤ p + q := by omega
    have hp : (2 : ℤ) ^ (ell + m) = a * b := by
      rw [hell, hm, pow_add, two_even, two_even]
    have hn : N = 4 * a * b - 1 := by rw [hp] at hN; nlinarith only [hN]
    have hc : C = 2 * a * b - 1 := by rw [hp] at hC; nlinarith only [hC]
    have hs' : 3 * w 0 = C - b := by simpa only [hm, neg_two_even] using hs
    have hr' : 3 * w (2 * p + 1) = C - a := by
      simpa only [hell, sign_even, one_mul, neg_two_even] using hr
    have h6s : 6 * w 0 - N = -(2 * b + 1) := by nlinarith
    have h6r : 6 * w (2 * p + 1) - N = -(2 * a + 1) := by nlinarith
    let f := fun j => 3 * w j
    obtain ⟨word, hperm, hstrip, hsum, hdel⟩ := even_placement p q hpq hne a b N C rfl rfl hn hc f
      hs' hr' (by
        intro i hi
        have h1 := hfirst (2 * i) (by omega)
        have h2 := hfirst (2 * i + 1) (by omega)
        rw [sign_even, one_mul, two_even, h6s] at h1
        rw [sign_odd, neg_one_mul, pow_succ, two_even, h6s] at h2
        simp only [f]
        rw [show 2 * i + 1 + 1 = 2 * i + 2 by omega] at h2
        constructor <;> nlinarith only [h1, h2]) (by
        intro j hj
        have h1 := hsecond (2 * j) (by omega)
        have h2 := hsecond (2 * j + 1) (by omega)
        simp only [hell, sign_even, one_mul] at h1 h2
        rw [two_even, h6r] at h1
        rw [sign_odd, neg_one_mul, pow_succ, two_even, h6r] at h2
        rw [show 2 * p + 1 + (2 * j + 1) = 2 * p + 2 + 2 * j by omega] at h1
        rw [show 2 * p + 1 + (2 * j + 1 + 1) = 2 * p + 3 + 2 * j by omega] at h2
        constructor <;> nlinarith only [h1, h2])
    refine ⟨word, by simpa [hell, hm, Nat.add_assoc] using hperm,
      unscale_strip w C 0 word hstrip, ?_, ?_⟩
    have hsum' : 3 * (word.map w).sum = 0 := by
      simpa only [f, List.sum_map_mul_left] using hsum
    · omega
    · simpa [hell, hm] using hdel
  · have hell : ell = 2 * p + 1 := by dsimp [p]; omega
    have hm : m = 2 * q + 1 := by dsimp [q]; omega
    let a : ℤ := 2 * (4 : ℤ) ^ p
    let b : ℤ := 2 * (4 : ℤ) ^ q
    have hp : (2 : ℤ) ^ (ell + m) = a * b := by
      rw [hell, hm, pow_add, pow_succ, pow_succ, two_even, two_even]
      dsimp [a, b]; ring
    have hn : N = 4 * a * b - 1 := by rw [hp] at hN; nlinarith only [hN]
    have hc : C = 2 * a * b - 1 := by rw [hp] at hC; nlinarith only [hC]
    have hs' : 3 * w 0 = C + b := by
      rw [hm, pow_succ, neg_two_even] at hs
      dsimp [b]; nlinarith only [hs]
    have hr' : 3 * (-w (2 * p + 2)) = C + a := by
      rw [hell, sign_odd, neg_one_mul, pow_succ, neg_two_even] at hr
      rw [show 2 * p + 1 + 1 = 2 * p + 2 by omega] at hr
      dsimp [a]; nlinarith only [hr]
    have h6s : 6 * w 0 - N = 2 * b - 1 := by nlinarith
    have h6r : 6 * (-w (2 * p + 2)) - N = 2 * a - 1 := by nlinarith
    let f := fun j => 3 * w j
    obtain ⟨word, hperm, hstrip, hsum, hdel⟩ := odd_placement p q a b N C rfl rfl hn hc f
      hs' (by dsimp [f]; nlinarith only [hr']) (by
        intro i hi
        have ht := hfirst (2 * i) (by omega)
        rw [sign_even, one_mul, two_even, h6s] at ht
        dsimp [f]; nlinarith only [ht]) (by
        intro i hi
        have ht := hfirst (2 * i + 1) (by omega)
        rw [sign_odd, neg_one_mul, pow_succ, two_even, h6s] at ht
        rw [show 2 * i + 1 + 1 = 2 * i + 2 by omega] at ht
        dsimp [f]; nlinarith only [ht]) (by
        intro j hj
        have ht := hsecond (2 * j) (by omega)
        simp only [hell, sign_odd, sign_even, neg_one_mul, one_mul] at ht
        rw [show 2 * p + 1 + 1 = 2 * p + 2 by omega, two_even, h6r] at ht
        rw [show 2 * p + 2 + (2 * j + 1) = 2 * p + 3 + 2 * j by omega] at ht
        dsimp [f]; nlinarith only [ht]) (by
        intro j hj
        have ht := hsecond (2 * j + 1) (by omega)
        simp only [hell, sign_odd, neg_one_mul] at ht
        rw [show 2 * p + 1 + 1 = 2 * p + 2 by omega,
          pow_succ, two_even, h6r] at ht
        rw [show 2 * p + 2 + (2 * j + 1 + 1) = 2 * p + 4 + 2 * j by omega] at ht
        dsimp [f]; nlinarith only [ht])
    refine ⟨word, by simpa only [show ell + m + 2 = 2 * p + 2 * q + 4 by omega] using hperm,
      unscale_strip w C 0 word hstrip, ?_, ?_⟩
    have hsum' : 3 * (word.map w).sum = 0 := by
      simpa only [f, List.sum_map_mul_left] using hsum
    · omega
    · simpa [hell, hm] using hdel



/-- Negating a zero-total strip word admits a cyclic cut whose every prefix
is nonnegative and bounded by both the strip width and the original cut height. -/
theorem negate_rotation_prefix_bound {α : Type*} (f : α → ℤ) (C : ℤ) (L : List α)
    (hs : InStrip f C 0 L) (hm : (L.map f).sum = 0) :
    ∃ j ≤ L.length, ∀ n : ℕ,
      0 ≤ (((L.rotate j).take n).map (fun x => -f x)).sum ∧
      (((L.rotate j).take n).map (fun x => -f x)).sum ≤ C ∧
      (((L.rotate j).take n).map (fun x => -f x)).sum ≤ ((L.take j).map f).sum := by
  classical
  let w := L.map (fun x => -f x)
  have hw : w.sum = 0 := by dsimp [w]; rw [sum_neg_map, hm]; omega
  have hb (n : ℕ) : -C ≤ (w.take n).sum ∧ (w.take n).sum ≤ 0 := by
    have hp := inStrip_prefix hs n
    have he : (w.take n).sum = -((L.take n).map f).sum := by
      dsimp [w]
      rw [← List.map_take, sum_neg_map]
    rw [he]
    omega
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image (Finset.range (w.length + 1))
    (fun n => (w.take n).sum) ⟨0, by simp⟩
  have hj' : j ≤ w.length := by simp only [Finset.mem_range] at hj; omega
  have hminimum : ∀ n ≤ w.length, (w.take j).sum ≤ (w.take n).sum :=
    fun n hn => hmin n (Finset.mem_range.mpr (by omega))
  have hnonneg :=
    D5.S1.Words.Compositions.ZeroSumWordCount.nonnegative_rotate_of_minimum hw hj' hminimum
  refine ⟨j, by simpa [w] using hj', ?_⟩
  intro n
  have hupper : ((w.rotate j).take n).sum ≤ -(w.take j).sum := by
    have hsplit := congrArg List.sum (List.take_append_drop j w)
    simp only [List.sum_append] at hsplit
    rw [List.rotate_eq_drop_append_take hj', List.take_append, List.sum_append]
    by_cases hn : n ≤ w.length - j
    · have hz : n - (w.drop j).length = 0 := by simp only [List.length_drop]; omega
      rw [hz, List.take_zero, List.sum_nil, add_zero]
      have he := D5.S1.Words.Compositions.ZeroSumWordCount.prefix_segment_sum w j n
      have h2 := hb (j + n)
      omega
    · have hd : (w.drop j).length ≤ n := by simp only [List.length_drop]; omega
      rw [List.take_of_length_le hd, List.take_take]
      have h2 := hb (min (n - (w.drop j).length) j)
      omega
  have hcut : (w.take j).sum = -((L.take j).map f).sum := by
    dsimp [w]
    rw [← List.map_take, sum_neg_map]
  have hwidth := (hb j).1
  have hh : 0 ≤ ((w.rotate j).take n).sum ∧
      ((w.rotate j).take n).sum ≤ C ∧
      ((w.rotate j).take n).sum ≤ ((L.take j).map f).sum :=
    ⟨hnonneg n, by omega, by omega⟩
  simpa only [w, List.map_rotate, List.map_take] using hh

/-- A zero-total strip word can be negated by cutting at an attained minimum
of the negated prefix sums. Only a cyclic rotation of labels is made. -/
theorem negate_rotation {α : Type*} (f : α → ℤ) (C : ℤ) (L : List α)
    (hs : InStrip f C 0 L) (hm : (L.map f).sum = 0) :
    ∃ j ≤ L.length, ∀ n : ℕ,
      0 ≤ (((L.rotate j).take n).map (fun x => -f x)).sum ∧
      (((L.rotate j).take n).map (fun x => -f x)).sum ≤ C := by
  obtain ⟨j, hj, hprefix⟩ := negate_rotation_prefix_bound f C L hs hm
  exact ⟨j, hj, fun n => ⟨(hprefix n).1, (hprefix n).2.1⟩⟩

/-- Complete native completion for exactly two physical SMALL occurrences.
No gate, competitor, favorable source rotation or value-injectivity premise
is supplied. Every natural take, endpoint, and physical inventory is retained. -/
theorem actualSource_two_small_full_completion {k : ℕ} (hk : 3 ≤ k) (t : ℕ)
    (htwo : (Finset.univ.filter (fun i : Fin k =>
      |actualSource k t i| < quarter k)).card = 2) :
    ∃ L : List (Fin k),
      L.Perm (List.ofFn (fun q : Fin k => q)) ∧
      L.Nodup ∧ L.toFinset = Finset.univ ∧
      InStrip (actualSource k t) (half k) 0 L ∧
      (∀ n : ℕ, 0 ≤ mass (actualSource k t) (L.take n) ∧
        mass (actualSource k t) (L.take n) ≤ half k) ∧
      mass (actualSource k t) L = 0 ∧ Legal k t L ∧
      (L.filter (fun i => decide (quarter k ≤ |actualSource k t i|))).IsRotated
        ((List.finRange k).filter (fun i => decide (quarter k ≤ |actualSource k t i|))) := by
  classical
  letI : NeZero k := ⟨by omega⟩
  obtain ⟨o, negative, ell, m, hk', hle, hpar, hspos, hrpos,
    hs, hr, hfirst, hlarge, hsecond⟩ := actual_two_gap_profile hk t htwo
  let w := fun j => orient negative (actualSource k t (phase (by omega) o j))
  obtain ⟨hQ, hN, hC, hN0, hodd⟩ := source_geometry hk
  have hpow : quarter k = (2 : ℤ) ^ (ell + m) := by
    unfold quarter; congr 1; omega
  have hn : modulus k = 4 * (2 : ℤ) ^ (ell + m) - 1 := by rwa [hpow] at hN
  have hc : half k = 2 * (2 : ℤ) ^ (ell + m) - 1 := by rwa [hpow] at hC
  obtain ⟨word, hp, hwstrip, hwsum, hdeleted⟩ := normalized_placement ell m hle hpar (by omega)
    (modulus k) (half k) hn hc w hs hr hfirst hsecond
  let phi := phase (by omega : 0 < k) o
  let L := word.map phi
  let e : Equiv.Perm (Fin k) := Equiv.addLeft o
  have hbase : (List.range k).map phi = List.ofFn e := by
    rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
    apply List.map_congr_left
    intro i _
    change phase (by omega) o i.val = o + i
    apply Fin.ext
    rfl
  have hphase : (List.range k).map phi = (List.finRange k).rotate o.val := by
    rw [hbase]
    apply List.ext_getElem
    · simp
    · intro i hi₁ hi₂
      simp only [List.getElem_ofFn, List.getElem_rotate, List.getElem_finRange,
        List.length_ofFn, List.length_rotate, List.length_finRange]
      apply Fin.ext
      simp [e, phi, phase, Fin.val_add, Nat.add_mod, Nat.add_comm]
  let p : Fin k → Bool := fun i => decide (quarter k ≤ |actualSource k t i|)
  let q : ℕ → Bool := fun j => decide (j ≠ 0 ∧ j ≠ ell + 1)
  have hpred (j : ℕ) (hj : j ∈ word) : p (phi j) = q j := by
    have hjk : j < k := by
      have hh := hp.mem_iff.mp hj
      simp only [List.mem_range] at hh
      omega
    have hh := hlarge j hjk
    apply decide_eq_decide.mpr
    simpa only [p, q, phi, w, orient_abs] using hh
  have hwordfilter : L.filter p = (word.filter q).map phi := by
    dsimp only [L]
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro j hj
    simpa only [Function.comp_def] using hpred j hj
  have hfullfilter : ((List.range k).map phi).filter p =
      ((List.range k).filter q).map phi := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro j hj
    have hjk := List.mem_range.mp hj
    have hh := hlarge j hjk
    apply decide_eq_decide.mpr
    simpa only [Function.comp_def, p, q, phi, w, orient_abs] using hh
  have hforwardQ : (List.range k).filter q = word.filter q := by
    rw [hk', range_filter_delete]
    simpa only [q] using hdeleted.symm
  have hphaseorder : L.filter p ~r (List.finRange k).filter p := by
    rw [hwordfilter, ← hforwardQ, ← hfullfilter, hphase]
    exact filter_rotate p (List.finRange k) o.val

  have hpL : L.Perm (List.ofFn (fun q : Fin k => q)) := by
    have hh := hp.map phi
    rw [← hk', hbase] at hh
    exact hh.trans (by simpa only [Function.comp_def, id_eq] using e.ofFn_comp_perm (fun q => q))
  have hpref (n : ℕ) :
      0 ≤ mass (fun q => orient negative (actualSource k t q)) (L.take n) ∧
      mass (fun q => orient negative (actualSource k t q)) (L.take n) ≤ half k := by
    have hh := inStrip_prefix hwstrip n
    simpa only [L, phi, w, mass, ← List.map_take, List.map_map, Function.comp_def,
      zero_add] using hh
  have hstrip : InStrip (fun q => orient negative (actualSource k t q)) (half k) 0 L :=
    strip_of_all_prefixes L (by simpa only [zero_add] using hpref)
  have hsum : (L.map (fun q => orient negative (actualSource k t q))).sum = 0 := by
    simpa only [L, phi, w, List.map_map, Function.comp_def] using hwsum
  have hcompletion : ∃ R : List (Fin k), R.Perm (List.ofFn (fun q : Fin k => q)) ∧
      InStrip (actualSource k t) (half k) 0 R ∧ mass (actualSource k t) R = 0 ∧
      L.IsRotated R := by
    cases negative with
    | false => exact ⟨L, hpL, by simpa only [orient, Bool.false_eq_true, ite_false] using hstrip,
        by simpa only [orient, Bool.false_eq_true, ite_false, mass] using hsum,
        List.IsRotated.refl L⟩
    | true =>
      obtain ⟨j, hj, hrot⟩ := negate_rotation
        (fun q => orient true (actualSource k t q)) (half k) L hstrip hsum
      have hpR := (List.rotate_perm L j).trans hpL
      have hprefixR (n : ℕ) : 0 ≤ mass (actualSource k t) ((L.rotate j).take n) ∧
          mass (actualSource k t) ((L.rotate j).take n) ≤ half k := by
        simpa only [orient, ite_true, neg_neg, mass] using hrot n
      have hmL : mass (actualSource k t) L = 0 := by
        simp only [orient, ite_true, sum_neg_map] at hsum
        dsimp [mass]; omega
      have hmR : mass (actualSource k t) (L.rotate j) = 0 := by
        dsimp [mass]
        rw [((List.rotate_perm L j).map (actualSource k t)).sum_eq]
        exact hmL
      exact ⟨L.rotate j, hpR, strip_of_all_prefixes _ (by simpa using hprefixR), hmR,
        (List.IsRotated.forall L j).symm⟩
  obtain ⟨R, hpR, hsR, hmR, hLR⟩ := hcompletion
  have hnR : R.Nodup := hpR.nodup_iff.mpr
    (List.nodup_ofFn_ofInjective (f := fun q : Fin k => q) (fun _ _ h => h))
  have huR : R.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro q
    exact List.mem_toFinset.mpr (hpR.mem_iff.mpr (List.mem_ofFn.mpr ⟨q, rfl⟩))
  have hlegal : Legal k t R := legal_of_strip hnR hsR
  have hRfilter : R.filter p ~r (List.finRange k).filter p := by
    rcases hLR with ⟨j, hj⟩
    rw [← hj]
    exact (filter_rotate p L j).trans hphaseorder
  exact ⟨R, hpR, hnR, huR, hsR, hlegal.2, hmR, hlegal, by simpa only [p] using hRfilter⟩



end D5.S3.Combinatorics.Circle.TwoSmallSource
