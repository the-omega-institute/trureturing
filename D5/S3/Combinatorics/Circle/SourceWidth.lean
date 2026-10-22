/- GID: D5/S3/Combinatorics/Circle/SourceWidth
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/SourceWidth
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.Int.ModEq, mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical source labels and full-arc binary schedules for a universal width bound. -/
import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Rotate
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic

/-! # Labelled centered sources and binary full-arc expansion -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.SourceWidth

/-- The odd modulus of the original source. -/
def modulus (k : ℕ) : ℤ := (2 : ℤ) ^ k - 1

/-- Centered residue, with the integer half-modulus shift. -/
def centered (N x : ℤ) : ℤ := (x + N / 2) % N - N / 2

/-- Values retain their physical labels even when different labels have equal values. -/
def actualSource (k t : ℕ) (p : Fin k) : ℤ :=
  centered (modulus k) ((2 : ℤ) ^ p.val * (t : ℤ))

/-- The support capacity, larger than the conjectured half-modulus capacity. -/
def capacity (k : ℕ) : ℤ := modulus k - modulus k / 3 - 2

theorem centered_bounds {N : ℤ} (hN : 0 < N) (hodd : N % 2 = 1) (x : ℤ) :
    -(N / 2) ≤ centered N x ∧ centered N x ≤ N / 2 := by
  have hlo := Int.emod_nonneg (x + N / 2) (ne_of_gt hN)
  have hhi := Int.emod_lt_of_pos (x + N / 2) hN
  have he := Int.emod_add_mul_ediv N 2
  dsimp [centered]
  omega

private theorem centered_mod (N x : ℤ) : centered N x % N = x % N := by
  simp only [centered, Int.emod_sub_emod, add_sub_cancel_right]

private theorem centered_unique {N x y : ℤ} (hN : 0 < N) (hodd : N % 2 = 1)
    (hx : -(N / 2) ≤ x ∧ x ≤ N / 2)
    (hy : -(N / 2) ≤ y ∧ y ≤ N / 2) (he : x % N = y % N) : x = y := by
  have hd := (Int.modEq_iff_dvd).mp he
  obtain ⟨q, hq⟩ := hd
  have hn := Int.emod_add_mul_ediv N 2
  have hq0 : q = 0 := by
    by_contra h
    rcases lt_or_gt_of_ne h with h | h
    · have := mul_le_mul_of_nonneg_left (show q ≤ -1 by omega) (le_of_lt hN)
      nlinarith
    · have := mul_le_mul_of_nonneg_left (show 1 ≤ q by omega) (le_of_lt hN)
      nlinarith
  simp [hq0] at hq
  omega

private theorem centered_congr {N x y : ℤ} (h : x % N = y % N) :
    centered N x = centered N y := by
  unfold centered
  exact congrArg (fun z : ℤ => z - N / 2) (Int.add_emod_eq_add_emod_right (N / 2) h)

/-- The strict centered-doubling branches; oddness rules out half endpoints. -/
def doubleStep (N s : ℤ) : ℤ :=
  if N < 4 * s then 2 * s - N else if 4 * s < -N then 2 * s + N else 2 * s

theorem centered_double {N : ℤ} (hN : 0 < N) (hodd : N % 2 = 1) (x : ℤ) :
    centered N (2 * x) = doubleStep N (centered N x) := by
  let s := centered N x
  have hs : -(N / 2) ≤ s ∧ s ≤ N / 2 := centered_bounds hN hodd x
  have he : centered N (2 * x) % N = (2 * s) % N := by
    rw [centered_mod]
    change (2 * x) % N = (2 * centered N x) % N
    rw [Int.mul_emod 2 x N, Int.mul_emod 2 (centered N x) N, centered_mod]
  apply centered_unique hN hodd (centered_bounds hN hodd (2 * x))
  · dsimp [doubleStep]
    split_ifs <;> have hn := Int.emod_add_mul_ediv N 2 <;> omega
  · dsimp [doubleStep]
    split_ifs <;> simpa only [Int.sub_emod_right, Int.add_emod_right] using he

theorem unsigned_step {N s : ℤ} (hN : 0 < N) (hodd : N % 2 = 1)
    (hs : -(N / 2) ≤ s ∧ s ≤ N / 2) :
    (doubleStep N s + if doubleStep N s < 0 then N else 0) -
      (s + if s < 0 then N else 0) = s := by
  have hn := Int.emod_add_mul_ediv N 2
  dsimp [doubleStep]
  split_ifs <;> omega


/-- Every intermediate integer height, including the two endpoints. -/
def InStrip {α : Type*} (f : α → ℤ) (B h : ℤ) : List α → Prop
  | [] => 0 ≤ h ∧ h ≤ B
  | x :: xs => 0 ≤ h ∧ h ≤ B ∧ InStrip f B (h + f x) xs

theorem inStrip_prefix {α : Type*} {f : α → ℤ} {B h : ℤ} {l : List α}
    (hl : InStrip f B h l) (n : ℕ) :
    0 ≤ h + ((l.take n).map f).sum ∧ h + ((l.take n).map f).sum ≤ B := by
  induction l generalizing h n with
  | nil => simpa [InStrip] using hl
  | cons x xs ih =>
    cases n with
    | zero => simpa using And.intro hl.1 hl.2.1
    | succ n =>
      have hn := ih hl.2.2 n
      simpa [List.take_succ_cons, add_assoc] using hn

theorem inStrip_append {α : Type*} {f : α → ℤ} {B h : ℤ} {l r : List α}
    (hl : InStrip f B h l) (hr : InStrip f B (h + (l.map f).sum) r) :
    InStrip f B h (l ++ r) := by
  induction l generalizing h with
  | nil => simpa using hr
  | cons x xs ih =>
    refine ⟨hl.1, hl.2.1, ih hl.2.2 ?_⟩
    simpa [List.map_cons, List.sum_cons, add_assoc] using hr

theorem inStrip_nonpos {α : Type*} {f : α → ℤ} {B h : ℤ} {l : List α}
    (hf : ∀ x ∈ l, f x ≤ 0) (hh : h ≤ B) (hend : 0 ≤ h + (l.map f).sum) :
    InStrip f B h l := by
  induction l generalizing h with
  | nil => simpa [InStrip] using And.intro hend hh
  | cons x xs ih =>
    have hx := hf x (by simp)
    have hxs : ∀ y ∈ xs, f y ≤ 0 := fun y hy => hf y (by simp [hy])
    have hs : (xs.map f).sum ≤ 0 := by simpa using (List.sum_le_sum hxs)
    simp only [List.map_cons, List.sum_cons] at hend
    refine ⟨by omega, hh, ih hxs (by omega) ?_⟩
    omega

private theorem inStrip_reflect {α : Type*} {f : α → ℤ} {B h : ℤ} {l : List α}
    (hl : InStrip (fun x => -f x) B (B - h) l) : InStrip f B h l := by
  induction l generalizing h with
  | nil => dsimp [InStrip] at *; omega
  | cons x xs ih =>
    dsimp only [InStrip] at hl ⊢
    refine ⟨by omega, by omega, ih ?_⟩
    convert hl.2.2 using 1 <;> ring

/-- The original occurrence list carries an increasing dyadic ladder. -/
def Dyadic {α : Type*} (f : α → ℤ) : ℤ → List α → Prop
  | _, [] => True
  | b, x :: xs => f x = b ∧ Dyadic f (2 * b) xs

theorem dyadic_sum {α : Type*} {f : α → ℤ} {b : ℤ} {l : List α}
    (hl : Dyadic f b l) : (l.map f).sum = ((2 : ℤ) ^ l.length - 1) * b := by
  induction l generalizing b with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, hl.1, ih hl.2, List.length_cons, pow_succ]
    ring

private theorem dyadic_nonneg {α : Type*} {f : α → ℤ} {b : ℤ} {l : List α}
    (hb : 0 ≤ b) (hl : Dyadic f b l) : ∀ x ∈ l, 0 ≤ f x := by
  induction l generalizing b with
  | nil => simp
  | cons x xs ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · simpa [hl.1] using hb
    · exact ih (by omega) hl.2 y hy

/-- Binary digit selection on physical occurrences, retaining the complementary occurrences. -/
theorem dyadic_select {α : Type*} {f : α → ℤ} {b : ℤ} {l : List α}
    (hl : Dyadic f b l) (n : ℕ) (hn : n < 2 ^ l.length) :
    ∃ before after : List α, (before ++ after).Perm l ∧
      (before.map f).sum = (n : ℤ) * b := by
  induction l generalizing b n with
  | nil =>
    have : n = 0 := by simpa using hn
    subst n
    exact ⟨[], [], by simp, by simp⟩
  | cons x xs ih =>
    have hdiv : n / 2 < 2 ^ xs.length := by
      have hp : 0 < 2 ^ xs.length := pow_pos (by decide) _
      rw [List.length_cons, pow_succ] at hn
      omega
    obtain ⟨pre, post, hperm, hsum⟩ := ih hl.2 (n / 2) hdiv
    by_cases heven : n % 2 = 0
    · refine ⟨pre, x :: post, ?_, ?_⟩
      · exact (List.perm_middle).trans (hperm.cons x)
      · have hn' : (n : ℤ) = 2 * (n / 2 : ℕ) := by omega
        rw [hsum, hn']; ring
    · refine ⟨x :: pre, post, ?_, ?_⟩
      · simpa using hperm.cons x
      · have hn' : (n : ℤ) = 2 * (n / 2 : ℕ) + 1 := by omega
        simp only [List.map_cons, List.sum_cons, hl.1, hsum]
        rw [hn']; ring


theorem sum_neg_map {α : Type*} (f : α → ℤ) (l : List α) :
    (l.map (fun x => -f x)).sum = -(l.map f).sum := by
  simpa [List.map_map, Function.comp_def, negAddMonoidHom] using
    (map_list_sum (negAddMonoidHom : ℤ →+ ℤ) (l.map f)).symm

private theorem positive_packet {α : Type*} {f : α → ℤ} (parent : α) (l : List α)
    {a b B h : ℤ} (ha : f parent = a) (hb : 0 < b)
    (hl : Dyadic (fun x => -f x) b l) (hcap : a + b - 1 ≤ B)
    (hh : 0 ≤ h ∧ h ≤ B)
    (hend : 0 ≤ h + a + (l.map f).sum ∧ h + a + (l.map f).sum ≤ B) :
    ∃ word : List α, word.Perm (parent :: l) ∧ InStrip f B h word := by
  let S := (l.map (fun x => -f x)).sum
  have hS : S = ((2 : ℤ) ^ l.length - 1) * b := dyadic_sum hl
  have hsf : (l.map f).sum = -S := by dsimp [S]; rw [sum_neg_map]; omega
  have hnpos := dyadic_nonneg (le_of_lt hb) hl
  have hnneg : ∀ x ∈ l, f x ≤ 0 := by intro x hx; have := hnpos x hx; omega
  have hS0 : 0 ≤ S := List.sum_nonneg (by simpa [S] using hnpos)
  by_cases hbig : S ≤ h
  · refine ⟨l ++ [parent], ?_, ?_⟩
    · simpa using (List.perm_append_comm : (l ++ [parent]).Perm ([parent] ++ l))
    · apply inStrip_append (inStrip_nonpos hnneg hh.2 (by omega))
      simp only [InStrip, ha]
      omega
  · let n := (h / b).toNat
    have hq : 0 ≤ h / b := Int.ediv_nonneg hh.1 (le_of_lt hb)
    have hn : (n : ℤ) = h / b := Int.toNat_of_nonneg hq
    have hrem := Int.emod_nonneg h (ne_of_gt hb)
    have hrem' := Int.emod_lt_of_pos h hb
    have hdiv := Int.emod_add_mul_ediv h b
    have hnlt : n < 2 ^ l.length := by
      by_contra hn'
      have hc : (2 : ℤ) ^ l.length ≤ (n : ℤ) := by exact_mod_cast (show 2 ^ l.length ≤ n by omega)
      have hm := mul_le_mul_of_nonneg_right hc (le_of_lt hb)
      rw [hn] at hm
      nlinarith
    obtain ⟨pre, post, hp, ht⟩ := dyadic_select hl n hnlt
    have hpre : (pre.map f).sum = -(n : ℤ) * b := by
      rw [sum_neg_map] at ht
      nlinarith
    have htotal := (hp.map f).sum_eq
    simp only [List.map_append, List.sum_append] at htotal
    have hmem : ∀ x ∈ pre ++ post, f x ≤ 0 := by
      intro x hx
      exact hnneg x (hp.mem_iff.mp hx)
    have hpre' : ∀ x ∈ pre, f x ≤ 0 := fun x hx => hmem x (by simp [hx])
    have hpost' : ∀ x ∈ post, f x ≤ 0 := fun x hx => hmem x (by simp [hx])
    refine ⟨pre ++ parent :: post, List.perm_middle.trans (hp.cons parent), ?_⟩
    apply inStrip_append (inStrip_nonpos hpre' hh.2 (by nlinarith [hn]))
    change 0 ≤ h + (pre.map f).sum ∧ h + (pre.map f).sum ≤ B ∧
      InStrip f B (h + (pre.map f).sum + f parent) post
    refine ⟨by nlinarith [hn], by nlinarith [hn], ?_⟩
    apply inStrip_nonpos hpost'
    · rw [ha, hpre, hn]
      nlinarith
    · rw [ha]
      omega

private theorem signed_packet {α : Type*} {f : α → ℤ} (parent : α) (l : List α)
    {a b B h : ℤ} (hb : 0 < b) (hcap : a + b - 1 ≤ B)
    (hh : 0 ≤ h ∧ h ≤ B)
    (hend : 0 ≤ h + ((parent :: l).map f).sum ∧
      h + ((parent :: l).map f).sum ≤ B)
    (hform : (f parent = a ∧ Dyadic (fun x => -f x) b l) ∨
      (f parent = -a ∧ Dyadic f b l)) :
    ∃ word : List α, word.Perm (parent :: l) ∧ InStrip f B h word := by
  rcases hform with ⟨ha, hl⟩ | ⟨ha, hl⟩
  · apply positive_packet parent l ha hb hl hcap hh
    simpa [ha, add_assoc] using hend
  · have hh' : 0 ≤ B - h ∧ B - h ≤ B := by omega
    have hend' : 0 ≤ B - h + a + (l.map (fun x => -f x)).sum ∧
        B - h + a + (l.map (fun x => -f x)).sum ≤ B := by
      simp only [List.map_cons, List.sum_cons, ha] at hend
      rw [sum_neg_map]
      omega
    have hl' : Dyadic (fun x => - -f x) b l := by simpa using hl
    obtain ⟨word, hp, hw⟩ := positive_packet (f := fun x => -f x) parent l
      (by omega) hb hl' hcap hh' hend'
    exact ⟨word, hp, inStrip_reflect hw⟩


/-- A path retains the original labels, source successor, and unsigned potential. -/
inductive SourcePath {α : Type*} (N : ℤ) (f u : α → ℤ) : α → List α → α → Prop
  | nil (a : α) : SourcePath N f u a [] a
  | cons {a b z : α} {l : List α}
      (potential : u b - u a = f a) (successor : f b = doubleStep N (f a))
      (tail : SourcePath N f u b l z) : SourcePath N f u a (a :: l) z

theorem path_sum {α : Type*} {N : ℤ} {f u : α → ℤ} {a z : α} {l : List α}
    (hp : SourcePath N f u a l z) : (l.map f).sum = u z - u a := by
  induction hp with
  | nil => simp
  | cons hpot _ _ ih => simp only [List.map_cons, List.sum_cons]; omega

private theorem path_append {α : Type*} {N : ℤ} {f u : α → ℤ}
    {a b z : α} {l r : List α} (hl : SourcePath N f u a l b)
    (hr : SourcePath N f u b r z) : SourcePath N f u a (l ++ r) z := by
  induction hl with
  | nil => exact hr
  | cons hpot hstep _ ih => exact .cons hpot hstep (ih hr)

private theorem path_split {α : Type*} {N : ℤ} {f u : α → ℤ}
    {a z : α} (l r : List α) (hp : SourcePath N f u a (l ++ r) z) :
    ∃ b, SourcePath N f u a l b ∧ SourcePath N f u b r z := by
  induction l generalizing a with
  | nil => exact ⟨a, .nil a, hp⟩
  | cons x xs ih =>
    cases hp with
    | cons hpot hstep ht =>
      obtain ⟨b, hb, hr⟩ := ih ht
      exact ⟨b, .cons hpot hstep hb, hr⟩

private theorem path_rotate {α : Type*} {N : ℤ} {f u : α → ℤ}
    {a x : α} {l : List α} (hp : SourcePath N f u a l a) (hx : x ∈ l) :
    ∃ r : List α, r.Perm l ∧ SourcePath N f u x r x := by
  obtain ⟨left, right, he⟩ := List.mem_iff_append.mp hx
  subst l
  obtain ⟨b, hb, ht⟩ := path_split left (x :: right) hp
  cases ht with
  | cons hpot hstep tail =>
    refine ⟨(x :: right) ++ left, List.perm_append_comm, ?_⟩
    exact path_append (.cons hpot hstep tail) hb

private theorem path_until {α : Type*} {N : ℤ} {f u : α → ℤ} (P : α → Prop)
    {a z : α} {l : List α} (hp : SourcePath N f u a l z) (hz : P z) :
    ∃ mid rest : List α, ∃ q : α, l = mid ++ rest ∧
      SourcePath N f u a mid q ∧ SourcePath N f u q rest z ∧
      P q ∧ (∀ x ∈ mid, ¬ P x) := by
  classical
  induction hp with
  | nil a => exact ⟨[], [], a, rfl, .nil a, .nil a, hz, by simp⟩
  | @cons a b z l hpot hstep ht ih =>
    by_cases ha : P a
    · exact ⟨[], a :: l, a, rfl, .nil a, .cons hpot hstep ht, ha, by simp⟩
    · obtain ⟨mid, rest, q, he, hm, hr, hq, hsmall⟩ := ih hz
      refine ⟨a :: mid, rest, q, by simp [he], .cons hpot hstep hm, hr, hq, ?_⟩
      simpa using And.intro ha hsmall

private theorem path_strip {α : Type*} {N v B : ℤ} {f u : α → ℤ}
    {a z : α} {l : List α} (hp : SourcePath N f u a l z)
    (hheight : ∀ x, 0 ≤ u x - v ∧ u x - v ≤ B) :
    InStrip f B (u a - v) l := by
  induction hp with
  | nil a => exact hheight a
  | @cons a b z l hpot hstep ht ih =>
    refine ⟨(hheight a).1, (hheight a).2, ?_⟩
    convert ih using 1 <;> omega

private theorem step_exception {N A x : ℤ} (hA : 0 < A) (hN : N = 3 * A)
    (hx : x = A ∨ x = -A) : doubleStep N x = -x := by
  rcases hx with rfl | rfl <;> dsimp [doubleStep] <;> split_ifs <;> omega

private theorem path_trap {α : Type*} {N A : ℤ} {f u : α → ℤ}
    (hA : 0 < A) (hN : N = 3 * A) {a z : α} {l : List α}
    (hp : SourcePath N f u a l z) (ha : f a = A ∨ f a = -A) :
    (f z = A ∨ f z = -A) ∧ ∀ x ∈ l, f x = A ∨ f x = -A := by
  induction hp with
  | nil => exact ⟨ha, by simp⟩
  | @cons a b z l hpot hstep ht ih =>
    have hb : f b = A ∨ f b = -A := by
      rw [hstep, step_exception hA hN ha]
      rcases ha with h | h <;> simp [h]
    obtain ⟨hz, hm⟩ := ih hb
    exact ⟨hz, by simpa using And.intro ha hm⟩

private theorem small_step {N A x y : ℤ} (hA : 0 ≤ A)
    (hN : N = 3 * A ∨ N = 3 * A + 1)
    (hx : -A ≤ x ∧ x ≤ A) (hy : -A ≤ y ∧ y ≤ A)
    (hs : y = doubleStep N x) :
    y = 2 * x ∨ (N = 3 * A ∧ (x = A ∨ x = -A)) := by
  dsimp [doubleStep] at hs
  split_ifs at hs <;> rcases hN with hN | hN <;> omega

private theorem path_dyadic {α : Type*} {N A : ℤ} {f u : α → ℤ}
    (hA : 0 < A) (hN : N = 3 * A ∨ N = 3 * A + 1)
    {a z : α} {l : List α} (hp : SourcePath N f u a l z)
    (hz : A < |f z|) (hsmall : ∀ x ∈ l, |f x| ≤ A) :
    Dyadic f (f a) l := by
  induction hp with
  | nil => trivial
  | @cons a b z l hpot hstep ht ih =>
    refine ⟨rfl, ?_⟩
    cases l with
    | nil => trivial
    | cons c cs =>
      cases ht with
      | cons hpot' hstep' tail =>
        have ha := abs_le.mp (hsmall a (by simp))
        have hb := abs_le.mp (hsmall b (by simp))
        have he : f b = 2 * f a := by
          rcases small_step (le_of_lt hA) hN ha hb hstep with he | ⟨hN', ha'⟩
          · exact he
          · have htrap := (path_trap hA hN' (.cons hpot hstep (.cons hpot' hstep' tail)) ha').1
            rcases htrap with h | h <;> simp [h, abs_of_pos hA] at hz
        have hd := ih hz (by
          intro x hx
          exact hsmall x (List.mem_cons_of_mem a hx))
        rw [he] at hd
        exact hd

private theorem dyadic_neg {α : Type*} {f : α → ℤ} {b : ℤ} {l : List α}
    (hl : Dyadic f b l) : Dyadic (fun x => -f x) (-b) l := by
  induction l generalizing b with
  | nil => trivial
  | cons x xs ih =>
    refine ⟨by simp [hl.1], ?_⟩
    convert ih hl.2 using 1 <;> ring


private theorem large_step {N A x : ℤ} (hA : 2 ≤ A)
    (hN : N = 3 * A ∨ N = 3 * A + 1) (hodd : N % 2 = 1)
    (hx : -(N / 2) ≤ x ∧ x ≤ N / 2) (hlarge : A < |x|) :
    0 < N - 2 * |x| ∧ N - 2 * |x| ≤ A ∧
      ((x = |x| ∧ doubleStep N x = -(N - 2 * |x|)) ∨
        (x = -|x| ∧ doubleStep N x = N - 2 * |x|)) := by
  have he := Int.emod_add_mul_ediv N 2
  by_cases hx0 : 0 ≤ x
  · rw [abs_of_nonneg hx0] at *
    have ht : N < 4 * x := by rcases hN with h | h <;> omega
    refine ⟨by omega, ?_, Or.inl ⟨rfl, ?_⟩⟩
    · rcases hN with h | h <;> omega
    · rw [doubleStep, if_pos ht]
      ring
  · have hxneg : x < 0 := by omega
    rw [abs_of_neg hxneg] at *
    have ht : 4 * x < -N := by rcases hN with h | h <;> omega
    have ht' : ¬ N < 4 * x := by rcases hN with h | h <;> omega
    simp only [doubleStep, if_neg ht', if_pos ht]
    omega

private theorem large_path {α : Type*} {N A B v : ℤ} {f u : α → ℤ}
    (hA : 2 ≤ A) (hN : N = 3 * A ∨ N = 3 * A + 1) (hodd : N % 2 = 1)
    (hB : B = N - A - 2) (hbound : ∀ x, -(N / 2) ≤ f x ∧ f x ≤ N / 2)
    (hheight : ∀ x, A < |f x| → 0 ≤ u x - v ∧ u x - v ≤ B)
    (fuel : ℕ) {a z : α} {l : List α} (hp : SourcePath N f u a l z)
    (hlen : l.length ≤ fuel) (ha : A < |f a|) (hz : A < |f z|) :
    ∃ word : List α, word.Perm l ∧ InStrip f B (u a - v) word := by
  induction fuel generalizing a l with
  | zero =>
    have hl : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst l
    exact ⟨[], List.Perm.refl [], hheight a ha⟩
  | succ fuel ih =>
    cases hp with
    | nil => exact ⟨[], List.Perm.refl [], hheight _ ha⟩
    | @cons a b z tail hpot hstep ht =>
      obtain ⟨mid, rest, q, he, hm, hr, hq, hsmall⟩ :=
        path_until (fun x => A < |f x|) ht hz
      have hsmall' : ∀ x ∈ mid, |f x| ≤ A := by
        intro x hx
        have := hsmall x hx
        omega
      have hd := path_dyadic (by omega : 0 < A) hN hm hq hsmall'
      obtain ⟨hbpos, hbsmall, hform⟩ := large_step hA hN hodd (hbound a) ha
      have hcap : |f a| + (N - 2 * |f a|) - 1 ≤ B := by omega
      have hpath : SourcePath N f u a (a :: mid) q := .cons hpot hstep hm
      have hsum := path_sum hpath
      have hend : 0 ≤ u a - v + ((a :: mid).map f).sum ∧
          u a - v + ((a :: mid).map f).sum ≤ B := by
        have := hheight q hq
        omega
      have hform' :
          (f a = |f a| ∧ Dyadic (fun x => -f x) (N - 2 * |f a|) mid) ∨
          (f a = -|f a| ∧ Dyadic f (N - 2 * |f a|) mid) := by
        rcases hform with ⟨hfa, hs⟩ | ⟨hfa, hs⟩
        · left
          refine ⟨hfa, ?_⟩
          have hb : f b = -(N - 2 * |f a|) := hstep.trans hs
          rw [hb] at hd
          simpa using dyadic_neg hd
        · right
          refine ⟨hfa, ?_⟩
          have hb : f b = N - 2 * |f a| := hstep.trans hs
          rwa [hb] at hd
      obtain ⟨first, hfperm, hfstrip⟩ := signed_packet a mid hbpos hcap
        (hheight a ha) hend hform'
      have hrestlen : rest.length ≤ fuel := by
        simp only [List.length_cons] at hlen
        rw [he, List.length_append] at hlen
        omega
      obtain ⟨last, hlperm, hlstrip⟩ := ih hr hrestlen hq
      refine ⟨first ++ last, ?_, inStrip_append hfstrip ?_⟩
      · have htperm := hfperm.append hlperm
        simpa [he] using htperm
      · have heq := (hfperm.map f).sum_eq
        convert hlstrip using 1 <;> omega

private theorem small_maximum {N A x : ℤ} (hA : 2 ≤ A)
    (hN : N = 3 * A ∨ N = 3 * A + 1)
    (hxpos : 0 < |x|) (hxsmall : |x| ≤ A)
    (hs : |doubleStep N x| ≤ |x|) : N = 3 * A ∧ (x = A ∨ x = -A) := by
  have hs' := abs_le.mp hs
  by_cases hx0 : 0 ≤ x
  · rw [abs_of_nonneg hx0] at *
    dsimp [doubleStep] at hs'
    split_ifs at hs' <;> rcases hN with h | h <;> omega
  · have hxneg : x < 0 := by omega
    rw [abs_of_neg hxneg] at *
    dsimp [doubleStep] at hs'
    split_ifs at hs' <;> rcases hN with h | h <;> omega

private theorem cycle_schedule {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {N A : ℤ} {f u : α → ℤ} (hA : 2 ≤ A)
    (hN : N = 3 * A ∨ N = 3 * A + 1) (hodd : N % 2 = 1)
    (hbound : ∀ x, -(N / 2) ≤ f x ∧ f x ≤ N / 2)
    (hu : ∀ x, u x = f x + if f x < 0 then N else 0)
    {a : α} {l : List α} (hp : SourcePath N f u a l a)
    (hcomplete : ∀ x, x ∈ l) :
    ∃ word : List α, word.Perm l ∧ InStrip f (N - A - 2) 0 word := by
  classical
  have hB : 0 ≤ N - A - 2 := by rcases hN with h | h <;> omega
  by_cases hlarge : ∃ x, A < |f x|
  · let parents := Finset.univ.filter (fun x => A < |f x|)
    have hne : parents.Nonempty := by
      obtain ⟨x, hx⟩ := hlarge
      exact ⟨x, by simp [parents, hx]⟩
    obtain ⟨p, hpP, hpmin⟩ := parents.exists_min_image u hne
    have hpL : A < |f p| := (Finset.mem_filter.mp hpP).2
    have hpot : ∀ x, A < |f x| → A + 1 ≤ u x ∧ u x ≤ N - A - 1 := by
      intro x hx
      have hxbound := hbound x
      rw [hu]
      split_ifs with hs
      · rw [abs_of_neg hs] at hx
        omega
      · rw [abs_of_nonneg (by omega)] at hx
        omega
    have hheight : ∀ x, A < |f x| →
        0 ≤ u x - u p ∧ u x - u p ≤ N - A - 2 := by
      intro x hx
      have hmin := hpmin x (by simp [parents, hx])
      have hpx := hpot x hx
      have hpp := hpot p hpL
      omega
    obtain ⟨r, hr, hpath⟩ := path_rotate hp (hcomplete p)
    obtain ⟨word, hw, hstrip⟩ := large_path hA hN hodd rfl hbound hheight r.length
      hpath (le_refl _) hpL hpL
    exact ⟨word, hw.trans hr, by simpa using hstrip⟩
  · have hsmall : ∀ x, |f x| ≤ A := by simpa using hlarge
    obtain ⟨p, _, hpmax⟩ := Finset.univ.exists_max_image (fun x => |f x|) Finset.univ_nonempty
    have hmax : ∀ x, |f x| ≤ |f p| := fun x => hpmax x (Finset.mem_univ x)
    by_cases hzero : f p = 0
    · have hfzero : ∀ x, f x = 0 := by
        intro x
        have hx := hmax x
        simp only [hzero, abs_zero, abs_nonpos_iff] at hx
        exact hx
      have huzero : ∀ x, u x = 0 := by intro x; simp [hu, hfzero]
      have hs := path_strip (v := 0) (B := N - A - 2) hp (fun x => by rw [huzero]; omega)
      exact ⟨l, List.Perm.refl _, by simpa [huzero] using hs⟩
    · obtain ⟨r, hr, hpath⟩ := path_rotate hp (hcomplete p)
      have hrcomplete : ∀ x, x ∈ r := fun x => hr.mem_iff.mpr (hcomplete x)
      have htrap : ∀ x, f x = A ∨ f x = -A := by
        have hnonempty : r ≠ [] := by intro he; simpa [he] using hrcomplete p
        cases hpath with
        | nil p => exact False.elim (hnonempty rfl)
        | @cons p b p' tail hpot hstep ht =>
          have hs : |doubleStep N (f p)| ≤ |f p| := by rw [← hstep]; exact hmax b
          have hppos : 0 < |f p| := abs_pos.mpr hzero
          obtain ⟨hN', hp'⟩ := small_maximum hA hN hppos (hsmall p) hs
          have ht' := path_trap (by omega : 0 < A) hN' (.cons hpot hstep ht) hp'
          exact fun x => ht'.2 x (hrcomplete x)
      have hN' : N = 3 * A := by
        have hpx := htrap p
        have hs := hsmall p
        rcases hN with h | h
        · exact h
        · exfalso
          -- A boundary orbit at N = 3A+1 would immediately leave the small region.
          have hnonempty : r ≠ [] := by intro he; simpa [he] using hrcomplete p
          cases hpath with
          | nil p => exact hnonempty rfl
          | @cons p b p' tail hpot hstep ht =>
            have hbb := hsmall b
            rcases hpx with hx | hx <;> rw [hstep, hx] at hbb <;>
              dsimp [doubleStep] at hbb <;> split_ifs at hbb <;>
              have hab := abs_le.mp hbb <;> omega
      have hurange : ∀ x, A ≤ u x ∧ u x ≤ 2 * A := by
        intro x
        rcases htrap x with hx | hx <;> rw [hu, hx, hN'] <;> split_ifs <;> omega
      obtain ⟨q, _, hqmin⟩ := Finset.univ.exists_min_image u Finset.univ_nonempty
      obtain ⟨rr, hrr, hrrpath⟩ := path_rotate hp (hcomplete q)
      have hheight : ∀ x, 0 ≤ u x - u q ∧ u x - u q ≤ N - A - 2 := by
        intro x
        have hmin := hqmin x (Finset.mem_univ x)
        have hx := hurange x
        have hq := hurange q
        omega
      exact ⟨rr, hrr, by simpa using path_strip hrrpath hheight⟩


private theorem modulus_facts {k : ℕ} (hk : 3 ≤ k) :
    7 ≤ modulus k ∧ modulus k % 2 = 1 ∧
      (modulus k = 3 * (modulus k / 3) ∨ modulus k = 3 * (modulus k / 3) + 1) ∧
      2 ≤ modulus k / 3 := by
  have hpow : (8 : ℤ) ≤ 2 ^ k := by
    calc (8 : ℤ) = 2 ^ 3 := by norm_num
         _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hall : ∀ j : ℕ, (2 : ℤ) ^ j % 3 = 1 ∨ (2 : ℤ) ^ j % 3 = 2 := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih => rw [pow_succ]; omega
  have hmod3 := hall k
  have hodd : modulus k % 2 = 1 := by
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [modulus, hj, pow_succ]
    omega
  dsimp [modulus] at *
  omega

theorem centered_full_period (k t : ℕ) :
    centered (modulus k) ((2 : ℤ) ^ k * (t : ℤ)) =
      centered (modulus k) (t : ℤ) := by
  apply centered_congr
  have he : (2 : ℤ) ^ k * (t : ℤ) = (t : ℤ) + (t : ℤ) * modulus k := by
    dsimp [modulus]; ring
  rw [he, Int.add_mul_emod_self_right]

theorem path_range {α : Type*} {N : ℤ} {f u : α → ℤ} (p : ℕ → α)
    (n : ℕ) (hpot : ∀ i < n, u (p (i + 1)) - u (p i) = f (p i))
    (hstep : ∀ i < n, f (p (i + 1)) = doubleStep N (f (p i))) :
    SourcePath N f u (p 0) ((List.range n).map p) (p n) := by
  induction n with
  | zero => exact .nil _
  | succ n ih =>
    have ht := ih (fun i hi => hpot i (by omega)) (fun i hi => hstep i (by omega))
    have hl : SourcePath N f u (p n) [p n] (p (n + 1)) :=
      .cons (hpot n (by omega)) (hstep n (by omega)) (.nil _)
    simpa [List.range_succ, List.map_append] using path_append ht hl

/-- Every original centered doubling source admits one complete physical-label word
with all prefix heights between zero and `N - N/3 - 2`. This is a support bound,
not the conjectured half-modulus bound. -/
theorem universal_source_width (k : ℕ) (hk : 3 ≤ k) (t : ℕ) :
    ∃ word : List (Fin k), word.Nodup ∧ word.toFinset = Finset.univ ∧
      ∀ n : ℕ, n ≤ k →
        ((word.take n).map (actualSource k t)).sum ∈ Set.Icc (0 : ℤ) (capacity k) := by
  classical
  have hkpos : 0 < k := by omega
  letI : NeZero k := ⟨ne_of_gt hkpos⟩
  obtain ⟨hN, hodd, hN3, hA⟩ := modulus_facts hk
  let f := actualSource k t
  let u : Fin k → ℤ := fun p => f p + if f p < 0 then modulus k else 0
  let p : ℕ → Fin k := fun i => ⟨i % k, Nat.mod_lt i hkpos⟩
  let original := (List.range k).map p
  have hbound : ∀ x, -(modulus k / 2) ≤ f x ∧ f x ≤ modulus k / 2 :=
    fun x => centered_bounds (by omega) hodd _
  have hf (i : ℕ) (hi : i < k) :
      f (p i) = centered (modulus k) ((2 : ℤ) ^ i * (t : ℤ)) := by
    simp [f, actualSource, p, Nat.mod_eq_of_lt hi]
  have hfnext (i : ℕ) (hi : i < k) :
      f (p (i + 1)) = centered (modulus k) ((2 : ℤ) ^ (i + 1) * (t : ℤ)) := by
    by_cases hnext : i + 1 < k
    · exact hf _ hnext
    · have he : i + 1 = k := by omega
      rw [he, centered_full_period]
      simp [f, actualSource, p]
  have hstep : ∀ i < k, f (p (i + 1)) = doubleStep (modulus k) (f (p i)) := by
    intro i hi
    rw [hfnext i hi, hf i hi]
    have he : (2 : ℤ) ^ (i + 1) * (t : ℤ) = 2 * (2 ^ i * (t : ℤ)) := by
      rw [pow_succ]; ring
    rw [he, centered_double (by omega) hodd]
  have hpot : ∀ i < k, u (p (i + 1)) - u (p i) = f (p i) := by
    intro i hi
    dsimp [u]
    rw [hstep i hi]
    exact unsigned_step (by omega) hodd (hbound _)
  have hpath : SourcePath (modulus k) f u (p 0) original (p 0) := by
    have ht := path_range p k hpot hstep
    have he : p k = p 0 := by apply Fin.ext; simp [p]
    simpa only [he] using ht
  have hcomplete : ∀ x : Fin k, x ∈ original := by
    intro x
    apply List.mem_map.mpr
    refine ⟨x.val, List.mem_range.mpr x.isLt, ?_⟩
    apply Fin.ext
    simp [p, Nat.mod_eq_of_lt x.isLt]
  have horiginal : original = List.finRange k := by
    apply List.ext_getElem
    · simp [original]
    · intro i hi hi'
      simp only [original, List.getElem_map, List.getElem_range, List.getElem_finRange]
      apply Fin.ext
      simp [p, Nat.mod_eq_of_lt (show i < k by simpa [original] using hi)]
  obtain ⟨word, hw, hstrip⟩ := cycle_schedule hA hN3 hodd hbound (fun _ => rfl) hpath hcomplete
  refine ⟨word, hw.nodup_iff.mpr (by rw [horiginal]; exact List.nodup_finRange k), ?_, ?_⟩
  · apply Finset.eq_univ_of_forall
    intro x
    exact List.mem_toFinset.mpr (hw.mem_iff.mpr (hcomplete x))
  · intro n _
    have hs := inStrip_prefix hstrip n
    simpa [capacity] using hs

#print axioms universal_source_width


private theorem geometric_quotient (r m : ℕ) (hm : 1 ≤ m) :
    let B : ℕ := 2 ^ m
    (B ^ r - 1) / (B - 1) = ∑ j ∈ Finset.range r, B ^ j := by
  dsimp only
  have hB : 1 < 2 ^ m := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hm
    norm_num at this ⊢
    omega
  have he := geom_sum_mul_of_one_le (le_of_lt hB) r
  rw [← he, Nat.mul_div_cancel _ (by omega : 0 < 2 ^ m - 1)]

set_option maxHeartbeats 1200000 in
-- Source range certificates and the indexed block decomposition share one proof.
/-- The geometric source forces the entire physical unsigned-potential envelope. -/
private theorem geometric_source_envelope
    (r m d : ℕ) (hr : 1 ≤ r) (hm : 1 ≤ m) (hd : 1 ≤ d) :
    let B : ℕ := 2 ^ m
    let k : ℕ := r * m + d
    let t : ℕ := (B ^ r - 1) / (B - 1)
    let a : ℕ := d - 1
    let A : ℤ := 2 ^ a
    let N : ℤ := modulus k
    let v : ℕ → ℤ := fun i => centered N ((2 : ℤ) ^ i * (t : ℤ))
    let U : ℕ → ℤ := fun i => v i + if v i < 0 then N else 0
    U a = A * (t : ℤ) ∧
      (∀ i : ℕ, i < a → v i = (2 : ℤ) ^ i * (t : ℤ)) ∧
      (∀ i : ℕ, a ≤ i → i ≤ k - 1 →
        A * (t : ℤ) ≤ U i ∧ U i ≤ A * (B : ℤ) * (t : ℤ)) ∧
      U (a + m) = A * (B : ℤ) * (t : ℤ) ∧
      U (k - 1) = (N + (t : ℤ)) / 2 ∧
      v (k - 1) = ((t : ℤ) - N) / 2 := by
  classical
  dsimp only
  let b : ℤ := 2 ^ m
  let k := r * m + d
  let t : ℕ := ((2 ^ m) ^ r - 1) / (2 ^ m - 1)
  let T : ℤ := t
  let a := d - 1
  let A : ℤ := 2 ^ a
  let N := modulus k
  let S : ℕ → ℤ := fun j => ∑ e ∈ Finset.range j, b ^ e
  let u : ℕ → ℤ := fun j => 2 * A * T - (2 * A - 1) * S j
  let v : ℕ → ℤ := fun i => centered N ((2 : ℤ) ^ i * T)
  let U : ℕ → ℤ := fun i => v i + if v i < 0 then N else 0
  change U a = A * T ∧ (∀ i < a, v i = 2 ^ i * T) ∧
    (∀ i, a ≤ i → i ≤ k - 1 → A * T ≤ U i ∧ U i ≤ A * (2 ^ m : ℕ) * T) ∧
    U (a + m) = A * (2 ^ m : ℕ) * T ∧ U (k - 1) = (N + T) / 2 ∧
    v (k - 1) = (T - N) / 2
  have hb : 2 ≤ b := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hm
    norm_num at this
    exact this
  have hA : 1 ≤ A := one_le_pow₀ (by norm_num)
  have hS (j : ℕ) : S j * (b - 1) = b ^ j - 1 := geom_sum_mul b j
  have hSr : S r = T := by
    have hg : t = ∑ j ∈ Finset.range r, (2 ^ m : ℕ) ^ j := geometric_quotient r m hm
    have hc := congrArg (fun x : ℕ => (x : ℤ)) hg
    simp only [Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] at hc
    exact hc.symm
  have hS0 (j : ℕ) : 0 ≤ S j := Finset.sum_nonneg (fun _ _ => pow_nonneg (by omega) _)
  have hmono {i j : ℕ} (hij : i ≤ j) : S i ≤ S j := by
    have hp := pow_le_pow_right₀ (by omega : 1 ≤ b) hij
    have hi := hS i
    have hj := hS j
    nlinarith
  have hS1 : S 1 = 1 := by simp [S]
  have hT : 1 ≤ T := by have := hmono hr; rw [hS1, hSr] at this; exact this
  have hT0 : 0 ≤ T := by omega
  have hA0 : 0 ≤ A := by omega
  have hAT0 : 0 ≤ A * T := mul_nonneg hA0 hT0
  have hAT1 : 1 ≤ A * T := by nlinarith
  have ht : T * (b - 1) = b ^ r - 1 := by rw [← hSr]; exact hS r
  have hshort (j : ℕ) (hj : j < r) : 2 * S j ≤ T - 1 := by
    have hrec : S (j + 1) = b * S j + 1 := by
      dsimp [S]
      rw [Finset.sum_range_succ]
      have := hS j
      dsimp [S] at this
      nlinarith
    have hle := hmono (show j + 1 ≤ r by omega)
    rw [hrec, hSr] at hle
    have := mul_nonneg (show 0 ≤ b - 2 by omega) (hS0 j)
    nlinarith
  have hp : (2 : ℤ) ^ (r * m) = b ^ r := by simp [b, ← pow_mul, Nat.mul_comm]
  have hN : N = 2 * A * b ^ r - 1 := by
    dsimp [N, modulus, k]
    rw [show r * m + d = (a + r * m) + 1 by dsimp [a]; omega,
      pow_succ, pow_add, hp]
    dsimp [A]
    ring
  have hNpos : 0 < N := by have := pow_pos (by omega : 0 < b) r; nlinarith
  have hN2 : N = 2 * (A * b ^ r) - 1 := by rw [hN]; ring
  have hodd : N % 2 = 1 := by omega
  have htop : A * b * T < N := by
    have hn := mul_nonneg hAT0 (show 0 ≤ b - 2 by omega)
    nlinarith [ht]
  have hAt : A * T ≤ N / 2 := by
    have htmax : T ≤ b ^ r - 1 := by nlinarith [mul_nonneg hT0 (show 0 ≤ b - 2 by omega)]
    have hh := mul_le_mul_of_nonneg_left htmax hA0
    nlinarith [Int.emod_add_mul_ediv N 2,
      Int.emod_nonneg N (by decide : (2 : ℤ) ≠ 0),
      Int.emod_lt_of_pos N (by decide : (0 : ℤ) < 2)]
  have hU (i : ℕ) : U i = ((2 : ℤ) ^ i * T) % N := by
    have hv := centered_bounds hNpos hodd ((2 : ℤ) ^ i * T)
    change -(N / 2) ≤ v i ∧ v i ≤ N / 2 at hv
    have hn := Int.emod_add_mul_ediv N 2
    have hmod := centered_mod N ((2 : ℤ) ^ i * T)
    change v i % N = _ at hmod
    have hu0 : 0 ≤ U i := by dsimp only [U]; split_ifs <;> omega
    have huN : U i < N := by dsimp only [U]; split_ifs <;> omega
    have he : U i % N = ((2 : ℤ) ^ i * T) % N := by
      dsimp only [U]
      split_ifs <;> simpa only [add_zero, Int.add_emod_right] using hmod
    rwa [Int.emod_eq_of_lt hu0 huN] at he
  have hrep (i : ℕ) (R : ℤ) (hR0 : 0 ≤ R) (hRN : R < N)
      (he : ((2 : ℤ) ^ i * T) % N = R % N) : U i = R := by
    rw [hU i, he, Int.emod_eq_of_lt hR0 hRN]
  have hlow (i : ℕ) (hi : i ≤ a) : v i = (2 : ℤ) ^ i * T := by
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hi
    have hx : 0 ≤ (2 : ℤ) ^ i * T := by positivity
    have hxhi : (2 : ℤ) ^ i * T ≤ N / 2 := by nlinarith [mul_le_mul_of_nonneg_right hp hT0]
    exact centered_unique hNpos hodd (centered_bounds hNpos hodd _)
      ⟨by omega, hxhi⟩ (centered_mod N _)
  have hstart : U a = A * T := by
    dsimp only [U]
    rw [hlow a le_rfl]
    simp only [show ¬ (2 : ℤ) ^ a * T < 0 by change ¬ A * T < 0; omega, ite_false, add_zero]
    rfl
  have hu (j : ℕ) (hj : j < r) : A * T ≤ u j ∧ u j ≤ 2 * A * T := by
    have hq := hshort j hj
    have hL := hS0 j
    have hmul := mul_nonneg hA0 (show 0 ≤ T - 1 - 2 * S j by omega)
    have hmul' := mul_nonneg (show 0 ≤ 2 * A - 1 by omega) hL
    dsimp [u]
    constructor <;> nlinarith
  have hpower (j : ℕ) :
      (2 : ℤ) ^ (a + j * m + 1) * T = N * S j + u j := by
    have hjpow : (2 : ℤ) ^ (j * m) = b ^ j := by simp [b, ← pow_mul, Nat.mul_comm]
    rw [pow_succ, pow_add, hjpow]
    have hj := hS j
    dsimp [u]
    have he : b ^ j * T = b ^ r * S j + T - S j := by
      nlinarith only [congrArg (fun x : ℤ => x * T) hj,
        congrArg (fun x : ℤ => x * S j) ht]
    rw [hN]
    dsimp [A] at *
    linear_combination 2 * 2 ^ a * he
  have hblock (j ell : ℕ) (hj : 1 ≤ j) (hjr : j < r)
      (he1 : 1 ≤ ell) (hem : ell ≤ m) :
      U (a + j * m + ell) = (2 : ℤ) ^ (ell - 1) * u j := by
    have huj := hu j hjr
    have hpell : (2 : ℤ) ^ ell ≤ b := pow_le_pow_right₀ (by norm_num) hem
    have htwo : (2 : ℤ) ^ ell = 2 * 2 ^ (ell - 1) := by
      calc (2 : ℤ) ^ ell = 2 ^ ((ell - 1) + 1) := by congr 1 <;> omega
           _ = 2 * 2 ^ (ell - 1) := by rw [pow_succ]; ring
    have hpow1 : (1 : ℤ) ≤ 2 ^ (ell - 1) := one_le_pow₀ (by norm_num)
    have huj0 : 0 ≤ u j := le_trans hAT0 huj.1
    have hR0 : 0 ≤ (2 : ℤ) ^ (ell - 1) * u j := mul_nonneg (by positivity) huj0
    have hRhi : (2 : ℤ) ^ (ell - 1) * u j ≤ A * b * T := by
      have h1 := mul_le_mul_of_nonneg_right hpell (by omega : 0 ≤ u j)
      have h2 := mul_le_mul_of_nonneg_left huj.2 (by omega : 0 ≤ b)
      rw [htwo] at h1
      nlinarith
    apply hrep _ _ hR0 (lt_of_le_of_lt hRhi htop)
    have hexp : a + j * m + ell = (a + j * m + 1) + (ell - 1) := by omega
    rw [hexp, pow_add, mul_right_comm, hpower j]
    have he : (N * S j + u j) * (2 : ℤ) ^ (ell - 1) =
        (2 : ℤ) ^ (ell - 1) * u j + (S j * 2 ^ (ell - 1)) * N := by ring
    rw [he, Int.add_mul_emod_self_right]
  have hfirst (ell : ℕ) (he : ell ≤ m) : U (a + ell) = A * 2 ^ ell * T := by
    have hpell : (2 : ℤ) ^ ell ≤ b := pow_le_pow_right₀ (by norm_num) he
    have hlo : 0 ≤ A * (2 : ℤ) ^ ell * T := by positivity
    have hhi : A * (2 : ℤ) ^ ell * T ≤ A * b * T := by
      nlinarith [mul_le_mul_of_nonneg_left hpell hAT0]
    apply hrep _ _ hlo (lt_of_le_of_lt hhi htop)
    simp [pow_add, A]
  have henvelope (i : ℕ) (hai : a ≤ i) (hik : i ≤ k - 1) :
      A * T ≤ U i ∧ U i ≤ A * b * T := by
    by_cases hi : i ≤ a + m
    · have he : i = a + (i - a) := by omega
      rw [he, hfirst _ (by omega)]
      have hp1 : (1 : ℤ) ≤ 2 ^ (i - a) := one_le_pow₀ (by norm_num)
      have hp2 : (2 : ℤ) ^ (i - a) ≤ b := pow_le_pow_right₀ (by norm_num) (by omega)
      constructor <;> nlinarith [mul_le_mul_of_nonneg_left hp1 (show 0 ≤ A * T by positivity),
        mul_le_mul_of_nonneg_left hp2 (show 0 ≤ A * T by positivity)]
    · let j := (i - a - 1) / m
      let ell := (i - a - 1) % m + 1
      have hdiv := Nat.mod_add_div (i - a - 1) m
      rw [Nat.mul_comm m] at hdiv
      have hmod := Nat.mod_lt (i - a - 1) (by omega : 0 < m)
      have hj : 1 ≤ j := by
        dsimp only [j]
        apply (Nat.le_div_iff_mul_le (by omega : 0 < m)).mpr
        omega
      have hjr : j < r := by
        dsimp [j]
        apply (Nat.div_lt_iff_lt_mul (by omega : 0 < m)).mpr
        dsimp [k, a] at *
        omega
      have he1 : 1 ≤ ell := by dsimp [ell]; omega
      have hem : ell ≤ m := by dsimp [ell]; omega
      have he : i = a + j * m + ell := by dsimp [j, ell]; omega
      rw [he, hblock j ell hj hjr he1 hem]
      have huj := hu j hjr
      have hp1 : (1 : ℤ) ≤ 2 ^ (ell - 1) := one_le_pow₀ (by norm_num)
      have hp2 : (2 : ℤ) ^ ell ≤ b := pow_le_pow_right₀ (by norm_num) hem
      have htwo : (2 : ℤ) ^ ell = 2 * 2 ^ (ell - 1) := by
        calc (2 : ℤ) ^ ell = 2 ^ ((ell - 1) + 1) := by congr 1 <;> omega
           _ = 2 * 2 ^ (ell - 1) := by rw [pow_succ]; ring
      have h1 := mul_le_mul_of_nonneg_left hp1 (show 0 ≤ u j by omega)
      have h2 := mul_le_mul_of_nonneg_right hp2 (show 0 ≤ u j by omega)
      have h3 := mul_le_mul_of_nonneg_left huj.2 (show 0 ≤ b by omega)
      rw [htwo] at h2
      constructor <;> nlinarith
  have hpeak : U (a + m) = A * b * T := by simpa [b] using hfirst m le_rfl
  have hreturn (j : ℕ) (hj : 1 ≤ j) (hjr : j ≤ r) :
      2 * U (a + j * m) = N + u j := by
    have hrec : S j = b * S (j - 1) + 1 := by
      have hs := hS (j - 1)
      have he : S j = S (j - 1) + b ^ (j - 1) := by
        conv_lhs => rw [show j = (j - 1) + 1 by omega]
        exact Finset.sum_range_succ _ _
      nlinarith only [hs, he]
    by_cases hj1 : j = 1
    · rw [hj1, one_mul, hpeak]
      dsimp only [u]
      rw [hS1, hN]
      linear_combination 2 * A * ht
    · have hjprev : 1 ≤ j - 1 := by omega
      have hjrprev : j - 1 < r := by omega
      have he : a + j * m = a + (j - 1) * m + m := by
        have hh : (j - 1) + 1 = j := by omega
        nlinarith
      rw [he, hblock (j - 1) m hjprev hjrprev hm le_rfl]
      have htwo : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
        calc (2 : ℤ) ^ m = 2 ^ ((m - 1) + 1) := by congr 1 <;> omega
             _ = 2 * 2 ^ (m - 1) := by rw [pow_succ]; ring
      have hrecU : b * u (j - 1) = N + u j := by
        dsimp only [u]
        rw [hrec, hN]
        linear_combination 2 * A * ht
      calc 2 * (2 ^ (m - 1) * u (j - 1)) = b * u (j - 1) := by
             rw [← mul_assoc, ← htwo]
           _ = N + u j := hrecU
  have hnegative (j : ℕ) (hj : 1 ≤ j) (hjr : j ≤ r) :
      v (a + j * m) = (u j - N) / 2 := by
    have hSj := hmono hjr
    rw [hSr] at hSj
    have huj : T ≤ u j := by
      have hh := mul_nonneg (show 0 ≤ 2 * A - 1 by omega) (show 0 ≤ T - S j by omega)
      dsimp only [u]
      nlinarith only [hh]
    have he := hreturn j hj hjr
    have hv := centered_bounds hNpos hodd ((2 : ℤ) ^ (a + j * m) * T)
    change -(N / 2) ≤ v (a + j * m) ∧ v (a + j * m) ≤ N / 2 at hv
    have hn : v (a + j * m) < 0 := by
      dsimp only [U] at he
      split_ifs at he <;> omega
    dsimp only [U] at he
    rw [if_pos hn] at he
    omega
  have hkidx : k - 1 = a + r * m := by dsimp [k, a]; omega
  have hur : u r = T := by dsimp only [u]; rw [hSr]; ring
  have hend : 2 * U (k - 1) = N + T := by
    rw [hkidx]
    simpa only [hur] using hreturn r hr le_rfl
  have hlast : v (k - 1) = (T - N) / 2 := by
    rw [hkidx]
    simpa only [hur] using hnegative r hr le_rfl

  refine ⟨hstart, fun i hi => hlow i (by omega), ?_, ?_, by omega, hlast⟩
  · intro i hi hk
    simpa only [Nat.cast_pow, Nat.cast_ofNat, b] using henvelope i hi hk
  · simpa only [Nat.cast_pow, Nat.cast_ofNat, b] using hpeak

set_option maxHeartbeats 1600000 in
-- The literal word, integer potential and both attained peaks are checked together.
/-- Relocating the low physical labels gives this geometric source an exact attained width. -/
theorem geometric_source_relocation
    (r m d : ℕ) (hr : 1 ≤ r) (hm : 1 ≤ m) (hd : 1 ≤ d) :
    let B : ℕ := 2 ^ m
    let k : ℕ := r * m + d
    let t : ℕ := (B ^ r - 1) / (B - 1)
    let A : ℤ := 2 ^ (d - 1)
    let C : ℤ := (2 : ℤ) ^ (k - 1) - 1
    let W : ℤ := C - min (A - 1) (((t : ℤ) - 1) / 2)
    let f : Fin k → ℤ := actualSource k t
    let word : List (Fin k) :=
      (((List.finRange k).take (k - 1)).rotate (d - 1)) ++
        (List.finRange k).drop (k - 1)
    word.Perm (List.finRange k) ∧
      W ≤ C ∧
      (∀ n : ℕ, ((word.take n).map f).sum ∈ Set.Icc (0 : ℤ) W) ∧
      (word.map f).sum = 0 ∧
      (∃ n : ℕ, n ≤ k ∧ ((word.take n).map f).sum = W) := by
  classical
  dsimp only
  let B : ℕ := 2 ^ m
  let k := r * m + d
  let t : ℕ := (B ^ r - 1) / (B - 1)
  let a := d - 1
  let A : ℤ := 2 ^ a
  let C : ℤ := (2 : ℤ) ^ (k - 1) - 1
  let T : ℤ := t
  let N := modulus k
  let W := C - min (A - 1) ((T - 1) / 2)
  let f := actualSource k t
  let word := (((List.finRange k).take (k - 1)).rotate a) ++
    (List.finRange k).drop (k - 1)
  let v : ℕ → ℤ := fun i => centered N ((2 : ℤ) ^ i * T)
  let U : ℕ → ℤ := fun i => v i + if v i < 0 then N else 0
  let q := k - 1
  let len := r * m
  let main := List.range' a len
  let low := List.range a
  let order := main ++ low ++ [q]
  change word.Perm (List.finRange k) ∧ W ≤ C ∧
    (∀ n : ℕ, ((word.take n).map f).sum ∈ Set.Icc (0 : ℤ) W) ∧
    (word.map f).sum = 0 ∧ ∃ n : ℕ, n ≤ k ∧ ((word.take n).map f).sum = W
  have hlen : 1 ≤ len := by dsimp [len]; nlinarith
  have hk : 2 ≤ k := by dsimp [k, len] at *; omega
  have hq : a + len = q := by dsimp [a, len, q, k]; omega
  have ham : a + m ≤ q := by dsimp [len] at hlen hq; nlinarith
  have hA : 1 ≤ A := one_le_pow₀ (by norm_num)
  have hB : (2 : ℤ) ≤ B := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hm
    simpa [B] using this
  have hT0 : 0 ≤ T := Int.natCast_nonneg t
  have hTsum : T = ∑ j ∈ Finset.range r, (B : ℤ) ^ j := by
    have hg : t = ∑ j ∈ Finset.range r, B ^ j := geometric_quotient r m hm
    have hc := congrArg (fun x : ℕ => (x : ℤ)) hg
    simpa only [Nat.cast_sum, Nat.cast_pow] using hc
  have ht : T * ((B : ℤ) - 1) = (B : ℤ) ^ r - 1 := by
    rw [hTsum]
    exact geom_sum_mul _ _
  have hT : 1 ≤ T := by
    have hp := pow_le_pow_right₀ (by omega : (1 : ℤ) ≤ B) hr
    rw [pow_one] at hp
    by_contra h
    have hz : T = 0 := by omega
    rw [hz] at ht
    nlinarith
  have hN : N = 2 * C + 1 := by
    dsimp [N, modulus, C]
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
    ring
  have hC : 1 ≤ C := by
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show 1 ≤ k - 1 by omega)
    norm_num at hp
    dsimp [C]
    omega
  have hNpos : 0 < N := by omega
  have hodd : N % 2 = 1 := by omega
  have hQ : (2 : ℤ) ^ (k - 1) = A * (B : ℤ) ^ r := by
    rw [show k - 1 = a + r * m by dsimp [k, a]; omega, pow_add]
    congr 1
    simp [B, ← pow_mul, Nat.mul_comm]
  have hM : A * (B : ℤ) * T - A * T = C - (A - 1) := by
    dsimp only [C]
    rw [hQ]
    linear_combination A * ht
  let M := C - (A - 1)
  let L := C - (T - 1) / 2
  have hMW : M ≤ W := by dsimp [M, W]; omega
  have hLW : L ≤ W := by dsimp [L, W]; omega
  have hmax : W = M ∨ W = L := by dsimp [M, L, W]; omega
  have hWC : W ≤ C := by dsimp [W]; omega
  obtain ⟨hstart, hlow, henv, hpeak, hend, hlast⟩ := geometric_source_envelope r m d hr hm hd
  change U a = A * T at hstart
  change (∀ i < a, v i = (2 : ℤ) ^ i * T) at hlow
  change (∀ i, a ≤ i → i ≤ q → A * T ≤ U i ∧ U i ≤ A * (B : ℤ) * T) at henv
  change U (a + m) = A * (B : ℤ) * T at hpeak
  change U q = (N + T) / 2 at hend
  change v q = (T - N) / 2 at hlast
  have hstep (i : ℕ) : v (i + 1) = doubleStep N (v i) := by
    dsimp only [v]
    rw [show (2 : ℤ) ^ (i + 1) * T = 2 * (2 ^ i * T) by rw [pow_succ]; ring]
    exact centered_double hNpos hodd _
  have hpot (i : ℕ) : U (i + 1) - U i = v i := by
    dsimp only [U]
    rw [hstep i]
    exact unsigned_step hNpos hodd (centered_bounds hNpos hodd _)
  have hsum (s n : ℕ) : ((List.range' s n).map v).sum = U (s + n) - U s := by
    have heq : (fun i => v (s + i)) = fun i => U (s + (i + 1)) - U (s + i) := by
      funext i
      simpa only [Nat.add_assoc] using (hpot (s + i)).symm
    rw [List.range'_eq_map_range, List.map_map]
    change ((List.range n).map (fun i => v (s + i))).sum = _
    rw [heq]
    simpa only [Nat.add_zero] using List.sum_range_sub n (fun i => U (s + i))
  have hperm : word.Perm (List.finRange k) := by
    dsimp only [word]
    exact ((List.rotate_perm _ _).append_right _).trans (by rw [List.take_append_drop])
  have horiginal : (List.finRange k).map f = (List.range k).map v := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_map, List.getElem_finRange, List.getElem_range]
      rfl
  have hvalues : word.map f = order.map v := by
    dsimp only [word, order, main, low, q]
    rw [List.map_append, List.map_rotate, List.map_take, List.map_drop, horiginal,
      List.rotate_eq_drop_append_take (by simp; omega)]
    simp only [← List.map_take, ← List.map_drop, ← List.map_append]
    congr 1
    simp only [List.take_range, Nat.min_eq_left (by omega : k - 1 ≤ k),
      Nat.min_eq_left (show a ≤ k - 1 by omega)]
    simp only [List.range_eq_range', List.drop_range', Nat.mul_one, Nat.zero_add]
    rw [show k - 1 - a = len by omega, show k - (k - 1) = 1 by omega]
    simp [List.range'_succ, List.append_assoc]
  have hperiod : U k = U 0 := by
    have he : v k = v 0 := by simpa only [v, N, T, pow_zero, one_mul] using centered_full_period k t
    simp only [U, he]
  have htotal : (word.map f).sum = 0 := by
    rw [hperm.map f |>.sum_eq, horiginal, List.range_eq_range', hsum]
    simp only [Nat.zero_add, hperiod, sub_self]
  have htotalOrder : ((main.map v).sum + (low.map v).sum) + v q = 0 := by
    rw [hvalues] at htotal
    simpa [order, List.map_append, List.sum_append, add_assoc] using htotal
  have hmainSum : (main.map v).sum = U q - A * T := by rw [hsum, hq, hstart]
  have hmain0 : 0 ≤ (main.map v).sum := by
    rw [hmainSum]
    have := henv q (by omega) le_rfl
    omega
  have hlowpos (i : ℕ) (hi : i ∈ low) : 0 ≤ v i := by
    have hi' : i < a := List.mem_range.mp hi
    rw [hlow i hi']
    positivity
  have hlow0 : 0 ≤ (low.map v).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hlowpos i hi
  have hEnd : (main.map v).sum + (low.map v).sum = L := by
    dsimp only [L]
    rw [hlast, hN] at htotalOrder
    omega
  have hEnd0 : 0 ≤ L := by omega
  have hW0 : 0 ≤ W := by omega
  have hsegment : ∀ n s : ℕ, a ≤ s → s + n ≤ q →
      InStrip v W (U s - A * T) (List.range' s n) := by
    intro n
    induction n with
    | zero =>
      intro s has hsq
      have hh := henv s has (by omega)
      simp only [List.range'_zero, InStrip]
      constructor <;> omega
    | succ n ih =>
      intro s has hsq
      have hh := henv s has (by omega)
      rw [List.range'_succ]
      refine ⟨by omega, by omega, ?_⟩
      have hn := ih (s + 1) (by omega) (by omega)
      have hp := hpot s
      convert hn using 1 <;> omega
  have hmain : InStrip v W 0 main := by
    have hh := hsegment len a le_rfl (by omega)
    simpa only [hstart, sub_self] using hh
  have hlowstrip : InStrip v W (main.map v).sum low := by
    apply inStrip_reflect
    apply inStrip_nonpos
    · intro i hi
      have := hlowpos i hi
      omega
    · omega
    · rw [sum_neg_map]
      omega
  have hfinal : InStrip v W ((main.map v).sum + (low.map v).sum) [q] := by
    simp only [InStrip]
    exact ⟨by omega, by omega, by omega, by omega⟩
  have hstrip : InStrip v W 0 order := by
    dsimp only [order]
    rw [List.append_assoc]
    apply inStrip_append hmain
    simpa only [zero_add] using inStrip_append hlowstrip hfinal
  have hprefix (n : ℕ) : ((word.take n).map f).sum = ((order.take n).map v).sum := by
    simp only [List.map_take, hvalues]
  refine ⟨hperm, hWC, ?_, htotal, ?_⟩
  · intro n
    rw [hprefix]
    simpa only [zero_add, Set.mem_Icc] using inStrip_prefix hstrip n
  · rcases hmax with hmax | hmax
    · refine ⟨m, by omega, ?_⟩
      rw [hprefix]
      have ht : order.take m = List.range' a m := by
        dsimp only [order]
        rw [List.append_assoc, List.take_append_of_le_length (by simpa [main] using (show m ≤ len by dsimp [len]; nlinarith))]
        exact List.take_range'_of_length_ge (show m ≤ len by dsimp [len]; nlinarith)
      rw [ht, hsum, hpeak, hstart, hM]
      exact hmax.symm
    · refine ⟨q, by dsimp [q]; omega, ?_⟩
      rw [hprefix]
      have hlength : (main ++ low).length = q := by simp [main, low]; omega
      have ht : order.take q = main ++ low := by
        dsimp only [order]
        conv_lhs => rw [← hlength]
        exact List.take_append_length
      rw [ht, List.map_append, List.sum_append, hEnd, ← hmax]

#print axioms geometric_source_relocation

end D5.S3.Combinatorics.Circle.SourceWidth
