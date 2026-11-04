/- GID: D5/S3/Combinatorics/PackingDomatic/PackingDomaticInfiniteSix
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PackingDomatic/PackingDomaticInfiniteSix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Int.Interval]
   utility: none
   digest: The unrestricted six-class packing-domatic palette is exactly five. -/

module

public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.NormNum.DivMod

/-! # Six broadcast-dominating packing classes on the two-way infinite path -/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PackingDomatic.PackingDomaticInfiniteSix

open Finset

/-- Arbitrary positive bounded packing colours and one common six-class partition on Z. -/
def Q (t : ℕ) : Prop :=
  ∃ (f : ℤ → ℕ) (c : ℤ → Fin 6),
    (∀ x, 1 ≤ f x ∧ f x ≤ t) ∧
    (∀ u v, u ≠ v → f u = f v → (f u : ℤ) < |u - v|) ∧
    (∀ x (i : Fin 6), ∃ a, c a = i ∧ |x - a| ≤ (f a : ℤ))

/-- Increasing a palette bound preserves the same realization and partition. -/
private theorem palette_mono {s t : ℕ} (hst : s ≤ t) : Q s → Q t := by
  rintro ⟨f, c, hb, hp, hd⟩
  exact ⟨f, c, fun x => ⟨(hb x).1, (hb x).2.trans hst⟩, hp, hd⟩

/-- A finite-window obstruction applies to every integer realization, without periodicity. -/
private theorem no_four : ¬ Q 4 := by
  classical
  rintro ⟨f, c, hb, hp, hd⟩
  let J : Finset ℤ := Icc 0 999
  let I : Finset ℤ := Icc 4 995
  let N (j : ℕ) := (J.filter fun a => f a = j).card
  let B (x : ℤ) := J.filter fun a => |x - a| ≤ (f a : ℤ)
  let C (a : ℤ) := I.filter fun x => |x - a| ≤ (f a : ℤ)
  have jcard : J.card = 1000 := by norm_num [J]
  have icard : I.card = 992 := by norm_num [I]
  have count_dom (x : ℤ) (hx : x ∈ I) : 6 ≤ (B x).card := by
    choose g hgc hgd using fun i => hd x i
    have hx' := mem_Icc.mp hx
    have maps : ∀ i ∈ (univ : Finset (Fin 6)), g i ∈ B x := by
      intro i _
      have hg := abs_le.mp (hgd i)
      have hbound := (hb (g i)).2
      have hgj : g i ∈ J := by
        apply mem_Icc.mpr
        omega
      exact mem_filter.mpr ⟨hgj, hgd i⟩
    have inj : Set.InjOn g (univ : Finset (Fin 6)) := by
      intro i _ j _ hij
      exact (hgc i).symm.trans ((congrArg c hij).trans (hgc j))
    have h := card_le_card_of_injOn g maps inj
    simpa using h
  have capacity (a : ℤ) : (C a).card ≤ 2 * f a + 1 := by
    have sub : C a ⊆ Icc (a - (f a : ℤ)) (a + (f a : ℤ)) := by
      intro x hx
      have hh := abs_le.mp (mem_filter.mp hx).2
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    have h := card_le_card sub
    have hcard : (Icc (a - (f a : ℤ)) (a + (f a : ℤ))).card = 2 * f a + 1 := by
      simp only [Int.card_Icc]
      omega
    omega
  have double_count : (∑ x ∈ I, (B x).card) = ∑ a ∈ J, (C a).card := by
    simp only [B, C, card_eq_sum_ones, sum_filter]
    exact sum_comm
  have demand : 5952 ≤ ∑ a ∈ J, (2 * f a + 1) := by
    calc
      5952 = ∑ _x ∈ I, 6 := by simp [icard]
      _ ≤ ∑ x ∈ I, (B x).card := sum_le_sum count_dom
      _ = ∑ a ∈ J, (C a).card := double_count
      _ ≤ ∑ a ∈ J, (2 * f a + 1) := sum_le_sum fun a _ => capacity a
  have count_bound (j : ℕ) (hj : j = 2 ∨ j = 3 ∨ j = 4) :
      N j ≤ 999 / (j + 1) + 1 := by
    let D : Finset ℤ := Icc 0 (999 / ((j : ℤ) + 1))
    have maps : ∀ a ∈ J.filter (fun a => f a = j), a / ((j : ℤ) + 1) ∈ D := by
      intro a ha
      have hja := mem_Icc.mp (mem_filter.mp ha).1
      apply mem_Icc.mpr
      rcases hj with rfl | rfl | rfl <;> dsimp <;> omega
    have inj : Set.InjOn (fun a : ℤ => a / ((j : ℤ) + 1)) (J.filter fun a => f a = j) := by
      intro a ha b hb' hab
      have ha' := (mem_filter.mp ha).2
      have hb'' := (mem_filter.mp hb').2
      by_contra hne
      have hpack := hp a b hne (ha'.trans hb''.symm)
      rw [ha'] at hpack
      have hsmall : |a - b| ≤ (j : ℤ) := by
        apply abs_le.mpr
        rcases hj with rfl | rfl | rfl <;> norm_num at hab ⊢ <;> omega
      omega
    have h := card_le_card_of_injOn (fun a : ℤ => a / ((j : ℤ) + 1)) maps inj
    have hD : D.card = 999 / (j + 1) + 1 := by
      rcases hj with rfl | rfl | rfl <;> norm_num [D]
    simpa only [N, hD] using h
  have n2 : N 2 ≤ 334 := by simpa using count_bound 2 (Or.inl rfl)
  have n3 : N 3 ≤ 250 := by simpa using count_bound 3 (Or.inr (Or.inl rfl))
  have n4 : N 4 ≤ 200 := by simpa using count_bound 4 (Or.inr (Or.inr rfl))
  have weights : (∑ a ∈ J, (2 * f a + 1)) = 3 * J.card + 2 * N 2 + 4 * N 3 + 6 * N 4 := by
    have atom (a : ℤ) : 2 * f a + 1 = 3 + (if f a = 2 then 2 else 0) +
        (if f a = 3 then 4 else 0) + (if f a = 4 then 6 else 0) := by
      have h := hb a
      split_ifs <;> omega
    simp_rw [atom, sum_add_distrib]
    simp [N, sum_ite, Nat.mul_comm]
  omega

/-- The five-colour pattern from Brešar--Ferme--Hu, Theorem 3.6. -/
private def upperColour (x : ℤ) : ℕ :=
  if x % 6 = 0 then 5 else if x % 6 = 1 then 1 else if x % 6 = 2 then 2
  else if x % 6 = 3 then 4 else if x % 6 = 4 then 1 else 3

/-- The six partition classes from the same construction, with zero-based class labels. -/
private def upperClass (x : ℤ) : Fin 6 :=
  if x % 6 = 1 ∨ x % 6 = 4 then 0
  else if x % 30 = 0 ∨ x % 30 = 8 ∨ x % 30 = 15 ∨ x % 30 = 23 then 1
  else if x % 30 = 2 ∨ x % 30 = 9 ∨ x % 30 = 17 ∨ x % 30 = 24 then 2
  else if x % 30 = 3 ∨ x % 30 = 11 ∨ x % 30 = 18 ∨ x % 30 = 26 then 3
  else if x % 30 = 5 ∨ x % 30 = 12 ∨ x % 30 = 20 ∨ x % 30 = 27 then 4
  else 5

/-- The source construction is valid on every integer translate. -/
private theorem five_exists : Q 5 := by
  refine ⟨upperColour, upperClass, ?_, ?_, ?_⟩
  · intro x
    unfold upperColour
    split_ifs <;> norm_num
  · intro u v huv heq
    by_contra h
    have hh := abs_le.mp (le_of_not_gt h)
    unfold upperColour at heq hh
    split_ifs at heq hh <;> omega
  · have finite_cover : ∀ (r : Fin 30) (i : Fin 6), ∃ d : Fin 11,
        upperClass ((r : ℤ) + (d : ℤ) - 5) = i ∧
          |(d : ℤ) - 5| ≤ (upperColour ((r : ℤ) + (d : ℤ) - 5) : ℤ) := by
      decide
    intro x i
    let r : Fin 30 := ⟨(x % 30).toNat, by omega⟩
    have hr : (r : ℤ) = x % 30 := by dsimp [r]; omega
    obtain ⟨d, hclass, hdist⟩ := finite_cover r i
    have h30 : (x + (d : ℤ) - 5) % 30 = ((r : ℤ) + (d : ℤ) - 5) % 30 := by omega
    have h6 : (x + (d : ℤ) - 5) % 6 = ((r : ℤ) + (d : ℤ) - 5) % 6 := by omega
    have hcolour : upperColour (x + (d : ℤ) - 5) = upperColour ((r : ℤ) + (d : ℤ) - 5) := by
      simp only [upperColour, h6]
    refine ⟨x + (d : ℤ) - 5, ?_, ?_⟩
    · simpa only [upperClass, h30, h6] using hclass
    · rw [hcolour]
      have he : x - (x + (d : ℤ) - 5) = -((d : ℤ) - 5) := by omega
      simpa only [he, abs_neg] using hdist

/-- The least positive palette for six broadcast-dominating classes on the two-way path is five. -/
theorem result : Q 5 ∧ ∀ t : ℕ, Q t → 5 ≤ t := by
  refine ⟨five_exists, ?_⟩
  intro t ht
  by_contra h
  exact no_four (palette_mono (by omega) ht)

end D5.S3.Combinatorics.PackingDomatic.PackingDomaticInfiniteSix
