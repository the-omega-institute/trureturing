/- GID: D5/S3/Arith/Lattices/KisielewiczFleetWinners
   generality: S
   mirror-B: D5/B/S3/Arith/Lattices/KisielewiczFleetWinners
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Two fixed nonperiodic cube fleets have a non-eventually-periodic winner sequence. -/

import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Two nonperiodic fleets with alternating strict winners along a subsequence of window sizes. -/

namespace KisielewiczFleetWinners

open Finset
open scoped BigOperators

abbrev Origin := ℤ × ℤ × ℤ
abbrev Shift := Bool × Bool × Bool

def bit (b : Bool) : ℤ := if b then 1 else 0

/-- The phase condition is imposed only on slabs meeting a nonnegative window. -/
def Layered (F : Set Origin) (q : ℤ → Bool) : Prop :=
  ∀ x y z : ℤ, 0 ≤ z →
    ((x, y, z) ∈ F ↔ z % 2 = 0 ∧ x % 2 = bit (q (z / 2)) ∧
      y % 2 = bit (q (z / 2)))

def axis (a : ℕ) (s : Bool) : Finset ℤ :=
  Ico (bit s) (bit s + (a : ℤ))

def box (a : ℕ) (s : Shift) : Finset Origin :=
  (axis a s.1) ×ˢ ((axis a s.2.1) ×ˢ (axis a s.2.2))

open Classical in
noncomputable def score (F : Set Origin) (a : ℕ) (s : Shift) : ℕ :=
  ((box a s).filter (· ∈ F)).card

def prefixZero (q : ℤ → Bool) (n : ℕ) : ℕ :=
  ((Ioc (0 : ℤ) (n : ℤ)).filter (fun j => q j = false)).card

private def slabs (n : ℕ) (v : Bool) : Finset ℤ :=
  if v then Ioc 0 (n : ℤ) else insert 0 (Ioc 0 (n : ℤ))

def totalSlabs (n : ℕ) (v : Bool) : ℕ := if v then n else n + 1

def zeroSlabs (q : ℤ → Bool) (n : ℕ) (v : Bool) : ℕ :=
  if v then prefixZero q n else prefixZero q n + 1

private theorem vertical_axis (n : ℕ) (v : Bool) (j : ℤ) :
    2 * j ∈ axis (2 * n + 1) v ↔ j ∈ slabs n v := by
  cases v <;> simp [axis, slabs, bit] <;> omega

private def parityAxis (n : ℕ) (s q : Bool) : Finset ℤ :=
  (axis (2 * n + 1) s).filter (fun x => x % 2 = bit q)

private def axisCount (n : ℕ) (s q : Bool) : ℕ :=
  if s = q then n + 1 else n

private theorem parityAxis_card (n : ℕ) (s q : Bool) :
    (parityAxis n s q).card = axisCount n s q := by
  have h := Int.Ico_filter_modEq_card (bit s) (bit s + ((2 * n + 1 : ℕ) : ℤ))
    (r := 2) (by decide) (bit q)
  have hq : bit q % 2 = bit q := by cases q <;> decide
  simp only [Int.ModEq, hq] at h
  change (((parityAxis n s q).card : ℕ) : ℤ) = _ at h
  have ceilDiv (u : ℤ) : ⌈(u : ℚ) / 2⌉ = -((-u) / 2) := by
    exact Rat.ceil_intCast_div_natCast u 2
  simp only [← Int.cast_sub, Int.cast_ofNat] at h
  rw [ceilDiv, ceilDiv] at h
  cases s <;> cases q <;> simp [bit, axisCount] at h ⊢ <;> omega

open Classical in
private theorem slab_fiber_card (F : Set Origin) (q : ℤ → Bool) (hF : Layered F q)
    (n : ℕ) (x y v : Bool) (j : ℤ) (hj : j ∈ slabs n v) :
    (((box (2 * n + 1) (x, y, v)).filter (· ∈ F)).filter
      (fun o => o.2.2 / 2 = j)).card =
      axisCount n x (q j) * axisCount n y (q j) := by
  rw [← parityAxis_card, ← parityAxis_card, ← Finset.card_product]
  refine Finset.card_nbij' (fun o : Origin => (o.1, o.2.1))
    (fun b : ℤ × ℤ => (b.1, b.2, 2 * j)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c⟩ h
    simp only [Finset.mem_coe, Finset.mem_filter, box, Finset.mem_product] at h
    rcases h with ⟨⟨⟨ha, hb, hc⟩, ho⟩, hd⟩
    have hc0 : 0 ≤ c := by
      have hh := (Finset.mem_Ico.mp hc).1
      cases v <;> simp [bit] at hh <;> omega
    obtain ⟨_, hx, hy⟩ := (hF a b c hc0).mp ho
    simpa only [Finset.mem_coe, Finset.mem_product, parityAxis, Finset.mem_filter, ← hd]
      using And.intro (And.intro ha hx) (And.intro hb hy)
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_coe, Finset.mem_product, parityAxis, Finset.mem_filter] at h
    rcases h with ⟨⟨ha, hx⟩, ⟨hb, hy⟩⟩
    have hc := (vertical_axis n v j).mpr hj
    have hc0 : 0 ≤ 2 * j := by
      have hh := (Finset.mem_Ico.mp hc).1
      cases v <;> simp [bit] at hh <;> omega
    have hd : 2 * j / 2 = j := by omega
    have ho : (a, b, 2 * j) ∈ F := (hF _ _ _ hc0).mpr (by
      rw [hd]
      exact ⟨by omega, hx, hy⟩)
    simpa only [Finset.mem_coe, Finset.mem_filter, box, Finset.mem_product]
      using And.intro (And.intro (And.intro ha (And.intro hb hc)) ho) hd
  · rintro ⟨a, b, c⟩ h
    simp only [Finset.mem_coe, Finset.mem_filter, box, Finset.mem_product] at h
    rcases h with ⟨⟨⟨_, _, hc⟩, ho⟩, hd⟩
    have hc0 : 0 ≤ c := by
      have hh := (Finset.mem_Ico.mp hc).1
      cases v <;> simp [bit] at hh <;> omega
    have he := ((hF a b c hc0).mp ho).1
    have hz : 2 * j = c := by omega
    simp [hz]
  · intro b _
    rfl

private theorem score_eq_slab_sum (F : Set Origin) (q : ℤ → Bool) (hF : Layered F q)
    (n : ℕ) (x y v : Bool) :
    score F (2 * n + 1) (x, y, v) =
      ∑ j ∈ slabs n v, axisCount n x (q j) * axisCount n y (q j) := by
  unfold score
  rw [Finset.card_eq_sum_card_fiberwise (f := fun o : Origin => o.2.2 / 2)
    (t := slabs n v)]
  · exact Finset.sum_congr rfl (fun j hj => slab_fiber_card F q hF n x y v j hj)
  · rintro ⟨a, b, c⟩ h
    simp only [Finset.mem_coe, Finset.mem_filter, box, Finset.mem_product] at h
    rcases h with ⟨⟨_, _, hc⟩, ho⟩
    have hc0 : 0 ≤ c := by
      have hh := (Finset.mem_Ico.mp hc).1
      cases v <;> simp [bit] at hh <;> omega
    have he := ((hF a b c hc0).mp ho).1
    apply (vertical_axis n v (c / 2)).mp
    have hz : 2 * (c / 2) = c := by omega
    rwa [hz]

private theorem slabs_card (n : ℕ) (v : Bool) : (slabs n v).card = totalSlabs n v := by
  cases v <;> simp [slabs, totalSlabs, Int.card_Ioc]

private theorem zeroSlabs_card (q : ℤ → Bool) (hq : q 0 = false) (n : ℕ) (v : Bool) :
    ((slabs n v).filter (fun j => q j = false)).card = zeroSlabs q n v := by
  cases v
  · change #((insert (0 : ℤ) (Ioc 0 (n : ℤ))).filter (fun j => q j = false)) =
      prefixZero q n + 1
    rw [Finset.filter_insert]
    simp only [hq, ite_true]
    rw [Finset.card_insert_of_notMem (by simp)]
    rfl
  · rfl

private theorem otherSlabs_card (q : ℤ → Bool) (hq : q 0 = false) (n : ℕ) (v : Bool) :
    ((slabs n v).filter (fun j => q j ≠ false)).card =
      totalSlabs n v - zeroSlabs q n v := by
  have h := Finset.card_filter_add_card_filter_not (s := slabs n v) (fun j => q j = false)
  rw [zeroSlabs_card q hq, slabs_card] at h
  exact (Nat.eq_sub_of_add_eq (Nat.add_comm .. |>.trans h))

private theorem score_phase_sum (F : Set Origin) (q : ℤ → Bool)
    (hF : Layered F q) (hq : q 0 = false) (n : ℕ) (x y v : Bool) :
    score F (2 * n + 1) (x, y, v) =
      zeroSlabs q n v * (axisCount n x false * axisCount n y false) +
      (totalSlabs n v - zeroSlabs q n v) * (axisCount n x true * axisCount n y true) := by
  rw [score_eq_slab_sum F q hF, ← Finset.sum_filter_add_sum_filter_not
    (slabs n v) (fun j => q j = false)]
  congr 1
  · rw [Finset.sum_const_nat, zeroSlabs_card q hq]
    intro j hj
    rw [(Finset.mem_filter.mp hj).2]
  · rw [Finset.sum_const_nat, otherSlabs_card q hq]
    intro j hj
    have hj' : q j = true := by
      have hh := (Finset.mem_filter.mp hj).2
      cases h : q j <;> simp_all
    rw [hj']

/-- The four horizontal scores in each of the two vertical windows. -/
private theorem horizontal_scores (F : Set Origin) (q : ℤ → Bool)
    (hF : Layered F q) (hq : q 0 = false) (n : ℕ) (v : Bool) :
    let M := totalSlabs n v
    let P := zeroSlabs q n v
    score F (2 * n + 1) (false, false, v) = M * n^2 + (2 * n + 1) * P ∧
    score F (2 * n + 1) (true, true, v) = M * n^2 + (2 * n + 1) * (M - P) ∧
    score F (2 * n + 1) (false, true, v) = M * n^2 + M * n ∧
    score F (2 * n + 1) (true, false, v) = M * n^2 + M * n := by
  have hsum : zeroSlabs q n v + (totalSlabs n v - zeroSlabs q n v) = totalSlabs n v := by
    rw [← otherSlabs_card q hq, ← zeroSlabs_card q hq, ← slabs_card]
    exact Finset.card_filter_add_card_filter_not _
  dsimp only
  simp only [score_phase_sum F q hF hq, axisCount, ite_true, ite_false,
    Bool.false_eq_true, Bool.true_eq_false]
  generalize zeroSlabs q n v = P at hsum ⊢
  generalize totalSlabs n v - P = Q at hsum ⊢
  rw [← hsum]
  exact ⟨by ring, by ring, by ring, by ring⟩

/-- Each of the 64 ordered shift pairs contributes one signed comparison. -/
noncomputable def margin (F G : Set Origin) (a : ℕ) : ℤ :=
  ∑ e : Shift × Shift, Int.sign ((score F a e.1 : ℤ) - (score G a e.2 : ℤ))

/-- The nine distinct scores of the two fleets in ascending order.
The first five use vertical shift one and the last four use shift zero. -/
private def orderedScore (t : ℤ) (i : Fin 9) : ℤ :=
  let n := 4 * t + 1
  let a := 2 * n + 1
  let lo := n * n^2
  let hi := (n + 1) * n^2
  match i.val with
  | 0 => lo + a * (t + 1)
  | 1 => lo + a * (2 * t)
  | 2 => lo + n * n
  | 3 => lo + a * (2 * t + 1)
  | 4 => lo + a * (3 * t)
  | 5 => hi + a * (t + 1)
  | 6 => hi + (n + 1) * n
  | 7 => hi + a * (2 * t + 1)
  | _ => hi + a * (3 * t + 1)

private theorem orderedScore_strict (t : ℤ) (ht : 2 ≤ t) : StrictMono (orderedScore t) := by
  have hquad : 0 ≤ t * (t - 2) := mul_nonneg (by omega) (by omega)
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i <;> norm_num [orderedScore, Fin.castSucc, Fin.succ] <;>
    nlinarith only [ht, hquad]

private def rankF : Shift → Fin 9
  | (false, false, true) => 1
  | (true, true, true) => 3
  | (_, _, true) => 2
  | (false, false, false) => 7
  | (true, true, false) => 7
  | (_, _, false) => 6

private def rankG : Shift → Fin 9
  | (false, false, true) => 4
  | (true, true, true) => 0
  | (_, _, true) => 2
  | (false, false, false) => 8
  | (true, true, false) => 5
  | (_, _, false) => 6

private theorem score_rankF (F : Set Origin) (q : ℤ → Bool) (hF : Layered F q)
    (hq : q 0 = false) (t : ℕ) (hp : prefixZero q (4 * t + 1) = 2 * t) (s : Shift) :
    (score F (8 * t + 3) s : ℤ) = orderedScore t (rankF s) := by
  rcases s with ⟨x, y, v⟩
  obtain ⟨h00, h11, h01, h10⟩ := horizontal_scores F q hF hq (4 * t + 1) v
  have ha : 2 * (4 * t + 1) + 1 = 8 * t + 3 := by omega
  rw [ha] at h00 h11 h01 h10
  have hrest : totalSlabs (4 * t + 1) v - zeroSlabs q (4 * t + 1) v = 2 * t + 1 := by
    cases v <;> simp [totalSlabs, zeroSlabs, hp] <;> omega
  rw [hrest] at h11
  cases x <;> cases y <;> cases v <;>
    simp only [h00, h11, h01, h10, totalSlabs, zeroSlabs, hp, Bool.false_eq_true,
      ite_true, ite_false, rankF] <;>
    unfold orderedScore <;> push_cast <;> ring_nf <;> rfl

private theorem score_rankG (G : Set Origin) (q : ℤ → Bool) (hG : Layered G q)
    (hq : q 0 = false) (t : ℕ) (hp : prefixZero q (4 * t + 1) = 3 * t) (s : Shift) :
    (score G (8 * t + 3) s : ℤ) = orderedScore t (rankG s) := by
  rcases s with ⟨x, y, v⟩
  obtain ⟨h00, h11, h01, h10⟩ := horizontal_scores G q hG hq (4 * t + 1) v
  have ha : 2 * (4 * t + 1) + 1 = 8 * t + 3 := by omega
  rw [ha] at h00 h11 h01 h10
  have hrest : totalSlabs (4 * t + 1) v - zeroSlabs q (4 * t + 1) v = t + 1 := by
    cases v <;> simp [totalSlabs, zeroSlabs, hp] <;> omega
  rw [hrest] at h11
  cases x <;> cases y <;> cases v <;>
    simp only [h00, h11, h01, h10, totalSlabs, zeroSlabs, hp, Bool.false_eq_true,
      ite_true, ite_false, rankG] <;>
    unfold orderedScore <;> push_cast <;> ring_nf <;> rfl

private theorem sign_orderedScore (t : ℤ) (ht : 2 ≤ t) (i j : Fin 9) :
    Int.sign (orderedScore t i - orderedScore t j) = Int.sign ((i.val : ℤ) - j.val) := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hscore := orderedScore_strict t ht hij
    have hrank : i.val < j.val := hij
    rw [Int.sign_eq_neg_one_of_neg (by omega), Int.sign_eq_neg_one_of_neg (by omega)]
  · simp
  · have hscore := orderedScore_strict t ht hji
    have hrank : j.val < i.val := hji
    rw [Int.sign_eq_one_of_pos (by omega), Int.sign_eq_one_of_pos (by omega)]

/-- At the first registered pair of prefix totals, the literal margin is four. -/
private theorem margin_pos_four (F G : Set Origin) (qF qG : ℤ → Bool)
    (hF : Layered F qF) (hG : Layered G qG) (hF0 : qF 0 = false) (hG0 : qG 0 = false)
    (t : ℕ) (ht : 2 ≤ t)
    (hpF : prefixZero qF (4 * t + 1) = 2 * t)
    (hpG : prefixZero qG (4 * t + 1) = 3 * t) :
    margin F G (8 * t + 3) = 4 := by
  have ht' : (2 : ℤ) ≤ t := by exact_mod_cast ht
  unfold margin
  simp_rw [score_rankF F qF hF hF0 t hpF, score_rankG G qG hG hG0 t hpG,
    sign_orderedScore t ht']
  decide

private theorem margin_swap (F G : Set Origin) (a : ℕ) :
    margin F G a = -margin G F a := by
  unfold margin
  rw [← Finset.sum_neg_distrib]
  apply Fintype.sum_equiv (Equiv.prodComm Shift Shift)
  rintro ⟨e, d⟩
  change Int.sign ((score F a e : ℤ) - (score G a d : ℤ)) =
    -Int.sign ((score G a d : ℤ) - (score F a e : ℤ))
  rw [← Int.sign_neg]
  congr 1
  omega

/-- Swapping the registered prefix totals gives the opposite literal margin. -/
private theorem margin_neg_four (F G : Set Origin) (qF qG : ℤ → Bool)
    (hF : Layered F qF) (hG : Layered G qG) (hF0 : qF 0 = false) (hG0 : qG 0 = false)
    (t : ℕ) (ht : 2 ≤ t)
    (hpF : prefixZero qF (4 * t + 1) = 3 * t)
    (hpG : prefixZero qG (4 * t + 1) = 2 * t) :
    margin F G (8 * t + 3) = -4 := by
  rw [margin_swap, margin_pos_four G F qG qF hG hF hG0 hF0 t ht hpG hpF]

/-- A lattice point belongs to the origin's translate of `{0,1}³`. -/
def Covers (origin point : Origin) : Prop :=
  (origin.1 ≤ point.1 ∧ point.1 < origin.1 + 2) ∧
  (origin.2.1 ≤ point.2.1 ∧ point.2.1 < origin.2.1 + 2) ∧
  (origin.2.2 ≤ point.2.2 ∧ point.2.2 < origin.2.2 + 2)

/-- Every lattice point belongs to the cell of exactly one origin. -/
def UniqueCover (F : Set Origin) : Prop :=
  ∀ point, ∃! origin, origin ∈ F ∧ Covers origin point

/-- A translation that preserves origin membership in both directions is zero. -/
def TrivialStabilizer (F : Set Origin) : Prop :=
  ∀ dx dy dz : ℤ, (∀ x y z : ℤ,
    ((x + dx, y + dy, z + dz) ∈ F ↔ (x, y, z) ∈ F)) →
    dx = 0 ∧ dy = 0 ∧ dz = 0

/-- Strict winner at every side length, with zero for equal win probabilities. -/
noncomputable def outcome (F G : Set Origin) (a : ℕ) : ℤ := Int.sign (margin F G a)

private def slab (q : ℤ → Bool) (j x y : ℤ) : Prop :=
  if j = -1 then y % 2 = 0 ∧ x % 2 = (if y = 0 then 1 else 0)
  else if j = -2 then x % 2 = 0 ∧ y % 2 = (if x = 0 then 1 else 0)
  else x % 2 = bit (q j) ∧ y % 2 = bit (q j)

private def fleet (q : ℤ → Bool) : Set Origin :=
  {o | o.2.2 % 2 = 0 ∧ slab q (o.2.2 / 2) o.1 o.2.1}

private theorem fleet_layered (q : ℤ → Bool) : Layered (fleet q) q := by
  intro x y z hz
  have h₁ : z / 2 ≠ -1 := by omega
  have h₂ : z / 2 ≠ -2 := by omega
  simp [fleet, slab, h₁, h₂]

private theorem axis_cover (p r : ℤ) (hr₀ : 0 ≤ r) (hr₂ : r < 2) :
    ∃! a : ℤ, a % 2 = r ∧ (a ≤ p ∧ p < a + 2) := by
  refine ⟨2 * ((p - r) / 2) + r, ⟨by omega, by omega, by omega⟩, ?_⟩
  intro a ha
  omega

private theorem slab_cover (q : ℤ → Bool) (j px py : ℤ) :
    ∃! o : ℤ × ℤ, slab q j o.1 o.2 ∧
      (o.1 ≤ px ∧ px < o.1 + 2) ∧ (o.2 ≤ py ∧ py < o.2 + 2) := by
  by_cases h₁ : j = -1
  · simp only [slab, h₁, ite_true]
    obtain ⟨y, hy, uy⟩ := axis_cover py 0 (by decide) (by decide)
    obtain ⟨x, hx, ux⟩ := axis_cover px (if y = 0 then 1 else 0)
      (by split <;> decide) (by split <;> decide)
    refine ⟨(x, y), ⟨⟨hy.1, hx.1⟩, hx.2, hy.2⟩, ?_⟩
    rintro ⟨a, b⟩ ⟨⟨hb, ha⟩, hpx, hpy⟩
    have hby := uy b ⟨hb, hpy⟩
    subst b
    exact Prod.ext (ux a ⟨ha, hpx⟩) rfl
  by_cases h₂ : j = -2
  · simp only [slab, h₂, ite_true]
    obtain ⟨x, hx, ux⟩ := axis_cover px 0 (by decide) (by decide)
    obtain ⟨y, hy, uy⟩ := axis_cover py (if x = 0 then 1 else 0)
      (by split <;> decide) (by split <;> decide)
    refine ⟨(x, y), ⟨⟨hx.1, hy.1⟩, hx.2, hy.2⟩, ?_⟩
    rintro ⟨a, b⟩ ⟨⟨ha, hb⟩, hpx, hpy⟩
    have hax := ux a ⟨ha, hpx⟩
    subst a
    exact Prod.ext rfl (uy b ⟨hb, hpy⟩)
  simp only [slab, h₁, h₂, ite_false]
  have hr₀ : 0 ≤ bit (q j) := by cases q j <;> decide
  have hr₂ : bit (q j) < 2 := by cases q j <;> decide
  obtain ⟨x, hx, ux⟩ := axis_cover px (bit (q j)) hr₀ hr₂
  obtain ⟨y, hy, uy⟩ := axis_cover py (bit (q j)) hr₀ hr₂
  refine ⟨(x, y), ⟨⟨hx.1, hy.1⟩, hx.2, hy.2⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨⟨ha, hb⟩, hpx, hpy⟩
  exact Prod.ext (ux a ⟨ha, hpx⟩) (uy b ⟨hb, hpy⟩)

private theorem fleet_cover (q : ℤ → Bool) : UniqueCover (fleet q) := by
  rintro ⟨px, py, pz⟩
  obtain ⟨z, hz, uz⟩ := axis_cover pz 0 (by decide) (by decide)
  obtain ⟨⟨x, y⟩, hxy, uxy⟩ := slab_cover q (z / 2) px py
  refine ⟨(x, y, z), ⟨⟨hz.1, hxy.1⟩, hxy.2.1, hxy.2.2, hz.2⟩, ?_⟩
  rintro ⟨a, b, c⟩ ⟨⟨hc, hab⟩, hpx, hpy, hpz⟩
  have hcz := uz c ⟨hc, hpz⟩
  subst c
  have h := uxy (a, b) ⟨hab, hpx, hpy⟩
  exact congrArg (fun xy : ℤ × ℤ => (xy.1, xy.2, z)) h

private theorem slab_x_parity (q : ℤ → Bool) {j x y : ℤ} (hj : j ≠ -1)
    (h : slab q j x y) : x % 2 = if j = -2 then 0 else bit (q j) := by
  by_cases hs : j = -2
  · rw [ite_eq_left hs]
    exact (show x % 2 = 0 ∧ _ from by simpa [slab, hj, hs] using h).1
  · rw [ite_eq_right hs]
    exact (show x % 2 = bit (q j) ∧ _ from by simpa [slab, hj, hs] using h).1

private theorem fleet_stabilizer (q : ℤ → Bool) : TrivialStabilizer (fleet q) := by
  intro dx dy dz h
  have hmarked : (1, 0, -2) ∈ fleet q := by simp [fleet, slab]
  have hplain : (0, 2, -2) ∈ fleet q := by simp [fleet, slab]
  have h₁ := (h 1 0 (-2)).mpr hmarked
  have h₂ := (h 0 2 (-2)).mpr hplain
  change (-2 + dz) % 2 = 0 ∧ slab q ((-2 + dz) / 2) (1 + dx) (0 + dy) at h₁
  change (-2 + dz) % 2 = 0 ∧ slab q ((-2 + dz) / 2) (0 + dx) (2 + dy) at h₂
  have hj : (-2 + dz) / 2 = -1 := by
    by_contra hn
    have hx := (slab_x_parity q hn h₁.2).trans (slab_x_parity q hn h₂.2).symm
    omega
  have hz : dz = 0 := by have he := h₁.1; omega
  subst dz
  let y : ℤ := if dy = -2 then 4 else 2
  have hy : y ≠ 0 ∧ y + dy ≠ 0 ∧ y % 2 = 0 := by
    dsimp [y]
    split <;> omega
  have hrow : (0, y, -2) ∈ fleet q := by simp [fleet, slab, hy.1, hy.2.2]
  have hx : dx % 2 = 0 := by
    have hh : (y + dy) % 2 = 0 ∧ dx % 2 = 0 := by
      simpa [fleet, slab, hy.2.1] using (h 0 y (-2)).mpr hrow
    exact hh.2
  have hdy : dy = 0 := by
    by_contra hne
    have hh := (h 1 0 (-2)).mpr hmarked
    simp [fleet, slab, hne] at hh
    omega
  subst dy
  have hcol : (0, 1, -4) ∈ fleet q := by simp [fleet, slab]
  have hdx : dx = 0 := by
    by_contra hne
    have hh := (h 0 1 (-4)).mpr hcol
    simp [fleet, slab, hne] at hh
  exact ⟨hdx, rfl, rfl⟩

private def scale (k : ℕ) : ℕ := 8 ^ (k + 1) * (k + 1).factorial

private theorem scale_growth (k : ℕ) : 16 * scale k ≤ scale (k + 1) := by
  calc
    16 * scale k ≤ (8 * (k + 2)) * scale k :=
      Nat.mul_le_mul_right _ (by omega)
    _ = scale (k + 1) := by
      simp only [scale, pow_succ 8 (k + 1), Nat.factorial_succ (k + 1)]
      ring

private theorem scale_lower (k : ℕ) : k + 2 ≤ scale k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hg := scale_growth k
    omega

private def endpoint : ℕ → ℕ
  | 0 => 0
  | k + 1 => 4 * scale k + 1

private theorem endpoint_strict : StrictMono endpoint := by
  apply strictMono_nat_of_lt_succ
  rintro (_ | k)
  · simp [endpoint]
  · have hg := scale_growth k
    have hl := scale_lower k
    simp only [endpoint]
    omega

private def target (weight : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => weight k * scale k

private theorem target_step (weight : ℕ → ℕ) (hw : ∀ k, 2 ≤ weight k ∧ weight k ≤ 3)
    (k : ℕ) :
    target weight k ≤ target weight (k + 1) ∧
    target weight (k + 1) - target weight k ≤ endpoint (k + 1) - endpoint k := by
  have bounds (i : ℕ) : 2 * scale i ≤ weight i * scale i ∧
      weight i * scale i ≤ 3 * scale i :=
    ⟨Nat.mul_le_mul_right _ (hw i).1, Nat.mul_le_mul_right _ (hw i).2⟩
  cases k with
  | zero =>
    have h := bounds 0
    simp only [target, endpoint]
    omega
  | succ k =>
    have h₁ := bounds k
    have h₂ := bounds (k + 1)
    have hg := scale_growth k
    simp only [target, endpoint]
    omega

private theorem endpoint_unbounded (n : ℕ) : ∃ k, n ≤ endpoint (k + 1) := by
  refine ⟨n, ?_⟩
  have h := scale_lower n
  simp only [endpoint]
  omega

private def slabPhase (weight : ℕ → ℕ) (j : ℤ) : Bool :=
  if 0 < j then
    let k := Nat.find (endpoint_unbounded j.toNat)
    decide ((endpoint k : ℤ) + ((target weight (k + 1) - target weight k : ℕ) : ℤ) < j)
  else false

private theorem slabPhase_block (weight : ℕ → ℕ) (k : ℕ) (j : ℤ)
    (hl : (endpoint k : ℤ) < j) (hr : j ≤ (endpoint (k + 1) : ℤ)) :
    slabPhase weight j = false ↔
      j ≤ (endpoint k : ℤ) + ((target weight (k + 1) - target weight k : ℕ) : ℤ) := by
  have hj : 0 < j := by omega
  have hu := endpoint_unbounded j.toNat
  have he : Nat.find hu = k := by
    apply le_antisymm
    · apply Nat.find_min'
      omega
    · by_contra! h
      have he := endpoint_strict.monotone (show Nat.find hu + 1 ≤ k by omega)
      have hs := Nat.find_spec hu
      omega
  simp only [slabPhase, ite_eq_left hj, he, decide_eq_false_iff_not, not_lt]

private theorem prefix_at_endpoint (weight : ℕ → ℕ)
    (hw : ∀ k, 2 ≤ weight k ∧ weight k ≤ 3) (k : ℕ) :
    prefixZero (slabPhase weight) (endpoint k) = target weight k := by
  induction k with
  | zero => simp [prefixZero, endpoint, target]
  | succ k ih =>
    let lo : ℤ := endpoint k
    let hi : ℤ := endpoint (k + 1)
    let inc : ℕ := target weight (k + 1) - target weight k
    have hstep := target_step weight hw k
    have hlo : 0 ≤ lo := by dsimp [lo]; omega
    have hhi : lo ≤ hi := by
      dsimp [lo, hi]
      exact_mod_cast (endpoint_strict.monotone (Nat.le_succ k))
    have hcap : lo + (inc : ℤ) ≤ hi := by
      dsimp [lo, hi, inc]
      omega
    have hdisj : Disjoint ((Ioc 0 lo).filter (fun j => slabPhase weight j = false))
        ((Ioc lo hi).filter (fun j => slabPhase weight j = false)) := by
      rw [Finset.disjoint_left]
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      omega
    have hfresh : (Ioc lo hi).filter (fun j => slabPhase weight j = false) =
        Ioc lo (lo + inc) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨hl, hr⟩, hq⟩
        exact ⟨hl, (slabPhase_block weight k j hl hr).mp hq⟩
      · rintro ⟨hl, hr⟩
        exact ⟨⟨hl, hr.trans hcap⟩, (slabPhase_block weight k j hl (hr.trans hcap)).mpr hr⟩
    change #((Ioc 0 hi).filter (fun j => slabPhase weight j = false)) = target weight (k + 1)
    rw [← Finset.Ioc_union_Ioc_eq_Ioc hlo hhi, Finset.filter_union,
      Finset.card_union_of_disjoint hdisj, hfresh, Int.card_Ioc]
    change prefixZero (slabPhase weight) (endpoint k) + (lo + (inc : ℤ) - lo).toNat = _
    rw [ih]
    dsimp [inc]
    omega

private def weight (swap : Bool) (k : ℕ) : ℕ :=
  if (k % 2 = 0) ↔ swap = false then 2 else 3

private theorem weight_bounds (swap : Bool) (k : ℕ) :
    2 ≤ weight swap k ∧ weight swap k ≤ 3 := by
  unfold weight
  split <;> decide

private def witness (swap : Bool) : Set Origin := fleet (slabPhase (weight swap))

private def side (k : ℕ) : ℕ := 8 * scale k + 3

private theorem witness_margin (k : ℕ) :
    margin (witness false) (witness true) (side k) = if k % 2 = 0 then 4 else -4 := by
  have hF := fleet_layered (slabPhase (weight false))
  have hG := fleet_layered (slabPhase (weight true))
  have hF0 : slabPhase (weight false) 0 = false := by simp [slabPhase]
  have hG0 : slabPhase (weight true) 0 = false := by simp [slabPhase]
  have hpF := prefix_at_endpoint _ (weight_bounds false) (k + 1)
  have hpG := prefix_at_endpoint _ (weight_bounds true) (k + 1)
  have ht : 2 ≤ scale k := by have h := scale_lower k; omega
  by_cases hk : k % 2 = 0
  · simp [endpoint, target, weight, hk] at hpF hpG
    simpa [witness, side, hk] using margin_pos_four _ _ _ _ hF hG hF0 hG0 _ ht hpF hpG
  · simp [endpoint, target, weight, hk] at hpF hpG
    simpa [witness, side, hk] using margin_neg_four _ _ _ _ hF hG hF0 hG0 _ ht hpF hpG

private theorem witness_outcome (k : ℕ) :
    outcome (witness false) (witness true) (side k) = if k % 2 = 0 then 1 else -1 := by
  unfold outcome
  rw [witness_margin]
  split <;> decide

private theorem side_lower (k : ℕ) : k + 1 ≤ side k := by
  have h := scale_lower k
  unfold side
  omega

private theorem side_step (k : ℕ) : side k ≤ side (k + 1) := by
  have h := scale_growth k
  unfold side
  omega

private theorem side_residue (P k : ℕ) (hP : 0 < P) (hk : P ≤ k + 1) :
    side k ≡ 3 [MOD P] := by
  have hd : P ∣ scale k := dvd_mul_of_dvd_right (Nat.dvd_factorial hP hk) _
  apply Nat.ModEq.add_right 3
  exact Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right hd _)

private theorem witness_no_period (P : ℕ) (hP : 0 < P) (B : ℕ) :
    ∃ c, max 1 B ≤ c ∧
      outcome (witness false) (witness true) (c + P) ≠
        outcome (witness false) (witness true) c := by
  let k := 2 * max P B
  have hk : P ≤ k + 1 := by dsimp [k]; omega
  have hB : max 1 B ≤ side k := by
    apply le_trans _ (side_lower k)
    dsimp [k]
    omega
  have heven : k % 2 = 0 := by dsimp [k]; omega
  have hodd : (k + 1) % 2 ≠ 0 := by omega
  have hmod := (side_residue P k hP hk).trans
    (side_residue P (k + 1) hP (by omega)).symm
  obtain ⟨m, hm⟩ := (Nat.modEq_iff_dvd' (side_step k)).mp hmod
  have hnext : side (k + 1) = side k + m * P := by
    rw [Nat.mul_comm m P]
    have h := side_step k
    omega
  by_contra! hperiod
  have hiterate (i : ℕ) :
      outcome (witness false) (witness true) (side k + i * P) =
        outcome (witness false) (witness true) (side k) := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Nat.succ_mul, ← Nat.add_assoc, hperiod _ (by omega), ih]
  have hsame := hiterate m
  rw [← hnext, witness_outcome, witness_outcome, ite_eq_right hodd, ite_eq_left heven] at hsame
  contradiction

/-- An affirmative answer to Kisielewicz's Problem 4 for a fixed pair of three-dimensional
cube fleets at base zero. The outcome uses every positive integral window side. -/
theorem exists_nonperiodic_fleets :
    ∃ F G : Set Origin,
      UniqueCover F ∧ UniqueCover G ∧ TrivialStabilizer F ∧ TrivialStabilizer G ∧
      (∀ B : ℕ, ∃ a b : ℕ, max 1 B ≤ a ∧ max 1 B ≤ b ∧
        outcome F G a = 1 ∧ outcome F G b = -1) ∧
      (∀ P : ℕ, 0 < P → ∀ B : ℕ, ∃ c : ℕ, max 1 B ≤ c ∧
        outcome F G (c + P) ≠ outcome F G c) := by
  refine ⟨witness false, witness true, fleet_cover _, fleet_cover _,
    fleet_stabilizer _, fleet_stabilizer _, ?_, witness_no_period⟩
  intro B
  let k := 2 * B
  have heven : k % 2 = 0 := by dsimp [k]; omega
  have hodd : (k + 1) % 2 ≠ 0 := by omega
  have hB : max 1 B ≤ side k := by
    apply le_trans _ (side_lower k)
    dsimp [k]
    omega
  refine ⟨side k, side (k + 1), hB, hB.trans (side_step k), ?_, ?_⟩
  · rw [witness_outcome, ite_eq_left heven]
  · rw [witness_outcome, ite_eq_right hodd]

#print axioms exists_nonperiodic_fleets

end KisielewiczFleetWinners
