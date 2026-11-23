/- GID: D5/S3/Arith/Lattices/KisielewiczFleetScoreProbe
   generality: S
   mirror-B: none
   mirror-E: none
   anchors: []
   utility: none
   digest: Odd-window scores and signed margins for layered cube origins. -/

import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Literal finite-window counts for the layered construction in Kisielewicz's Problem 4. -/

namespace KisielewiczFleetScoreProbe

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
theorem horizontal_scores (F : Set Origin) (q : ℤ → Bool)
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
theorem margin_pos_four (F G : Set Origin) (qF qG : ℤ → Bool)
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
theorem margin_neg_four (F G : Set Origin) (qF qG : ℤ → Bool)
    (hF : Layered F qF) (hG : Layered G qG) (hF0 : qF 0 = false) (hG0 : qG 0 = false)
    (t : ℕ) (ht : 2 ≤ t)
    (hpF : prefixZero qF (4 * t + 1) = 3 * t)
    (hpG : prefixZero qG (4 * t + 1) = 2 * t) :
    margin F G (8 * t + 3) = -4 := by
  rw [margin_swap, margin_pos_four G F qG qF hG hF hG0 hF0 t ht hpG hpF]

#print axioms horizontal_scores
#print axioms margin_pos_four
#print axioms margin_neg_four

end KisielewiczFleetScoreProbe
