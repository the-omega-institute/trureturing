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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace KisielewiczFleetScoreProbe

open Finset
open scoped BigOperators Classical

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
  push_cast at h
  have ceilDiv (u : ℤ) : ⌈(u : ℚ) / 2⌉ = -((-u) / 2) := by
    exact Rat.ceil_intCast_div_natCast u 2
  rw [← Int.cast_sub, ← Int.cast_sub] at h
  change _ = max (⌈(_ : ℤ) / (2 : ℚ)⌉ - ⌈(_ : ℤ) / (2 : ℚ)⌉) 0 at h
  rw [ceilDiv, ceilDiv] at h
  cases s <;> cases q <;> simp [bit, axisCount] at h ⊢ <;> omega

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
  cases v <;> simp [slabs, totalSlabs, Finset.card_insert_of_notMem, Int.card_Ioc]

private theorem zeroSlabs_card (q : ℤ → Bool) (hq : q 0 = false) (n : ℕ) (v : Bool) :
    ((slabs n v).filter (fun j => q j = false)).card = zeroSlabs q n v := by
  cases v <;> simp [slabs, zeroSlabs, prefixZero, hq, Finset.filter_insert,
    Finset.card_insert_of_notMem]

private theorem otherSlabs_card (q : ℤ → Bool) (hq : q 0 = false) (n : ℕ) (v : Bool) :
    ((slabs n v).filter (fun j => q j ≠ false)).card =
      totalSlabs n v - zeroSlabs q n v := by
  have h := Finset.card_filter_add_card_filter_not (s := slabs n v) (fun j => q j = false)
  rw [zeroSlabs_card q hq, slabs_card] at h
  omega

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
    exact Finset.card_filter_add_card_filter_not _ _
  dsimp only
  simp only [score_phase_sum F q hF hq, axisCount, if_pos, if_false, Bool.false_eq_true,
    Bool.true_eq_false]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    conv_rhs => rw [← hsum] <;>
    ring

#print axioms horizontal_scores

end KisielewiczFleetScoreProbe
