/- GID: D5/S3/Combinatorics/PathAlignedPacking/Metric
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PathAlignedPacking/Metric
   mirror-E: none(waiver:distance-certificate-infrastructure)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: A shortest-route lower bound for walks, and reflection of the two arcs. -/

import D5.S3.Combinatorics.PathAlignedPacking.Defs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PathAlignedPacking.Metric

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Defs

/-- The shorter of the two arcs between positions in a cycle. -/
def cycleSep (n x y : ℤ) : ℤ :=
  if x ≤ y then min (y - x) (n + x - y) else min (x - y) (n + y - x)

/-- Length of the canonical shortest route in the chain. Only its lower-bound
    property is needed for the infinite constructions. -/
def chainSep (a b : ℤ) (u v : Point) : ℤ :=
  if u.1 = v.1 then cycleSep (a + b) u.2 v.2
  else if u.1 < v.1 then
    cycleSep (a + b) u.2 a +
      ((v.1 : ℤ) - (u.1 : ℤ) - 1) * (min a b + 1) + 1 +
      cycleSep (a + b) 0 v.2
  else
    cycleSep (a + b) u.2 0 +
      ((u.1 : ℤ) - (v.1 : ℤ) - 1) * (min a b + 1) + 1 +
      cycleSep (a + b) a v.2

private theorem cycle_self (n x : ℤ) (hn : 0 ≤ n) : cycleSep n x x = 0 := by
  simp [cycleSep, hn]

private theorem cycle_symm (n x y : ℤ) : cycleSep n x y = cycleSep n y x := by
  simp only [cycleSep, min_def]
  split_ifs <;> omega

private theorem cycle_nonneg (n x y : ℤ) (hx : 0 ≤ x) (hxn : x < n)
    (hy : 0 ≤ y) (hyn : y < n) : 0 ≤ cycleSep n x y := by
  simp only [cycleSep, min_def]
  split_ifs <;> omega

private theorem cycle_triangle (n x y z : ℤ)
    (hx : 0 ≤ x) (hxn : x < n) (hy : 0 ≤ y) (hyn : y < n)
    (hz : 0 ≤ z) (hzn : z < n) :
    cycleSep n x z ≤ cycleSep n x y + cycleSep n y z := by
  simp only [cycleSep, min_def]
  split_ifs <;> omega

private theorem cycle_edge (n x y : ℤ) (hx : 0 ≤ x) (hxn : x < n)
    (hy : 0 ≤ y) (hyn : y < n) (h : CycleAdj n x y) : cycleSep n x y ≤ 1 := by
  unfold CycleAdj at h
  rcases h with h | h | h | h
  all_goals simp only [cycleSep, min_def]; split_ifs <;> omega

private theorem cycle_gate (a b : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    cycleSep (a + b) a 0 = min a b ∧ cycleSep (a + b) 0 a = min a b := by
  simp only [cycleSep, min_def]
  split_ifs <;> omega

theorem chain_symm (a b : ℤ) (u v : Point) : chainSep a b u v = chainSep a b v u := by
  simp only [chainSep]
  split_ifs <;> try omega
  all_goals rw [cycle_symm (a + b) u.2, cycle_symm (a + b) v.2] <;> ring

/-- Moving across one graph edge changes distance from a fixed source by at most one. -/
theorem chain_step (a b : ℤ) (s u v : Point) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hs : 0 ≤ s.2 ∧ s.2 < a + b) (hu : 0 ≤ u.2 ∧ u.2 < a + b)
    (hv : 0 ≤ v.2 ∧ v.2 < a + b) (h : RawAdj a b u v) :
    chainSep a b s v ≤ chainSep a b s u + 1 := by
  have h0 : 0 < a + b := by omega
  have hga := (cycle_gate a b ha hb).1
  have hgb := (cycle_gate a b ha hb).2
  have hsa := cycle_triangle (a + b) s.2 a 0 hs.1 hs.2 (by omega) (by omega)
    (by omega) h0
  have hsb := cycle_triangle (a + b) s.2 0 a hs.1 hs.2 (by omega) h0
    (by omega) (by omega)
  rw [hga] at hsa
  rw [hgb] at hsb
  rcases s with ⟨r, z⟩
  rcases u with ⟨i, x⟩
  rcases v with ⟨j, y⟩
  rcases h with ⟨hij, hxy⟩ | ⟨hij, hx, hy⟩ | ⟨hij, hy, hx⟩
  · simp only [Prod.fst, Prod.snd] at hu hv hij hxy
    subst j
    have hxy' := cycle_edge (a + b) x y hu.1 hu.2 hv.1 hv.2 hxy
    have hsy := cycle_triangle (a + b) z x y hs.1 hs.2 hu.1 hu.2 hv.1 hv.2
    have h0y := cycle_triangle (a + b) 0 x y (by omega) h0 hu.1 hu.2 hv.1 hv.2
    have hay := cycle_triangle (a + b) a x y (by omega) (by omega)
      hu.1 hu.2 hv.1 hv.2
    simp only [chainSep, Prod.fst, Prod.snd]
    split_ifs <;> omega
  · simp only [Prod.fst, Prod.snd] at hu hv hij hx hy
    subst j; subst x; subst y
    simp only [chainSep, Prod.fst, Prod.snd, Nat.cast_add, Nat.cast_one]
    split_ifs <;>
      try simp only [cycle_self (a + b) 0 (by omega),
        cycle_self (a + b) a (by omega), Nat.cast_add, Nat.cast_one]
    all_goals try subst r
    all_goals try simp only [Nat.cast_add, Nat.cast_one] at *
    all_goals ring_nf at *; omega
  · simp only [Prod.fst, Prod.snd] at hu hv hij hx hy
    subst i; subst x; subst y
    simp only [chainSep, Prod.fst, Prod.snd, Nat.cast_add, Nat.cast_one]
    split_ifs <;>
      try simp only [cycle_self (a + b) 0 (by omega),
        cycle_self (a + b) a (by omega), Nat.cast_add, Nat.cast_one]
    all_goals try subst r
    all_goals try simp only [Nat.cast_add, Nat.cast_one] at *
    all_goals ring_nf at *; omega

/-- Consequently this arithmetic distance is a lower bound for every actual walk. -/
theorem walk_lower (n ℓ t : ℕ) (hℓ : 4 ≤ ℓ) (hℓn : ℓ ≤ n)
    {u v : Vertex t n} (p : (graph n ℓ t).Walk u v) :
    chainSep (ℓ - 1 : ℕ) (n - ℓ + 1 : ℕ) (point u) (point v) ≤ p.length := by
  have chain_self (a b : ℤ) (u : Point) (ha : 1 ≤ a) (hb : 1 ≤ b) :
      chainSep a b u u = 0 := by
    simp [chainSep, cycle_self, show 0 ≤ a + b by omega]
  have hab : (ℓ - 1 : ℕ) + (n - ℓ + 1) = n := by omega
  have ha : (1 : ℤ) ≤ (ℓ - 1 : ℕ) := by omega
  have hb : (1 : ℤ) ≤ (n - ℓ + 1 : ℕ) := by omega
  have bounds (w : Vertex t n) :
      0 ≤ (point w).2 ∧ (point w).2 < (ℓ - 1 : ℕ) + (n - ℓ + 1 : ℕ) := by
    have := w.2.isLt
    simp only [point, Prod.snd]
    exact ⟨by omega, by exact_mod_cast (show w.2.val < (ℓ - 1) + (n - ℓ + 1) by omega)⟩
  induction p with
  | @nil w => simpa using le_of_eq (chain_self _ _ (point w) ha hb)
  | @cons x y z h q ih =>
    have hs := chain_step _ _ (point z) (point y) (point x) ha hb
      (bounds z) (bounds y) (bounds x) ((graph n ℓ t).symm.symm x y h).2
    rw [chain_symm _ _ (point z) (point x),
      chain_symm _ _ (point z) (point y)] at hs
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one] at ih hs ⊢
    omega

theorem far_blocks (a b : ℤ) (u v : Point) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hu : 0 ≤ u.2 ∧ u.2 < a + b) (hv : 0 ≤ v.2 ∧ v.2 < a + b)
    (h : u.1 + 4 ≤ v.1) : 6 < chainSep a b u v := by
  have hx := cycle_nonneg (a + b) u.2 a hu.1 hu.2 (by omega) (by omega)
  have hy := cycle_nonneg (a + b) 0 v.2 (by omega) (by omega) hv.1 hv.2
  have hm : 1 ≤ min a b := le_min ha hb
  have hd : (3 : ℤ) ≤ (v.1 : ℤ) - (u.1 : ℤ) - 1 := by omega
  have hp := mul_le_mul_of_nonneg_right hd (show 0 ≤ min a b + 1 by omega)
  simp only [chainSep, if_neg (show u.1 ≠ v.1 by omega), if_pos (show u.1 < v.1 by omega)]
  nlinarith

/-- An infinite arithmetic packing certificate, later restricted to any number of blocks. -/
def HasMetricColor (a b : ℤ) (k : ℕ) : Prop :=
  ∃ f : Point → ℕ,
    (∀ u, 0 ≤ u.2 → u.2 < a + b → 1 ≤ f u ∧ f u ≤ k) ∧
    ∀ u v, 0 ≤ u.2 → u.2 < a + b → 0 ≤ v.2 → v.2 < a + b →
      u ≠ v → f u = f v → (f u : ℤ) < chainSep a b u v

theorem metric_to_packing (n ℓ t k : ℕ) (hℓ : 4 ≤ ℓ) (hℓn : ℓ ≤ n)
    (h : HasMetricColor (ℓ - 1 : ℕ) (n - ℓ + 1 : ℕ) k) :
    HasPacking (graph n ℓ t) k := by
  rcases h with ⟨f, hb, hp⟩
  have bounds (v : Vertex t n) :
      0 ≤ (point v).2 ∧ (point v).2 < (ℓ - 1 : ℕ) + (n - ℓ + 1 : ℕ) := by
    have := v.2.isLt
    simp only [point, Prod.snd]
    constructor <;> omega
  refine ⟨fun v => f (point v), ?_, ?_⟩
  · intro v; exact hb (point v) (bounds v).1 (bounds v).2
  · intro u v hne heq p
    have hpoint : point u ≠ point v := by
      intro he
      apply hne
      apply Prod.ext <;> apply Fin.ext
      · exact congrArg Prod.fst he
      · have := congrArg Prod.snd he; simpa [point] using this
    have hsep := hp (point u) (point v) (bounds u).1 (bounds u).2
      (bounds v).1 (bounds v).2 hpoint heq
    have hl := walk_lower n ℓ t hℓ hℓn p
    change f (point u) < p.length
    exact_mod_cast (lt_of_lt_of_le hsep hl)

def reflect (n : ℤ) (u : Point) : Point := (u.1, if u.2 = 0 then 0 else n - u.2)

private theorem reflect_cycle (n x y : ℤ) (hx : 0 ≤ x) (hxn : x < n)
    (hy : 0 ≤ y) (hyn : y < n) :
    cycleSep n (if x = 0 then 0 else n - x) (if y = 0 then 0 else n - y) =
      cycleSep n x y := by
  simp only [cycleSep, min_def]
  split_ifs <;> omega

private theorem reflect_sep (a b : ℤ) (u v : Point) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hu : 0 ≤ u.2 ∧ u.2 < a + b) (hv : 0 ≤ v.2 ∧ v.2 < a + b) :
    chainSep b a (reflect (a + b) u) (reflect (a + b) v) = chainSep a b u v := by
  have hab : b + a = a + b := by ring
  have h0 : (if (0 : ℤ) = 0 then 0 else a + b - 0) = 0 := by simp
  have hx : (if a = 0 then 0 else a + b - a) = b := by simp [show a ≠ 0 by omega]
  have huv := reflect_cycle (a + b) u.2 v.2 hu.1 hu.2 hv.1 hv.2
  have hua := reflect_cycle (a + b) u.2 a hu.1 hu.2 (by omega) (by omega)
  have hu0 := reflect_cycle (a + b) u.2 0 hu.1 hu.2 (by omega) (by omega)
  have hav := reflect_cycle (a + b) a v.2 (by omega) (by omega) hv.1 hv.2
  have h0v := reflect_cycle (a + b) 0 v.2 (by omega) (by omega) hv.1 hv.2
  simp only [hx, h0] at hua hu0 hav h0v
  simp only [chainSep, reflect, Prod.fst, Prod.snd, hab, min_comm b a]
  split_ifs <;> simp_all

theorem metric_swap (a b : ℤ) (k : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : HasMetricColor a b k) : HasMetricColor b a k := by
  rcases h with ⟨f, hbounds, hpacking⟩
  have bounds (u : Point) (hu : 0 ≤ u.2 ∧ u.2 < b + a) :
      0 ≤ (reflect (a + b) u).2 ∧ (reflect (a + b) u).2 < a + b := by
    simp only [reflect, Prod.snd]; split_ifs <;> omega
  refine ⟨fun u => f (reflect (a + b) u), ?_, ?_⟩
  · intro u hu hun
    exact hbounds _ (bounds u ⟨hu, hun⟩).1 (bounds u ⟨hu, hun⟩).2
  · intro u v hu hun hv hvn hne heq
    have hne' : reflect (a + b) u ≠ reflect (a + b) v := by
      intro he
      apply hne; apply Prod.ext
      · simpa only [reflect] using congrArg Prod.fst he
      · have := congrArg Prod.snd he
        simp only [reflect, Prod.snd] at this
        split_ifs at this <;> omega
    have hh := hpacking _ _ (bounds u ⟨hu, hun⟩).1 (bounds u ⟨hu, hun⟩).2
      (bounds v ⟨hv, hvn⟩).1 (bounds v ⟨hv, hvn⟩).2 hne' heq
    have hr := reflect_sep b a u v hb ha ⟨hu, hun⟩ ⟨hv, hvn⟩
    have hr' : chainSep a b (reflect (a + b) u) (reflect (a + b) v) =
        chainSep b a u v := by simpa [add_comm] using hr
    rw [hr'] at hh
    exact hh

end D5.S3.Combinatorics.PathAlignedPacking.Metric
