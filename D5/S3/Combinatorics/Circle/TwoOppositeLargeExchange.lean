/- GID: D5/S3/Combinatorics/Circle/TwoOppositeLargeExchange
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/TwoOppositeLargeExchange
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: Native two-edge two-opposite-LARGE exchange with derived gates and physical inventory. -/
module
public import D5.S3.Combinatorics.Circle.SmallStepOrdering
public import D5.S3.Combinatorics.Circle.MixedSuffixEnergy
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! Three explicit physical exchanges exhaust the two-opposite-LARGE branch.
The actual-source geometry, all natural prefixes, inventories and descent are proved below. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.TwoOppositeLargeExchange
open SourceWidth ExpandingSourcePath MixedSuffixEnergy SmallStepOrdering
open scoped BigOperators

abbrev s := actualSource
abbrev N := modulus
abbrev C := half
abbrev Q := quarter

local macro "source_arith" : tactic =>
  `(tactic| ((try simp only [s, N, C, Q, Large, mass, List.cons_append,
    List.nil_append, List.take_zero, List.take_succ_cons, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
    add_zero, zero_add] at *) <;> omega))

def Legal (k t : ℕ) (W : List (Fin k)) : Prop :=
  W.Nodup ∧ ∀ j : ℕ, 0 ≤ mass (s k t) (W.take j) ∧ mass (s k t) (W.take j) ≤ C k

def hit (k j : ℕ) (p : Fin k) : Fin k := ((finRotate k : Fin k → Fin k)^[j]) p

@[simp] theorem hit_zero {k : ℕ} (p : Fin k) : hit k 0 p = p := rfl

def W2 {k : ℕ} (p z1 z2 : Fin k) (A T0 T1 T2 : List (Fin k)) : List (Fin k) :=
  A ++ [hit k 2 p] ++ T0 ++ [z1] ++ T1 ++ [z2] ++ T2

def F1 {k : ℕ} (p z1 : Fin k) (A T0 : List (Fin k)) : List (Fin k) :=
  A ++ [hit k 2 p] ++ T0 ++ [z1]

def departure {k : ℕ} (t : ℕ) (p z1 : Fin k) (A T0 T1 : List (Fin k)) : ℤ :=
  let v := mass (s k t) (F1 p z1 A T0 ++ T1)
  if 0 < s k t p then v else C k - v

def V2 {k : ℕ} (t : ℕ) (p z1 z2 : Fin k) (A T0 T1 T2 L E : List (Fin k)) : List (Fin k) :=
  if |s k t p| ≤ |s k t z1| then F1 p z1 A T0 ++ [p, hit k 1 p]
  else if departure t p z1 A T0 T1 < |s k t p| then
    (F1 p z1 A T0 ++ T1 ++ [z2]) ++ [p]
  else A ++ [p, hit k 1 p] ++ L ++ [z1] ++ E

def inserted {k : ℕ} (t : ℕ) (p z1 : Fin k) (A T0 T1 : List (Fin k)) : List (Fin k) :=
  if |s k t p| ≤ |s k t z1| then [p, hit k 1 p]
  else if departure t p z1 A T0 T1 < |s k t p| then [p] else [p, hit k 1 p]

def returned {k : ℕ} (t : ℕ) (p z1 z2 : Fin k) (A T0 T1 T2 : List (Fin k)) : List (Fin k) :=
  if |s k t p| ≤ |s k t z1| then T1 ++ [z2] ++ T2
  else if departure t p z1 A T0 T1 < |s k t p| then T2 else [hit k 2 p, z2]

def remainingSmall {k : ℕ} (t : ℕ) (W : List (Fin k)) : Finset (Fin k) :=
  W.toFinsetᶜ.filter (fun q => ¬ Large k t q)

/-- Coordinate reflection is confined to arithmetic; the physical word is unchanged. -/
def coord (negative : Bool) (cap h : ℤ) : ℤ := if negative then cap - h else h

theorem coord_mass {α : Type*} (negative : Bool) (cap h : ℤ) (f : α → ℤ) (L : List α) :
    coord negative cap (h + mass f L) =
      coord negative cap h + mass (fun q => orient negative (f q)) L := by
  cases negative <;> simp [coord, orient, mass, sum_neg_map] <;> ring

theorem strip_coordinate {α : Type*} (negative : Bool) {f : α → ℤ} {cap h : ℤ} {L : List α} :
    InStrip f cap h L ↔ InStrip (fun q => orient negative (f q)) cap (coord negative cap h) L := by
  cases negative
  · simp [orient, coord]
  · constructor
    · intro hs
      have hh : InStrip (fun q => - -f q) cap (cap - (cap - h)) L := by simpa using hs
      simpa [orient, coord] using (inStrip_reflect (f := fun q => -f q) hh)
    · intro hs
      exact inStrip_reflect (by simpa [orient, coord] using hs)

theorem legal_of_strip {k t : ℕ} {W : List (Fin k)} (hn : W.Nodup)
    (hs : InStrip (s k t) (C k) 0 W) : Legal k t W := by
  refine ⟨hn, fun j => ?_⟩
  simpa [mass] using inStrip_prefix hs j

theorem strip_of_legal {k t : ℕ} {W : List (Fin k)} (hW : Legal k t W) :
    InStrip (s k t) (C k) 0 W := by
  apply strip_of_all_prefixes W
  simpa only [zero_add] using hW.2

/-- A checked total-word permutation exposes both exact physical partitions.
The additive balances also cover returning SMALL labels. -/
structure Inventory (k t : ℕ) (W V I R : List (Fin k)) : Prop where
  nodup : V.Nodup
  used : V.toFinset = (W.toFinset \ R.toFinset) ∪ I.toFinset
  usedDisjoint : Disjoint (W.toFinset \ R.toFinset) I.toFinset
  unused : V.toFinsetᶜ = (W.toFinsetᶜ \ I.toFinset) ∪ R.toFinset
  unusedDisjoint : Disjoint (W.toFinsetᶜ \ I.toFinset) R.toFinset
  largeBalance : G k t V + largeUsed k t I = G k t W + largeUsed k t R
  energyBalance : H k t V + H k t R = H k t W + H k t I
  countBalance : U V + I.length = U W + R.length
  complementSum : remainingMass (s k t) V = -mass (s k t) V
  sourceBalance : mass (s k t) V + mass (s k t) R = mass (s k t) W + mass (s k t) I
  smallPartition : remainingSmall t V = remainingSmall t W ∪ R.toFinset.filter (fun q => ¬ Large k t q)
  smallDisjoint : Disjoint (remainingSmall t W) (R.toFinset.filter (fun q => ¬ Large k t q))

theorem inventory_of_perm {k : ℕ} (hk : 3 ≤ k) (t : ℕ) (W V I R : List (Fin k))
    (hW : W.Nodup) (hI : I.Nodup) (hIW : ∀ q ∈ I, q ∉ W)
    (hR : ∀ q ∈ R, q ∈ W) (hIL : ∀ q ∈ I, Large k t q)
    (hp : (V ++ R).Perm (W ++ I)) : Inventory k t W V I R := by
  classical
  have hWI : (W ++ I).Nodup := hW.append hI (List.disjoint_left.mpr (by
    intro q hqW hqI; exact hIW q hqI hqW))
  have hn := List.nodup_append'.mp (hp.nodup_iff.mpr hWI)
  have hV := hn.1
  have hVR : ∀ q ∈ V, q ∉ R := fun q hq => List.disjoint_left.mp hn.2.2 hq
  have hm (q : Fin k) : (q ∈ V ∨ q ∈ R) ↔ (q ∈ W ∨ q ∈ I) := by
    simpa only [List.mem_append] using (hp.mem_iff (a := q))
  have hu : V.toFinset = (W.toFinset \ R.toFinset) ∪ I.toFinset := by
    ext q
    have hvq := hVR q
    have hiq := hIW q
    have hrq := hR q
    have hmq := hm q
    simp only [List.mem_toFinset, Finset.mem_union, Finset.mem_sdiff]
    tauto
  have hr : V.toFinsetᶜ = (W.toFinsetᶜ \ I.toFinset) ∪ R.toFinset := by
    ext q
    have hvq := hVR q
    have hiq := hIW q
    have hrq := hR q
    have hmq := hm q
    simp only [Finset.mem_compl, List.mem_toFinset, Finset.mem_union, Finset.mem_sdiff]
    tauto
  have hud : Disjoint (W.toFinset \ R.toFinset) I.toFinset := by
    apply Finset.disjoint_left.mpr
    intro q hq hi
    exact hIW q (List.mem_toFinset.mp hi) (List.mem_toFinset.mp (Finset.mem_sdiff.mp hq).1)
  have hrd : Disjoint (W.toFinsetᶜ \ I.toFinset) R.toFinset := by
    apply Finset.disjoint_left.mpr
    intro q hq hqR
    exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp hq).1)
      (List.mem_toFinset.mpr (hR q (List.mem_toFinset.mp hqR)))
  have hmass {β : Type} [AddCommMonoid β] (w : Fin k → β) :
      mass w V + mass w R = mass w W + mass w I := by
    simpa [mass] using (hp.map w).sum_eq
  have hwg := physical_balance (largeWeight k t) W hW
  have hvg := physical_balance (largeWeight k t) V hV
  have hlg := hmass (largeWeight k t)
  change G k t W + largeUsed k t W = _ at hwg
  change G k t V + largeUsed k t V = _ at hvg
  change largeUsed k t V + largeUsed k t R = largeUsed k t W + largeUsed k t I at hlg
  have hwc : U W + W.length = k := by
    simpa [U, mass, List.map_const'] using physical_balance (fun _ : Fin k => (1 : ℕ)) W hW
  have hvc : U V + V.length = k := by
    simpa [U, mass, List.map_const'] using physical_balance (fun _ : Fin k => (1 : ℕ)) V hV
  have hlen := hp.length_eq
  simp only [List.length_append] at hlen
  have hzero := physical_balance (s k t) V hV
  rw [(ZeroSumSubsets.source_cycle (by source_arith : 0 < k) t).2.1] at hzero
  have hsmall : remainingSmall t V = remainingSmall t W ∪ R.toFinset.filter (fun q => ¬ Large k t q) := by
    ext q
    have hlarge : q ∈ I → Large k t q := hIL q
    rw [remainingSmall, hr]
    simp only [remainingSmall, Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_compl, List.mem_toFinset]
    tauto
  have hsd : Disjoint (remainingSmall t W) (R.toFinset.filter (fun q => ¬ Large k t q)) := by
    apply Finset.disjoint_left.mpr
    intro q hq hqR
    exact (Finset.mem_compl.mp (Finset.mem_filter.mp hq).1)
      (List.mem_toFinset.mpr (hR q (List.mem_toFinset.mp (Finset.mem_filter.mp hqR).1)))
  exact ⟨hV, hu, hud, hr, hrd, by source_arith, hmass (energyWeight k t), by source_arith,
    by source_arith, hmass (s k t), hsmall, hsd⟩

theorem small_weights {k : ℕ} (t : ℕ) (T : List (Fin k))
    (hsmall : ∀ q ∈ T, |s k t q| < Q k) : largeUsed k t T = 0 ∧ H k t T = 0 := by
  revert hsmall
  induction T with
  | nil => intro _; simp [largeUsed, H, mass]
  | cons q T ih =>
    intro hsmall
    have hq : ¬ Large k t q := by have hh := hsmall q (by simp); unfold Large; source_arith
    have ht := ih (fun r hr => hsmall r (by simp [hr]))
    simpa [largeUsed, H, mass, largeWeight, energyWeight, hq] using ht

private theorem hit_phase {k : ℕ} (hk : 0 < k) (p : Fin k) (j : ℕ) :
    hit k j p = phase hk p j := by
  letI : NeZero k := ⟨ne_of_gt hk⟩
  induction j with
  | zero => simp [hit]
  | succ j ih =>
    rw [hit, Function.iterate_succ_apply']
    change finRotate k (hit k j p) = _
    rw [ih, finRotate_apply]
    apply Fin.ext
    simp [phase, Fin.val_add, Nat.mod_add_mod, Nat.add_assoc]

private theorem step_orient (negative : Bool) (n z : ℤ) (hn : 0 ≤ n) :
    orient negative (doubleStep n z) = doubleStep n (orient negative z) := by
  cases negative
  · rfl
  · change -doubleStep n z = doubleStep n (-z)
    exact (doubleStep_neg hn).symm

/-- Every scalar fact in this record is derived from the actual physical source. -/
structure Geometry (k t : ℕ) (p : Fin k) : Prop where
  pLarge : Large k t p
  nLarge : Large k t (hit k 1 p)
  xLarge : Large k t (hit k 2 p)
  nValue : orient (decide (s k t p < 0)) (s k t (hit k 1 p)) = -|s k t (hit k 1 p)|
  xValue : orient (decide (s k t p < 0)) (s k t (hit k 2 p)) = |s k t (hit k 2 p)|
  firstEquation : |s k t (hit k 1 p)| = N k - 2 * |s k t p|
  secondEquation : |s k t (hit k 2 p)| = 4 * |s k t p| - N k
  strictOrder : |s k t (hit k 1 p)| < |s k t p| ∧ |s k t p| < |s k t (hit k 2 p)|
  budget : 2 * |s k t p| ≤ C k + Q k
  energy : (3 : ℕ) ^ (s k t p).natAbs + (3 : ℕ) ^ (s k t (hit k 1 p)).natAbs <
    (3 : ℕ) ^ (s k t (hit k 2 p)).natAbs

theorem native_geometry {k : ℕ} (hk : 3 ≤ k) (t : ℕ) (p : Fin k)
    (hn : Q k ≤ |s k t (hit k 1 p)|) (hex : N k < 3 * |s k t p|) : Geometry k t p := by
  obtain ⟨hQ, hN, hC, hN0, hodd⟩ := source_geometry hk
  have hb (q : Fin k) : |s k t q| ≤ C k := by
    exact abs_le.mpr (centered_bounds hN0 hodd _)
  let neg : Bool := decide (s k t p < 0)
  let g : Fin k → ℤ := fun q => orient neg (s k t q)
  have hp : Large k t p := by unfold Large; source_arith
  have hgp : g p = |s k t p| := orient_choose _
  have hs (j : ℕ) : g (hit k (j + 1) p) = doubleStep (N k) (g (hit k j p)) := by
    simp only [g, s, hit_phase (by ((try dsimp only [g, neg] at *); source_arith) : 0 < k)]
    rw [phase_step hk t p j, step_orient neg (N k) _ (le_of_lt hN0)]
  have hsn := hs 0
  simp only [hit_zero] at hsn
  rw [hgp, doubleStep, if_pos (by unfold Large at hp; ((try dsimp only [g, neg] at *); source_arith))] at hsn
  change g (hit k 1 p) = 2 * |s k t p| - N k at hsn
  have hgn : g (hit k 1 p) < 0 := by have hh := hb p; ((try dsimp only [g, neg] at *); source_arith)
  have hDn : |s k t (hit k 1 p)| = -g (hit k 1 p) := by
    rw [← orient_abs neg, abs_of_neg hgn]
  have hsx := hs 1
  rw [doubleStep, if_neg (by ((try dsimp only [g, neg] at *); source_arith)), if_pos (by ((try dsimp only [g, neg] at *); source_arith))] at hsx
  change g (hit k 2 p) = 2 * g (hit k 1 p) + N k at hsx
  have hL : ∀ j < 2, Large k t (phase (by ((try dsimp only [g, neg] at *); source_arith)) p j) := by
    intro j hj
    have he : j = 0 ∨ j = 1 := by ((try dsimp only [g, neg] at *); source_arith)
    rcases he with rfl | rfl
    · simpa using hp
    · simpa only [Large, Q, s, ← hit_phase (by ((try dsimp only [g, neg] at *); source_arith) : 0 < k)] using hn
  have hd : 0 < 3 * orient neg (s k t p) - N k := by rw [orient_choose]; ((try dsimp only [g, neg] at *); source_arith)
  obtain ⟨hxpos, hxL, _, _, _, henergy⟩ := expanding_path_estimates hk t p 2
    (by ((try dsimp only [g, neg] at *); source_arith)) (by decide) neg hL hd
  have hxpos' : 0 < g (hit k 2 p) := by simpa only [hit_phase (by ((try dsimp only [g, neg] at *); source_arith) : 0 < k)] using hxpos
  have hrx : |s k t (hit k 2 p)| = g (hit k 2 p) := by
    rw [← orient_abs neg, abs_of_pos hxpos']
  have hE : (3 : ℕ) ^ (s k t p).natAbs + (3 : ℕ) ^ (s k t (hit k 1 p)).natAbs <
      (3 : ℕ) ^ (s k t (hit k 2 p)).natAbs := by
    simpa [path, List.range_succ, ← hit_phase (by ((try dsimp only [g, neg] at *); source_arith) : 0 < k), hit] using henergy
  refine ⟨hp, hn, ?_, by ((try dsimp only [g, neg] at *); source_arith), by ((try dsimp only [g, neg] at *); source_arith), by ((try dsimp only [g, neg] at *); source_arith), by ((try dsimp only [g, neg] at *); source_arith), ⟨by ((try dsimp only [g, neg] at *); source_arith), by ((try dsimp only [g, neg] at *); source_arith)⟩,
    ?_, hE⟩
  · simpa only [← hit_phase (by ((try dsimp only [g, neg] at *); source_arith) : 0 < k)] using hxL
  · have hh := hb (hit k 2 p); ((try dsimp only [g, neg] at *); source_arith)

/-- A native expanding source has no physical occurrence of Q-1.
The proof enumerates the actual k-cycle from that value; it assumes no
injectivity of numerical source values. -/
theorem actual_source_ne_q_sub_one
    (k t : ℕ) (hk : 3 ≤ k) (p : Fin k)
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|) :
    ∀ i : Fin k, s k t i ≠ Q k - 1 := by
  obtain ⟨hQ, hN, hC, hNpos, _hNodd⟩ := source_geometry hk
  change 2 ≤ Q k at hQ
  change N k = 4 * Q k - 1 at hN
  change C k = 2 * Q k - 1 at hC
  change 0 < N k at hNpos
  have geo := native_geometry hk t p hnlarge hexpand
  have hex : N k < 3 * s k t p := by
    simpa only [abs_of_pos hpositive] using hexpand
  have hbudget : 2 * s k t p ≤ 3 * Q k - 1 := by
    have hb := geo.budget
    rw [abs_of_pos hpositive] at hb
    omega
  have hkfour : 4 ≤ k := by
    by_contra h
    have hkthree : k = 3 := by omega
    subst k
    norm_num [N, modulus, Q, quarter] at hbudget hex
    omega
  have hQfour : 4 ≤ Q k := by
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
      (show 2 ≤ k - 2 by omega)
    calc
      4 = (2 : ℤ) ^ 2 := by norm_num
      _ ≤ Q k := by simpa only [Q, quarter] using hp
  intro i hi
  let w : ℕ → ℤ := fun j => s k t (phase (by omega) i j)
  have hwzero : w 0 = Q k - 1 := by simpa only [w, phase_zero] using hi
  have hstep (j : ℕ) : w (j + 1) = doubleStep (N k) (w j) := by
    exact phase_step hk t i j
  have hwone : w 1 = 2 * Q k - 2 := by
    have hs := hstep 0
    rw [Nat.zero_add, hwzero, doubleStep, if_neg (by omega), if_neg (by omega)] at hs
    omega
  have hwtwo : w 2 = -3 := by
    have hs := hstep 1
    norm_num at hs
    rw [hwone, doubleStep, if_pos (by omega)] at hs
    omega
  have htail : ∀ m : ℕ, m + 2 < k → w (m + 2) = -3 * (2 : ℤ) ^ m := by
    intro m
    induction m with
    | zero =>
        intro _
        simpa only [Nat.zero_add, pow_zero, mul_one] using hwtwo
    | succ m ih =>
        intro hm
        have hmold : m + 2 < k := by omega
        have hiold := ih hmold
        have hpowfour : 4 * (2 : ℤ) ^ m ≤ Q k := by
          have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
            (show m + 2 ≤ k - 2 by omega)
          have hpform : (2 : ℤ) ^ (m + 2) = 4 * (2 : ℤ) ^ m := by
            rw [pow_add]
            ring
          rw [hpform] at hp
          simpa only [Q, quarter] using hp
        have hpowpos : 0 < (2 : ℤ) ^ m := pow_pos (by norm_num) _
        rw [show m.succ + 2 = (m + 2) + 1 by omega, hstep, hiold,
          doubleStep, if_neg (by nlinarith), if_neg (by nlinarith), pow_succ]
        ring
  -- The phase covers every physical label in fewer than k steps, even
  -- when the numerical source has a shorter period.
  obtain ⟨j, hj, hjp⟩ : ∃ j : ℕ, j < k ∧ phase (by omega) i j = p := by
    by_cases hip : i.val ≤ p.val
    · refine ⟨p.val - i.val, by omega, ?_⟩
      apply Fin.ext
      change (i.val + (p.val - i.val)) % k = p.val
      have he : i.val + (p.val - i.val) = p.val := by omega
      rw [he, Nat.mod_eq_of_lt p.isLt]
    · refine ⟨k + p.val - i.val, by omega, ?_⟩
      apply Fin.ext
      change (i.val + (k + p.val - i.val)) % k = p.val
      have he : i.val + (k + p.val - i.val) = k + p.val := by omega
      rw [he]
      simp only [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_eq_of_lt p.isLt]
  have hwp : w j = s k t p := by
    dsimp only [w]
    rw [hjp]
  by_cases hjzero : j = 0
  · subst j
    rw [hwzero] at hwp
    omega
  by_cases hjone : j = 1
  · subst j
    rw [hwone] at hwp
    omega
  have hjtwo : 2 ≤ j := by omega
  have hjform : j = (j - 2) + 2 := by omega
  have hneg := htail (j - 2) (by omega)
  rw [← hjform, hwp] at hneg
  have hpowpos : 0 < (2 : ℤ) ^ (j - 2) := pow_pos (by norm_num) _
  nlinarith

/-- The positive-coordinate construction allows an arbitrary initial height.
For negative native orientation that height is C, while the ACTUAL word still starts at zero. -/
private theorem positive_construction {α : Type*} (f : α → ℤ) (cap q h0 : ℤ)
    (p n x z1 z2 : α) (A T0 T1 T2 : List α) (P D r Z1 Z2 : ℤ)
    (hW : InStrip f cap h0 (A ++ [x] ++ T0 ++ [z1] ++ T1 ++ [z2] ++ T2))
    (hp : f p = P) (hn : f n = -D) (hx : f x = r)
    (hz1 : f z1 = -Z1) (hz2 : f z2 = -Z2)
    (hpos : 0 < D) (horder : D < P ∧ P < r) (hr : r = 2 * P - D)
    (hbudget : 2 * P ≤ cap + q) (hZ1 : q ≤ Z1 ∧ Z1 ≤ cap)
    (hZ2 : q ≤ Z2 ∧ Z2 ≤ cap)
    (hsmall : ∀ a ∈ T0 ++ T1 ++ T2, |f a| < q)
    (hC : cap = 2 * q - 1)
    (hblock : cap - P < h0 + mass f (A ++ [x] ++ T0 ++ [z1] ++ T1 ++ [z2] ++ T2) ∧
      h0 + mass f (A ++ [x] ++ T0 ++ [z1] ++ T1 ++ [z2] ++ T2) < D) :
    ∃ L E : List α, L.Perm (T0 ++ T1) ∧ E.Perm T2 ∧
      InStrip f cap h0
        (if P ≤ Z1 then (A ++ [x] ++ T0 ++ [z1]) ++ [p,n]
         else if h0 + mass f (A ++ [x] ++ T0 ++ [z1] ++ T1) < P then
           (A ++ [x] ++ T0 ++ [z1] ++ T1 ++ [z2]) ++ [p]
         else A ++ [p,n] ++ L ++ [z1] ++ E) := by
  classical
  let F := A ++ [x] ++ T0 ++ [z1]
  let B := F ++ T1
  have hsplit1 := strip_split F (T1 ++ [z2] ++ T2) (by simpa [F, List.append_assoc] using hW)
  have hsplit2 := strip_split (B ++ [z2]) T2 (by simpa [B, F, List.append_assoc] using hW)
  have hsplitB := strip_split B ([z2] ++ T2) (by simpa [B, F, List.append_assoc] using hW)
  have hsplitA := strip_split A ([x] ++ T0 ++ [z1] ++ T1 ++ [z2] ++ T2)
    (by simpa [List.append_assoc] using hW)
  have ha := inStrip_prefix hsplitA.2 0
  have hay := inStrip_prefix hsplitA.2 1
  have hv := inStrip_prefix hsplitB.2 0
  have hw2 := inStrip_prefix hsplitB.2 1
  simp only [List.take_zero, List.take_succ_cons, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, mass, hx, hz2] at ha hay hv hw2
  by_cases hA : P ≤ Z1
  · refine ⟨T0 ++ T1, T2, .refl _, .refl _, ?_⟩
    simp only [if_pos hA]
    have hbefore := strip_split (A ++ [x] ++ T0) ([z1] ++ T1 ++ [z2] ++ T2)
      (by simpa [List.append_assoc] using hW)
    have hw1 := inStrip_prefix hbefore.2 1
    have hu1 := inStrip_prefix hbefore.2 0
    simp only [List.take_zero, List.take_succ_cons, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, hz1] at hw1 hu1
    have heq : h0 + mass f F = h0 + mass f (A ++ [x] ++ T0) - Z1 := by
      simp [F, mass, hz1]; ring
    apply inStrip_append hsplit1.1
    change 0 ≤ h0 + mass f F ∧ h0 + mass f F ≤ cap ∧
      0 ≤ h0 + mass f F + f p ∧ h0 + mass f F + f p ≤ cap ∧
      0 ≤ h0 + mass f F + f p + f n ∧ h0 + mass f F + f p + f n ≤ cap
    rw [hp, hn]
    exact ⟨by ((try dsimp only [F, B] at *); source_arith), by ((try dsimp only [F, B] at *); source_arith), by ((try dsimp only [F, B] at *); source_arith), by ((try dsimp only [F, B] at *); source_arith), by ((try dsimp only [F, B] at *); source_arith), by ((try dsimp only [F, B] at *); source_arith)⟩
  · by_cases hB : h0 + mass f B < P
    · refine ⟨T0 ++ T1, T2, .refl _, .refl _, ?_⟩
      simp only [if_neg hA, if_pos (show h0 + mass f (A ++ [x] ++ T0 ++ [z1] ++ T1) < P from hB)]
      apply inStrip_append hsplit2.1
      have heq : h0 + mass f (B ++ [z2]) = h0 + mass f B - Z2 := by simp [mass, hz2]; ring
      change 0 ≤ h0 + mass f (B ++ [z2]) ∧ h0 + mass f (B ++ [z2]) ≤ cap ∧
        0 ≤ h0 + mass f (B ++ [z2]) + f p ∧ h0 + mass f (B ++ [z2]) + f p ≤ cap
      rw [hp]
      exact ⟨by ((try dsimp only [F, B] at *); source_arith), by ((try dsimp only [F, B] at *); source_arith), by ((try dsimp only [F, B] at *); source_arith), by ((try dsimp only [F, B] at *); source_arith)⟩
    · let b := h0 + mass f A + P - D
      let v := h0 + mass f B
      let bridge := b + mass f (T0 ++ T1)
      let e := h0 + mass f (A ++ [x] ++ T0 ++ [z1] ++ T1 ++ [z2] ++ T2) + Z2 - P
      have hb : 0 ≤ b ∧ b ≤ cap := by dsimp [b]; ((try dsimp only [F, B] at *); source_arith)
      have hbridgeEq : bridge = v + Z1 - P := by
        dsimp [bridge, b, v, B, F]
        simp only [mass, List.map_append, List.map_cons, List.map_nil,
          List.sum_append, List.sum_cons, List.sum_nil, add_zero, hx, hz1]
        ((try dsimp only [F, B] at *); source_arith)
      have hbridge : 0 ≤ bridge ∧ bridge ≤ cap := by dsimp [v, B] at *; ((try dsimp only [F, B] at *); source_arith)
      have hafter : 0 ≤ bridge - Z1 ∧ bridge - Z1 ≤ cap := by dsimp [v, B] at *; ((try dsimp only [F, B] at *); source_arith)
      have he : 0 ≤ e ∧ e ≤ cap := by dsimp [e]; ((try dsimp only [F, B] at *); source_arith)
      have heq : e = bridge - Z1 + mass f T2 := by
        dsimp [e, bridge, b]
        simp only [mass, List.map_append, List.map_cons, List.map_nil,
          List.sum_append, List.sum_cons, List.sum_nil, add_zero, hx, hz1, hz2]
        ((try dsimp only [F, B] at *); source_arith)
      have hcompat (T : List α) (hT : ∀ a ∈ T, |f a| < q) :
          ∀ a ∈ T, ∀ d ∈ T, 0 < f a → f d < 0 → f a - f d ≤ cap := by
        intro a ha d hd hap hdn
        have haa := hT a ha
        have hdd := hT d hd
        rw [abs_of_pos hap] at haa
        rw [abs_of_neg hdn] at hdd
        ((try dsimp only [F, B] at *); source_arith)
      obtain ⟨L, hL, hLs⟩ := exists_order_between f (T0 ++ T1) cap b hb hbridge
        (hcompat _ (by intro a ha; exact hsmall a (List.mem_append_left T2 ha)))
      obtain ⟨E, hE, hEs⟩ := exists_order_between f T2 cap (bridge - Z1) hafter
        (by simpa only [heq, mass] using he)
        (hcompat _ (by intro a ha; apply hsmall a; simp [ha]))
      refine ⟨L, E, hL, hE, ?_⟩
      simp only [if_neg hA, if_neg (show ¬ h0 + mass f (A ++ [x] ++ T0 ++ [z1] ++ T1) < P from hB)]
      have hPN : InStrip f cap (h0 + mass f A) [p,n] := by
        change 0 ≤ h0 + mass f A ∧ h0 + mass f A ≤ cap ∧
          0 ≤ h0 + mass f A + f p ∧ h0 + mass f A + f p ≤ cap ∧
          0 ≤ h0 + mass f A + f p + f n ∧ h0 + mass f A + f p + f n ≤ cap
        rw [hp, hn]
        exact ⟨by ((try dsimp only [F, B] at *); source_arith), by ((try dsimp only [F, B] at *); source_arith), by ((try dsimp only [F, B] at *); source_arith), by ((try dsimp only [F, B] at *); source_arith), by ((try dsimp only [F, B] at *); source_arith), by ((try dsimp only [F, B] at *); source_arith)⟩
      have hAL := inStrip_append hsplitA.1 hPN
      have hAL' : InStrip f cap h0 (A ++ [p,n] ++ L) := by
        apply inStrip_append hAL
        simpa [b, mass, hp, hn, sub_eq_add_neg, add_assoc] using hLs
      have hLm := (hL.map f).sum_eq
      simp only [List.map_append, List.sum_append] at hLm
      have hbeforeZ : h0 + mass f (A ++ [p,n] ++ L) = bridge := by
        dsimp [bridge, b]
        simp only [mass, List.map_append, List.map_cons, List.map_nil,
          List.sum_append, List.sum_cons, List.sum_nil, add_zero, hp, hn]
        ((try dsimp only [F, B] at *); source_arith)
      have htail : InStrip f cap (h0 + mass f (A ++ [p,n] ++ L)) ([z1] ++ E) := by
        rw [hbeforeZ]
        change 0 ≤ bridge ∧ bridge ≤ cap ∧ InStrip f cap (bridge + f z1) E
        exact ⟨hbridge.1, hbridge.2, by simpa [hz1, sub_eq_add_neg] using hEs⟩
      simpa only [List.append_assoc] using inStrip_append hAL' htail

/-- Exact branch accounting uses addition in Nat, without truncated subtraction. -/
def BranchAccounting {k : ℕ} (t : ℕ) (p z1 z2 : Fin k)
    (A T0 T1 T2 V : List (Fin k)) : Prop :=
  let W := W2 p z1 z2 A T0 T1 T2
  if |s k t p| ≤ |s k t z1| then
    G k t V + 1 = G k t W ∧ U V + 1 = U W + T1.length + T2.length ∧
    H k t V + 3 ^ (s k t z2).natAbs = H k t W + 3 ^ (s k t p).natAbs + 3 ^ (s k t (hit k 1 p)).natAbs
  else if departure t p z1 A T0 T1 < |s k t p| then
    G k t V + 1 = G k t W ∧ U V + 1 = U W + T2.length ∧ H k t V = H k t W + 3 ^ (s k t p).natAbs
  else G k t V = G k t W ∧ U V = U W ∧
    H k t V + 3 ^ (s k t (hit k 2 p)).natAbs + 3 ^ (s k t z2).natAbs =
      H k t W + 3 ^ (s k t p).natAbs + 3 ^ (s k t (hit k 1 p)).natAbs

@[simp] theorem largeUsed_append {k : ℕ} (t : ℕ) (A B : List (Fin k)) :
    largeUsed k t (A ++ B) = largeUsed k t A + largeUsed k t B := by simp [largeUsed, mass]
@[simp] theorem energy_append {k : ℕ} (t : ℕ) (A B : List (Fin k)) :
    H k t (A ++ B) = H k t A + H k t B := by simp [H, mass]
@[simp] theorem largeUsed_nil (k t : ℕ) : largeUsed k t ([] : List (Fin k)) = 0 := rfl
@[simp] theorem energy_nil (k t : ℕ) : H k t ([] : List (Fin k)) = 0 := rfl
@[simp] theorem largeUsed_cons {k : ℕ} (t : ℕ) (q : Fin k) (A : List (Fin k)) :
    largeUsed k t (q :: A) = largeWeight k t q + largeUsed k t A := rfl
@[simp] theorem energy_cons {k : ℕ} (t : ℕ) (q : Fin k) (A : List (Fin k)) :
    H k t (q :: A) = energyWeight k t q + H k t A := rfl

private theorem oriented_opposite (a b : ℤ) (hh : a * b < 0) :
    orient (decide (a < 0)) b = -|b| := by
  rcases mul_neg_iff.mp hh with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simp [orient, show ¬ a < 0 by source_arith, abs_of_neg hb]
  · simp [orient, ha, abs_of_pos hb]

/-- The strengthened native result includes exact inventory and every natural take.
No scalar source profile, gate, support set, endpoint, or global minimum is a premise. -/
theorem actualSource_twoOpposite_twoStep_full
    (k t : ℕ) (hk : 3 ≤ k)
    (p z1 z2 : Fin k) (A T0 T1 T2 : List (Fin k))
    (hW : Legal k t (W2 p z1 z2 A T0 T1 T2))
    (hunused : ∀ j < 2, hit k j p ∉ W2 p z1 z2 A T0 T1 T2)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hopposite : ∀ z ∈ [z1,z2], Q k ≤ |s k t z| ∧ s k t p * s k t z < 0)
    (hsmall : ∀ q ∈ T0 ++ T1 ++ T2, |s k t q| < Q k)
    (hblocked : ∀ j < 2, ¬ Legal k t ((W2 p z1 z2 A T0 T1 T2) ++ [hit k j p])) :
    ∃ L E : List (Fin k), L.Perm (T0 ++ T1) ∧ E.Perm T2 ∧
      (let W := W2 p z1 z2 A T0 T1 T2
       let V := V2 t p z1 z2 A T0 T1 T2 L E
       Legal k t V ∧ InStrip (s k t) (C k) 0 V ∧
       Inventory k t W V (inserted t p z1 A T0 T1) (returned t p z1 z2 A T0 T1 T2) ∧
       BranchAccounting t p z1 z2 A T0 T1 T2 V ∧
       (G k t V < G k t W ∨ (G k t V = G k t W ∧ H k t V < H k t W)) ∧
       J k t V < J k t W) := by
  classical
  let W := W2 p z1 z2 A T0 T1 T2
  let n := hit k 1 p
  let x := hit k 2 p
  let neg : Bool := decide (s k t p < 0)
  let g : Fin k → ℤ := fun q => orient neg (s k t q)
  let h0 := coord neg (C k) 0
  have geo := native_geometry hk t p hnlarge hexpand
  obtain ⟨hQ, hN, hC, hN0, hodd⟩ := source_geometry hk
  have hbound (q : Fin k) : |s k t q| ≤ C k := abs_le.mpr (centered_bounds hN0 hodd _)
  obtain ⟨hz1L, hz1op⟩ := hopposite z1 (by simp)
  obtain ⟨hz2L, hz2op⟩ := hopposite z2 (by simp)
  change Large k t z1 at hz1L
  change Large k t z2 at hz2L
  have hp0 : 0 < |s k t p| := by have hh := geo.pLarge; unfold Large at hh; ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith)
  have hgp : g p = |s k t p| := orient_choose _
  have hgn : g n = -|s k t n| := geo.nValue
  have hgx : g x = |s k t x| := geo.xValue
  have hgz1 : g z1 = -|s k t z1| := oriented_opposite _ _ hz1op
  have hgz2 : g z2 = -|s k t z2| := oriented_opposite _ _ hz2op
  have hcoord (B : List (Fin k)) : h0 + mass g B =
      if 0 < s k t p then mass (s k t) B else C k - mass (s k t) B := by
    have he := coord_mass neg (C k) 0 (s k t) B
    by_cases hn : s k t p < 0
    · have hp : ¬ 0 < s k t p := by ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith)
      simpa [h0, g, neg, coord, hn, hp] using he.symm
    · have hp : 0 < s k t p := by have hab := hp0; rw [abs_of_nonneg (by ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith))] at hab; ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith)
      simpa [h0, g, neg, coord, hn, hp] using he.symm
  have hstrip : InStrip g (C k) h0 W :=
    (strip_coordinate neg).mp (strip_of_legal hW)
  have huP : p ∉ W := by simpa [W, hit] using hunused 0 (by ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith))
  have huN : n ∉ W := hunused 1 (by ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith))
  have hpn : p ≠ n := by
    intro he
    have hdpos : 0 < |s k t n| := by dsimp [n]; ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith)
    rw [he] at hgp
    ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith)
  have hblockedGate (u : Fin k) (hu : u ∉ W) (huB : ¬ Legal k t (W ++ [u])) :
      ¬ (0 ≤ h0 + mass g W + g u ∧ h0 + mass g W + g u ≤ C k) := by
    intro hgate
    have hh : 0 ≤ h0 + mass g W ∧ h0 + mass g W ≤ C k := by
      simpa [mass] using inStrip_prefix hstrip W.length
    have hglegal : InStrip g (C k) h0 (W ++ [u]) :=
      inStrip_append hstrip ⟨hh.1, hh.2, hgate⟩
    have hflegal : InStrip (s k t) (C k) 0 (W ++ [u]) := (strip_coordinate neg).mpr hglegal
    have hnod : (W ++ [u]).Nodup := hW.1.append (by simp) (List.disjoint_left.mpr (by
      intro q hq hqu; have he : q = u := List.mem_singleton.mp hqu; subst q; exact hu hq))
    exact huB (legal_of_strip hnod hflegal)
  have hbp := hblockedGate p huP (by simpa [W, hit] using hblocked 0 (by ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith)))
  have hbn := hblockedGate n huN (hblocked 1 (by ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith)))
  have hh : 0 ≤ h0 + mass g W ∧ h0 + mass g W ≤ C k := by
    simpa [mass] using inStrip_prefix hstrip W.length
  have hblocks : C k - |s k t p| < h0 + mass g W ∧ h0 + mass g W < |s k t n| := by
    rw [hgp] at hbp
    rw [hgn] at hbn
    have hDpos : 0 < |s k t n| := by dsimp [n]; ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith)
    constructor <;> ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith)
  have hr : |s k t x| = 2 * |s k t p| - |s k t n| := by
    have hn := geo.firstEquation
    have hx := geo.secondEquation
    dsimp [n, x]; ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith)
  have hsmallg : ∀ q ∈ T0 ++ T1 ++ T2, |g q| < Q k := by
    intro q hq
    simpa [g] using hsmall q hq
  obtain ⟨L, E, hL, hE, hnew⟩ := positive_construction g (C k) (Q k) h0 p n x z1 z2
    A T0 T1 T2 |s k t p| |s k t n| |s k t x| |s k t z1| |s k t z2|
    (by simpa [W, W2, x] using hstrip) hgp hgn hgx hgz1 hgz2
    (by dsimp [n]; ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith)) geo.strictOrder hr geo.budget
    ⟨hz1L, hbound z1⟩ ⟨hz2L, hbound z2⟩ hsmallg hC (by simpa [W, W2, x] using hblocks)
  let V := V2 t p z1 z2 A T0 T1 T2 L E
  let I := inserted t p z1 A T0 T1
  let R := returned t p z1 z2 A T0 T1 T2
  have hdep : departure t p z1 A T0 T1 =
      h0 + mass g (A ++ [x] ++ T0 ++ [z1] ++ T1) := by
    simpa [departure, F1, x] using (hcoord (F1 p z1 A T0 ++ T1)).symm
  have hVg : InStrip g (C k) h0 V := by
    simpa only [V, V2, F1, hdep, x, n] using hnew
  have hVstrip : InStrip (s k t) (C k) 0 V := (strip_coordinate neg).mpr hVg
  have hI : I.Nodup := by
    dsimp [I, inserted]
    split_ifs <;> simp [show p ≠ hit k 1 p from hpn]
  have hIW' : ∀ q ∈ I, q ∉ W := by
    intro q hq
    by_cases ha : |s k t p| ≤ |s k t z1|
    · simp only [I, inserted, if_pos ha, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact huP
      · exact huN
    · by_cases hb : departure t p z1 A T0 T1 < |s k t p|
      · have he : q = p := by simpa [I, inserted, ha, hb] using hq
        simpa [he] using huP
      · simp only [I, inserted, if_neg ha, if_neg hb, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact huP
        · exact huN
  have hIL : ∀ q ∈ I, Large k t q := by
    intro q hq
    by_cases ha : |s k t p| ≤ |s k t z1|
    · simp only [I, inserted, if_pos ha, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact geo.pLarge
      · exact geo.nLarge
    · by_cases hb : departure t p z1 A T0 T1 < |s k t p|
      · have he : q = p := by simpa [I, inserted, ha, hb] using hq
        simpa [he] using geo.pLarge
      · simp only [I, inserted, if_neg ha, if_neg hb, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact geo.pLarge
        · exact geo.nLarge
  have hRW : ∀ q ∈ R, q ∈ W := by
    intro q hq
    simp only [W, W2, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc]
    by_cases ha : |s k t p| ≤ |s k t z1|
    · simp only [R, returned, if_pos ha, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, or_assoc] at hq
      rcases hq with hq | rfl | hq
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hq))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hq)))))
    · by_cases hb : departure t p z1 A T0 T1 < |s k t p|
      · have hq' : q ∈ T2 := by simpa only [R, returned, if_neg ha, if_pos hb] using hq
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hq')))))
      · simp only [R, returned, if_neg ha, if_neg hb, List.mem_cons,
          List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hperm : (V ++ R).Perm (W ++ I) := by
    apply List.perm_iff_count.mpr
    intro q
    have hl := hL.count_eq q
    have he := hE.count_eq q
    simp only [List.count_append] at hl
    dsimp [V, R, W, I, V2, returned, inserted, W2, F1]
    split_ifs <;> simp only [List.count_append, List.count_cons, List.count_nil] at * <;> ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith)
  have inv := inventory_of_perm hk t W V I R hW.1 hI hIW' hRW hIL hperm
  have hs1 := small_weights t T1 (by intro q hq; apply hsmall q; simp [hq])
  have hs2 := small_weights t T2 (by intro q hq; apply hsmall q; simp [hq])
  have accounting : BranchAccounting t p z1 z2 A T0 T1 T2 V := by
    have hg := inv.largeBalance
    have he := inv.energyBalance
    have hu := inv.countBalance
    dsimp only [W] at hg he hu
    unfold BranchAccounting
    dsimp only
    by_cases ha : |s k t p| ≤ |s k t z1|
    · simp only [if_pos ha]
      simp [I, R, inserted, returned, ha, largeWeight, energyWeight,
        geo.pLarge, geo.nLarge, hz2L, hs1.1, hs1.2, hs2.1, hs2.2] at hg he hu
      exact ⟨by ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith), by ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith), by ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith)⟩
    · simp only [if_neg ha]
      by_cases hb : departure t p z1 A T0 T1 < |s k t p|
      · simp only [if_pos hb]
        simp [I, R, inserted, returned, ha, hb, largeWeight, energyWeight,
          geo.pLarge, hs2.1, hs2.2] at hg he hu
        exact ⟨by ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith), by ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith), by ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith)⟩
      · simp only [if_neg hb]
        simp [I, R, inserted, returned, ha, hb, largeWeight, energyWeight,
          geo.pLarge, geo.nLarge, geo.xLarge, hz2L] at hg he hu
        exact ⟨by ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith), by ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith), by ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith)⟩
  have descent : G k t V < G k t W ∨ (G k t V = G k t W ∧ H k t V < H k t W) := by
    have ha := accounting
    dsimp only [W]
    unfold BranchAccounting at ha
    dsimp only at ha
    split_ifs at ha
    · exact Or.inl (by ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith))
    · exact Or.inl (by ((try dsimp only [g, h0, neg, n, x, W] at *); source_arith))
    · refine Or.inr ⟨ha.1, ?_⟩
      have he := ha.2.2
      have hle := Nat.le_add_right (H k t V + 3 ^ (s k t (hit k 2 p)).natAbs)
        (3 ^ (s k t z2).natAbs)
      rw [he] at hle
      have hlt := (Nat.add_lt_add_left geo.energy (H k t V)).trans_le
        (by simpa only [Nat.add_assoc] using hle)
      exact (Nat.add_lt_add_iff_right).mp hlt
  have hJ : J k t V < J k t W := by
    apply Prod.Lex.toLex_lt_toLex.mpr
    rcases descent with hg | ⟨hg, he⟩
    · exact Or.inl hg
    · exact Or.inr ⟨hg, Prod.Lex.toLex_lt_toLex.mpr (Or.inl he)⟩
  exact ⟨L, E, hL, hE, legal_of_strip inv.nodup hVstrip, hVstrip, inv, accounting, descent, hJ⟩


end D5.S3.Combinatorics.Circle.TwoOppositeLargeExchange
