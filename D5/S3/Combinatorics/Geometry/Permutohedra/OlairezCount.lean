/- GID: D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/Permutohedra/OlairezCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount.latticePointCount_terminalSum; instance=D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount.fourOneInput
   digest: Count lattice points of the dihedral orbit hull by a prefix recurrence. -/
import D5.S3.Combinatorics.Geometry.Permutohedra.OlairezWrapHull
import Mathlib.Algebra.Order.Floor.Ring

/-!
The integral cyclic difference sends points of the source orbit hull to a dilation-dependent
affine coset. Each feasible difference has a unique least feasible translate. A prefix
recurrence counts the translated vectors by their sum, weighted residue, absolute sum
and number of positive entries.
-/

namespace OlairezCount

open Finset OlairezQ62 OlairezWrapHull
open scoped BigOperators Pointwise

/-- Integer coordinates in the real dilation of the literal source hull. -/
abbrev SourcePoints (n k : ℕ) :=
  {x : ZMod n → ℤ // (fun i => (x i : ℝ)) ∈ (k : ℝ) • OlairezQ62.Q n}

abbrev ZVector (n : ℕ) := ZMod n → ℤ

def sourceSum (n : ℕ) : ℤ := ((n * (n + 1) / 2 : ℕ) : ℤ)
def weightSum (n : ℕ) : ℤ := ((n * (n - 1) / 2 : ℕ) : ℤ)

def forward {n : ℕ} (x : ZVector n) : ZVector n := fun i => x (i + 1) - x i

def weight {n : ℕ} [NeZero n] (x : ZVector n) : ℤ := ∑ i, (i.val : ℤ) * x i

private theorem sum_forward {n : ℕ} [NeZero n] (x : ZVector n) : ∑ i, forward x i = 0 := by
  exact (Equiv.sum_comp (shift (1 : ZMod n)) (fun i => x i - x (i - 1))).trans
    (D5.S3.Arith.Primes.CyclicDifferencePrimeContent.sum_diff x) |> fun h => by
      simpa only [show ∀ i : ZMod n, shift 1 i = i + 1 by intro i; rfl,
        add_sub_cancel_right, forward] using h

private theorem val_sum {n : ℕ} [NeZero n] : ∑ i : ZMod n, (i.val : ℤ) = weightSum n := by
  rw [← Nat.cast_sum]
  congr 1
  change (∑ i : ZMod n, i.val) = n * (n - 1) / 2
  rw [← Equiv.sum_comp (ZMod.finEquiv n).toEquiv (fun i : ZMod n => i.val)]
  have h (i : Fin n) : (ZMod.finEquiv n i).val = i.val := by
    cases n with
    | zero => exact (Nat.not_lt_zero _ i.isLt).elim
    | succ n => rfl
  have he : (∑ j : Fin n, ((ZMod.finEquiv n).toEquiv j).val) = ∑ j : Fin n, j.val :=
    sum_congr rfl fun j _ => h j
  rw [he, Fin.sum_univ_eq_sum_range (fun i : ℕ => i), Finset.sum_range_id]

private theorem sourceSum_twice (n : ℕ) : 2 * sourceSum n = (n : ℤ) * (n + 1) := by
  have h := Finset.sum_range_id_mul_two (n + 1)
  rw [Finset.sum_range_id, Nat.add_sub_cancel] at h
  unfold sourceSum
  have hc : ((n * (n + 1) / 2 : ℕ) : ℤ) * 2 = (n + 1 : ℤ) * n := by
    exact_mod_cast (show n * (n + 1) / 2 * 2 = (n + 1) * n by simpa [Nat.mul_comm] using h)
  linarith

private theorem val_previous {n : ℕ} [NeZero n] (hn : 3 ≤ n) (i : ZMod n) :
    ((i - 1).val : ℤ) = (i.val : ℤ) - 1 + if i = 0 then (n : ℤ) else 0 := by
  by_cases hi : i = 0
  · subst i
    have hlt : n - 1 < n := by omega
    have hcast : (((n - 1 : ℕ) : ℕ) : ZMod n) = 0 - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self, Nat.cast_one]
    rw [← hcast, ZMod.val_natCast_of_lt hlt, ZMod.val_zero]
    simp
    omega
  · have hp := (ZMod.val_pos (a := i)).mpr hi
    have hlt := ZMod.val_lt i
    have hcast : ((i.val - 1 : ℕ) : ZMod n) = i - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ i.val), Nat.cast_one, ZMod.natCast_zmod_val]
    rw [← hcast, ZMod.val_natCast_of_lt (by omega : i.val - 1 < n)]
    simp [hi]

private theorem weight_forward {n : ℕ} [NeZero n] (hn : 3 ≤ n) (x : ZVector n) :
    weight (forward x) = (n : ℤ) * x 0 - ∑ i, x i := by
  have hr := Equiv.sum_comp (shift (1 : ZMod n)) (fun i => ((i - 1).val : ℤ) * x i)
  change (∑ i, (((i + 1 - 1 : ZMod n).val : ℤ) * x (i + 1))) =
    ∑ i, ((i - 1).val : ℤ) * x i at hr
  simp only [add_sub_cancel_right] at hr
  simp only [weight, forward, mul_sub, sum_sub_distrib, hr, val_previous hn, add_mul,
    sub_mul, sum_add_distrib, one_mul, ite_mul, zero_mul, sum_ite_eq',
    mem_univ, ite_true]
  ring

def prefixSum {n : ℕ} (d : ZVector n) (i : ZMod n) : ℤ :=
  ∑ j ∈ range i.val, d (j : ZMod n)

private theorem prefix_forward {n : ℕ} [NeZero n] (hn : 3 ≤ n) (d : ZVector n)
    (hd : ∑ i, d i = 0) : forward (prefixSum d) = d := by
  funext i
  have hcast : ((i.val : ℕ) : ZMod n) = i := ZMod.natCast_zmod_val i
  have hi := ZMod.val_lt i
  have hnext : i + 1 = ((i.val + 1 : ℕ) : ZMod n) := by
    rw [Nat.cast_add, hcast, Nat.cast_one]
  by_cases hlt : i.val + 1 < n
  · simp only [forward, prefixSum, hnext, ZMod.val_natCast_of_lt hlt, sum_range_succ, hcast]
    abel
  · have hlast : i.val + 1 = n := by omega
    have hsum : ∑ j ∈ range n, d (j : ZMod n) = 0 := by
      rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => d (j : ZMod n))]
      have he (j : Fin n) : ZMod.finEquiv n j = (j.val : ZMod n) := by
        cases n with
        | zero => exact (Nat.not_lt_zero _ j.isLt).elim
        | succ n => exact (Fin.natCast_eq_mk j.isLt).symm
      have h := (Equiv.sum_comp (ZMod.finEquiv n).toEquiv d).trans hd
      change (∑ j : Fin n, d (ZMod.finEquiv n j)) = 0 at h
      simpa only [he] using h
    have hsum' : ∑ j ∈ range (i.val + 1), d (j : ZMod n) = 0 := by
      simpa only [hlast] using hsum
    rw [sum_range_succ, hcast] at hsum'
    simp only [forward, prefixSum, hnext, hlast, ZMod.natCast_self, ZMod.val_zero, range_zero,
      sum_empty, zero_sub]
    linarith only [hsum']

private theorem residue_even {n k m : ℕ} [NeZero n] (hn : n = 2 * m) :
    ((-((k : ℤ) * sourceSum n) : ℤ) : ZMod n) = (k : ZMod n) * (m : ZMod n) := by
  have hc : (n : ℤ) = 2 * (m : ℤ) := by exact_mod_cast hn
  have hs := sourceSum_twice n
  have he : sourceSum n = (m : ℤ) * ((n : ℤ) + 1) := by nlinarith
  have hm : (-(m : ZMod n)) = (m : ZMod n) := by
    have hz := congrArg (fun j : ℕ => (j : ZMod n)) hn
    simp only [ZMod.natCast_self, two_mul, Nat.cast_add] at hz
    exact neg_eq_iff_add_eq_zero.mpr hz.symm
  calc
    _ = -((k : ZMod n) * (m : ZMod n)) := by simp [he]
    _ = (k : ZMod n) * (m : ZMod n) := by rw [← mul_neg, hm]

private theorem residue_odd {n k m : ℕ} [NeZero n] (hn : n = 2 * m + 1) :
    ((-((k : ℤ) * sourceSum n) : ℤ) : ZMod n) = 0 := by
  have hc : (n : ℤ) = 2 * (m : ℤ) + 1 := by exact_mod_cast hn
  have hs := sourceSum_twice n
  have he : sourceSum n = (n : ℤ) * ((m : ℤ) + 1) := by nlinarith
  simp [he]

private theorem residue_even_even {n m j : ℕ} [NeZero n] (hn : n = 2 * m) :
    ((-(((2 * j : ℕ) : ℤ) * sourceSum n) : ℤ) : ZMod n) = 0 := by
  rw [residue_even hn]
  have hz : (2 : ZMod n) * m = 0 := by
    exact_mod_cast (show ((2 * m : ℕ) : ZMod n) = 0 by rw [← hn, ZMod.natCast_self])
  push_cast
  calc
    (2 * (j : ZMod n)) * m = j * (2 * (m : ZMod n)) := by ring
    _ = 0 := by rw [hz, mul_zero]

private theorem residue_even_odd {n m j : ℕ} [NeZero n] (hn : n = 2 * m) :
    ((-(((2 * j + 1 : ℕ) : ℤ) * sourceSum n) : ℤ) : ZMod n) = (m : ZMod n) := by
  rw [residue_even hn]
  have hz := residue_even_even (j := j) hn
  rw [residue_even hn] at hz
  push_cast at hz ⊢
  rw [add_mul, hz, zero_add, one_mul]

/-- Residue of the affine difference lattice for dilation k. -/
def sourceResidue (n k : ℕ) : ZMod n :=
  if n % 2 = 0 ∧ k % 2 = 1 then (n / 2 : ℕ) else 0

private theorem sourceResidue_eq (n k : ℕ) [NeZero n] :
    sourceResidue n k = ((-((k : ℤ) * sourceSum n) : ℤ) : ZMod n) := by
  by_cases hn : n % 2 = 0
  · have he : n = 2 * (n / 2) := by omega
    by_cases hk : k % 2 = 1
    · have hko : k = 2 * (k / 2) + 1 := by omega
      simp only [sourceResidue, hn, hk, and_self, ite_true]
      rw [hko]
      exact (residue_even_odd he).symm
    · have hke : k = 2 * (k / 2) := by omega
      simp only [sourceResidue, hn, hk, and_false, ite_false]
      rw [hke]
      exact (residue_even_even he).symm
  · have ho : n = 2 * (n / 2) + 1 := by omega
    simp only [sourceResidue, hn, false_and, ite_false]
    exact (residue_odd ho).symm

def Coset (n k : ℕ) [NeZero n] :=
  {d : ZVector n // (∑ i, d i = 0) ∧
    (weight d : ZMod n) = sourceResidue n k}

def Plane (n k : ℕ) [NeZero n] :=
  {x : ZVector n // ∑ i, x i = (k : ℤ) * sourceSum n}

private theorem forward_injective_plane {n k : ℕ} [NeZero n] {x y : Plane n k}
    (h : forward x.val = forward y.val) : x = y := by
  have hs : ∑ i, (x.val i - y.val i) = 0 := by
    rw [sum_sub_distrib, x.property, y.property, sub_self]
  apply Subtype.ext
  funext i
  apply sub_eq_zero.mp
  apply D5.S3.Arith.Primes.CyclicDifferencePrimeContent.diff_injective_sum_zero
    (show (n : ℤ) ≠ 0 by exact_mod_cast NeZero.ne n) (fun j => x.val j - y.val j) hs _ i
  intro j
  have hj := congrFun h (j - 1)
  simp only [forward, sub_add_cancel] at hj
  omega

/-- Integrate the differences and use the affine plane to fix the constant. -/
private def liftVector {n k : ℕ} [NeZero n] (d : Coset n k) : ZVector n :=
  fun i => prefixSum d.val i +
    (((k : ℤ) * sourceSum n - ∑ j, prefixSum d.val j) / (n : ℤ))

private theorem lift_spec {n k : ℕ} [NeZero n] (hn : 3 ≤ n) (d : Coset n k) :
    (∑ i, liftVector d i) = (k : ℤ) * sourceSum n ∧ forward (liftVector d) = d.val := by
  let p := prefixSum d.val
  have hd : forward p = d.val := prefix_forward hn d.val d.property.1
  have hw := weight_forward hn p
  rw [hd] at hw
  have hp : p 0 = 0 := by simp [p, prefixSum]
  rw [hp, mul_zero, zero_sub] at hw
  have hm := d.property.2.trans (sourceResidue_eq n k)
  rw [hw, Int.cast_neg, Int.cast_neg, neg_inj] at hm
  have hz := (ZMod.intCast_eq_intCast_iff_dvd_sub
    (∑ i, p i) ((k : ℤ) * sourceSum n) n).mp hm
  obtain ⟨t, ht⟩ := hz
  have hx (i : ZMod n) : liftVector d i = p i + t := by
    have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
    change p i + (((k : ℤ) * sourceSum n - ∑ j, p j) / (n : ℤ)) = p i + t
    rw [ht, mul_comm, Int.mul_ediv_cancel _ hn0]
  constructor
  · simp only [hx, sum_add_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
    linarith
  · rw [← hd]
    funext i
    simp only [forward, hx]
    ring

/-- Cyclic difference and its integral inverse between the affine plane and coset. -/
def planeEquivCoset {n k : ℕ} [NeZero n] (hn : 3 ≤ n) : Plane n k ≃ Coset n k where
  toFun x := ⟨forward x.val, sum_forward x.val, by
    rw [sourceResidue_eq, weight_forward hn, x.property, Int.cast_sub, Int.cast_mul,
      Int.cast_natCast, ZMod.natCast_self, zero_mul, zero_sub, Int.cast_neg]⟩
  invFun d := ⟨liftVector d, (lift_spec hn d).1⟩
  left_inv x := forward_injective_plane (lift_spec hn _).2
  right_inv d := Subtype.ext (lift_spec hn d).2

section RealHull

noncomputable section

variable {n : ℕ} [NeZero n]

def realVector (x : ZVector n) : Coordinates n := fun i => x i

private theorem source_coordinates (hn : 3 ≤ n) (k : ℕ) (x : Coordinates n) :
    x ∈ (k : ℝ) • OlairezQ62.Q n ↔
      ∃ w : sumZero n, w ∈ (k : ℝ) • centeredQ n ∧ x = w.val + (k : ℝ) • center n := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hamb, _, _, _⟩ := source_coordinate_conjugacy n hn
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y - center n ∈ (fun x : Coordinates n => x - center n) '' Q n := ⟨y, hy, rfl⟩
    rw [← hamb] at hy'
    obtain ⟨w, hw, he⟩ := hy'
    refine ⟨(k : ℝ) • w, ⟨w, hw, rfl⟩, ?_⟩
    change (k : ℝ) • y = (k : ℝ) • w.val + (k : ℝ) • center n
    change w.val = y - center n at he
    rw [← smul_add, he, sub_add_cancel]
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have hw' : w.val ∈ (fun w : sumZero n => w.val) '' centeredQ n := ⟨w, hw, rfl⟩
    rw [hamb] at hw'
    obtain ⟨y, hy, he⟩ := hw'
    refine ⟨y, hy, ?_⟩
    change (k : ℝ) • y = (k : ℝ) • w.val + (k : ℝ) • center n
    change y - center n = w.val at he
    rw [← smul_add, ← he, sub_add_cancel]

private theorem centered_sum (k : ℕ) :
    (∑ i : ZMod n, ((k : ℝ) • center n) i) = ((k : ℤ) * sourceSum n : ℤ) := by
  have hs : (2 : ℝ) * (sourceSum n : ℝ) = (n : ℝ) * ((n : ℝ) + 1) := by
    exact_mod_cast sourceSum_twice n
  simp only [center, Pi.smul_apply, smul_eq_mul, sum_const, card_univ, ZMod.card, nsmul_eq_mul,
    Int.cast_mul, Int.cast_natCast]
  linear_combination (k : ℝ) / 2 * (-hs)

private theorem source_on_plane (hn : 3 ≤ n) {k : ℕ} (x : SourcePoints n k) :
    ∑ i, x.val i = (k : ℤ) * sourceSum n := by
  obtain ⟨w, _, hw⟩ := (source_coordinates hn k (realVector x.val)).mp x.property
  have hs : ∑ i, w.val i = 0 := w.property
  have he := congrArg (fun v : Coordinates n => ∑ i, v i) hw
  change (∑ i, (x.val i : ℝ)) = ∑ i, (w.val i + ((k : ℝ) • center n) i) at he
  rw [sum_add_distrib, hs, zero_add, centered_sum k, ← Int.cast_sum] at he
  exact_mod_cast he

def recenter {k : ℕ} (x : Plane n k) : sumZero n :=
  ⟨realVector x.val - (k : ℝ) • center n, by
    change ∑ i, ((x.val i : ℝ) - ((k : ℝ) • center n) i) = 0
    rw [sum_sub_distrib, centered_sum k, ← Int.cast_sum, x.property, sub_self]⟩

private theorem source_iff_real_translate (hn : 3 ≤ n) {k : ℕ} (x : Plane n k) :
    realVector x.val ∈ (k : ℝ) • OlairezQ62.Q n ↔
      ∃ t : ℝ, absoluteSum (fun i => (forward x.val i : ℝ) + t) ≤ (n : ℝ) * k := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hdelta, _, hhull⟩ := source_coordinate_conjugacy n hn
  have he : realVector x.val ∈ (k : ℝ) • OlairezQ62.Q n ↔ recenter x ∈ (k : ℝ) • centeredQ n := by
    rw [source_coordinates hn]
    constructor
    · rintro ⟨w, hw, he⟩
      have h : recenter x = w := by
        apply Subtype.ext
        change realVector x.val - (k : ℝ) • center n = w.val
        rw [he, add_sub_cancel_right]
      rwa [h]
    · intro hx
      exact ⟨recenter x, hx, by change _ = realVector x.val - _ + _; rw [sub_add_cancel]⟩
  rw [he]
  have himage : delta n '' ((k : ℝ) • centeredQ n) = (k : ℝ) • convexHull ℝ (signedPoints n) := by
    rw [image_smul_setₛₗ, hhull, RingHom.id_apply]
  have hmem : recenter x ∈ (k : ℝ) • centeredQ n ↔
      delta n (recenter x) ∈ (k : ℝ) • convexHull ℝ (signedPoints n) := by
    rw [← himage]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨y, hy, h⟩ => (LinearEquiv.injective _ h) ▸ hy⟩
  rw [hmem, scaled_wrap_hull_iff]
  have hd (i : ZMod n) : (delta n (recenter x)).val i = (forward x.val i : ℝ) := by
    rw [hdelta]
    change ((x.val (i + 1) : ℝ) - (k : ℝ) * (((n : ℝ) + 1) / 2)) -
      ((x.val i : ℝ) - (k : ℝ) * (((n : ℝ) + 1) / 2)) = ((x.val (i + 1) - x.val i : ℤ) : ℝ)
    push_cast
    ring
  simp_rw [hd]

end

end RealHull

section LeastTranslate

variable {n : ℕ} [NeZero n]

def translate (d : ZVector n) (t : ℤ) : ZVector n := fun i => d i + t

def intNorm (z : ZVector n) : ℕ := ∑ i, (z i).natAbs

def positiveCount (z : ZVector n) : ℕ := ∑ i, if 0 < z i then 1 else 0

noncomputable def shiftCost (d : ZVector n) (t : ℝ) : ℝ := absoluteSum (fun i => (d i : ℝ) + t)

private theorem realCost_int (d : ZVector n) (t : ℤ) : shiftCost d t = (intNorm (translate d t) : ℝ) := by
  simp [shiftCost, absoluteSum, intNorm, translate, Nat.cast_sum, Nat.cast_natAbs, Int.cast_abs]

private theorem shiftCost_convex (d : ZVector n) (s t a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    shiftCost d (a * s + b * t) ≤ a * shiftCost d s + b * shiftCost d t := by
  unfold shiftCost absoluteSum
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro i _
  have h : (d i : ℝ) + (a * s + b * t) = a * ((d i : ℝ) + s) + b * ((d i : ℝ) + t) := by
    linear_combination -(d i : ℝ) * hab
  change |(d i : ℝ) + (a * s + b * t)| ≤ a * |(d i : ℝ) + s| + b * |(d i : ℝ) + t|
  rw [h]
  simpa only [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using
    abs_add_le (a * ((d i : ℝ) + s)) (b * ((d i : ℝ) + t))

private theorem shiftCost_floor (d : ZVector n) (u : ℝ) :
    let l : ℤ := ⌊u⌋
    let f : ℝ := u - l
    shiftCost d u = (1 - f) * shiftCost d l + f * shiftCost d ((l : ℝ) + 1) := by
  dsimp only
  let l : ℤ := ⌊u⌋
  let f : ℝ := u - l
  change shiftCost d u = (1 - f) * shiftCost d l + f * shiftCost d ((l : ℝ) + 1)
  have hlo : (l : ℝ) ≤ u := Int.floor_le u
  have hhi : u < (l : ℝ) + 1 := Int.lt_floor_add_one u
  simp only [shiftCost, absoluteSum, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  by_cases h : 0 ≤ d i + l
  · have h' : 0 ≤ (d i : ℝ) + (l : ℝ) := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith : 0 ≤ (d i : ℝ) + u), abs_of_nonneg h',
      abs_of_nonneg (by linarith : 0 ≤ (d i : ℝ) + ((l : ℝ) + 1))]
    dsimp [f]
    ring
  · have h' : (d i : ℝ) + (l : ℝ) ≤ -1 := by
      exact_mod_cast (show d i + l ≤ -1 by omega)
    rw [abs_of_nonpos (by linarith : (d i : ℝ) + u ≤ 0),
      abs_of_nonpos (by linarith : (d i : ℝ) + (l : ℝ) ≤ 0),
      abs_of_nonpos (by linarith : (d i : ℝ) + ((l : ℝ) + 1) ≤ 0)]
    dsimp [f]
    ring

private theorem feasible_real_iff_int (d : ZVector n) (B : ℕ) :
    (∃ t : ℝ, shiftCost d t ≤ B) ↔ ∃ t : ℤ, intNorm (translate d t) ≤ B := by
  constructor
  · rintro ⟨u, hu⟩
    let l : ℤ := ⌊u⌋
    let f : ℝ := u - l
    have hf0 : 0 ≤ f := sub_nonneg.mpr (Int.floor_le u)
    have hf1 : 0 ≤ 1 - f := by
      have hh : u < (l : ℝ) + 1 := Int.lt_floor_add_one u
      dsimp [f]
      linarith
    have hlin : shiftCost d u = (1 - f) * shiftCost d l + f * shiftCost d ((l : ℝ) + 1) :=
      shiftCost_floor d u
    by_contra! h
    have hl : (B : ℝ) < shiftCost d l := by rw [realCost_int]; exact_mod_cast h l
    have hr : (B : ℝ) < shiftCost d ((l : ℝ) + 1) := by
      rw [← Int.cast_one, ← Int.cast_add, realCost_int]
      exact_mod_cast h (l + 1)
    have hla := mul_le_mul_of_nonneg_left hl.le hf1
    have hra := mul_le_mul_of_nonneg_left hr.le hf0
    rcases hf0.eq_or_lt' with hf | hf
    · rw [hf] at hlin
      simp at hlin
      linarith
    · have hr' := mul_lt_mul_of_pos_left hr hf
      nlinarith only [hlin, hu, hla, hr']
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [realCost_int]
    exact_mod_cast ht

private theorem sum_translate (d : ZVector n) (t : ℤ) :
    ∑ i, translate d t i = (∑ i, d i) + (n : ℤ) * t := by
  simp [translate, sum_add_distrib, ZMod.card]

private theorem weight_translate (d : ZVector n) (t : ℤ) :
    weight (translate d t) = weight d + weightSum n * t := by
  simp only [weight, translate, mul_add, sum_add_distrib, ← sum_mul, val_sum]

private theorem feasible_shift_bound (d : ZVector n) (hd : ∑ i, d i = 0) (k : ℕ) (t : ℤ)
    (h : intNorm (translate d t) ≤ n * k) : -(k : ℤ) ≤ t ∧ t ≤ k := by
  have hh := Finset.abs_sum_le_sum_abs (fun i => translate d t i) (univ : Finset (ZMod n))
  rw [sum_translate, hd, zero_add, abs_mul, abs_of_nonneg (Int.natCast_nonneg n)] at hh
  have hn : 0 < (n : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hz : ∑ i, |translate d t i| = (intNorm (translate d t) : ℤ) := by
    simp [intNorm, Nat.cast_sum, Nat.cast_natAbs]
  rw [hz] at hh
  have hh' : (intNorm (translate d t) : ℤ) ≤ (n : ℤ) * k := by exact_mod_cast h
  exact abs_le.mp ((mul_le_mul_iff_right₀ hn).mp (hh.trans hh'))

private theorem feasible_between (d : ZVector n) {B : ℕ} {s t u : ℤ}
    (hs : intNorm (translate d s) ≤ B) (ht : intNorm (translate d t) ≤ B)
    (hsu : s ≤ u) (hut : u ≤ t) : intNorm (translate d u) ≤ B := by
  by_cases hst : s = t
  · have hu : u = s := by omega
    exact hu ▸ hs
  have hh : (s : ℝ) < (t : ℝ) := by exact_mod_cast (show s < t by omega)
  let a : ℝ := ((t : ℝ) - u) / ((t : ℝ) - s)
  let b : ℝ := ((u : ℝ) - s) / ((t : ℝ) - s)
  have hts : 0 < (t : ℝ) - s := sub_pos.mpr hh
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr (by exact_mod_cast hut)) hts.le
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr (by exact_mod_cast hsu)) hts.le
  have hab : a + b = 1 := by
    dsimp [a, b]
    field_simp
    ring
  have hu : a * (s : ℝ) + b * (t : ℝ) = u := by
    dsimp [a, b]
    field_simp
    ring
  have h := shiftCost_convex d (s : ℝ) (t : ℝ) a b ha hb hab
  rw [hu, realCost_int, realCost_int, realCost_int] at h
  have hs' : (intNorm (translate d s) : ℝ) ≤ B := by exact_mod_cast hs
  have ht' : (intNorm (translate d t) : ℝ) ≤ B := by exact_mod_cast ht
  have he : (intNorm (translate d u) : ℝ) ≤ B := by
    calc
      _ ≤ a * (intNorm (translate d s) : ℝ) + b * (intNorm (translate d t) : ℝ) := h
      _ ≤ a * (B : ℝ) + b * (B : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hs' ha) (mul_le_mul_of_nonneg_left ht' hb)
      _ = B := by rw [← add_mul, hab, one_mul]
  exact_mod_cast he

def IsFirst (d : ZVector n) (B : ℕ) (t : ℤ) : Prop :=
  intNorm (translate d t) ≤ B ∧ B < intNorm (translate d (t - 1))

private theorem first_least (d : ZVector n) {B : ℕ} {t : ℤ}
    (h : IsFirst d B t) (s : ℤ) (hs : intNorm (translate d s) ≤ B) : t ≤ s := by
  by_contra! hst
  exact (not_le_of_gt h.2) (feasible_between d hs h.1 (by omega : s ≤ t - 1) (by omega))

private theorem first_exists_unique (d : ZVector n) (hd : ∑ i, d i = 0) (k : ℕ)
    (h : ∃ t : ℤ, intNorm (translate d t) ≤ n * k) : ∃! t, IsFirst d (n * k) t := by
  classical
  let T := (Icc (-(k : ℤ)) (k : ℤ)).filter fun t => intNorm (translate d t) ≤ n * k
  have hT (t : ℤ) : t ∈ T ↔ intNorm (translate d t) ≤ n * k := by
    simp only [T, mem_filter, mem_Icc]
    exact ⟨And.right, fun ht => ⟨feasible_shift_bound d hd k t ht, ht⟩⟩
  have hne : T.Nonempty := by
    obtain ⟨t, ht⟩ := h
    exact ⟨t, (hT t).mpr ht⟩
  let t := T.min' hne
  have ht : IsFirst d (n * k) t := by
    refine ⟨(hT t).mp (T.min'_mem hne), ?_⟩
    by_contra! hprev
    have hle : t ≤ t - 1 := T.min'_le _ ((hT (t - 1)).mpr hprev)
    omega
  exact ⟨t, ht, fun q hq => le_antisymm (first_least d hq t ht.1) (first_least d ht q hq.1)⟩

private theorem predecessor_norm (z : ZVector n) :
    intNorm (translate z (-1)) + 2 * positiveCount z = intNorm z + n := by
  have h (v : ℤ) : (v - 1).natAbs + 2 * (if 0 < v then 1 else 0) = v.natAbs + 1 := by
    by_cases hv : 0 < v
    · have hv' : 0 ≤ v - 1 := by omega
      have ha := Int.natAbs_of_nonneg hv.le
      have hb := Int.natAbs_of_nonneg hv'
      simp only [ite_eq_left hv]
      omega
    · push Not at hv
      have ha := Int.ofNat_natAbs_of_nonpos hv
      have hb := Int.ofNat_natAbs_of_nonpos (show v - 1 ≤ 0 by omega)
      simp only [ite_eq_right (not_lt.mpr hv)]
      omega
  simp only [intNorm, positiveCount, translate]
  have hmul := Finset.mul_sum (univ : Finset (ZMod n)) (fun i => if 0 < z i then (1 : ℕ) else 0) 2
  rw [hmul, ← sum_add_distrib]
  calc
    _ = ∑ i : ZMod n, ((z i).natAbs + 1) := by
      apply sum_congr rfl
      intro i _
      simpa only [sub_eq_add_neg] using h (z i)
    _ = _ := by simp [sum_add_distrib, ZMod.card]

private theorem first_terminal (d : ZVector n) (B : ℕ) (t : ℤ) :
    IsFirst d B t ↔ intNorm (translate d t) ≤ B ∧
      B + 2 * positiveCount (translate d t) < intNorm (translate d t) + n := by
  have he : translate d (t - 1) = translate (translate d t) (-1) := by
    funext i
    simp [translate, sub_eq_add_neg, add_assoc]
  rw [IsFirst, he]
  have h := predecessor_norm (translate d t)
  omega

end LeastTranslate

section Representatives

noncomputable section

variable {n k : ℕ} [NeZero n]

def Feasible (d : Coset n k) : Prop :=
  ∃ t : ℤ, intNorm (translate d.val t) ≤ n * k

private theorem source_iff_feasible (hn : 3 ≤ n) (x : Plane n k) :
    realVector x.val ∈ (k : ℝ) • OlairezQ62.Q n ↔ Feasible (planeEquivCoset hn x) := by
  rw [source_iff_real_translate hn]
  exact_mod_cast feasible_real_iff_int (forward x.val) (n * k)

def pointsEquivFeasible (hn : 3 ≤ n) : SourcePoints n k ≃ {d : Coset n k // Feasible d} := by
  let e : SourcePoints n k ≃
      {x : Plane n k // realVector x.val ∈ (k : ℝ) • OlairezQ62.Q n} :=
    { toFun := fun x => ⟨⟨x.val, source_on_plane hn x⟩, x.property⟩
      invFun := fun x => ⟨x.val.val, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact e.trans ((planeEquivCoset hn).subtypeEquiv (source_iff_feasible hn))

def LeastPair (n k : ℕ) [NeZero n] :=
  {p : Coset n k × ℤ // IsFirst p.1.val (n * k) p.2}

def feasibleEquivLeast : {d : Coset n k // Feasible d} ≃ LeastPair n k := by
  let f : LeastPair n k → {d : Coset n k // Feasible d} := fun p =>
    ⟨p.val.1, p.val.2, p.property.1⟩
  refine (Equiv.ofBijective f ⟨?_, ?_⟩).symm
  · intro p q he
    have hd : p.val.1 = q.val.1 := congrArg Subtype.val he
    have ht : p.val.2 = q.val.2 := by
      have hp := p.property
      have hq := q.property
      rw [← hd] at hq
      exact le_antisymm (first_least _ hp _ hq.1) (first_least _ hq _ hp.1)
    exact Subtype.ext (Prod.ext hd ht)
  · intro d
    obtain ⟨t, ht, _⟩ := first_exists_unique d.val.val d.val.property.1 k d.property
    exact ⟨⟨(d.val, t), ht⟩, rfl⟩

def terminalPredicate (n k : ℕ) (s : ℤ) (r : ZMod n) (a p : ℕ) : Prop :=
  ∃ t : ℤ, (-(k : ℤ) ≤ t ∧ t ≤ k) ∧ s = (n : ℤ) * t ∧
    r = ((weightSum n * t - (k : ℤ) * sourceSum n : ℤ) : ZMod n) ∧
    a ≤ n * k ∧ n * k + 2 * p < a + n

def isRepresentative (n k : ℕ) [NeZero n] (z : ZVector n) : Prop :=
  terminalPredicate n k (∑ i, z i) (weight z : ZMod n) (intNorm z) (positiveCount z)

abbrev Representatives (n k : ℕ) [NeZero n] :=
  {z : ZVector n // isRepresentative n k z}

def leastEquivRepresentatives : LeastPair n k ≃ Representatives n k := by
  let f : LeastPair n k → Representatives n k := fun x => ⟨translate x.val.1.val x.val.2, by
    have hcost := (first_terminal _ _ _).mp x.property
    refine ⟨x.val.2, feasible_shift_bound _ x.val.1.property.1 k _ hcost.1, ?_, ?_, hcost⟩
    · rw [sum_translate, x.val.1.property.1, zero_add]
    · have hr := x.val.1.property.2.trans (sourceResidue_eq n k)
      change (weight (translate x.val.1.val x.val.2) : ZMod n) = _
      rw [weight_translate, Int.cast_add]
      calc
        _ = ((-((k : ℤ) * sourceSum n) : ℤ) : ZMod n) + (↑(weightSum n * x.val.2) : ZMod n) :=
          congrArg (fun r : ZMod n => r + (↑(weightSum n * x.val.2) : ZMod n)) hr
        _ = _ := by push_cast; ring⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    have hz : translate x.val.1.val x.val.2 = translate y.val.1.val y.val.2 :=
      congrArg Subtype.val h
    have hs := congrArg (fun z : ZVector n => ∑ i, z i) hz
    rw [sum_translate, sum_translate, x.val.1.property.1, y.val.1.property.1, zero_add, zero_add] at hs
    have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
    have ht := mul_left_cancel₀ hn hs
    apply Subtype.ext
    refine Prod.ext (Subtype.ext (funext fun i => ?_)) ht
    exact add_right_cancel (by simpa only [translate, ht] using congrFun hz i)
  · intro z
    obtain ⟨t, _, hs, hr, ha, hp⟩ := z.property
    let d := translate z.val (-t)
    have hsum : ∑ i, d i = 0 := by rw [sum_translate, hs, mul_neg, add_neg_cancel]
    have hres : (weight d : ZMod n) = sourceResidue n k := by
      rw [sourceResidue_eq, weight_translate, Int.cast_add, hr, mul_neg, Int.cast_neg,
        Int.cast_sub, Int.cast_neg]
      abel
    have he : translate d t = z.val := by
      funext i
      simp [d, translate]
    have hf : IsFirst d (n * k) t := by
      rw [first_terminal, he]
      exact ⟨ha, hp⟩
    exact ⟨⟨(⟨d, hsum, hres⟩, t), hf⟩, Subtype.ext he⟩

def pointsEquivRepresentatives (hn : 3 ≤ n) : SourcePoints n k ≃ Representatives n k :=
  (pointsEquivFeasible hn).trans (feasibleEquivLeast.trans leastEquivRepresentatives)

end

end Representatives

/-- Prefix sum, weighted residue, absolute sum and positive entry count. -/
structure State (n : ℕ) where
  s : ℤ
  r : ZMod n
  a : ℕ
  p : ℕ
  deriving DecidableEq

def values (m : ℕ) : List ℤ :=
  (List.range (2 * m + 1)).map fun (j : ℕ) => (j : ℤ) - m

def step (i : ℕ) (q : State n) (v : ℤ) : State n :=
  ⟨q.s + v, q.r + (i : ZMod n) * (v : ZMod n), q.a + v.natAbs, q.p + if 0 < v then 1 else 0⟩

/-- One list entry per prefix path. Equal states retain their multiplicities. -/
def contributions (n B : ℕ) : ℕ → List (State n)
  | 0 => [⟨0, 0, 0, 0⟩]
  | i + 1 => (contributions n B i).flatMap fun q => (values (B - q.a)).map (step i q)

def D (n B i : ℕ) (q : State n) : ℕ :=
  (contributions n B i).countP fun q' => decide (q' = q)

def terminal (n k : ℕ) (q : State n) : Bool :=
  let t := q.s / (n : ℤ)
  decide ((-(k : ℤ) ≤ t ∧ t ≤ k) ∧ q.s = (n : ℤ) * t ∧
    q.r = ((weightSum n * t - (k : ℤ) * sourceSum n : ℤ) : ZMod n) ∧
    q.a ≤ n * k ∧ n * k + 2 * q.p < q.a + n)

def recurrenceCount (n k : ℕ) : ℕ :=
  (contributions n (n * k) n).countP (terminal n k)

private theorem terminal_iff (n k : ℕ) [NeZero n] (q : State n) :
    terminal n k q = true ↔ terminalPredicate n k q.s q.r q.a q.p := by
  simp only [terminal, decide_eq_true_eq, terminalPredicate]
  refine ⟨fun h => ⟨_, h⟩, ?_⟩
  rintro ⟨t, ht, hs, hr, ha, hp⟩
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have he : q.s / (n : ℤ) = t := by rw [hs, Int.mul_comm, Int.mul_ediv_cancel _ hn]
  rw [he]
  exact ⟨ht, hs, hr, ha, hp⟩

private theorem mem_values (m : ℕ) (v : ℤ) : v ∈ values m ↔ v.natAbs ≤ m := by
  simp only [values, List.mem_map]
  have habs : v.natAbs ≤ m ↔ -(m : ℤ) ≤ v ∧ v ≤ m := by
    have h : (v.natAbs : ℤ) = |v| := Nat.cast_natAbs v
    calc
      v.natAbs ≤ m ↔ (v.natAbs : ℤ) ≤ (m : ℤ) := by omega
      _ ↔ _ := by rw [h, abs_le]
  rw [habs]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj' := List.mem_range.mp hj
    omega
  · rintro ⟨hlo, hhi⟩
    exact ⟨(v + m).toNat, List.mem_range.mpr (by omega), by omega⟩

private theorem values_nodup (m : ℕ) : (values m).Nodup := by
  unfold values
  exact List.nodup_range.map (show Function.Injective (fun j : ℕ => (j : ℤ) - m) from
    fun a b h => by
      change (a : ℤ) - m = (b : ℤ) - m at h
      omega)

def stats (n : ℕ) {i : ℕ} (x : Fin i → ℤ) : State n :=
  ⟨∑ j, x j, ∑ j, (j.val : ZMod n) * (x j : ZMod n),
    ∑ j, (x j).natAbs, ∑ j, if 0 < x j then 1 else 0⟩

private theorem stats_snoc (n : ℕ) {i : ℕ} (x : Fin i → ℤ) (v : ℤ) :
    stats n (Fin.snoc x v) = step i (stats n x) v := by
  simp only [stats, step, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    Fin.val_castSucc, Fin.val_last]

def prefixes (B : ℕ) : (i : ℕ) → List (Fin i → ℤ)
  | 0 => [Fin.elim0]
  | i + 1 => (prefixes B i).flatMap fun x =>
      (values (B - ∑ j, (x j).natAbs)).map (Fin.snoc x)

private theorem contributions_eq (n B i : ℕ) :
    contributions n B i = (prefixes B i).map (stats n) := by
  induction i with
  | zero => simp [contributions, prefixes, stats]
  | succ i ih =>
    simp only [contributions, prefixes, ih, List.map_flatMap, List.flatMap_map, List.map_map,
      Function.comp_def, stats_snoc]
    rfl

private theorem mem_prefixes (B i : ℕ) (x : Fin i → ℤ) :
    x ∈ prefixes B i ↔ (stats 1 x).a ≤ B := by
  induction i with
  | zero =>
    have h : x = Fin.elim0 := funext fun i => i.elim0
    simp [prefixes, stats, h]
  | succ i ih =>
    constructor
    · intro h
      simp only [prefixes, List.mem_flatMap, List.mem_map] at h
      obtain ⟨y, hy, v, hv, rfl⟩ := h
      have hy' := (ih y).mp hy
      have hv' := (mem_values _ _).mp hv
      rw [stats_snoc]
      change ((stats 1 y).a + v.natAbs) ≤ B
      change v.natAbs ≤ B - (stats 1 y).a at hv'
      omega
    · intro h
      let y := Fin.init x
      let v := x (Fin.last i)
      have he : Fin.snoc y v = x := Fin.snoc_init_self _
      rw [← he, stats_snoc] at h
      change ((stats 1 y).a + v.natAbs) ≤ B at h
      simp only [prefixes, List.mem_flatMap, List.mem_map]
      exact ⟨y, (ih y).mpr (by omega), v, (mem_values _ _).mpr (by
        change v.natAbs ≤ B - (stats 1 y).a
        omega), he⟩

private theorem prefixes_nodup (B i : ℕ) : (prefixes B i).Nodup := by
  induction i with
  | zero => simp [prefixes]
  | succ i ih =>
    rw [prefixes, List.nodup_flatMap]
    constructor
    · intro x _
      exact (values_nodup _).map fun a b h => (Fin.snoc_injective2 h).2
    · apply ih.imp
      intro x y hne z hx hy
      obtain ⟨a, _, ha⟩ := List.mem_map.mp hx
      obtain ⟨b, _, hb⟩ := List.mem_map.mp hy
      exact hne (Fin.snoc_injective2 (ha.trans hb.symm)).1

private theorem D_counts_prefixes (n B i : ℕ) (q : State n) :
    D n B i q = (prefixes B i).countP (fun x => decide (stats n x = q)) := by
  unfold D
  rw [contributions_eq, List.countP_map]
  rfl

private theorem stat_congr (n : ℕ) [NeZero n] (z : ZVector n) :
    stats n (z ∘ ZMod.finEquiv n) =
      ⟨∑ i, z i, (weight z : ZMod n), intNorm z, positiveCount z⟩ := by
  have he (i : Fin n) : (ZMod.finEquiv n i).val = i.val := by
    cases n with
    | zero => exact (Nat.not_lt_zero _ i.isLt).elim
    | succ n => rfl
  unfold stats weight intNorm positiveCount
  push_cast
  congr 1
  · exact Equiv.sum_comp (ZMod.finEquiv n).toEquiv _
  · have h := Equiv.sum_comp (ZMod.finEquiv n).toEquiv
        (fun i : ZMod n => (i.val : ZMod n) * (z i : ZMod n))
    change (∑ j : Fin n, ((ZMod.finEquiv n j).val : ZMod n) * (z (ZMod.finEquiv n j) : ZMod n)) = _ at h
    simpa only [he, Function.comp_apply] using h
  · exact Equiv.sum_comp (ZMod.finEquiv n).toEquiv (fun i => (z i).natAbs)
  · exact Equiv.sum_comp (ZMod.finEquiv n).toEquiv (fun i => if 0 < z i then 1 else 0)

private theorem representatives_count (n k : ℕ) [NeZero n] :
    Finite (Representatives n k) ∧ Nat.card (Representatives n k) = recurrenceCount n k := by
  classical
  let l := (prefixes (n * k) n).filter fun x => terminal n k (stats n x)
  have hnodup : l.Nodup := (prefixes_nodup _ _).filter _
  have hlen : l.length = recurrenceCount n k := by
    unfold recurrenceCount
    rw [contributions_eq, List.countP_map, List.countP_eq_length_filter]
    rfl
  have hmem (z : ZVector n) :
      isRepresentative n k z ↔ (z ∘ ZMod.finEquiv n) ∈ l.toFinset := by
    simp only [List.mem_toFinset, l, List.mem_filter, mem_prefixes, terminal_iff, stat_congr]
    change terminalPredicate n k (∑ i, z i) (weight z : ZMod n) (intNorm z) (positiveCount z)
      ↔ (stats 1 (z ∘ ZMod.finEquiv n)).a ≤ n * k ∧
        terminalPredicate n k (∑ i, z i) (weight z : ZMod n) (intNorm z) (positiveCount z)
    have he : (stats 1 (z ∘ ZMod.finEquiv n)).a = intNorm z :=
      Equiv.sum_comp (ZMod.finEquiv n).toEquiv (fun i => (z i).natAbs)
    rw [he]
    exact ⟨fun h => ⟨by obtain ⟨_, _, _, _, ha, _⟩ := h; exact ha, h⟩, And.right⟩
  let e : ZVector n ≃ (Fin n → ℤ) :=
    { toFun := fun z => z ∘ ZMod.finEquiv n
      invFun := fun x => x ∘ (ZMod.finEquiv n).symm
      left_inv := fun z => funext fun i => by simp
      right_inv := fun z => funext fun i => by simp }
  let f := e.subtypeEquiv hmem
  refine ⟨Finite.of_equiv _ f.symm, ?_⟩
  rw [Nat.card_congr f, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnodup, hlen]

private theorem countP_sum_buckets {α β : Type*} [DecidableEq β]
    (l : List α) (f : α → β) (s : Finset β) :
    l.countP (fun x => decide (f x ∈ s)) =
      ∑ a ∈ s, l.countP (fun x => decide (f x = a)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons, decide_eq_true_eq, sum_add_distrib, sum_ite_eq, ih]

def terminalIndices (n k : ℕ) : Finset (ℤ × ℕ × ℕ) :=
  ((Icc (-(k : ℤ)) (k : ℤ)) ×ˢ (range (n * k + 1) ×ˢ range (n + 1))).filter
    fun q => n * k + 2 * q.2.2 < q.2.1 + n

def terminalState (n k : ℕ) (q : ℤ × ℕ × ℕ) : State n :=
  ⟨(n : ℤ) * q.1, ((weightSum n * q.1 - (k : ℤ) * sourceSum n : ℤ) : ZMod n),
    q.2.1, q.2.2⟩

/-- Sum of the recurrence entries passing the strict least-translate test. -/
def terminalSum (n k : ℕ) : ℕ :=
  ∑ q ∈ terminalIndices n k, D n (n * k) n (terminalState n k q)

private theorem terminalState_injective (n k : ℕ) [NeZero n] :
    Function.Injective (terminalState n k) := by
  intro a b h
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  exact Prod.ext (mul_left_cancel₀ hn (congrArg State.s h))
    (Prod.ext (congrArg State.a h) (congrArg State.p h))

private theorem contribution_positive_bound (n B i : ℕ) (q : State n)
    (hq : q ∈ contributions n B i) : q.p ≤ i := by
  rw [contributions_eq, List.mem_map] at hq
  obtain ⟨x, _, rfl⟩ := hq
  change (∑ j : Fin i, if 0 < x j then 1 else 0) ≤ i
  calc
    _ ≤ ∑ _ : Fin i, (1 : ℕ) := sum_le_sum fun j _ => by split <;> omega
    _ = i := by simp

private theorem recurrence_eq_terminal_sum (n k : ℕ) [NeZero n] :
    recurrenceCount n k = terminalSum n k := by
  let S := (terminalIndices n k).image (terminalState n k)
  have h (q : State n) (hq : q ∈ contributions n (n * k) n) :
      terminal n k q = true ↔ q ∈ S := by
    rw [terminal_iff]
    simp only [S, mem_image, terminalIndices, mem_filter, mem_product, mem_Icc, mem_range]
    constructor
    · rintro ⟨t, ht, hs, hr, ha, hp⟩
      have hpn := contribution_positive_bound _ _ _ _ hq
      refine ⟨⟨t, q.a, q.p⟩, ⟨⟨ht, Nat.lt_succ_of_le ha, Nat.lt_succ_of_le hpn⟩, hp⟩, ?_⟩
      cases q
      simp_all [terminalState]
    · rintro ⟨⟨t, a, p⟩, ⟨⟨ht, ha, _⟩, hp⟩, rfl⟩
      exact ⟨t, ht, rfl, rfl, Nat.le_of_lt_succ ha, hp⟩
  have hprefix (x : Fin n → ℤ) (hx : x ∈ prefixes (n * k) n) :
      terminal n k (stats n x) = true ↔ stats n x ∈ S := by
    apply h
    rw [contributions_eq]
    exact List.mem_map.mpr ⟨x, hx, rfl⟩
  calc
    recurrenceCount n k = (prefixes (n * k) n).countP (fun x => terminal n k (stats n x)) := by
      simp only [recurrenceCount, contributions_eq, List.countP_map, Function.comp_def]
    _ = (prefixes (n * k) n).countP (fun x => decide (stats n x ∈ S)) := by
      apply List.countP_congr
      intro x hx
      simpa only [decide_eq_true_eq] using hprefix x hx
    _ = ∑ a ∈ S, (prefixes (n * k) n).countP (fun x => decide (stats n x = a)) :=
      countP_sum_buckets _ _ _
    _ = ∑ a ∈ S, D n (n * k) n a := by simp only [D_counts_prefixes]
    _ = terminalSum n k := by
      unfold terminalSum
      exact sum_image (terminalState_injective n k).injOn

/-- The real dilation of the source hull has finitely many integral points.
Their cardinality is the terminal sum of the prefix recurrence. -/
theorem latticePointCount_terminalSum (n k : ℕ) (hn : 3 ≤ n) :
    Finite (SourcePoints n k) ∧ Nat.card (SourcePoints n k) = terminalSum n k := by
  let _ : NeZero n := ⟨by omega⟩
  obtain ⟨hf, hc⟩ := representatives_count n k
  let _ : Finite (Representatives n k) := hf
  let e := pointsEquivRepresentatives (k := k) hn
  exact ⟨Finite.of_equiv _ e.symm,
    (Nat.card_congr e).trans (hc.trans (recurrence_eq_terminal_sum n k))⟩

/-- The coordinate count and dilation for the first recurrence check. -/
def fourOneInput : ℕ × ℕ := (4, 1)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
example : Nat.card (SourcePoints fourOneInput.1 fourOneInput.2) = 22 := by
  letI : NeZero fourOneInput.1 := ⟨by decide⟩
  calc
    _ = terminalSum fourOneInput.1 fourOneInput.2 :=
      (latticePointCount_terminalSum _ _ (by decide)).2
    _ = recurrenceCount fourOneInput.1 fourOneInput.2 :=
      (recurrence_eq_terminal_sum _ _).symm
    _ = 22 := by decide

end OlairezCount
