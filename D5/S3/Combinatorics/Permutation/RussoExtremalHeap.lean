/- GID: D5/S3/Combinatorics/Permutation/RussoExtremalHeap
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/RussoExtremalHeap
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The extremal Heap sweep ends in reversal for sizes two modulo four. -/

import D5.S3.Combinatorics.Permutation.RussoHeapLowerSweep
import D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing
import Mathlib.Order.PiLex

open Equiv Equiv.Perm

namespace D5.S3.Combinatorics.Permutation.RussoExtremalHeap

open D5.S3.Combinatorics.Permutation.RussoHeapLowerSweep

/- The support is written in U-cycle order starting at the penultimate
position. Coordinates 0 and 1 are source positions n-1 and 2. -/
private abbrev carrierSize (a : ℕ) := 2*(2*a)+2
private abbrev cycleSize (a : ℕ) := 2*a+2

local macro "size_omega" : tactic =>
  `(tactic| (first | (dsimp only [carrierSize, cycleSize] at * <;> omega) | omega))

private def cycleValue (a i : ℕ) : ℕ :=
  if i = 0 then 4*a else if i ≤ a then 2*i-1 else 2*(i-a-1)

private def cyclePoint (a i : ℕ) : Fin (carrierSize a) :=
  slot (carrierSize a) (cycleValue a i)

private theorem cyclePoint_value {a i : ℕ} (hi : i < cycleSize a) :
    (cyclePoint a i).val = cycleValue a i := by
  apply slot_val
  unfold cycleValue
  split_ifs <;> size_omega

private def marks (a : ℕ) : Set (Fin (carrierSize a)) :=
  {x | x.val ≤ 2*a ∨ x.val = 4*a}

private theorem cyclePoint_marks {a i : ℕ} (hi : i < cycleSize a) :
    cyclePoint a i ∈ marks a := by
  change (cyclePoint a i).val ≤ 2*a ∨ (cyclePoint a i).val = 4*a
  rw [cyclePoint_value hi]
  unfold cycleValue
  split_ifs <;> size_omega

private theorem cyclePoint_inj {a i j : ℕ} (ha : 0 < a)
    (hi : i < cycleSize a) (hj : j < cycleSize a)
    (h : cyclePoint a i = cyclePoint a j) : i = j := by
  have he := congrArg Fin.val h
  rw [cyclePoint_value hi, cyclePoint_value hj] at he
  unfold cycleValue at he
  split_ifs at he <;> size_omega

private theorem cyclePoint_surj {a : ℕ} (ha : 0 < a)
    (x : Fin (carrierSize a)) (hx : x ∈ marks a) :
    ∃ i < cycleSize a, cyclePoint a i = x := by
  change x.val ≤ 2*a ∨ x.val = 4*a at hx
  by_cases ht : x.val = 4*a
  · refine ⟨0, by size_omega, Fin.ext ?_⟩
    rw [cyclePoint_value (by size_omega), cycleValue, ite_eq_left (rfl : (0 : ℕ) = 0)]
    exact ht.symm
  · have hlow : x.val ≤ 2*a := hx.resolve_right ht
    by_cases heven : x.val % 2 = 0
    · refine ⟨x.val/2+a+1, by size_omega, Fin.ext ?_⟩
      rw [cyclePoint_value (by size_omega), cycleValue, ite_eq_right (by size_omega), ite_eq_right (by size_omega)]
      size_omega
    · refine ⟨(x.val+1)/2, by size_omega, Fin.ext ?_⟩
      rw [cyclePoint_value (by size_omega), cycleValue, ite_eq_right (by size_omega), ite_eq_left (by size_omega)]
      size_omega

private def supportList (a : ℕ) : List (Fin (carrierSize a)) :=
  List.ofFn (fun i : Fin (cycleSize a) => cyclePoint a i.val)

private theorem supportList_nodup {a : ℕ} (ha : 0 < a) : (supportList a).Nodup :=
  nodup_ofFn_labels (cyclePoint a) (fun _ hi _ hj h => cyclePoint_inj ha hi hj h)

private theorem supportList_mem {a : ℕ} (ha : 0 < a) (x : Fin (carrierSize a)) :
    x ∈ supportList a ↔ x ∈ marks a := by
  rw [supportList, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    exact cyclePoint_marks i.isLt
  · intro hx
    obtain ⟨i, hi, he⟩ := cyclePoint_surj ha x hx
    exact ⟨⟨i, hi⟩, he⟩

private theorem cycleValue_succ {a i : ℕ} (ha : 0 < a) (hi : i < cycleSize a) :
    uArrow (2*a) (cycleValue a i) = cycleValue a ((i+1) % cycleSize a) := by
  by_cases hlast : i+1 = cycleSize a
  · rw [hlast, Nat.mod_self]
    unfold uArrow cycleValue
    split_ifs <;> size_omega
  · rw [Nat.mod_eq_of_lt (by size_omega : i+1 < cycleSize a)]
    unfold uArrow cycleValue
    split_ifs <;> size_omega

private theorem literal_net_support_cycle (a : ℕ) (ha : 0 < a) :
    actualU (carrierSize a) = (supportList a).formPerm := by
  apply Equiv.ext
  intro x
  apply Fin.ext
  rw [literal_net_value (2*a) (by size_omega)]
  by_cases hx : x ∈ marks a
  · obtain ⟨i, hi, rfl⟩ := cyclePoint_surj ha x hx
    have hstep := formPerm_ofFn_pow (cyclePoint a) (supportList_nodup ha) 1 i hi
    rw [pow_one] at hstep
    change (supportList a).formPerm (cyclePoint a i) = _ at hstep
    rw [hstep, cyclePoint_value hi,
      cyclePoint_value (Nat.mod_lt _ (by size_omega : 0 < cycleSize a))]
    exact cycleValue_succ ha hi
  · rw [List.formPerm_apply_of_notMem (fun h => hx ((supportList_mem ha x).1 h))]
    change ¬ (x.val ≤ 2*a ∨ x.val = 4*a) at hx
    unfold uArrow
    split_ifs <;> size_omega

private theorem U_pow_on_support {a p i : ℕ} (ha : 0 < a) (hi : i < cycleSize a) :
    (actualU (carrierSize a) ^ p) (cyclePoint a i) = cyclePoint a ((i+p)%cycleSize a) := by
  rw [literal_net_support_cycle a ha]
  exact formPerm_ofFn_pow (cyclePoint a) (supportList_nodup ha) p i hi

private theorem U_fixes_complement {a : ℕ} (ha : 0 < a) {x : Fin (carrierSize a)}
    (hx : x ∉ marks a) : actualU (carrierSize a) x = x := by
  rw [literal_net_support_cycle a ha]
  exact List.formPerm_apply_of_notMem (fun h => hx ((supportList_mem ha x).1 h))

private theorem literal_Z_square (a : ℕ) (ha : 0 < a) :
    literalZ (carrierSize a) = actualU (carrierSize a) ^ (2 : ℕ) * Fin.revPerm := by
  let U := actualU (carrierSize a)
  have hcycle : U ^ cycleSize a = 1 := by
    change actualU (carrierSize a) ^ cycleSize a = 1
    rw [literal_net_support_cycle a ha]
    have hlen : (supportList a).length = cycleSize a := List.length_ofFn
    rw [← hlen]
    exact List.formPerm_pow_length_eq_one_of_nodup _ (supportList_nodup ha)
  have hperiod : U ^ (cycleSize a : ℤ) = 1 := by
    simpa only [zpow_natCast] using hcycle
  have hcast : -(carrierSize a : ℤ) = (cycleSize a : ℤ) * (-2) + 2 := by
    push_cast
    size_omega
  change U ^ (-(carrierSize a : ℤ)) * Fin.revPerm = U ^ (2 : ℕ) * Fin.revPerm
  rw [hcast, zpow_add, zpow_mul, hperiod, one_zpow, one_mul]
  rfl

private theorem square_rotation_value {L : ℕ} [NeZero L] (x : Fin L) :
    (((initial L L).formPerm ^ (2 : ℕ)) x).val = (x.val + 2) % L := by
  have h := formPerm_ofFn_pow (slot L) (initial_nodup (le_refl L)) 2 x.val x.isLt
  rw [show slot L x.val = x from Fin.ext (slot_val x.isLt)] at h
  rw [show ((initial L L).formPerm ^ (2 : ℕ)) x = _ from h,
    slot_val (Nat.mod_lt _ (NeZero.pos L))]

private def swap01 (L : ℕ) [NeZero L] : Perm (Fin L) :=
  swap (slot L 0) (slot L 1)

private theorem swap01_value {L : ℕ} [NeZero L] (hL : 1 < L) (x : Fin L) :
    (swap01 L x).val = if x.val = 0 then 1 else if x.val = 1 then 0 else x.val := by
  by_cases h0 : x.val = 0
  · have hx : x = slot L 0 := Fin.ext (h0.trans (slot_val (by omega : 0 < L)).symm)
    rw [ite_eq_left h0, hx, swap01, swap_apply_left, slot_val hL]
  · rw [ite_eq_right h0]
    by_cases h1 : x.val = 1
    · have hx : x = slot L 1 := Fin.ext (h1.trans (slot_val hL).symm)
      rw [ite_eq_left h1, hx, swap01, swap_apply_right, slot_val (by omega : 0 < L)]
    · rw [ite_eq_right h1, swap01, swap_apply_of_ne_of_ne]
      · exact fun h => h0 ((congrArg Fin.val h).trans (slot_val (by omega : 0 < L)))
      · exact fun h => h1 ((congrArg Fin.val h).trans (slot_val hL))

private def returnCoord (a : ℕ) : Perm (Fin (cycleSize a)) :=
  (initial (cycleSize a) (cycleSize a)).formPerm ^ (2 : ℕ) * swap01 (cycleSize a)

private theorem returnCoord_value {a : ℕ} (ha : 0 < a) (x : Fin (cycleSize a)) :
    (returnCoord a x).val =
      if x.val = 0 then 3 else if x.val = 1 then 2
      else if x.val+2 < cycleSize a then x.val+2 else x.val+2-cycleSize a := by
  rw [returnCoord, Perm.mul_apply, square_rotation_value, swap01_value (by size_omega)]
  have hx := x.isLt
  split_ifs with h0 h1 hlt
  · exact Nat.mod_eq_of_lt (by size_omega)
  · exact Nat.mod_eq_of_lt (by size_omega)
  · exact Nat.mod_eq_of_lt hlt
  · rw [Nat.mod_eq_sub_mod (by size_omega : cycleSize a ≤ x.val+2),
      Nat.mod_eq_of_lt (by size_omega : x.val+2-cycleSize a < cycleSize a)]

private theorem returnCoord_step {a i j : ℕ} (ha : 0 < a)
    (hi : i < cycleSize a) (hj : j < cycleSize a)
    (h : (if i = 0 then 3 else if i = 1 then 2
      else if i+2 < cycleSize a then i+2 else i+2-cycleSize a) = j) :
    (returnCoord a).SameCycle (slot (cycleSize a) i) (slot (cycleSize a) j) := by
  refine ⟨1, ?_⟩
  rw [zpow_one]
  apply Fin.ext
  rwa [returnCoord_value ha, slot_val hi, slot_val hj]

private theorem returnCoord_connected {a : ℕ} (ha : 0 < a) (x : Fin (cycleSize a)) :
    (returnCoord a).SameCycle (slot (cycleSize a) 0) x := by
  let atIndex := slot (cycleSize a)
  have oddPath (j : ℕ) (hj : j < a) :
      (returnCoord a).SameCycle (atIndex 0) (atIndex (2*j+3)) := by
    induction j with
    | zero =>
      apply returnCoord_step ha (by size_omega) (by size_omega)
      rfl
    | succ j ih =>
      apply (ih (by omega)).trans
      apply returnCoord_step ha (by size_omega) (by size_omega)
      split_ifs <;> size_omega
  have reachesOne : (returnCoord a).SameCycle (atIndex 0) (atIndex 1) := by
    apply (oddPath (a-1) (by omega)).trans
    apply returnCoord_step ha (by size_omega) (by size_omega)
    split_ifs <;> size_omega
  have evenPath (j : ℕ) (hj : j ≤ a) :
      (returnCoord a).SameCycle (atIndex 0) (atIndex (2*j)) := by
    induction j with
    | zero => exact SameCycle.rfl
    | succ j ih =>
      by_cases h : j = 0
      · subst j
        apply reachesOne.trans
        apply returnCoord_step ha (by size_omega) (by size_omega)
        rfl
      · apply (ih (by omega)).trans
        apply returnCoord_step ha (by size_omega) (by size_omega)
        split_ifs <;> size_omega
  have hx := x.isLt
  have he (i : ℕ) (h : i = x.val) : atIndex i = x := by
    subst i
    exact Fin.ext (slot_val x.isLt)
  by_cases hpar : x.val % 2 = 0
  · rw [← he (2*(x.val/2)) (by omega)]
    exact evenPath _ (by size_omega)
  · by_cases h1 : x.val = 1
    · rw [← he 1 h1.symm]
      exact reachesOne
    · rw [← he (2*((x.val-3)/2)+3) (by omega)]
      exact oddPath _ (by size_omega)

private noncomputable def supportEquiv {a : ℕ} (ha : 0 < a) :
    Fin (cycleSize a) ≃ marks a :=
  Equiv.ofBijective (fun i => ⟨cyclePoint a i.val, cyclePoint_marks i.isLt⟩) (by
    constructor
    · intro i j h
      apply Fin.ext
      exact cyclePoint_inj ha i.isLt j.isLt (congrArg Subtype.val h)
    · intro x
      obtain ⟨i, hi, he⟩ := cyclePoint_surj ha x.val x.property
      exact ⟨⟨i, hi⟩, Subtype.ext he⟩)

private theorem swap01_support {a : ℕ} (ha : 0 < a) (i : Fin (cycleSize a)) :
    cyclePoint a ((swap01 (cycleSize a)) i).val =
      swap (cyclePoint a 0) (cyclePoint a 1) (cyclePoint a i.val) := by
  rw [swap01_value (by size_omega)]
  by_cases h0 : i.val = 0
  · rw [ite_eq_left h0, h0, swap_apply_left]
  · rw [ite_eq_right h0]
    by_cases h1 : i.val = 1
    · rw [ite_eq_left h1, h1, swap_apply_right]
    · rw [ite_eq_right h1, swap_apply_of_ne_of_ne]
      · exact fun h => h0 (cyclePoint_inj ha i.isLt (by size_omega) h)
      · exact fun h => h1 (cyclePoint_inj ha i.isLt (by size_omega) h)

private noncomputable def returnOnMarks {a : ℕ} (ha : 0 < a) : Perm (marks a) :=
  (supportEquiv ha).permCongrHom (returnCoord a)

private theorem returnOnMarks_apply {a : ℕ} (ha : 0 < a) (x : marks a) :
    ((returnOnMarks ha x : marks a) : Fin (carrierSize a)) =
      (actualU (carrierSize a) ^ (2 : ℕ))
        (swap (cyclePoint a 0) (cyclePoint a 1) x.val) := by
  obtain ⟨i, rfl⟩ := (supportEquiv ha).surjective x
  rw [returnOnMarks, Equiv.permCongrHom_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  change cyclePoint a (returnCoord a i).val =
    (actualU (carrierSize a) ^ (2 : ℕ))
      (swap (cyclePoint a 0) (cyclePoint a 1) (cyclePoint a i.val))
  rw [← swap01_support ha i, U_pow_on_support ha (Fin.isLt _), returnCoord,
    Perm.mul_apply, square_rotation_value]

private theorem returnOnMarks_connected {a : ℕ} (ha : 0 < a) (x y : marks a) :
    (returnOnMarks ha).SameCycle x y := by
  let E := supportEquiv ha
  obtain ⟨i, rfl⟩ := E.surjective x
  obtain ⟨j, rfl⟩ := E.surjective y
  obtain ⟨p, hp⟩ := (returnCoord_connected ha i).symm.trans (returnCoord_connected ha j)
  refine ⟨p, ?_⟩
  change ((E.permCongrHom (returnCoord a)) ^ p) (E i) = E j
  rw [← map_zpow, Equiv.permCongrHom_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply, hp]

private theorem rev_first_mark {a : ℕ} (ha : 0 < a) :
    Fin.revPerm (cyclePoint a 0) = cyclePoint a 1 := by
  apply Fin.ext
  change carrierSize a - ((cyclePoint a 0).val + 1) = (cyclePoint a 1).val
  rw [cyclePoint_value (by size_omega : 0 < cycleSize a),
    cyclePoint_value (by size_omega : 1 < cycleSize a)]
  simp [cycleValue, show 1 ≤ a by omega, carrierSize]
  omega

private theorem rev_second_mark {a : ℕ} (ha : 0 < a) :
    Fin.revPerm (cyclePoint a 1) = cyclePoint a 0 := by
  rw [← rev_first_mark ha]
  exact Fin.rev_involutive _

private theorem rev_other_marks {a : ℕ} (ha : 0 < a) (x : marks a)
    (h0 : x.val ≠ cyclePoint a 0) (h1 : x.val ≠ cyclePoint a 1) :
    Fin.revPerm x.val ∉ marks a := by
  have hx := x.property
  change x.val.val ≤ 2*a ∨ x.val.val = 4*a at hx
  have hp0 : (cyclePoint a 0).val = 4*a := by
    rw [cyclePoint_value (by size_omega)]
    simp [cycleValue]
  have hp1 : (cyclePoint a 1).val = 1 := by
    rw [cyclePoint_value (by size_omega)]
    simp [cycleValue, show 1 ≤ a by omega]
  have hne0 : x.val.val ≠ 4*a := fun h => h0 (Fin.ext (h.trans hp0.symm))
  have hne1 : x.val.val ≠ 1 := fun h => h1 (Fin.ext (h.trans hp1.symm))
  change ¬ (carrierSize a - (x.val.val + 1) ≤ 2*a ∨
    carrierSize a - (x.val.val + 1) = 4*a)
  size_omega

private theorem rev_complement {a : ℕ} {x : Fin (carrierSize a)} (hx : x ∉ marks a) :
    Fin.revPerm x ∈ marks a := by
  change ¬ (x.val ≤ 2*a ∨ x.val = 4*a) at hx
  have hbounds := x.isLt
  change carrierSize a - (x.val + 1) ≤ 2*a ∨
    carrierSize a - (x.val + 1) = 4*a
  size_omega

open D5.S3.Combinatorics.PerfectMatchings.FiniteEndpointPairing

private theorem literal_first_visits {a : ℕ} (ha : 0 < a) (x : marks a) :
    ∃ j : ℕ, FirstVisit (literalZ (carrierSize a)) (marks a) x j ∧
      (literalZ (carrierSize a) ^ j) x = returnOnMarks ha x := by
  let f := literalZ (carrierSize a)
  let U := actualU (carrierSize a)
  have hZ (y : Fin (carrierSize a)) : f y = (U ^ (2 : ℕ)) (Fin.revPerm y) := by
    rw [show f = literalZ (carrierSize a) from rfl, literal_Z_square a ha, Perm.mul_apply]
  have hR := returnOnMarks_apply ha x
  change ((returnOnMarks ha x : marks a) : Fin (carrierSize a)) =
    (U ^ (2 : ℕ)) (swap (cyclePoint a 0) (cyclePoint a 1) x.val) at hR
  by_cases h : x.val = cyclePoint a 0 ∨ x.val = cyclePoint a 1
  · have hrev : Fin.revPerm x.val = swap (cyclePoint a 0) (cyclePoint a 1) x.val := by
      rcases h with h0 | h1
      · rw [h0, rev_first_mark ha, swap_apply_left]
      · rw [h1, rev_second_mark ha, swap_apply_right]
    have hstep : (f ^ (1 : ℕ)) x = (returnOnMarks ha x : marks a) := by
      rw [pow_one, hZ, hrev, hR]
    refine ⟨1, ⟨by omega, ?_, ?_⟩, hstep⟩
    · rw [hstep]; exact (returnOnMarks ha x).property
    · intro k hk hlt
      omega
  · have h0 : x.val ≠ cyclePoint a 0 := fun h0 => h (Or.inl h0)
    have h1 : x.val ≠ cyclePoint a 1 := fun h1 => h (Or.inr h1)
    have hout := rev_other_marks ha x h0 h1
    have hfix : U (Fin.revPerm x.val) = Fin.revPerm x.val := U_fixes_complement ha hout
    have hstep : f x = Fin.revPerm x.val := by
      rw [hZ, pow_two, Perm.mul_apply, hfix, hfix]
    have htwo : (f ^ (2 : ℕ)) x = (returnOnMarks ha x : marks a) := by
      rw [pow_two, Perm.mul_apply, hstep, hZ, hR, swap_apply_of_ne_of_ne h0 h1]
      exact congrArg (fun y => (U ^ (2 : ℕ)) y) (Fin.rev_involutive x.val)
    refine ⟨2, ⟨by omega, ?_, ?_⟩, htwo⟩
    · rw [htwo]; exact (returnOnMarks ha x).property
    · intro k hk hlt
      rw [show k = 1 by omega, pow_one, hstep]
      exact hout

private theorem orbit_of_marked_returns {X : Type*} [Finite X] (f : Perm X) (S : Set X)
    (R : Perm S) (x₀ : S)
    (hR : ∀ x y : S, R.SameCycle x y)
    (hvisit : ∀ x : S, ∃ j : ℕ, FirstVisit f S x j ∧ (f ^ j) x = R x)
    (hout : ∀ y ∉ S, ∃ x : S, f x = y) :
    f.IsCycleOn Set.univ := by
  refine ⟨Set.bijOn_univ.mpr f.bijective, ?_⟩
  have hs (x : S) : f.SameCycle x₀ x :=
    (same_cycle_of_first_visit f S R hvisit x₀ x).2 (hR x₀ x)
  have reach (y : X) : f.SameCycle x₀ y := by
    by_cases hy : y ∈ S
    · exact hs ⟨y, hy⟩
    · obtain ⟨x, hx⟩ := hout y hy
      rw [← hx]
      exact (hs x).apply_right
  intro x _ y _
  exact (reach x).symm.trans (reach y)

private theorem literal_orbit_parameterized (a : ℕ) (ha : 0 < a) :
    (literalZ (carrierSize a)).IsCycleOn Set.univ := by
  apply orbit_of_marked_returns _ (marks a) (returnOnMarks ha)
    ⟨cyclePoint a 0, cyclePoint_marks (by size_omega)⟩ (returnOnMarks_connected ha)
    (literal_first_visits ha)
  intro y hy
  refine ⟨⟨Fin.revPerm y, rev_complement hy⟩, ?_⟩
  have hfix := U_fixes_complement ha hy
  rw [literal_Z_square a ha, Perm.mul_apply]
  change (actualU (carrierSize a) ^ (2 : ℕ)) (Fin.revPerm (Fin.revPerm y)) = y
  rw [show Fin.revPerm (Fin.revPerm y) = y from Fin.rev_involutive y, pow_two, Perm.mul_apply, hfix, hfix]

private theorem literal_orbit (n : ℕ) (hn : 6 ≤ n) (hmod : n % 4 = 2) :
    letI : NeZero n := ⟨by omega⟩
    (literalZ n).IsCycleOn Set.univ := by
  have he : n = carrierSize (n/4) := by size_omega
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℕ, 0 < a ∧ n = carrierSize a :=
    ⟨n/4, by omega, he⟩
  exact literal_orbit_parameterized a ha

/-- The first prescribed item at the top is (Z(n)), then (Z^2(n)), and so on. -/
def topParkingItem (n : ℕ) [NeZero n] (j : ℕ) : Fin n :=
  (literalZ n ^ (j+1)) (slot n (n-1))

private theorem top_parked_pow (n : ℕ) [NeZero n] (j : ℕ) :
    parked (slot n (n-1)) (topParkingItem n) j = (literalZ n ^ j) (slot n (n-1)) := by
  cases j <;> simp [parked, topParkingItem]

private theorem top_isCycleOn (n : ℕ) [NeZero n] (hn : 6 ≤ n) (hmod : n % 4 = 2) :
    (literalZ n).IsCycleOn (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)) := by
  simpa only [Finset.coe_univ] using literal_orbit n hn hmod

/-- The successive powers at the last position list all items once. Index zero
is the item already parked there, and the remaining indices prescribe the rounds. -/
private theorem top_parking_order_bijective (n : ℕ) [NeZero n] (hn : 6 ≤ n) (hmod : n % 4 = 2) :
    Function.Bijective (fun j : Fin n => (literalZ n ^ j.val) (slot n (n-1))) := by
  have hcycle := top_isCycleOn n hn hmod
  have htop : slot n (n-1) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  refine ⟨?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    exact hcycle.injOn_pow_apply htop
      (by simpa only [Set.mem_Iio, Finset.card_univ, Fintype.card_fin] using i.isLt)
      (by simpa only [Set.mem_Iio, Finset.card_univ, Fintype.card_fin] using j.isLt) hij
  · intro x
    obtain ⟨j, hj, hx⟩ := hcycle.exists_pow_eq htop (Finset.mem_univ x)
    exact ⟨⟨j, by simpa only [Finset.card_univ, Fintype.card_fin] using hj⟩, hx⟩

private theorem top_parked_inj {n : ℕ} [NeZero n] (hn : 6 ≤ n) (hmod : n % 4 = 2)
    {i j : ℕ} (hi : i < n) (hj : j < n)
    (he : parked (slot n (n-1)) (topParkingItem n) i =
      parked (slot n (n-1)) (topParkingItem n) j) : i = j := by
  rw [top_parked_pow, top_parked_pow] at he
  exact congrArg (fun x : Fin n => x.val)
    ((top_parking_order_bijective n hn hmod).injective
      (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) he)

private theorem top_path_formPerm (n : ℕ) [NeZero n] (hn : 6 ≤ n) (hmod : n % 4 = 2) :
    (path (slot n (n-1)) (topParkingItem n) (n-1)).formPerm = literalZ n := by
  let top := slot n (n-1)
  let item : ℕ → Fin n := fun j => (literalZ n ^ j) top
  have hpath : path top (topParkingItem n) (n-1) =
      List.ofFn (fun j : Fin ((n-1)+1) => item j.val) := by
    rw [List.ofFn_succ, path]
    simp only [item, pow_zero, one_apply, Fin.val_zero, Fin.val_succ]
    rfl
  rw [show n-1+1 = n by omega] at hpath
  have hcycle := top_isCycleOn n hn hmod
  have hwrap : item n = item 0 := by
    simpa only [item, pow_zero, one_apply, Finset.card_univ, Fintype.card_fin] using
      hcycle.pow_card_apply (Finset.mem_univ top)
  have hnodup : (List.ofFn (fun j : Fin n => item j.val)).Nodup := by
    apply nodup_ofFn_labels
    intro i hi j hj he
    exact congrArg (fun x : Fin n => x.val)
      ((top_parking_order_bijective n hn hmod).injective
        (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) he)
  apply Equiv.ext
  intro x
  obtain ⟨i, rfl⟩ := (top_parking_order_bijective n hn hmod).surjective x
  change (path top (topParkingItem n) (n-1)).formPerm (item i.val) = literalZ n (item i.val)
  have he := formPerm_ofFn_pow item hnodup 1 i.val i.isLt
  rw [pow_one] at he
  rw [hpath, he, show literalZ n (item i.val) = item (i.val+1) by
    simp only [item, pow_succ', Perm.mul_apply]]
  by_cases hi : i.val+1 < n
  · rw [Nat.mod_eq_of_lt hi]
  · have hlast : i.val+1 = n := by have := i.isLt; omega
    rw [hlast, Nat.mod_self, hwrap]

/-- Definition 22's actual partner at round `j+1`, via Theorem 18(a). -/
def extremalTopPartner (n : ℕ) [NeZero n] (j : ℕ) : Fin n :=
  parkingPartner (actualU n) (slot n (n-1)) (topParkingItem n) j

private theorem extremal_top (n : ℕ) [NeZero n] (hn : 6 ≤ n) (hmod : n % 4 = 2) :
    PrefixSweep n
      (orderedSweep (penultimateSweep n) (slot n (n - 1)) (extremalTopPartner n) (n - 1)) ∧
      ∀ j < n - 1, (extremalTopPartner n j).val < n - 1 := by
  have hd : n - 1 + 1 = n := by omega
  have he := extendParkingSweep hd (penultimate_prefixSweep n hn hmod) (topParkingItem n)
    (fun _ hi _ hj h => top_parked_inj hn hmod (by omega) (by omega) h)
  rw [hd] at he
  exact he

/-- The exact ordered physical swaps of Definition 22 in the residue class
two, with its separate cyclic/classic branch at size two. -/
def extremalSweep (n : ℕ) [NeZero n] : List (Fin n × Fin n) :=
  if n = 2 then cyclicSweep n 1
  else orderedSweep (penultimateSweep n) (slot n (n-1)) (extremalTopPartner n) (n-1)

private theorem extremalSweep_two : extremalSweep 2 = [(0, 1)] := rfl

private theorem extremal_prefixSweep (n : ℕ) [NeZero n] (hn : 2 ≤ n) (hmod : n % 4 = 2) :
    PrefixSweep n (extremalSweep n) := by
  by_cases htwo : n = 2
  · subst n
    exact cyclic_prefixSweep 2 1 (by omega)
  · rw [extremalSweep, ite_eq_right htwo]
    exact (extremal_top n (by omega) hmod).1

private theorem execute_extremalSweep_two : executeSwaps (extremalSweep 2) 1 = Fin.revPerm := by
  rw [extremalSweep_two]
  apply Equiv.ext
  intro x
  fin_cases x <;> decide

private theorem execute_extremalSweep_large (n : ℕ) [NeZero n] (hn : 6 ≤ n) (hmod : n % 4 = 2) :
    executeSwaps (extremalSweep n) 1 = actualU n ^ n * literalZ n ∧
      actualU n ^ n * literalZ n = Fin.revPerm := by
  have htop : (slot n (n-1)).val = n-1 := slot_val (by omega)
  have hfix : actualU n (slot n (n-1)) = slot n (n-1) := by
    rw [actualU]
    exact prefixNet_fixes (penultimate_prefixSweep n hn hmod) _ (by rw [htop])
  constructor
  · rw [extremalSweep, ite_eq_right (by omega : n ≠ 2)]
    unfold extremalTopPartner
    have h := executeParkingSweep (penultimateSweep n) (slot n (n - 1)) (topParkingItem n)
      hfix (n - 1)
    dsimp only at h
    rw [top_path_formPerm n hn hmod, show n - 1 + 1 = n by omega] at h
    exact h
  · rw [literalZ, zpow_neg, zpow_natCast, ← mul_assoc, mul_inv_cancel, one_mul]

private theorem sweepStates_last {α : Type*} [DecidableEq α] (swaps : List (α × α))
    (start : Perm α) :
    (sweepStates swaps start).getLast? = some (executeSwaps swaps start) :=
  List.getLast?_scanl

private theorem sweepStates_step {α : Type*} [DecidableEq α] (swaps : List (α × α))
    (start : Perm α) (i : ℕ) :
    (sweepStates swaps start)[i + 1]? =
      ((sweepStates swaps start)[i]?).bind fun state =>
        swaps[i]?.map fun ab => swap ab.1 ab.2 * state :=
  List.getElem?_succ_scanl

/-- The boundary between the completed prefix of blocks and the next lower call. -/
private theorem sweepStates_ordered_boundary {α : Type*} [DecidableEq α] (lower : List (α × α))
    (top : α) (s : ℕ → α) (j : ℕ) (start : Perm α) :
    let previous := orderedSweep lower top s j
    let last := executeSwaps previous start
    (sweepStates previous start).getLast? = some last ∧
      (sweepStates lower (swap (s j) top * last)).head? = some (swap (s j) top * last) := by
  exact ⟨sweepStates_last _ _, List.head?_scanl⟩

/-- Read a state as an array, sending each position to the item it contains. -/
def sweepArrays {α : Type*} [DecidableEq α] (swaps : List (α × α)) (start : Perm α) :
    List (Perm α) :=
  (sweepStates swaps start).map Inv.inv

/-- The swap stored at index `i` acts on the positions of array `i` to give
array `i+1`. Right composition exchanges the two array entries. -/
private theorem sweepArrays_step {α : Type*} [DecidableEq α] (swaps : List (α × α))
    (start : Perm α) (i : ℕ) :
    (sweepArrays swaps start)[i + 1]? =
      ((sweepArrays swaps start)[i]?).bind fun array =>
        swaps[i]?.map fun ab => array * swap ab.1 ab.2 := by
  unfold sweepArrays
  rw [List.getElem?_map, sweepStates_step, List.getElem?_map]
  cases (sweepStates swaps start)[i]? <;> cases swaps[i]? <;> simp [mul_inv_rev, swap_inv]

/-- The preceding block's last array and the next block's first array differ
by the one recorded transposition at the boundary. -/
private theorem sweepArrays_ordered_boundary {α : Type*} [DecidableEq α] (lower : List (α × α))
    (top : α) (s : ℕ → α) (j : ℕ) (start : Perm α) :
    let previous := orderedSweep lower top s j
    let last := executeSwaps previous start
    let τ := swap (s j) top
    sweepArrays (orderedSweep lower top s (j+1)) start =
        sweepArrays previous start ++ sweepArrays lower (τ * last) ∧
      (sweepArrays previous start).getLast? = some last⁻¹ ∧
      (sweepArrays lower (τ * last)).head? = some (last⁻¹ * τ) := by
  obtain ⟨hl, hh⟩ := sweepStates_ordered_boundary lower top s j start
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simp only [sweepArrays, sweepStates_ordered_succ, List.map_append]
  · simp only [sweepArrays, List.getLast?_map, hl, Option.map_some]
  · simp only [sweepArrays, List.head?_map, hh, Option.map_some, mul_inv_rev, swap_inv]

private theorem sweepArrays_isChain {α : Type*} [DecidableEq α] (swaps : List (α × α))
    (start : Perm α) (hdist : ∀ ab ∈ swaps, ab.1 ≠ ab.2) :
    (sweepArrays swaps start).IsChain (fun p q => ∃ a b, a ≠ b ∧ q = p * swap a b) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hlength : (sweepArrays swaps start).length = swaps.length + 1 := by
    simp only [sweepArrays, List.length_map, sweepStates, List.length_scanl]
  have hi' : i < swaps.length := by omega
  have hi₀ : i < (sweepArrays swaps start).length := by omega
  have h := sweepArrays_step swaps start i
  rw [getElem?_pos (sweepArrays swaps start) (i+1) hi,
    getElem?_pos (sweepArrays swaps start) i hi₀, getElem?_pos swaps i hi'] at h
  exact ⟨swaps[i].1, swaps[i].2, hdist _ (List.getElem_mem hi'), Option.some.inj h⟩

/-- Reversal is the lexicographically greatest array on the ordered carrier. -/
private theorem reversal_lex_greatest {n : ℕ} (array : Perm (Fin n)) :
    array = Fin.revPerm ∨
      Pi.Lex (· < ·) (· < ·) (fun i => array i) (fun i => Fin.rev i) := by
  by_cases he : array = Fin.revPerm
  · exact Or.inl he
  right
  have hex : Set.Nonempty {i : Fin n | array i ≠ i.rev} := by
    have hd : ∃ i, array i ≠ i.rev := by
      by_contra! hi
      exact he (Equiv.ext fun i => hi i)
    exact hd
  obtain ⟨i, hi, hmin⟩ := wellFounded_lt.has_min _ hex
  have hearlier (j : Fin n) (hj : j < i) : array j = j.rev := by
    by_contra! hd
    exact hmin j hd hj
  refine ⟨i, hearlier, ?_⟩
  rcases lt_trichotomy (array i) i.rev with ht | ht | ht
  · exact ht
  · exact (hi ht).elim
  · have hj : (array i).rev < i := (Fin.rev_lt_iff.mp ht)
    have hc := hearlier (array i).rev hj
    rw [Fin.rev_rev] at hc
    exact (ne_of_lt hj (array.injective hc)).elim

/-- At size two the separate cyclic/classic branch emits the identity and the
reversal, in that order, with the single swap of positions zero and one. -/
private theorem extremal_arrays_two :
    sweepArrays (extremalSweep 2) 1 = [1, Fin.revPerm] := by
  rw [extremalSweep_two]
  have hs := execute_extremalSweep_two
  rw [extremalSweep_two] at hs
  simp only [sweepArrays, sweepStates, List.scanl_cons, List.scanl_nil, List.map_cons,
    List.map_nil, inv_one]
  change [1, (executeSwaps [(0, 1)] 1)⁻¹] = _
  rw [hs]
  change [1, Fin.revPerm.symm] = _
  rw [Fin.revPerm_symm]

/-- Russo §3.1 and Definition 22, for all sizes congruent to two modulo four.
Arrays are permutations from positions to items in zero-based coordinates. -/
private theorem extremal_sweep_exact (n : ℕ) (hn : 2 ≤ n) (hmod : n % 4 = 2) :
    letI : NeZero n := ⟨by omega⟩
    let swaps := extremalSweep n
    let emitted := sweepArrays swaps 1
    emitted.head? = some 1 ∧
      emitted.Nodup ∧
      (∀ array : Perm (Fin n), array ∈ emitted) ∧
      emitted.length = n.factorial ∧
      emitted.IsChain (fun p q => ∃ a b, a ≠ b ∧ q = p * swap a b) ∧
      (∀ i : ℕ, emitted[i+1]? = (emitted[i]?).bind fun array =>
        swaps[i]?.map fun ab => array * swap ab.1 ab.2) ∧
      emitted.getLast? = some Fin.revPerm ∧
      (executeSwaps swaps 1)⁻¹ = Fin.revPerm ∧
      ∀ array : Perm (Fin n), array = Fin.revPerm ∨
        Pi.Lex (· < ·) (· < ·) (fun i => array i) (fun i => Fin.rev i) := by
  let _ : NeZero n := ⟨by omega⟩
  let swaps := extremalSweep n
  let emitted := sweepArrays swaps 1
  have hprefix : PrefixSweep n swaps := extremal_prefixSweep n hn hmod
  have hnodup : emitted.Nodup := hprefix.nodup.map inv_injective
  have hall (p : Perm (Fin n)) : p ∈ emitted := by
    refine List.mem_map.mpr ⟨p⁻¹, (hprefix.mem_iff _).mpr ?_, inv_inv p⟩
    intro x hx
    exact False.elim (Nat.not_le_of_lt x.isLt hx)
  have hcard : emitted.length = n.factorial := by
    classical
    have huniv : emitted.toFinset = Finset.univ :=
      Finset.eq_univ_of_forall fun p => List.mem_toFinset.mpr (hall p)
    calc
      emitted.length = emitted.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
      _ = n.factorial := by rw [huniv, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have hfinalState : executeSwaps swaps 1 = Fin.revPerm := by
    by_cases htwo : n = 2
    · subst n
      exact execute_extremalSweep_two
    · obtain ⟨hnet, htarget⟩ := execute_extremalSweep_large n (by omega) hmod
      exact hnet.trans htarget
  have hfinalArray : (executeSwaps swaps 1)⁻¹ = Fin.revPerm := by
    rw [hfinalState]
    exact Fin.revPerm_symm
  refine ⟨?_, hnodup, hall, hcard, sweepArrays_isChain swaps 1 ?_,
    sweepArrays_step swaps 1, ?_, hfinalArray, reversal_lex_greatest⟩
  · simp [sweepArrays, sweepStates]
  · intro ab hab
    exact (hprefix.swaps_valid ab hab).2.2
  · change emitted.getLast? = some Fin.revPerm
    have hlast : emitted.getLast? = some ((executeSwaps swaps 1)⁻¹) := by
      simp only [emitted, sweepArrays, List.getLast?_map, sweepStates_last, Option.map_some]
    rw [hlast, hfinalArray]

/-- The residue-two case of Russo's extremal sweep, including its literal
quotient and the ordered emitted list. -/
theorem result :
    (extremalSweep 2 = [(0, 1)] ∧ sweepArrays (extremalSweep 2) 1 = [1, Fin.revPerm]) ∧
    ∀ (n : ℕ) (hn : 2 ≤ n), n % 4 = 2 →
      letI : NeZero n := ⟨by omega⟩
      let swaps := extremalSweep n
      let emitted := sweepArrays swaps 1
      emitted.head? = some 1 ∧
        emitted.Nodup ∧
        (∀ array : Perm (Fin n), array ∈ emitted) ∧
        emitted.length = n.factorial ∧
        emitted.IsChain (fun p q => ∃ a b, a ≠ b ∧ q = p * swap a b) ∧
        (∀ i : ℕ, emitted[i+1]? = (emitted[i]?).bind fun array =>
          swaps[i]?.map fun ab => array * swap ab.1 ab.2) ∧
        emitted.getLast? = some Fin.revPerm ∧
        (executeSwaps swaps 1)⁻¹ = Fin.revPerm ∧
        (∀ array : Perm (Fin n), array = Fin.revPerm ∨
          Pi.Lex (· < ·) (· < ·) (fun i => array i) (fun i => Fin.rev i)) ∧
      (∀ ab ∈ swaps, ab.1 ≠ ab.2) ∧
      (6 ≤ n →
        (literalZ n).IsCycleOn Set.univ ∧
        Function.Bijective (fun j : Fin n => (literalZ n ^ j.val) (slot n (n-1))) ∧
        (∀ j < n-1, (extremalTopPartner n j).val < n-1) ∧
        executeSwaps swaps 1 = actualU n ^ n * literalZ n ∧
        actualU n ^ n * literalZ n = Fin.revPerm ∧
        (∀ j < n-1,
          let lower := penultimateSweep n
          let previous := orderedSweep lower (slot n (n-1)) (extremalTopPartner n) j
          let last := executeSwaps previous 1
          let τ := swap (extremalTopPartner n j) (slot n (n-1))
          sweepArrays (orderedSweep lower (slot n (n-1)) (extremalTopPartner n) (j+1)) 1 =
              sweepArrays previous 1 ++ sweepArrays lower (τ * last) ∧
            (sweepArrays previous 1).getLast? = some last⁻¹ ∧
            (sweepArrays lower (τ * last)).head? = some (last⁻¹ * τ))) := by
  refine ⟨⟨extremalSweep_two, extremal_arrays_two⟩, ?_⟩
  intro n hn hmod
  let _ : NeZero n := ⟨by omega⟩
  obtain ⟨head, nodup, covers, length, chain, step, last, final, largest⟩ :=
    extremal_sweep_exact n hn hmod
  refine ⟨head, nodup, covers, length, chain, step, last, final, largest, ?_, ?_⟩
  · intro ab hab
    exact ((extremal_prefixSweep n hn hmod).swaps_valid ab hab).2.2
  · intro hlarge
    obtain ⟨net, target⟩ := execute_extremalSweep_large n hlarge hmod
    exact ⟨literal_orbit n hlarge hmod, top_parking_order_bijective n hlarge hmod,
      (extremal_top n hlarge hmod).2, net, target,
      fun j _ => sweepArrays_ordered_boundary (penultimateSweep n) (slot n (n-1))
        (extremalTopPartner n) j 1⟩

end D5.S3.Combinatorics.Permutation.RussoExtremalHeap
