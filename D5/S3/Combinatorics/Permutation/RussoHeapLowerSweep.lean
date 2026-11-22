/- GID: D5/S3/Combinatorics/Permutation/RussoHeapLowerSweep
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/RussoHeapLowerSweep
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered lower sweeps and their penultimate net. -/

import Mathlib.Data.Fin.Rev
import Mathlib.Data.List.OfFn
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.Chain

open Equiv Equiv.Perm

namespace D5.S3.Combinatorics.Permutation.RussoHeapLowerSweep

/- Russo v1, §3.1 and Lemma 14. Positions below use zero-based Fin coordinates.
Each block starts after the preceding lower call and its following physical swap. -/
private def blockStarts {α : Type*} [DecidableEq α] (C : Perm α) (top : α) (s : ℕ → α) :
    ℕ → Perm α
  | 0 => 1
  | j + 1 => swap (s j) top * C * blockStarts C top s j

private def orderedNet {α : Type*} [DecidableEq α] (C : Perm α) (top : α) (s : ℕ → α)
    (rounds : ℕ) : Perm α :=
  C * blockStarts C top s rounds

/- Theorem 18(a). Each swap partner is computed at the end of the preceding
lower call, using the current state of the prescribed parked item. -/
private def parkingStarts {α : Type*} [DecidableEq α] (C : Perm α) (top : α) (e : ℕ → α) :
    ℕ → Perm α
  | 0 => 1
  | j + 1 =>
    let θ := parkingStarts C top e j
    swap (C (θ (e j))) top * C * θ

def parkingPartner {α : Type*} [DecidableEq α] (C : Perm α) (top : α) (e : ℕ → α)
    (j : ℕ) : α :=
  C (parkingStarts C top e j (e j))

private theorem blockStarts_parking {α : Type*} [DecidableEq α]
    (C : Perm α) (top : α) (e : ℕ → α) (j : ℕ) :
    blockStarts C top (parkingPartner C top e) j = parkingStarts C top e j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [blockStarts, parkingStarts, parkingPartner, ih]

def path {α : Type*} (top : α) (e : ℕ → α) (j : ℕ) : List α :=
  top :: List.ofFn (fun i : Fin j => e i.val)

def parked {α : Type*} (top : α) (e : ℕ → α) : ℕ → α
  | 0 => top
  | j + 1 => e j

private theorem parkingStarts_parked {α : Type*} [DecidableEq α]
    (C : Perm α) (top : α) (e : ℕ → α) (j : ℕ) :
    parkingStarts C top e j (parked top e j) = top := by
  cases j <;> simp [parkingStarts, parked, Perm.mul_apply, swap_apply_left]

private theorem path_succ {α : Type*} (top : α) (e : ℕ → α) (j : ℕ) :
    path top e (j + 1) = path top e j ++ [e j] := by
  unfold path
  rw [List.ofFn_succ', List.concat_eq_append]
  rfl

private theorem path_formPerm_succ {α : Type*} [DecidableEq α]
    (top : α) (e : ℕ → α) (j : ℕ) :
    (path top e (j + 1)).formPerm = (path top e j).formPerm * swap (parked top e j) (e j) := by
  cases j with
  | zero => simp [path, parked, List.formPerm]
  | succ j =>
    rw [path_succ top e (j + 1), path_succ top e j]
    simpa only [List.append_assoc, List.cons_append, List.nil_append, parked] using
      List.formPerm_append_pair (path top e j) (e j) (e (j + 1))

private theorem parkingStarts_eq {α : Type*} [DecidableEq α]
    (C : Perm α) (top : α) (e : ℕ → α) (hC : C top = top) (j : ℕ) :
    parkingStarts C top e j = C ^ j * (path top e j).formPerm := by
  induction j with
  | zero => simp [parkingStarts, path, List.formPerm]
  | succ j ih =>
    have hpark : (C * parkingStarts C top e j) (parked top e j) = top := by
      rw [Perm.mul_apply, parkingStarts_parked, hC]
    calc
      parkingStarts C top e (j + 1) =
          (C * parkingStarts C top e j) * swap (e j) (parked top e j) := by
        rw [mul_swap_eq_swap_mul, hpark, Perm.mul_apply, parkingStarts, mul_assoc]
      _ = C ^ (j + 1) * (path top e (j + 1)).formPerm := by
        simp only [ih, path_formPerm_succ, pow_succ', swap_comm (e j), mul_assoc]

private theorem parking_net {α : Type*} [DecidableEq α]
    (C : Perm α) (top : α) (e : ℕ → α) (hC : C top = top) (j : ℕ) :
    orderedNet C top (parkingPartner C top e) j = C ^ (j + 1) * (path top e j).formPerm := by
  rw [orderedNet, blockStarts_parking, parkingStarts_eq C top e hC, pow_succ', mul_assoc]

private theorem parkingPartner_eq {α : Type*} [DecidableEq α]
    (C : Perm α) (top : α) (e : ℕ → α) (hC : C top = top) (j : ℕ)
    (he : e j ∉ path top e j) : parkingPartner C top e j = (C ^ (j + 1)) (e j) := by
  rw [parkingPartner, parkingStarts_eq C top e hC, pow_succ', Perm.mul_apply, Perm.mul_apply,
    List.formPerm_apply_of_notMem he]

private theorem orderedNet_congr {α : Type*} [DecidableEq α]
    (C : Perm α) (top : α) (s t : ℕ → α) (j : ℕ) (h : ∀ i < j, s i = t i) :
    orderedNet C top s j = orderedNet C top t j := by
  suffices blockStarts C top s j = blockStarts C top t j by
    simp only [orderedNet, this]
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [blockStarts, h j (by omega), ih (fun i hi => h i (by omega))]

abbrev slot (N : ℕ) [NeZero N] (i : ℕ) : Fin N := Fin.ofNat N i

theorem slot_val {N i : ℕ} [NeZero N] (hi : i < N) :
    (slot N i).val = i := Nat.mod_eq_of_lt hi

def initial (N : ℕ) [NeZero N] (k : ℕ) : List (Fin N) :=
  List.ofFn (fun i : Fin k => slot N i.val)

private theorem initial_succ (N : ℕ) [NeZero N] (k : ℕ) :
    initial N (k + 1) = initial N k ++ [slot N k] := by
  unfold initial
  rw [List.ofFn_succ', List.concat_eq_append]
  rfl

theorem initial_nodup {N k : ℕ} [NeZero N] (hk : k ≤ N) :
    (initial N k).Nodup := by
  rw [initial, List.Nodup, List.pairwise_ofFn]
  intro i j hij h
  have hi := slot_val (N := N) (lt_of_lt_of_le i.isLt hk)
  have hj := slot_val (N := N) (lt_of_lt_of_le j.isLt hk)
  have he := congrArg Fin.val h
  rw [hi, hj] at he
  exact (ne_of_lt hij) (Fin.ext he)

private theorem mem_initial {N k : ℕ} [NeZero N] (hk : k ≤ N) (x : Fin N) :
    x ∈ initial N k ↔ x.val < k := by
  rw [initial, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    rw [slot_val (lt_of_lt_of_le i.isLt hk)]
    exact i.isLt
  · intro hx
    exact ⟨⟨x.val, hx⟩, Fin.ext (slot_val x.isLt)⟩

private theorem rotation_power {N k : ℕ} [NeZero N] (hk : k ≤ N) :
    (initial N k).formPerm ^ k = 1 := by
  have h := List.formPerm_pow_length_eq_one_of_nodup (initial N k) (initial_nodup hk)
  have hlength : (initial N k).length = k := List.length_ofFn
  rwa [hlength] at h

private theorem path_slot_cycle {N k : ℕ} [NeZero N] (hk : k < N) :
    (path (slot N k) (slot N) k).formPerm = (initial N (k + 1)).formPerm := by
  have hnd : (path (slot N k) (slot N) k).Nodup := by
    change (slot N k :: initial N k).Nodup
    rw [List.nodup_cons, mem_initial (by omega), slot_val hk]
    exact ⟨Nat.lt_irrefl k, initial_nodup (by omega)⟩
  rw [← List.formPerm_rotate_one _ hnd, initial_succ]
  change ((slot N k :: initial N k).rotate 1).formPerm =
    (initial N k ++ [slot N k]).formPerm
  rw [List.rotate_cons_succ, List.rotate_zero]

/- Definition 3. The index k is the physical top position, so this is level k+1.
At k=1 the first branch for an even level supplies the single partner 0. -/
def cyclicPartner (N : ℕ) [NeZero N] (k j : ℕ) : Fin N :=
  slot N (if k % 2 = 0 then 0 else if j = 0 then k - 1 else if j + 1 = k then 0 else j)

private def cyclicNet (N : ℕ) [NeZero N] : ℕ → Perm (Fin N)
  | 0 => 1
  | k + 1 =>
    orderedNet (cyclicNet N k) (slot N (k + 1)) (cyclicPartner N (k + 1)) (k + 1)

private theorem starts_constant {α : Type*} [DecidableEq α]
    (C : Perm α) (a top : α) (j : ℕ) :
    blockStarts C top (fun _ => a) j = (swap a top * C) ^ j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [blockStarts, pow_succ', ih]

private theorem rotation_add_top {N k : ℕ} [NeZero N] (hk : 0 < k) :
    swap (slot N 0) (slot N k) * (initial N k).formPerm =
      (path (slot N k) (slot N) k).formPerm := by
  cases k with
  | zero => omega
  | succ k =>
    change _ = (slot N (k + 1) :: List.ofFn (fun i : Fin (k + 1) => slot N i.val)).formPerm
    rw [List.ofFn_succ]
    rw [List.formPerm_cons_cons, swap_comm (slot N 0)]
    congr 1
    rw [initial, List.ofFn_succ]

private theorem cyclic_odd_level {N k : ℕ} [NeZero N] (hk : 0 < k) (hN : k < N)
    (he : k % 2 = 0) :
    orderedNet (initial N k).formPerm (slot N k) (cyclicPartner N k) k =
      swap (slot N 0) (slot N k) := by
  rw [orderedNet_congr _ _ _ (fun _ => slot N 0) k (fun j _ => by simp [cyclicPartner, he])]
  rw [orderedNet, starts_constant]
  let C := (initial N k).formPerm
  let τ := swap (slot N 0) (slot N k)
  change C * (τ * C)^k = τ
  have hcycle : (τ * C)^(k+1) = 1 := by
    dsimp only [τ, C]
    rw [rotation_add_top hk, path_slot_cycle hN]
    exact rotation_power (by omega)
  calc
    C * (τ * C)^k = τ * ((τ * C)^(k+1)) := by
      rw [pow_succ', ← mul_assoc, ← mul_assoc, swap_mul_self, one_mul]
    _ = τ := by rw [hcycle, mul_one]

private theorem slot_eq_iff {N i j : ℕ} [NeZero N] (hi : i < N) (hj : j < N) :
    slot N i = slot N j ↔ i = j := by
  constructor
  · intro h
    simpa only [slot_val hi, slot_val hj] using congrArg Fin.val h
  · rintro rfl
    rfl

private theorem cyclic_even_partner {N k : ℕ} [NeZero N] (hN : k < N)
    (ho : k % 2 = 1)
    (hfix : swap (slot N 0) (slot N (k - 1)) (slot N k) = slot N k)
    (hsq : swap (slot N 0) (slot N (k - 1)) ^ 2 = 1) :
    let C := swap (slot N 0) (slot N (k - 1))
    let top := slot N k
    ∀ j < k, cyclicPartner N k j = parkingPartner C top (slot N) j := by
  let C := swap (slot N 0) (slot N (k - 1))
  let top := slot N k
  change ∀ j < k, cyclicPartner N k j = parkingPartner C top (slot N) j
  intro j hj
  rw [parkingPartner_eq C top (slot N) hfix]
  · rw [pow_eq_pow_mod _ hsq]
    unfold cyclicPartner
    rw [ite_eq_right (by omega : ¬ k % 2 = 0)]
    by_cases hj0 : j = 0
    · subst j
      simp [swap_apply_left]
    · by_cases hjlast : j + 1 = k
      · have hmod : (j + 1) % 2 = 1 := by omega
        have hj' : j = k - 1 := by omega
        rw [ite_eq_right hj0, ite_eq_left hjlast, hmod, pow_one, hj']
        exact (swap_apply_right _ _).symm
      · simp only [ite_eq_right hj0, ite_eq_right hjlast]
        by_cases hpar : (j + 1) % 2 = 0
        · simp [hpar]
        · have hmod : (j + 1) % 2 = 1 := by omega
          rw [hmod, pow_one]
          symm
          apply swap_apply_of_ne_of_ne
          · exact fun h => hj0 ((slot_eq_iff (by omega : j < N) (by omega)).1 h)
          · intro h
            have := (slot_eq_iff (by omega : j < N) (by omega)).1 h
            omega
  · change slot N j ∉ top :: initial N j
    rw [List.mem_cons, mem_initial (by omega), slot_val (by omega : j < N)]
    simp only [top, slot_eq_iff (by omega : j < N) hN]
    omega

private theorem cyclic_even_level {N k : ℕ} [NeZero N] (hN : k < N)
    (ho : k % 2 = 1) :
    orderedNet (swap (slot N 0) (slot N (k - 1))) (slot N k) (cyclicPartner N k) k =
      (initial N (k + 1)).formPerm := by
  let C := swap (slot N 0) (slot N (k - 1))
  let top := slot N k
  have hfix : C top = top := by
    apply swap_apply_of_ne_of_ne
    · simpa only [top, ne_eq, slot_eq_iff hN (by omega : 0 < N)] using (show k ≠ 0 by omega)
    · simpa only [top, ne_eq, slot_eq_iff hN (by omega : k-1 < N)] using (show k ≠ k-1 by omega)
  have hsq : C ^ 2 = 1 := by rw [pow_two, swap_mul_self]
  have hp := cyclic_even_partner hN ho hfix hsq
  change orderedNet C top (cyclicPartner N k) k = _
  rw [orderedNet_congr _ _ _ _ _ hp, parking_net C top (slot N) hfix,
    pow_eq_pow_mod (k+1) hsq, show (k+1) % 2 = 0 by omega, pow_zero, one_mul]
  exact path_slot_cycle hN

private theorem cyclic_net_formula {N : ℕ} [NeZero N] (k : ℕ) (hN : k < N) :
    cyclicNet N k =
      if k % 2 = 0 then swap (slot N 0) (slot N k) else (initial N (k + 1)).formPerm := by
  induction k with
  | zero => simp [cyclicNet, swap_self, Equiv.Perm.one_def]
  | succ k ih =>
    rw [cyclicNet, ih (by omega)]
    by_cases h : (k + 1) % 2 = 0
    · rw [ite_eq_left h, ite_eq_right (by omega : ¬ k % 2 = 0)]
      exact cyclic_odd_level (by omega) hN h
    · rw [ite_eq_right h, ite_eq_left (by omega : k % 2 = 0)]
      exact cyclic_even_level hN (by omega)

/- Definition 22, residue class 2. The n-1 sweep runs cyclic level n-2
in the same ambient carrier, so its last position is fixed by construction. -/
def penultimateItem (n : ℕ) [NeZero n] (j : ℕ) : Fin n :=
  let m := (n - 2) / 2
  slot n (if j < m then j else 3 * m - 1 - j)

/- Physical swap sequence of §3.1. A level-one call performs no swaps.
At every higher level, the next round appends one swap and another lower call. -/
def orderedSweep {α : Type*} (lower : List (α × α)) (top : α) (s : ℕ → α) :
    ℕ → List (α × α)
  | 0 => lower
  | j + 1 => orderedSweep lower top s j ++ (s j, top) :: lower

def executeSwaps {α : Type*} [DecidableEq α] (swaps : List (α × α)) (start : Perm α) :
    Perm α :=
  swaps.foldl (fun state (a, b) => swap a b * state) start

def cyclicSweep (N : ℕ) [NeZero N] : ℕ → List (Fin N × Fin N)
  | 0 => []
  | k + 1 =>
    orderedSweep (cyclicSweep N k) (slot N (k + 1)) (cyclicPartner N (k + 1)) (k + 1)

private theorem executeSwaps_mul {α : Type*} [DecidableEq α] (swaps : List (α × α))
    (p q : Perm α) : executeSwaps swaps (p * q) = executeSwaps swaps p * q := by
  induction swaps generalizing p with
  | nil => rfl
  | cons ab swaps ih =>
    cases ab with
    | mk a b =>
      change executeSwaps swaps (swap a b * (p * q)) = executeSwaps swaps (swap a b * p) * q
      rw [← mul_assoc, ih]

private theorem executeSwaps_start {α : Type*} [DecidableEq α] (swaps : List (α × α))
    (start : Perm α) : executeSwaps swaps start = executeSwaps swaps 1 * start := by
  simpa only [one_mul] using executeSwaps_mul swaps 1 start

private theorem execute_orderedSweep {α : Type*} [DecidableEq α] (lower : List (α × α))
    (top : α) (s : ℕ → α) (j : ℕ) :
    executeSwaps (orderedSweep lower top s j) 1 = orderedNet (executeSwaps lower 1) top s j := by
  induction j with
  | zero => simp [orderedSweep, orderedNet, blockStarts]
  | succ j ih =>
    rw [orderedSweep]
    simp only [executeSwaps, List.foldl_append, List.foldl_cons]
    change executeSwaps lower (swap (s j) top * executeSwaps (orderedSweep lower top s j) 1) = _
    rw [ih, executeSwaps_start]
    simp only [orderedNet, blockStarts, mul_assoc]
    rfl

/-- The net of an ordered sweep with partners computed from the parked items. -/
theorem executeParkingSweep {α : Type*} [DecidableEq α]
    (lower : List (α × α)) (top : α) (e : ℕ → α)
    (hfix : executeSwaps lower 1 top = top) (j : ℕ) :
    let C := executeSwaps lower 1
    executeSwaps (orderedSweep lower top (parkingPartner C top e) j) 1 =
      C ^ (j + 1) * (path top e j).formPerm := by
  dsimp only
  rw [execute_orderedSweep, parking_net _ _ _ hfix]

private theorem execute_cyclicSweep (N : ℕ) [NeZero N] (k : ℕ) :
    executeSwaps (cyclicSweep N k) 1 = cyclicNet N k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [cyclicSweep, execute_orderedSweep, ih, cyclicNet]

/-- The penultimate sweep uses Definition 22's item order and Theorem 18(a)'s
partner recipe, with the actual cyclic sweep as its lower call. -/
def penultimateSweep (n : ℕ) [NeZero n] : List (Fin n × Fin n) :=
  let lower := cyclicSweep n (n-3)
  let top := slot n (n-2)
  orderedSweep lower top (parkingPartner (executeSwaps lower 1) top (penultimateItem n)) (n-2)

/-- Net of the actual penultimate sweep on the ambient carrier. -/
def actualU (n : ℕ) [NeZero n] : Perm (Fin n) :=
  executeSwaps (penultimateSweep n) 1

private theorem actualU_blocks (n : ℕ) [NeZero n] :
    actualU n =
      let C := cyclicNet n (n - 3)
      let top := slot n (n - 2)
      orderedNet C top (parkingPartner C top (penultimateItem n)) (n - 2) := by
  simp only [actualU, penultimateSweep, execute_orderedSweep, execute_cyclicSweep]

def literalZ (n : ℕ) [NeZero n] : Perm (Fin n) :=
  actualU n ^ (-(n : ℤ)) * Fin.revPerm

private def A (m : ℕ) : Perm (Fin (2*m+2)) := (initial (2*m+2) (2*m)).formPerm
private def B (m : ℕ) : Perm (Fin (2*m+2)) :=
  (path (slot (2*m+2) (2*m)) (penultimateItem (2*m+2)) (2*m)).formPerm

private theorem init_fixes {N k : ℕ} [NeZero N] (hk : k ≤ N) {x : Fin N}
    (hx : k ≤ x.val) : (initial N k).formPerm x = x :=
  List.formPerm_apply_of_notMem (fun h => (Nat.not_lt_of_ge hx) ((mem_initial hk x).1 h))

private theorem literal_net_AB (m : ℕ) (hm : 2 ≤ m) :
    actualU (2*m+2) = A m * B m := by
  have hsub : 2*m+2-3 = 2*m-1 := by omega
  have hpred : 2*m-1+1 = 2*m := by omega
  have htop : 2*m+2-2 = 2*m := by omega
  rw [actualU_blocks]
  dsimp only
  rw [hsub, htop, cyclic_net_formula _ (by omega), ite_eq_right (by omega), hpred]
  have hfix : A m (slot (2*m+2) (2*m)) = slot (2*m+2) (2*m) := by
    apply init_fixes (by omega)
    rw [slot_val (by omega : 2*m < 2*m+2)]
  change orderedNet (A m) (slot (2*m+2) (2*m))
    (parkingPartner (A m) (slot (2*m+2) (2*m)) (penultimateItem (2*m+2))) (2*m) = _
  rw [parking_net _ _ _ hfix]
  change A m ^ (2*m+1) * B m = _
  rw [pow_succ, show A m ^ (2*m) = 1 from rotation_power (by omega), one_mul]

theorem formPerm_ofFn_pow {α : Type*} [DecidableEq α] (label : ℕ → α) {L : ℕ}
    (h : (List.ofFn (fun i : Fin L => label i.val)).Nodup) (p i : ℕ) (hi : i < L) :
    ((List.ofFn (fun j : Fin L => label j.val)).formPerm ^ p) (label i) =
      label ((i+p)%L) := by
  let l := List.ofFn (fun j : Fin L => label j.val)
  have hl : i < l.length := by simpa [l] using hi
  simpa only [l, List.length_ofFn, List.getElem_ofFn] using
    List.formPerm_pow_apply_getElem l h p i hl

theorem nodup_ofFn_labels {α : Type*} (label : ℕ → α) {L : ℕ}
    (hinj : ∀ i < L, ∀ j < L, label i = label j → i = j) :
    (List.ofFn (fun i : Fin L => label i.val)).Nodup := by
  rw [List.Nodup, List.pairwise_ofFn]
  intro i j hij h
  exact (ne_of_lt hij) (Fin.ext (hinj _ i.isLt _ j.isLt h))

private theorem A_value (m : ℕ) (hm : 2 ≤ m) (x : Fin (2*m+2)) :
    (A m x).val = if x.val + 1 < 2*m then x.val+1 else if x.val < 2*m then 0 else x.val := by
  by_cases hx : x.val < 2*m
  · have hx' : slot (2*m+2) x.val = x := Fin.ext (slot_val x.isLt)
    have hpow := formPerm_ofFn_pow (slot (2*m+2)) (initial_nodup (by omega : 2*m ≤ 2*m+2)) 1 x.val hx
    rw [pow_one, hx'] at hpow
    change A m x = _ at hpow
    rw [hpow, slot_val (lt_trans (Nat.mod_lt _ (by omega : 0 < 2*m)) (by omega))]
    by_cases hs : x.val+1 < 2*m
    · rw [ite_eq_left hs, Nat.mod_eq_of_lt hs]
    · rw [ite_eq_right hs, ite_eq_left hx, show x.val+1=2*m by omega, Nat.mod_self]
  · rw [show A m x = x from init_fixes (by omega) (by omega), ite_eq_right (by omega), ite_eq_right hx]

private def bLabel (m i : ℕ) : ℕ :=
  if i = 0 then 2*m else if i ≤ m then i-1 else 3*m-i

private theorem bLabel_lt {m i : ℕ} (hi : i < 2*m+1) :
    bLabel m i < 2*m+2 := by
  unfold bLabel
  split_ifs <;> omega

private theorem bPath_eq_list (m : ℕ) :
    path (slot (2*m+2) (2*m)) (penultimateItem (2*m+2)) (2*m) =
      List.ofFn (fun i : Fin (2*m+1) => slot (2*m+2) (bLabel m i.val)) := by
  unfold path
  rw [List.ofFn_succ]
  simp only [Fin.val_zero, bLabel, ite_true, List.cons.injEq, true_and]
  apply congrArg List.ofFn
  funext i
  have hsub : (2*m+2-2)/2 = m := by omega
  simp only [penultimateItem, hsub, Fin.val_succ, Nat.add_one_ne_zero, ite_false]
  have hiff : i.val + 1 ≤ m ↔ i.val < m := by omega
  by_cases hi : i.val < m
  · simp [hi, hiff]
  · have he : 3*m-1-i.val = 3*m-(i.val+1) := by omega
    simp [hi, hiff, he]

private theorem B_eq_list (m : ℕ) :
    B m = (List.ofFn (fun i : Fin (2*m+1) => slot (2*m+2) (bLabel m i.val))).formPerm :=
  congrArg List.formPerm (bPath_eq_list m)

private theorem bLabel_inj {m i j : ℕ} (hm : 2 ≤ m) (hi : i < 2*m+1) (hj : j < 2*m+1)
    (h : slot (2*m+2) (bLabel m i) = slot (2*m+2) (bLabel m j)) : i = j := by
  have he := (slot_eq_iff (bLabel_lt hi) (bLabel_lt hj)).1 h
  unfold bLabel at he
  split_ifs at he <;> omega

private theorem bList_nodup (m : ℕ) (hm : 2 ≤ m) :
    (List.ofFn (fun i : Fin (2*m+1) => slot (2*m+2) (bLabel m i.val))).Nodup :=
  nodup_ofFn_labels (fun i => slot (2*m+2) (bLabel m i))
    (fun _ hi _ hj h => bLabel_inj hm hi hj h)

private theorem penultimate_physical_partner_lt (m : ℕ) (hm : 2 ≤ m) (j : ℕ) (hj : j < 2*m) :
    (parkingPartner (cyclicNet (2*m+2) (2*m+2-3)) (slot (2*m+2) (2*m))
      (penultimateItem (2*m+2)) j).val < 2*m := by
  let N := 2*m+2
  let top := slot N (2*m)
  let e := penultimateItem N
  have hc : cyclicNet N (N-3) = A m := by
    have hN : N = 2*m+2 := rfl
    rw [cyclic_net_formula _ (by omega), ite_eq_right (by omega)]
    have h : N-3+1 = 2*m := by omega
    rw [h]
    rfl
  have ht : A m top = top := init_fixes (by omega) (by
    change 2*m ≤ (slot N (2*m)).val
    rw [slot_val (by omega : 2*m < N)])
  have he (i : ℕ) : e i = slot N (bLabel m (i+1)) := by
    change penultimateItem N i = _
    have hhalf : (N-2)/2 = m := by omega
    simp only [penultimateItem, hhalf, bLabel, Nat.add_one_ne_zero, ite_false]
    by_cases hi : i < m
    · simp [hi, show i+1 ≤ m by omega]
    · simp [hi, show ¬ i+1 ≤ m by omega, show 3*m-1-i = 3*m-(i+1) by omega]
  have hfresh : e j ∉ path top e j := by
    rw [path, List.mem_cons, List.mem_ofFn]
    rintro (h | ⟨i, h⟩)
    · have heq : slot N (bLabel m (j+1)) = slot N (bLabel m 0) := by
        simpa [he, top, bLabel] using h
      have := bLabel_inj hm (by omega : j+1 < 2*m+1) (by omega : 0 < 2*m+1) heq
      omega
    · have hi := i.isLt
      rw [he _, he _] at h
      have := bLabel_inj hm (by omega : i.val+1 < 2*m+1) (by omega : j+1 < 2*m+1) h
      omega
  have heBound : (e j).val < 2*m := by
    rw [he, show (slot N (bLabel m (j+1))).val = bLabel m (j+1) from
      slot_val (bLabel_lt (by omega : j+1 < 2*m+1))]
    simp only [bLabel, Nat.add_one_ne_zero, ite_false]
    split_ifs <;> omega
  change (parkingPartner (cyclicNet N (N-3)) top e j).val < 2*m
  rw [hc, parkingPartner_eq _ _ _ ht j hfresh]
  by_contra h
  let y := (A m ^ (j+1)) (e j)
  have hy : 2*m ≤ y.val := by omega
  have hfix (d : ℕ) : (A m ^ d) y = y := by
    induction d with
    | zero => simp
    | succ d ih =>
      rw [pow_succ', Perm.mul_apply, ih]
      exact init_fixes (by omega) hy
  have hh : e j = y := (A m ^ (j+1)).injective (hfix (j+1)).symm
  rw [hh] at heBound
  omega

private theorem B_step (m : ℕ) (hm : 2 ≤ m) (i : ℕ) (hi : i < 2*m+1)
    (x : Fin (2*m+2)) (hx : x.val = bLabel m i) :
    (B m x).val = bLabel m ((i+1)%(2*m+1)) := by
  have he : slot (2*m+2) (bLabel m i) = x := Fin.ext ((slot_val (bLabel_lt hi)).trans hx.symm)
  have hp := formPerm_ofFn_pow (fun j => slot (2*m+2) (bLabel m j)) (bList_nodup m hm) 1 i hi
  rw [pow_one, he] at hp
  rw [B_eq_list, hp, slot_val (bLabel_lt (Nat.mod_lt _ (by omega)))]

private theorem B_value (m : ℕ) (hm : 2 ≤ m) (x : Fin (2*m+2)) :
    (B m x).val =
      if x.val = 2*m then 0 else if x.val+1 < m then x.val+1
      else if x.val+1 = m then 2*m-1 else if x.val = m then 2*m
      else if x.val < 2*m then x.val-1 else x.val := by
  by_cases htop : x.val = 2*m
  · rw [ite_eq_left htop, B_step m hm 0 (by omega) x (by simp [bLabel, htop]),
      Nat.mod_eq_of_lt (by omega : 0+1 < 2*m+1)]
    simp [bLabel, show 1 ≤ m by omega]
  · rw [ite_eq_right htop]
    by_cases hx : x.val < m
    · rw [B_step m hm (x.val+1) (by omega) x (by
          simp [bLabel, show x.val+1 ≤ m by omega]),
        Nat.mod_eq_of_lt (by omega : x.val+1+1 < 2*m+1)]
      by_cases hs : x.val+1 < m
      · simp [bLabel, hs, show x.val+1+1 ≤ m by omega]
      · have hh : x.val+1=m := by omega
        rw [ite_eq_right hs, ite_eq_left hh]
        simp only [bLabel, show x.val+1+1 ≠ 0 by omega, ite_false,
          ite_eq_right (by omega : ¬ x.val+1+1 ≤ m)]
        omega
    · rw [ite_eq_right (by omega : ¬ x.val+1 < m),
        ite_eq_right (by omega : ¬ x.val+1 = m)]
      by_cases hm' : x.val = m
      · have he : x.val = bLabel m (2*m) := by
          simp only [bLabel, show 2*m ≠ 0 by omega, ite_false,
            ite_eq_right (by omega : ¬2*m ≤ m)]
          omega
        rw [ite_eq_left hm', B_step m hm (2*m) (by omega) x he, Nat.mod_self]
        simp [bLabel]
      · rw [ite_eq_right hm']
        by_cases hb : x.val < 2*m
        · have he : x.val = bLabel m (3*m-x.val) := by
            simp only [bLabel, show 3*m-x.val ≠ 0 by omega, ite_false,
              ite_eq_right (by omega : ¬ 3*m-x.val ≤ m)]
            omega
          rw [ite_eq_left hb, B_step m hm (3*m-x.val) (by omega) x he,
            Nat.mod_eq_of_lt (by omega : 3*m-x.val+1 < 2*m+1)]
          simp only [bLabel, show 3*m-x.val+1 ≠ 0 by omega, ite_false,
            ite_eq_right (by omega : ¬3*m-x.val+1 ≤ m)]
          omega
        · rw [ite_eq_right hb]
          have hfixed : B m x = x := by
            rw [B_eq_list]
            apply List.formPerm_apply_of_notMem
            rw [List.mem_ofFn]
            rintro ⟨i, hi⟩
            have hval := congrArg Fin.val hi
            rw [slot_val (bLabel_lt i.isLt)] at hval
            have hib := i.isLt
            unfold bLabel at hval
            split_ifs at hval <;> omega
          rw [hfixed]

def uArrow (m x : ℕ) : ℕ :=
  if x = 2*m then 1 else if x+1 < m then x+2 else if x+1 = m then 0
  else if x = m then 2*m else x

theorem literal_net_value (m : ℕ) (hm : 2 ≤ m) (x : Fin (2*m+2)) :
    (actualU (2*m+2) x).val = uArrow m x.val := by
  rw [literal_net_AB m hm, Perm.mul_apply, A_value m hm, B_value m hm]
  unfold uArrow
  split_ifs <;> omega

/-- §3.1 emits the starting state and then the state immediately after each
physical swap. Composition is on the left because states send items to positions. -/
def sweepStates {α : Type*} [DecidableEq α] (swaps : List (α × α)) (start : Perm α) :
    List (Perm α) :=
  swaps.scanl (fun state (a, b) => swap a b * state) start

private theorem sweepStates_last {α : Type*} [DecidableEq α] (swaps : List (α × α))
    (start : Perm α) :
    (sweepStates swaps start).getLast? = some (executeSwaps swaps start) :=
  List.getLast?_scanl

private theorem sweepStates_mul {α : Type*} [DecidableEq α] (swaps : List (α × α))
    (p q : Perm α) :
    sweepStates swaps (p * q) = (sweepStates swaps p).map (· * q) := by
  induction swaps generalizing p with
  | nil => rfl
  | cons ab swaps ih =>
    simp only [sweepStates, List.scanl_cons, List.map_cons]
    rw [← mul_assoc]
    exact congrArg (List.cons (p * q)) (ih (swap ab.1 ab.2 * p))

/-- The recursive call before round `j` emits through its terminal state.
The next block starts with that state left-multiplied by the scheduled swap. -/
theorem sweepStates_ordered_succ {α : Type*} [DecidableEq α] (lower : List (α × α))
    (top : α) (s : ℕ → α) (j : ℕ) (start : Perm α) :
    sweepStates (orderedSweep lower top s (j + 1)) start =
      sweepStates (orderedSweep lower top s j) start ++
        sweepStates lower (swap (s j) top * executeSwaps (orderedSweep lower top s j) start) := by
  simp only [orderedSweep, sweepStates, executeSwaps, List.scanl_append, List.scanl_cons,
    List.tail_cons]

/-- Block `j+1` emits exactly the ordered lower call translated by its block start. -/
private theorem sweepStates_ordered_block {α : Type*} [DecidableEq α] (lower : List (α × α))
    (top : α) (s : ℕ → α) (j : ℕ) :
    sweepStates (orderedSweep lower top s (j + 1)) 1 =
      sweepStates (orderedSweep lower top s j) 1 ++
        (sweepStates lower 1).map (· * blockStarts (executeSwaps lower 1) top s (j + 1)) := by
  rw [sweepStates_ordered_succ, execute_orderedSweep]
  rw [orderedNet, ← mul_assoc]
  exact congrArg (sweepStates (orderedSweep lower top s j) 1 ++ ·)
    (by simpa only [one_mul, blockStarts] using
      sweepStates_mul lower 1 (blockStarts (executeSwaps lower 1) top s (j + 1)))

/-- The subgroup of states that fix every position outside the first `count`. -/
def FixesOutside {N : ℕ} (count : ℕ) (p : Perm (Fin N)) : Prop :=
  ∀ x : Fin N, count ≤ x.val → p x = x

private theorem fixesOutside_mul {N count : ℕ} {p q : Perm (Fin N)}
    (hp : FixesOutside count p) (hq : FixesOutside count q) : FixesOutside count (p * q) :=
  fun x hx => by rw [Perm.mul_apply, hq x hx, hp x hx]

private theorem fixesOutside_inv {N count : ℕ} {p : Perm (Fin N)}
    (hp : FixesOutside count p) : FixesOutside count p⁻¹ :=
  fun x hx => by apply p.injective; simp [hp x hx]

private theorem fixesOutside_mono {N k l : ℕ} {p : Perm (Fin N)}
    (hp : FixesOutside k p) (hkl : k ≤ l) : FixesOutside l p :=
  fun x hx => hp x (hkl.trans hx)

private theorem fixesOutside_swap {N count : ℕ} {a b : Fin N}
    (ha : a.val < count) (hb : b.val < count) : FixesOutside count (swap a b) := by
  intro x hx
  exact swap_apply_of_ne_of_ne (by rintro rfl; omega) (by rintro rfl; omega)

private theorem inverse_top_lt {N k : ℕ} [NeZero N] (hk : k < N)
    {p : Perm (Fin N)} (hp : FixesOutside (k+1) p) :
    (p⁻¹ (slot N k)).val < k + 1 := by
  by_contra! h
  have he := hp (p⁻¹ (slot N k)) h
  rw [show p (p⁻¹ (slot N k)) = slot N k from p.apply_symm_apply _] at he
  rw [← he, slot_val hk] at h
  omega

private theorem blockStarts_fixesOutside {N k rounds : ℕ} [NeZero N] (hk : k < N)
    {C : Perm (Fin N)} (hC : FixesOutside k C) {s : ℕ → Fin N}
    (hs : ∀ j < rounds, (s j).val < k) :
    FixesOutside (k+1) (blockStarts C (slot N k) s rounds) := by
  induction rounds with
  | zero => intro x _; rfl
  | succ rounds ih =>
    rw [blockStarts]
    exact fixesOutside_mul
      (fixesOutside_mul (fixesOutside_swap (by have := hs rounds (by omega); omega)
        (by rw [slot_val hk]; omega)) (fixesOutside_mono hC (by omega)))
      (ih (fun j hj => hs j (by omega)))

/-- At a fixed block start, the right translate of the lower subgroup is exactly
the fiber of the inverse item at the top, within the current active positions. -/
private theorem block_fiber {N k : ℕ} [NeZero N] (hk : k < N)
    {θ p : Perm (Fin N)} (hθ : FixesOutside (k+1) θ) :
    (∃ h : Perm (Fin N), FixesOutside k h ∧ h * θ = p) ↔
      FixesOutside (k+1) p ∧ p⁻¹ (slot N k) = θ⁻¹ (slot N k) := by
  have htop : (slot N k).val = k := slot_val hk
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨fixesOutside_mul (fixesOutside_mono hh (by omega)) hθ, ?_⟩
    apply (h * θ).injective
    calc
      (h * θ) ((h * θ)⁻¹ (slot N k)) = slot N k := (h * θ).apply_symm_apply _
      _ = h (θ (θ⁻¹ (slot N k))) := by
        rw [show θ (θ⁻¹ (slot N k)) = slot N k from θ.apply_symm_apply _,
          hh (slot N k) (by omega)]
      _ = (h * θ) (θ⁻¹ (slot N k)) := rfl
  · rintro ⟨hp, hf⟩
    refine ⟨p * θ⁻¹, ?_, by simp [mul_assoc]⟩
    intro x hx
    by_cases hgt : k + 1 ≤ x.val
    · exact fixesOutside_mul hp (fixesOutside_inv hθ) x hgt
    · have he : x = slot N k := Fin.ext (by omega)
      rw [he, Perm.mul_apply, ← hf]
      exact p.apply_symm_apply _

/-- A complete lower call lists precisely the smaller subgroup, once per state.
Every physical swap is internal to the prefix and uses distinct positions. -/
structure PrefixSweep {N : ℕ} (k : ℕ) (swaps : List (Fin N × Fin N)) : Prop where
  nodup : (sweepStates swaps 1).Nodup
  mem_iff : ∀ p, p ∈ sweepStates swaps 1 ↔ FixesOutside k p
  swaps_valid : ∀ ab ∈ swaps, ab.1.val < k ∧ ab.2.val < k ∧ ab.1 ≠ ab.2

/-- A complete lower call fixes every position outside its prefix. -/
theorem prefixNet_fixes {N k : ℕ} {lower : List (Fin N × Fin N)}
    (hlower : PrefixSweep k lower) : FixesOutside k (executeSwaps lower 1) :=
  (hlower.mem_iff _).mp (List.mem_of_getLast? (sweepStates_last _ _))

private theorem orderedSweep_valid {N k rounds : ℕ} [NeZero N] (hk : k < N)
    {lower : List (Fin N × Fin N)} (hlower : PrefixSweep k lower) {s : ℕ → Fin N}
    (hs : ∀ j < rounds, (s j).val < k) :
    ∀ ab ∈ orderedSweep lower (slot N k) s rounds,
      ab.1.val < k+1 ∧ ab.2.val < k+1 ∧ ab.1 ≠ ab.2 := by
  induction rounds with
  | zero =>
    intro ab hab
    obtain ⟨ha, hb, hne⟩ := hlower.swaps_valid ab hab
    exact ⟨by omega, by omega, hne⟩
  | succ rounds ih =>
    intro ab hab
    rw [orderedSweep, List.mem_append, List.mem_cons] at hab
    rcases hab with h | rfl | h
    · exact ih (fun j hj => hs j (by omega)) ab h
    · have ha := hs rounds (by omega)
      have hb := slot_val hk
      change (s rounds).val < k+1 ∧ (slot N k).val < k+1 ∧ s rounds ≠ slot N k
      refine ⟨by omega, by omega, fun he => ?_⟩
      have := congrArg Fin.val he
      exact (Nat.ne_of_lt (show (s rounds).val < (slot N k).val by omega)) this
    · obtain ⟨ha, hb, hne⟩ := hlower.swaps_valid ab h
      exact ⟨by omega, by omega, hne⟩

/-- For each prefix of rounds, the emissions are disjoint fibers indexed by the
inverse images of the top position under the corresponding block starts. -/
private theorem sweep_fibers {N k rounds : ℕ} [NeZero N] (hk : k < N)
    {lower : List (Fin N × Fin N)} (hlower : PrefixSweep k lower) {s : ℕ → Fin N}
    (hs : ∀ j < rounds, (s j).val < k)
    (hdist : ∀ i ≤ rounds, ∀ j ≤ rounds,
      (blockStarts (executeSwaps lower 1) (slot N k) s i)⁻¹ (slot N k) =
        (blockStarts (executeSwaps lower 1) (slot N k) s j)⁻¹ (slot N k) → i = j) :
    let θ := blockStarts (executeSwaps lower 1) (slot N k) s
    let emitted := sweepStates (orderedSweep lower (slot N k) s rounds) 1
    emitted.Nodup ∧ ∀ p, p ∈ emitted ↔
      FixesOutside (k+1) p ∧ ∃ j ≤ rounds, p⁻¹ (slot N k) = (θ j)⁻¹ (slot N k) := by
  let θ := blockStarts (executeSwaps lower 1) (slot N k) s
  induction rounds with
  | zero =>
    refine ⟨hlower.nodup, fun p => (hlower.mem_iff p).trans ?_⟩
    have hθ : FixesOutside (k+1) (θ 0) := by intro x _; rfl
    have hf := block_fiber (p := p) hk hθ
    change FixesOutside k p ↔ FixesOutside (k+1) p ∧
      ∃ j ≤ 0, p⁻¹ (slot N k) = (θ j)⁻¹ (slot N k)
    simpa only [Nat.le_zero, exists_eq_left, θ, blockStarts, mul_one, exists_eq_right] using hf
  | succ rounds ih =>
    have hsmall := fun j (hj : j < rounds) => hs j (by omega)
    have hind := ih hsmall (fun i hi j hj => hdist i (by omega) j (by omega))
    have hθ : FixesOutside (k+1) (θ (rounds+1)) :=
      blockStarts_fixesOutside hk (prefixNet_fixes hlower) hs
    have hblock (p : Perm (Fin N)) :
        p ∈ (sweepStates lower 1).map (· * θ (rounds+1)) ↔
          FixesOutside (k+1) p ∧ p⁻¹ (slot N k) = (θ (rounds+1))⁻¹ (slot N k) := by
      simpa only [List.mem_map, hlower.mem_iff] using block_fiber (p := p) hk hθ
    dsimp only at hind ⊢
    rw [sweepStates_ordered_block]
    refine ⟨List.nodup_append'.mpr ⟨hind.1, ?_, ?_⟩, ?_⟩
    · exact hlower.nodup.map (mul_left_injective _)
    · intro p hp hp'
      obtain ⟨_, i, hi, he⟩ := (hind.2 p).mp hp
      have hb := ((hblock p).mp hp').2
      have := hdist i (by omega) (rounds+1) (by omega) (he.symm.trans hb)
      omega
    · intro p
      rw [List.mem_append, hind.2, hblock]
      constructor
      · rintro (⟨hp, i, hi, he⟩ | ⟨hp, he⟩)
        · exact ⟨hp, i, by omega, he⟩
        · exact ⟨hp, rounds+1, by omega, he⟩
      · rintro ⟨hp, i, hi, he⟩
        by_cases h : i ≤ rounds
        · exact Or.inl ⟨hp, i, h, he⟩
        · have hi' : i = rounds+1 := by omega
          exact Or.inr ⟨hp, hi' ▸ he⟩

/-- There are as many distinct parked items as active positions, so their
fibers cover precisely the larger subgroup. -/
private theorem prefixSweep_ordered {N k : ℕ} [NeZero N] (hk : k < N)
    {lower : List (Fin N × Fin N)} (hlower : PrefixSweep k lower) {s : ℕ → Fin N}
    (hs : ∀ j < k, (s j).val < k)
    (hdist : ∀ i ≤ k, ∀ j ≤ k,
      (blockStarts (executeSwaps lower 1) (slot N k) s i)⁻¹ (slot N k) =
        (blockStarts (executeSwaps lower 1) (slot N k) s j)⁻¹ (slot N k) → i = j) :
    PrefixSweep (k+1) (orderedSweep lower (slot N k) s k) := by
  let θ := blockStarts (executeSwaps lower 1) (slot N k) s
  have hθ (j : Fin (k+1)) : FixesOutside (k+1) (θ j.val) :=
    blockStarts_fixesOutside hk (prefixNet_fixes hlower) (fun i hi => hs i (by have := j.isLt; omega))
  let parkedIndex (j : Fin (k+1)) : Fin (k+1) :=
    ⟨((θ j.val)⁻¹ (slot N k)).val, inverse_top_lt hk (hθ j)⟩
  have hinj : Function.Injective parkedIndex := by
    intro i j h
    apply Fin.ext
    exact hdist _ (by have := i.isLt; omega) _ (by have := j.isLt; omega)
      (Fin.ext (congrArg (fun z : Fin (k+1) => z.val) h))
  have hsurj := Finite.surjective_of_injective hinj
  have hf := sweep_fibers hk hlower hs hdist
  refine ⟨hf.1, fun p => (hf.2 p).trans ?_, orderedSweep_valid hk hlower hs⟩
  constructor
  · exact And.left
  · intro hp
    obtain ⟨j, hj⟩ := hsurj ⟨(p⁻¹ (slot N k)).val, inverse_top_lt hk hp⟩
    have hval := congrArg (fun z : Fin (k+1) => z.val) hj
    exact ⟨hp, j.val, by have := j.isLt; omega, Fin.ext hval.symm⟩

private theorem parking_inverse {α : Type*} [DecidableEq α]
    (C : Perm α) (top : α) (e : ℕ → α) (j : ℕ) :
    (blockStarts C top (parkingPartner C top e) j)⁻¹ top = parked top e j := by
  rw [blockStarts_parking]
  apply (parkingStarts C top e j).injective
  exact ((parkingStarts C top e j).apply_symm_apply top).trans
    (parkingStarts_parked C top e j).symm

private theorem parkingPartner_ne_top {α : Type*} [DecidableEq α]
    {C : Perm α} {top : α} {e : ℕ → α} (hC : C top = top) {j : ℕ}
    (hj : parked top e (j+1) ≠ parked top e j) :
    parkingPartner C top e j ≠ top := by
  intro h
  apply hj
  apply (parkingStarts C top e j).injective
  change parkingStarts C top e j (e j) = parkingStarts C top e j (parked top e j)
  rw [parkingStarts_parked]
  exact C.injective (h.trans hC.symm)

/-- An injective parking order extends a complete prefix sweep by one position.
The computed partners all lie strictly below that new position. -/
theorem extendParkingSweep {N k : ℕ} [NeZero N] (hk : k + 1 = N)
    {lower : List (Fin N × Fin N)} (hlower : PrefixSweep k lower) (e : ℕ → Fin N)
    (he : ∀ i ≤ k, ∀ j ≤ k, parked (slot N k) e i = parked (slot N k) e j → i = j) :
    let s := parkingPartner (executeSwaps lower 1) (slot N k) e
    PrefixSweep (k + 1) (orderedSweep lower (slot N k) s k) ∧
      ∀ j < k, (s j).val < k := by
  have hlt : k < N := by omega
  let C := executeSwaps lower 1
  let top := slot N k
  let s := parkingPartner C top e
  have hfix : C top = top := prefixNet_fixes hlower _ (by rw [slot_val hlt])
  have hpartner (j : ℕ) (hj : j < k) : (s j).val < k := by
    have hne : s j ≠ top :=
      parkingPartner_ne_top hfix (fun h => Nat.succ_ne_self j (he (j + 1)
        (by omega) j (by omega) h))
    have hval := (s j).isLt
    have htop := slot_val hlt
    by_contra! h
    exact hne (Fin.ext (by omega))
  refine ⟨prefixSweep_ordered hlt hlower hpartner ?_, hpartner⟩
  intro i hi j hj h
  rw [parking_inverse, parking_inverse] at h
  exact he i hi j hj h

private theorem cyclicPartner_lt {N k : ℕ} [NeZero N] (hN : k < N) {j : ℕ} (hj : j < k) :
    (cyclicPartner N k j).val < k := by
  have hval (i : ℕ) (hi : i < k) : (slot N i).val < k := by rw [slot_val (hi.trans hN)]; exact hi
  unfold cyclicPartner
  split_ifs <;> exact hval _ (by omega)

private theorem cyclic_starts_parked_inj {N k : ℕ} [NeZero N] (hk : 0 < k)
    (hN : k < N) :
    ∀ i ≤ k, ∀ j ≤ k,
      (blockStarts (cyclicNet N (k-1)) (slot N k) (cyclicPartner N k) i)⁻¹ (slot N k) =
        (blockStarts (cyclicNet N (k-1)) (slot N k) (cyclicPartner N k) j)⁻¹ (slot N k) →
      i = j := by
  rw [cyclic_net_formula _ (by omega)]
  by_cases hpar : k % 2 = 0
  · rw [ite_eq_right (by omega : ¬ (k-1) % 2 = 0), show k-1+1 = k by omega]
    let C := (initial N k).formPerm
    let R := (initial N (k+1)).formPerm
    have hpartners : cyclicPartner N k = fun _ => slot N 0 := by
      funext j
      simp only [cyclicPartner, hpar, ite_true]
    have hrotation : swap (slot N 0) (slot N k) * C = R := by
      rw [rotation_add_top hk, path_slot_cycle hN]
    rw [hpartners]
    have hpark (i : ℕ) (hi : i ≤ k) :
        (blockStarts C (slot N k) (fun _ => slot N 0) i)⁻¹ (slot N k) = slot N (k-i) := by
      rw [starts_constant, hrotation]
      apply (R ^ i).injective
      rw [show (R ^ i) ((R ^ i)⁻¹ (slot N k)) = slot N k from (R ^ i).apply_symm_apply _]
      change slot N k = ((initial N (k+1)).formPerm ^ i) (slot N (k-i))
      rw [initial, formPerm_ofFn_pow (slot N) (initial_nodup (by omega : k+1 ≤ N)) i (k-i) (by omega)]
      rw [show (k-i+i) % (k+1) = k by rw [Nat.sub_add_cancel hi, Nat.mod_eq_of_lt (by omega)]]
    intro i hi j hj he
    rw [hpark i hi, hpark j hj] at he
    have h := (slot_eq_iff (by omega : k-i < N) (by omega : k-j < N)).mp he
    omega
  · rw [ite_eq_left (by omega : (k-1) % 2 = 0)]
    let C := swap (slot N 0) (slot N (k-1))
    let top := slot N k
    have hfix : C top = top := fixesOutside_swap (count := k)
      (by rw [slot_val (by omega : 0 < N)]; omega)
      (by rw [slot_val (by omega : k-1 < N)]; omega) _ (by rw [slot_val hN])
    have hsq : C ^ 2 = 1 := by rw [pow_two, swap_mul_self]
    have hstarts (i : ℕ) (hi : i ≤ k) :
        blockStarts C top (cyclicPartner N k) i =
          blockStarts C top (parkingPartner C top (slot N)) i := by
      have he := orderedNet_congr C top _ _ i
        (fun j hj => cyclic_even_partner hN (by omega) hfix hsq j (hj.trans_le hi))
      exact mul_left_cancel he
    have hpark (i : ℕ) (hi : i ≤ k) :
        ((blockStarts C top (cyclicPartner N k) i)⁻¹ top).val =
          if i = 0 then k else i-1 := by
      rw [hstarts i hi, parking_inverse]
      cases i with
      | zero => exact slot_val hN
      | succ i =>
        simp only [parked, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
        exact slot_val (by omega)
    intro i hi j hj he
    have hval := congrArg Fin.val he
    rw [hpark i hi, hpark j hj] at hval
    split_ifs at hval <;> omega

theorem cyclic_prefixSweep (N : ℕ) [NeZero N] (k : ℕ) (hk : k < N) :
    PrefixSweep (k+1) (cyclicSweep N k) := by
  induction k with
  | zero =>
    refine ⟨by simp [cyclicSweep, sweepStates], ?_, by simp [cyclicSweep]⟩
    intro p
    change p ∈ ([1] : List (Perm (Fin N))) ↔ FixesOutside 1 p
    simp only [List.mem_singleton]
    constructor
    · rintro rfl x _
      rfl
    · intro hp
      apply Equiv.ext
      intro x
      by_cases hx : 1 ≤ x.val
      · exact hp x hx
      · change p x = x
        by_contra hne
        have hx' : 1 ≤ (p x).val := by
          by_contra! h
          exact hne (Fin.ext (by omega))
        exact hne (p.injective (hp (p x) hx'))
  | succ k ih =>
    rw [cyclicSweep]
    refine prefixSweep_ordered hk (ih (by omega)) (fun _ hj => cyclicPartner_lt hk hj) ?_
    rw [execute_cyclicSweep]
    simpa only [Nat.add_sub_cancel] using
      cyclic_starts_parked_inj (N := N) (by omega : 0 < k+1) hk

private theorem penultimate_parked_inj (m : ℕ) (hm : 2 ≤ m)
    (i : ℕ) (hi : i ≤ 2*m) (j : ℕ) (hj : j ≤ 2*m)
    (h : parked (slot (2*m+2) (2*m)) (penultimateItem (2*m+2)) i =
      parked (slot (2*m+2) (2*m)) (penultimateItem (2*m+2)) j) : i = j := by
  have hlabel (d : ℕ) :
      parked (slot (2*m+2) (2*m)) (penultimateItem (2*m+2)) d =
        slot (2*m+2) (bLabel m d) := by
    cases d with
    | zero => rfl
    | succ d =>
      change penultimateItem (2*m+2) d = _
      simp only [penultimateItem, show (2*m+2-2)/2 = m by omega, bLabel,
        Nat.add_one_ne_zero, ite_false]
      by_cases hd : d < m
      · simp only [hd, show d+1 ≤ m by omega, ite_true, Nat.add_sub_cancel]
      · simp only [hd, show ¬ d+1 ≤ m by omega, ite_false]
        rw [show 3*m-1-d = 3*m-(d+1) by omega]
  rw [hlabel, hlabel] at h
  exact bLabel_inj hm (by omega) (by omega) h

theorem penultimate_prefixSweep (n : ℕ) [NeZero n] (hn : 6 ≤ n) (hmod : n % 4 = 2) :
    PrefixSweep (n-1) (penultimateSweep n) := by
  obtain ⟨m, hm, rfl⟩ : ∃ m : ℕ, 2 ≤ m ∧ n = 2*m+2 :=
    ⟨(n-2)/2, by omega, by omega⟩
  have hlower := cyclic_prefixSweep (2*m+2) (2*m+2-3) (by omega)
  have hdim : 2*m+2-3+1 = 2*m+2-2 := by omega
  rw [hdim] at hlower
  have hdim' : (2*m+2-2)+1 = 2*m+2-1 := by omega
  rw [← hdim', penultimateSweep]
  refine prefixSweep_ordered (by omega) hlower ?_ ?_
  · intro j hj
    rw [execute_cyclicSweep, show 2*m+2-2 = 2*m by omega]
    exact penultimate_physical_partner_lt m hm j (by omega)
  · intro i hi j hj he
    rw [parking_inverse, parking_inverse, show 2*m+2-2 = 2*m by omega] at he
    exact penultimate_parked_inj m hm i (by omega) j (by omega) he

end D5.S3.Combinatorics.Permutation.RussoHeapLowerSweep
