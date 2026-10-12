/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryCompatibility
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryCompatibility
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Base-internal three-label boundary tables have safe actual common inverse streams. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCompatibility
open D5.S0.Tower.DBonacci.Names
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells WindowChargeInverse PhysicalWindowDecoder
open OriginalNarrowCost OriginalAcquiredTrace OriginalExecutionBridge DonorCorrection
open FirstWindowBoundaryAttainment FirstWindowBoundaryCodes GlobalPresetObstruction
open scoped BigOperators

/-- A normalized assignment for the six base-internal rows of table 29.19.
The donor coefficient acts only at the actual exterior phase m+1. -/
structure BaseAssignment where
  flip : ZMod 2
  exterior : ZMod 2
  donor : ZMod 2
  left : Pair
  right : Pair
  deriving DecidableEq

/-- Boundary classes 0,1,2 mean base, internal nonbase X, and third label Y. -/
def baseChoice (e t : ZMod 2) (x y : Fin 3) : BaseAssignment :=
  if x = 2 ∧ y = 2 then ⟨0, 0, 0, (t, 1), (0, 1)⟩
  else if x ≠ 0 ∧ y ≠ 0 then
    if t = 1 then ⟨0, 0, 0, (1, 1), (0, 1)⟩
    else ⟨0, 0, 1, (1, if x = 2 then 1 else 0), (1, if y = 2 then 1 else 0)⟩
  else if t = 1 then
    ⟨0, 0, 1, (if x = 2 then 1 else 0, if x = 2 then 1 else 0),
      (if y = 2 then 1 else 0, if y = 2 then 1 else 0)⟩
  else if e = 1 then
    ⟨1, 1, 0, (if x = 2 then 1 else 0, 1), (if y = 2 then 1 else 0, 1)⟩
  else ⟨1, 1, 0, (1, if x = 2 then 1 else 0), (1, if y = 2 then 1 else 0)⟩

private def baseClass (x y : Fin 3) (i : Fin 6) : Fin 3 :=
  if i = 3 then 1 else if i = 4 then x else if i = 5 then y else 0
private def baseRoleCode (a : BaseAssignment) (i : Fin 6) : Pair :=
  if i = 0 then (0, a.exterior) else if i = 1 then (0, a.exterior + a.donor)
  else if i = 2 then (a.flip, 0) else if i = 3 then (1 + a.flip, 0)
  else if i = 4 then a.left else a.right

private theorem base_choice_law : ∀ (e t : ZMod 2) (x y : Fin 3),
    x = 2 ∨ y = 2 →
    let a := baseChoice e t x y
    t + a.flip * e + a.left.1 + a.right.1 = 0 ∧
    a.exterior * (e + 1) + a.donor + a.left.2 + a.right.2 = 0 ∧
    (a.right.2 = 0 ∨ a.exterior + a.donor = 1 ∨ a.right.1 = 0) ∧
    ∀ i j, baseRoleCode a i = baseRoleCode a j → baseClass x y i = baseClass x y j := by
  decide

/-- The first physical row is nonbaseRoot; the second row uses ordered offsets
from m, with offset one equal to the actual donor m+1. -/
def baseSecond (m : ℕ) (a : BaseAssignment) (h : ℕ) : ZMod 2 :=
  a.exterior * supportRow (Finset.Ico 1 m) h + a.donor * supportRow {1} h +
    a.right.2 * supportRow {0} h + a.left.2 * supportRow {m} h

def baseWords (m : ℕ) (S : Finset ℕ) (a : BaseAssignment) : List (Fin m → Bool) :=
  [prefixWord m (nonbaseRoot m S a.flip a.left a.right), prefixWord m (baseSecond m a)]

def baseCode (m : ℕ) (S : Finset ℕ) (a : BaseAssignment) (j : Phase m) : Pair :=
  if j.val = 1 then a.left else if j.val = m then a.right
  else if 2 ≤ j.val ∧ j.val < m then (supportRow S j.val + a.flip, 0)
  else (0, a.exterior + if j.val = m + 1 then a.donor else 0)

private theorem base_even (m : ℕ) (hm : 5 ≤ m) (S : Finset ℕ)
    (inside : ∀ h ∈ S, 2 ≤ h ∧ h < m) (a : BaseAssignment)
    (first : (S.card : ZMod 2) + a.flip * (m : ℕ) + a.left.1 + a.right.1 = 0)
    (second : a.exterior * ((m : ZMod 2) + 1) + a.donor + a.left.2 + a.right.2 = 0) :
    (∑ h ∈ Finset.range (m + 1), nonbaseRoot m S a.flip a.left a.right h) = 0 ∧
    (∑ h ∈ Finset.range (m + 1), baseSecond m a h) = 0 ∧
    nonbaseRoot m S a.flip a.left a.right 0 = 0 := by
  have adaptedFirst : (S.card : ZMod 2) + a.flip * (m : ℕ) +
      (a.left.1, (0 : ZMod 2)).1 + (a.right.1, (m : ZMod 2) + 1).1 = 0 := first
  have adaptedSecond : (m : ZMod 2) + 1 + (a.left.1, (0 : ZMod 2)).2 +
      (a.right.1, (m : ZMod 2) + 1).2 = 0 := by simp [CharTwo.add_self_eq_zero]
  obtain ⟨rootSum, _, rootZero⟩ := nonbase_even m hm S inside a.flip
    (a.left.1, 0) (a.right.1, (m : ZMod 2) + 1) adaptedFirst adaptedSecond
  have rsum := support_sum m (Finset.Ico 1 m) (by intro h hh; simp at hh; omega)
  have onesum := support_sum m {1} (by intro h hh; simp at hh; omega)
  have lastsum := support_sum m {m} (by intro h hh; simp at hh; omega)
  have zerosum := support_sum m {0} (by intro h hh; simp at hh; omega)
  have rm : ((m - 1 : ℕ) : ZMod 2) = (m : ℕ) + 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    simp only [Nat.cast_one, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  refine ⟨by simpa only [nonbaseRoot] using rootSum, ?_, by simpa only [nonbaseRoot] using rootZero⟩
  simp only [baseSecond, Finset.sum_add_distrib, ← Finset.mul_sum,
    rsum, zerosum, onesum, lastsum, Nat.card_Ico, Finset.card_singleton, Nat.cast_one, mul_one, rm]
  simpa only [add_assoc, add_comm, add_left_comm] using second

private theorem base_charges (m : ℕ) (hm : 5 ≤ m) (S : Finset ℕ)
    (inside : ∀ h ∈ S, 2 ≤ h ∧ h < m) (a : BaseAssignment) (j : Phase m) :
    (windowCharge (2 * m - 2) m (nonbaseRoot m S a.flip a.left a.right) j,
     windowCharge (2 * m - 2) m (baseSecond m a) (j - (m : ℕ))) = baseCode m S a j := by
  have shift := shift_value m m hm (by omega) j
  have bound := ZMod.val_lt j
  have firstEq := congrArg Prod.fst (nonbase_charges m hm S inside a.flip a.left a.right j)
  apply Prod.ext
  · have same : (nonbaseCode m S a.flip a.left a.right j).1 = (baseCode m S a j).1 := by
      unfold nonbaseCode baseCode
      split_ifs <;> rfl
    exact firstEq.trans same
  · by_cases one : j.val = 1
    · have localVal : (j - (m : ℕ)).val = m := by rw [shift, if_neg (by omega)]; omega
      simp [windowCharge, localVal, baseSecond, baseCode, one, supportRow,
        show m ≠ 0 by omega, show m ≠ 1 by omega]
    · by_cases last : j.val = m
      · have localVal : (j - (m : ℕ)).val = 0 := by rw [shift, if_pos (by omega)]; omega
        simp [windowCharge, localVal, baseSecond, baseCode, last, supportRow,
          show (0 : ℕ) ≠ m by omega, show m ≠ 1 by omega]
      · by_cases mid : 2 ≤ j.val ∧ j.val < m
        · have localVal : m < (j - (m : ℕ)).val := by rw [shift, if_neg (by omega)]; omega
          simp [windowCharge, baseCode, one, last, mid, localVal]
        · have localVal : 1 ≤ (j - (m : ℕ)).val ∧ (j - (m : ℕ)).val < m := by
            rw [shift]; split_ifs <;> omega
          have donor : (j - (m : ℕ)).val = 1 ↔ j.val = m + 1 := by
            rw [shift]; split_ifs <;> omega
          simp [windowCharge, baseSecond, baseCode, one, last, mid, supportRow, donor,
            localVal, show (j - (m : ℕ)).val ≤ m by omega,
            show (j - (m : ℕ)).val ≠ 0 by omega, show (j - (m : ℕ)).val ≠ m by omega]

theorem base_script_code (m : ℕ) (hm : 5 ≤ m) (S : Finset ℕ)
    (inside : ∀ h ∈ S, 2 ≤ h ∧ h < m) (a : BaseAssignment)
    (first : (S.card : ZMod 2) + a.flip * (m : ℕ) + a.left.1 + a.right.1 = 0)
    (second : a.exterior * ((m : ZMod 2) + 1) + a.donor + a.left.2 + a.right.2 = 0)
    (seam : a.right.2 = 0 ∨ a.exterior + a.donor = 1 ∨ a.right.1 = 0)
    (v : ZMod 2) (j : Phase m) (s : ℕ) (hs : s < 2 * m - 2) :
    endpointDifferences (some v)
      ((scriptArchive (baseWords m S a) (some ⟨v, -j, s⟩)).map Prod.snd) =
      [some (baseCode m S a j).1, some (baseCode m S a j).2] := by
  obtain ⟨rootSum, secondSum, rootZero⟩ := base_even m hm S inside a first second
  obtain ⟨rootInv, rootHead, rootLast, _⟩ := short_window_charge_inverse
    (2 * m - 2) (by omega) m (by omega) (by omega) _ rootSum
  obtain ⟨secondInv, secondHead, _, _⟩ := short_window_charge_inverse
    (2 * m - 2) (by omega) m (by omega) (by omega) _ secondSum
  have headZero := rootHead.mpr rootZero
  obtain ⟨rootStep, rootTail⟩ := InternalZeroSafety.internal_zero_execution
    (2 * m - 2) (by omega) m (by omega) _ ⟨0, by omega⟩ headZero v (-j) s hs (Or.inr headZero)
  have tailBound : tailAfter 0 (prefixWord m (nonbaseRoot m S a.flip a.left a.right)) < 2 * m - 2 := by
    change tailAfter 0 (prefixWord m (nonbaseRoot m S a.flip a.left a.right)) ≤ m - 1 at rootTail
    omega
  have secondStep := by
    show runBits (2 * m - 2) (prefixWord m (baseSecond m a))
      (some ⟨v + wordIncrement (2 * m - 2) (-j) (prefixWord m (nonbaseRoot m S a.flip a.left a.right)),
        -j + (m : ℕ), tailAfter 0 (prefixWord m (nonbaseRoot m S a.flip a.left a.right))⟩) =
      some ⟨v + wordIncrement (2 * m - 2) (-j) (prefixWord m (nonbaseRoot m S a.flip a.left a.right)) +
        wordIncrement (2 * m - 2) (-j + (m : ℕ)) (prefixWord m (baseSecond m a)),
        -j + (m : ℕ) + (m : ℕ), tailAfter 0 (prefixWord m (baseSecond m a))⟩
    rcases seam with clear | toggle | last
    · have head := secondHead.mpr (by simp [baseSecond, supportRow, clear, show (0 : ℕ) ≠ m by omega])
      exact (short_safe_execution (2 * m - 2) (by omega) m (by omega) (by omega) _ _ _ _ tailBound (Or.inr head)).1
    · by_cases clear : a.right.2 = 0
      · have head := secondHead.mpr (by simp [baseSecond, supportRow, clear, show (0 : ℕ) ≠ m by omega])
        exact (short_safe_execution (2 * m - 2) (by omega) m (by omega) (by omega) _ _ _ _ tailBound (Or.inr head)).1
      · have one : a.right.2 = 1 := by
          have bound := ZMod.val_lt a.right.2
          have nonzero := (ZMod.val_ne_zero a.right.2).mpr clear
          exact ZMod.val_injective 2 (by change _ = 1; omega)
        have marked : prefixWord m (baseSecond m a) ⟨1, by omega⟩ = false := by
          simp [prefixWord, Finset.sum_range_succ, baseSecond, supportRow, one,
            show (0 : ℕ) ≠ m by omega, show (1 : ℕ) ≠ m by omega, show 1 < m by omega, toggle,
            CharTwo.add_self_eq_zero]
        exact (InternalZeroSafety.internal_zero_execution (2 * m - 2) (by omega) m (by omega)
          _ ⟨1, by omega⟩ marked _ _ _ tailBound
          (Or.inl (by change tailAfter 0 (prefixWord m (nonbaseRoot m S a.flip a.left a.right)) + 1 < 2 * m - 2; omega))).1
    · have noS : m ∉ S := by intro mem; have := inside m mem; omega
      have lastZero := rootLast.mpr (by
        simp [nonbaseRoot, supportRow, noS, last, show m ≠ 1 by omega])
      have tailZero : tailAfter 0 (prefixWord m (nonbaseRoot m S a.flip a.left a.right)) = 0 := by
        obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
        subst m
        exact last_false_tail n _ 0 lastZero
      rw [tailZero]
      exact (short_safe_execution (2 * m - 2) (by omega) m (by omega) (by omega) _ _ _ _
        (by omega) (Or.inl rfl)).1
  have eq : -j + (m : ℕ) = -(j - (m : ℕ)) := by ring
  simp only [baseWords, scriptArchive, rootStep, secondStep, endpointReading,
    List.map_cons, List.map_nil, endpointDifferences, Option.map_some]
  rw [eq, rootInv, secondInv]
  have charges := base_charges m hm S inside a j
  have firstEq := congrArg Prod.fst charges
  have secondEq := congrArg Prod.snd charges
  simp only [Prod.fst, Prod.snd] at firstEq secondEq
  rw [firstEq, secondEq]
  simp [endpointDifferences]

/-- All six base-internal three-label cases have the normalized table 29.19
literal stream, including its donor, own codes and full inherited-tail safety. -/
private theorem base_internal_attainment {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v)
    (three : (fullImage m H).card = 3) (two : (internalImage m H).card = 2)
    (base : (0 : Pair) ∈ internalImage m H) :
    ∃ (X : Pair) (S : Finset ℕ) (a : BaseAssignment),
      X ≠ 0 ∧ internalImage m H = {0, X} ∧
      S = (Finset.Ico 2 m).filter (fun h => membership m H (h : ℕ) = X) ∧
      a = baseChoice m S.card (classIndex X (membership m H (1 : ℕ)))
        (classIndex X (membership m H (m : ℕ))) ∧
      (∀ h ∈ S, 2 ≤ h ∧ h < m) ∧
      (S.card : ZMod 2) + a.flip * (m : ℕ) + a.left.1 + a.right.1 = 0 ∧
      a.exterior * ((m : ZMod 2) + 1) + a.donor + a.left.2 + a.right.2 = 0 ∧
      (baseWords m S a).length = 2 ∧
      (∀ p q, baseCode m S a p = baseCode m S a q → membership m H p = membership m H q) ∧
      OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2 ∧
      ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
        endpointDifferences (some v)
          ((scriptArchive (baseWords m S a) (some ⟨v, -j, s⟩)).map Prod.snd) =
          [some (baseCode m S a j).1, some (baseCode m S a j).2] ∧
        (scriptArchive (baseWords m S a) (some ⟨v, -j, s⟩)).length = 2 ∧
        ((scriptArchive (baseWords m S a) (some ⟨v, -j, s⟩)).flatMap
          (fun b => List.ofFn b.1)).length = 2 * m := by
  classical
  obtain ⟨X, Xzero, image⟩ : ∃ X : Pair, X ≠ 0 ∧ internalImage m H = {0, X} := by
    obtain ⟨p, q, different, eq⟩ := Finset.card_eq_two.mp two
    have member : p = 0 ∨ q = 0 := by simpa [eq, eq_comm] using base
    rcases member with rfl | rfl
    · exact ⟨q, different.symm, eq⟩
    · exact ⟨p, different, by simpa [Finset.pair_comm] using eq⟩
  have Xfull : X ∈ fullImage m H := by
    have mem : X ∈ internalImage m H := by simp [image]
    obtain ⟨j, _, eq⟩ := Finset.mem_image.mp mem
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, eq⟩
  have zeroFull : (0 : Pair) ∈ fullImage m H := by
    have mem := base
    obtain ⟨j, _, eq⟩ := Finset.mem_image.mp mem
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, eq⟩
  have sub : ({0, X} : Finset Pair) ⊆ fullImage m H := by simp [Finset.insert_subset_iff, zeroFull, Xfull]
  have missing : ∃ Z ∈ fullImage m H, Z ∉ ({0, X} : Finset Pair) := by
    by_contra h
    have fullSub : fullImage m H ⊆ ({0, X} : Finset Pair) := by
      intro Z mem
      by_contra no
      exact h ⟨Z, mem, no⟩
    have bound := Finset.card_le_card fullSub
    simp only [Finset.card_pair Xzero.symm, three] at bound
    omega
  obtain ⟨Z, Zfull, Znot⟩ := missing
  have Zzero : Z ≠ 0 := by intro h; apply Znot; simp [h]
  have ZX : Z ≠ X := by intro h; apply Znot; simp [h]
  have full : fullImage m H = {Z, 0, X} := by
    apply (Finset.eq_of_subset_of_card_le (Finset.insert_subset_iff.mpr ⟨Zfull, sub⟩) ?_).symm
    simp [three, Znot, Xzero.symm]
  have member (j : Phase m) : membership m H j = 0 ∨ membership m H j = X ∨ membership m H j = Z := by
    have mem : membership m H j ∈ fullImage m H := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    simpa [full, or_comm, or_left_comm, or_assoc] using mem
  have internal (j : Phase m) (lo : 2 ≤ j.val) (hi : j.val < m) :
      membership m H j = 0 ∨ membership m H j = X := by
    have mem : membership m H j ∈ internalImage m H :=
      Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, lo, hi⟩, rfl⟩
    simpa [image] using mem
  have outside (j : Phase m) (hj : ¬ (1 ≤ j.val ∧ j.val ≤ m)) : membership m H j = 0 := by
    have absent (v : ZMod 2) : j.val ∉ H v := fun mem => hj (inside v j.val mem)
    simp [membership, supportRow, absent]
  have boundary : membership m H (1 : ℕ) = Z ∨ membership m H (m : ℕ) = Z := by
    obtain ⟨j, _, eq⟩ := Finset.mem_image.mp Zfull
    by_cases one : j.val = 1
    · have cast : j = (1 : ℕ) := ZMod.val_injective _ (one.trans (ZMod.val_natCast_of_lt (by omega)).symm)
      exact Or.inl (cast ▸ eq)
    by_cases last : j.val = m
    · have cast : j = (m : ℕ) := ZMod.val_injective _ (last.trans (ZMod.val_natCast_of_lt (by omega)).symm)
      exact Or.inr (cast ▸ eq)
    by_cases mid : 2 ≤ j.val ∧ j.val < m
    · rcases internal j mid.1 mid.2 with zero | x
      · exact (Zzero (eq.symm.trans zero)).elim
      · exact (ZX (eq.symm.trans x)).elim
    · exact (Zzero (eq.symm.trans (outside j (by omega)))).elim
  let S := (Finset.Ico 2 m).filter (fun h => membership m H (h : ℕ) = X)
  have Sinside : ∀ h ∈ S, 2 ≤ h ∧ h < m := by intro h hh; exact Finset.mem_Ico.mp (Finset.mem_filter.mp hh).1
  let x := classIndex X (membership m H (1 : ℕ))
  let y := classIndex X (membership m H (m : ℕ))
  have allowed : x = 2 ∨ y = 2 := by
    rcases boundary with eq | eq
    · left; change classIndex X (membership m H (1 : ℕ)) = 2; rw [eq]; simp [classIndex, Zzero, ZX]
    · right; change classIndex X (membership m H (m : ℕ)) = 2; rw [eq]; simp [classIndex, Zzero, ZX]
  let a := baseChoice (m : ℕ) S.card x y
  obtain ⟨first, second, seam, separates⟩ := base_choice_law (m : ℕ) S.card x y allowed
  have restore (z : Pair) (mem : z = 0 ∨ z = X ∨ z = Z) : classLabel X Z (classIndex X z) = z :=
    class_restore X Z z Xzero Zzero ZX.symm mem
  let role (j : Phase m) : Fin 6 :=
    if j.val = 1 then 4 else if j.val = m then 5
    else if 2 ≤ j.val ∧ j.val < m then (if membership m H j = X then 3 else 2)
    else if j.val = m + 1 then 1 else 0
  have roleLabel (j : Phase m) : classLabel X Z (baseClass x y (role j)) = membership m H j := by
    have atOne : j.val = 1 → j = (1 : ℕ) := fun eq => ZMod.val_injective _ (eq.trans (ZMod.val_natCast_of_lt (by omega)).symm)
    have atLast : j.val = m → j = (m : ℕ) := fun eq => ZMod.val_injective _ (eq.trans (ZMod.val_natCast_of_lt (by omega)).symm)
    dsimp only [role]
    split_ifs with one last mid isX donor
    · have eq := atOne one; subst j; simpa [baseClass, x] using restore _ (member (1 : ℕ))
    · have eq := atLast last; subst j; simpa [baseClass, y] using restore _ (member (m : ℕ))
    · simp [baseClass, classLabel, isX]
    · have zero := (internal j mid.1 mid.2).resolve_right isX
      simp [baseClass, classLabel, zero]
    · simp [baseClass, classLabel, outside j (by omega)]
    · simp [baseClass, classLabel, outside j (by omega)]
  have roleCode (j : Phase m) : baseCode m S a j = baseRoleCode a (role j) := by
    have cast : ((j.val : ℕ) : Phase m) = j := ZMod.natCast_zmod_val j
    unfold baseCode
    dsimp only [role]
    split_ifs with one last mid isX donor
    · rfl
    · rfl
    · simp [baseRoleCode, supportRow, S, cast, mid, isX, add_comm]
    · simp [baseRoleCode, supportRow, S, cast, isX]
    · rfl
    · simp [baseRoleCode]
  have refines (p q : Phase m) (same : baseCode m S a p = baseCode m S a q) : membership m H p = membership m H q := by
    rw [roleCode p, roleCode q] at same
    exact (roleLabel p).symm.trans ((congrArg (classLabel X Z) (separates _ _ same)).trans (roleLabel q))
  let label (v : ZMod 2) (z : Pair) : Y :=
    if v = 0 then (if z.1 = 0 then A v else B v) else (if z.2 = 0 then A v else B v)
  have labels (v : ZMod 2) (j : Phase m) (s : ℕ) (hs : s < 2 * m - 2) : f (some ⟨v, -j, s⟩) = label v (membership m H j) := by
    rw [target v j s hs]
    have vc : v = 0 ∨ v = 1 := by
      fin_cases v
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases vc with rfl | rfl <;> simp [label, membership, supportRow]
  let decode (v : ZMod 2) (ar : NarrowWindowCost.Archive m) : Y :=
    if h : ∃ j, [some (baseCode m S a j).1, some (baseCode m S a j).2] = endpointDifferences (some v) (ar.map Prod.snd)
    then label v (membership m H (Classical.choose h)) else f none
  have feasible : OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2 := by
    change OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f (baseWords m S a).length
    apply script_global_preset (2 * m - 2) m (by omega) (by omega) alphabet f _ decode
    intro v phase s hs
    have readings := base_script_code m hm S Sinside a first second seam v (-phase) s hs
    simp only [neg_neg] at readings
    have existsPhase : ∃ j, [some (baseCode m S a j).1, some (baseCode m S a j).2] =
        endpointDifferences (some v) ((scriptArchive (baseWords m S a) (some ⟨v, phase, s⟩)).map Prod.snd) := ⟨-phase, readings.symm⟩
    dsimp only [decode]
    rw [dif_pos existsPhase]
    have same := (Classical.choose_spec existsPhase).trans readings
    simp only [List.cons.injEq, Option.some.injEq] at same
    rw [refines _ _ (Prod.ext same.1 same.2.1)]
    simpa only [neg_neg] using (labels v (-phase) s hs).symm
  refine ⟨X, S, a, Xzero, image, rfl, rfl, Sinside, first, second, rfl, refines, feasible, ?_⟩
  intro v j s hs
  refine ⟨base_script_code m hm S Sinside a first second seam v j s hs, ?_, ?_⟩
  · simp [baseWords, scriptArchive]
  · change (archiveWords (scriptArchive (baseWords m S a) (some ⟨v, -j, s⟩))).length = _
    rw [archive_length]
    simp [baseWords, scriptArchive]

/-- The closed relation for all three-label first-window support pairs. -/
def piThree (m : ℕ) (H : ZMod 2 → Finset ℕ) : Prop :=
  (internalImage m H).card ≤ 2 ∧
    (Odd m ∨ membership m H (1 : ℕ) ≠ 0 ∨ membership m H (m : ℕ) ≠ 0)

private theorem image_base_boundaries (m : ℕ) (hm : 5 ≤ m)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (oneZero : membership m H (1 : ℕ) = 0) (lastZero : membership m H (m : ℕ) = 0) :
    fullImage m H = insert 0 (internalImage m H) := by
  classical
  have outside (j : Phase m) (hj : ¬ (1 ≤ j.val ∧ j.val ≤ m)) : membership m H j = 0 := by
    have absent (v : ZMod 2) : j.val ∉ H v := fun mem => hj (inside v j.val mem)
    simp [membership, supportRow, absent]
  apply Finset.Subset.antisymm
  · intro z mem
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp mem
    by_cases one : j.val = 1
    · have cast : j = (1 : ℕ) := ZMod.val_injective _ (one.trans (ZMod.val_natCast_of_lt (by omega)).symm)
      rw [cast, oneZero]
      exact Finset.mem_insert_self _ _
    by_cases last : j.val = m
    · have cast : j = (m : ℕ) := ZMod.val_injective _ (last.trans (ZMod.val_natCast_of_lt (by omega)).symm)
      rw [cast, lastZero]
      exact Finset.mem_insert_self _ _
    by_cases mid : 2 ≤ j.val ∧ j.val < m
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, mid⟩, rfl⟩)
    · rw [outside j (by omega)]
      exact Finset.mem_insert_self _ _
  · intro z mem
    rcases Finset.mem_insert.mp mem with rfl | mem
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, outside 0 (by simp)⟩
    · obtain ⟨j, _, eq⟩ := Finset.mem_image.mp mem
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, eq⟩

private theorem three_compatibility {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v)
    (three : (fullImage m H).card = 3) :
    OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2 ↔ piThree m H := by
  classical
  constructor
  · intro feasible
    obtain ⟨_, _, _, _, _, _, _, _, bound⟩ :=
      (original_first_window_boundary_rows m hm alphabet H inside A B distinct f target).1 feasible
    refine ⟨bound, ?_⟩
    by_cases oneZero : membership m H (1 : ℕ) = 0
    · by_cases lastZero : membership m H (m : ℕ) = 0
      · have image := image_base_boundaries m hm H inside oneZero lastZero
        have nonbase : (0 : Pair) ∉ internalImage m H := by
          intro mem
          have fullCard : (fullImage m H).card = (internalImage m H).card := by
            rw [image, Finset.insert_eq_of_mem mem]
          omega
        have two : (internalImage m H).card = 2 := by
          have fullCard := congrArg Finset.card image
          rw [Finset.card_insert_of_notMem nonbase] at fullCard
          omega
        exact (original_first_window_nonbase_internal_stream m hm alphabet H inside A B distinct f target
          three two nonbase).1 feasible
      · exact Or.inr (Or.inr lastZero)
    · exact Or.inr (Or.inl oneZero)
  · rintro ⟨bound, admitted⟩
    have nonempty : (internalImage m H).Nonempty := by
      have val : ((2 : ℕ) : Phase m).val = 2 := ZMod.val_natCast_of_lt (by omega)
      exact ⟨membership m H (2 : ℕ), Finset.mem_image.mpr
        ⟨(2 : ℕ), Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [val]; omega⟩, rfl⟩⟩
    have positive := Finset.card_pos.mpr nonempty
    by_cases one : (internalImage m H).card = 1
    · exact ((original_first_window_boundary_rows m hm alphabet H inside A B distinct f target).2.2 one).1
    · have two : (internalImage m H).card = 2 := by omega
      by_cases base : (0 : Pair) ∈ internalImage m H
      · obtain ⟨X, S, a, _, _, _, _, _, _, _, _, _, feasible, _⟩ :=
          base_internal_attainment m hm alphabet H inside A B distinct f target three two base
        exact feasible
      · obtain ⟨S, flip, left, right, _, _, _, _, _, feasible, _⟩ :=
          (original_first_window_nonbase_internal_stream m hm alphabet H inside A B distinct f target
            three two base).2 admitted
        exact feasible

/-- The full three-label closed compatibility relation, with the complete
base-internal table as an actual normalized physical construction. -/
theorem original_first_window_three_label_compatibility {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v)
    (three : (fullImage m H).card = 3) :
    (OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2 ↔ piThree m H) ∧
    (∀ (two : (internalImage m H).card = 2) (base : (0 : Pair) ∈ internalImage m H),
    ∃ (X : Pair) (S : Finset ℕ) (a : BaseAssignment),
      X ≠ 0 ∧ internalImage m H = {0, X} ∧
      S = (Finset.Ico 2 m).filter (fun h => membership m H (h : ℕ) = X) ∧
      a = baseChoice m S.card (classIndex X (membership m H (1 : ℕ)))
        (classIndex X (membership m H (m : ℕ))) ∧
      (∀ h ∈ S, 2 ≤ h ∧ h < m) ∧
      (S.card : ZMod 2) + a.flip * (m : ℕ) + a.left.1 + a.right.1 = 0 ∧
      a.exterior * ((m : ZMod 2) + 1) + a.donor + a.left.2 + a.right.2 = 0 ∧
      (baseWords m S a).length = 2 ∧
      (∀ p q, baseCode m S a p = baseCode m S a q → membership m H p = membership m H q) ∧
      OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2 ∧
      ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
        endpointDifferences (some v)
          ((scriptArchive (baseWords m S a) (some ⟨v, -j, s⟩)).map Prod.snd) =
          [some (baseCode m S a j).1, some (baseCode m S a j).2] ∧
        (scriptArchive (baseWords m S a) (some ⟨v, -j, s⟩)).length = 2 ∧
        ((scriptArchive (baseWords m S a) (some ⟨v, -j, s⟩)).flatMap
          (fun b => List.ofFn b.1)).length = 2 * m) := by
  exact ⟨three_compatibility m hm alphabet H inside A B distinct f target three,
    base_internal_attainment m hm alphabet H inside A B distinct f target three⟩

#print axioms original_first_window_three_label_compatibility

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCompatibility
