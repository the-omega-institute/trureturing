/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryPrice
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryPrice
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Original first-window support normalization and actual-source fee laws. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryFourLabels
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAdaptive
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryPrice
open D5.S0.Tower.DBonacci.Names
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells WindowChargeInverse PhysicalWindowDecoder
open OriginalNarrowCost OriginalAcquiredTrace OriginalExecutionBridge DonorCorrection
open FirstWindowBoundaryAttainment FirstWindowBoundaryCodes FirstWindowBoundaryCompatibility FirstWindowBoundaryFourLabels GlobalPresetObstruction
open scoped BigOperators

private theorem erase_card_ge_two {α : Type*} [DecidableEq α]
    (K : Finset α) (hK : 3 ≤ K.card) (d : α) : 2 ≤ (K.erase d).card := by
  by_cases hd : d ∈ K
  · have h := Finset.card_erase_add_one hd
    omega
  · have htwo : 2 ≤ K.card := by omega
    simpa [hd] using htwo

private theorem r_one_true (m : ℕ) (hm : 5 ≤ m)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (four : (fullImage m H).card = 4)
    (r : (internalImage m H).card = 1) : piFour m H := by
  classical
  have sub := image_regions m hm H inside
  have erase : ((internalImage m H).erase (pivot m H)).card ≤ 1 := by
    exact (Finset.card_le_card (Finset.erase_subset _ _)).trans (by omega)
  have base : (0 : Pair) ∉ internalImage m H := by
    intro hz
    obtain ⟨a, eqK⟩ := Finset.card_eq_one.mp r
    have az : a = (0 : Pair) := by
      have ha : a ∈ ({a} : Finset Pair) := by simp
      have hz' : (0 : Pair) ∈ ({a} : Finset Pair) := by rwa [← eqK]
      exact (Finset.mem_singleton.mp hz').symm
    subst a
    have sub3 : fullImage m H ⊆ ({0, membership m H (1 : ℕ), membership m H (m : ℕ)} : Finset Pair) := by
      rw [sub, eqK]
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq ⊢
      tauto
    have cb := Finset.card_le_card sub3
    have c3 := Finset.card_le_three (a := (0 : Pair))
      (b := membership m H (1 : ℕ)) (c := membership m H (m : ℕ))
    omega
  exact ⟨erase, by simp [base]⟩

private theorem r_ge_three_false (m : ℕ) (H : ZMod 2 → Finset ℕ)
    (r : 3 ≤ (internalImage m H).card) : ¬ piFour m H := by
  intro h
  have er := erase_card_ge_two (internalImage m H) r (pivot m H)
  change ((internalImage m H).erase (pivot m H)).card ≤ 1 ∧ _ at h
  omega

private theorem membership_zero (m : ℕ) (H : ZMod 2 → Finset ℕ) (j : Phase m) :
    membership m H j = 0 ↔ j.val ∉ H 0 ∪ H 1 := by
  classical
  by_cases a : j.val ∈ H 0 <;> by_cases b : j.val ∈ H 1 <;>
    simp [membership, supportRow, a, b, Prod.ext_iff]

private theorem fullImage_one (m : ℕ) (hm : 5 ≤ m)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m) :
    (fullImage m H).card = 1 ↔ H 0 = ∅ ∧ H 1 = ∅ := by
  classical
  have base : (0 : Pair) ∈ fullImage m H := by
    rw [image_regions m hm H inside]; simp
  constructor
  · intro one
    obtain ⟨z, eq⟩ := Finset.card_eq_one.mp one
    have ze : z = (0 : Pair) := by
      have : (0 : Pair) = z := by simpa [eq] using base
      exact this.symm
    have singleton : fullImage m H = {0} := by simpa [ze] using eq
    have empty (v : ZMod 2) : H v = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro h mem
      have bound := inside v h mem
      have val : ((h : ℕ) : Phase m).val = h := ZMod.val_natCast_of_lt (by omega)
      have label : membership m H (h : ℕ) = 0 := by
        have member : membership m H (h : ℕ) ∈ fullImage m H :=
          Finset.mem_image.mpr ⟨(h : ℕ), Finset.mem_univ _, rfl⟩
        simpa [singleton] using member
      have absent := (membership_zero m H (h : ℕ)).mp label
      have values : v = 0 ∨ v = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) v
      rcases values with rfl | rfl
      · exact absent (by simp [val, mem])
      · exact absent (by simp [val, mem])
    exact ⟨empty 0, empty 1⟩
  · rintro ⟨zero, one⟩
    have image : fullImage m H = {0} := by
      ext z
      simp only [fullImage, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨j, rfl⟩; simp [membership, supportRow, zero, one]
      · intro eq; exact ⟨0, by simp [membership, supportRow, zero, one, eq]⟩
    simp [image]

private theorem fullImage_two (m : ℕ) (hm : 5 ≤ m)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (two : (fullImage m H).card = 2) :
    ∃ z : Pair, z ≠ 0 ∧ fullImage m H = {0, z} ∧
      (∀ j : Phase m, membership m H j = if j.val ∈ H 0 ∪ H 1 then z else 0) ∧
      (∀ v : ZMod 2, H v = ∅ ∨ H v = H 0 ∪ H 1) ∧
      ∃ v : ZMod 2, H v = H 0 ∪ H 1 := by
  classical
  have base : (0 : Pair) ∈ fullImage m H := by rw [image_regions m hm H inside]; simp
  have er : ((fullImage m H).erase 0).card = 1 := by
    have := Finset.card_erase_add_one base; omega
  obtain ⟨z, single⟩ := Finset.card_eq_one.mp er
  have nonzero : z ≠ 0 := by
    have mem : z ∈ (fullImage m H).erase 0 := by simp [single]
    exact (Finset.mem_erase.mp mem).1
  have image : fullImage m H = {0, z} := by
    rw [← Finset.insert_erase base, single]
  have table (j : Phase m) : membership m H j = if j.val ∈ H 0 ∪ H 1 then z else 0 := by
    by_cases mem : j.val ∈ H 0 ∪ H 1
    · rw [if_pos mem]
      have label : membership m H j ∈ fullImage m H := Finset.mem_image.mpr ⟨j, by simp, rfl⟩
      rw [image] at label
      rcases Finset.mem_insert.mp label with zero | other
      · exact ((membership_zero m H j).mp zero mem).elim
      · exact Finset.mem_singleton.mp other
    · rw [if_neg mem]; exact (membership_zero m H j).mpr mem
  have support (v : ZMod 2) : H v = ∅ ∨ H v = H 0 ∪ H 1 := by
    by_cases empty : H v = ∅
    · exact Or.inl empty
    · right
      obtain ⟨h, member⟩ := Finset.nonempty_iff_ne_empty.mpr empty
      have bound := inside v h member
      have val : ((h : ℕ) : Phase m).val = h := ZMod.val_natCast_of_lt (by omega)
      have values : v = 0 ∨ v = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) v
      rcases values with rfl | rfl
      all_goals
        have union : h ∈ H 0 ∪ H 1 := by simp [member]
        have row := table (h : ℕ)
        simp only [val, if_pos union] at row
        apply Finset.Subset.antisymm
        · intro a ha; simp [ha]
        · intro a ha
          have ab : 1 ≤ a ∧ a ≤ m := by
            rcases Finset.mem_union.mp ha with ha | ha <;> exact inside _ a ha
          have av : ((a : ℕ) : Phase m).val = a := ZMod.val_natCast_of_lt (by omega)
          have atA := table (a : ℕ)
          simp only [av, if_pos ha] at atA
          have eq := atA.trans row.symm
          simp only [av, membership, Prod.mk.injEq] at eq
          simp only [membership, supportRow, val, if_pos member] at eq
          by_contra no
          simp [supportRow, no] at eq
  have attained : ∃ v : ZMod 2, H v = H 0 ∪ H 1 := by
    rcases support 0 with e | e
    · rcases support 1 with f | f
      · have contradiction := (fullImage_one m hm H inside).mpr ⟨e, f⟩; omega
      · exact ⟨1, f⟩
    · exact ⟨0, e⟩
  exact ⟨z, nonzero, image, table, support, attained⟩

/-- With four membership labels, one internal label admits two blocks and at
least three internal labels forbid them. -/
theorem original_first_window_table_extremes {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v)
    (four : (fullImage m H).card = 4) :
    (OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2 ↔ piFour m H) ∧
    ((internalImage m H).card = 1 → piFour m H) ∧
    (3 ≤ (internalImage m H).card → ¬ piFour m H) := by
  have compatibility :=
    (original_first_window_four_label_compatibility m hm alphabet H inside A B distinct f target four).2.1
  exact ⟨compatibility, r_one_true m hm H inside four, r_ge_three_false m H⟩

def internalFiber (m : ℕ) (H : ZMod 2 → Finset ℕ) (z : Pair) : Finset ℕ :=
  (Finset.Ico 2 m).filter (fun h => membership m H (h : ℕ) = z)

def boundaryParity (m : ℕ) (H : ZMod 2 → Finset ℕ) : ℕ :=
  m - 1 + (if membership m H (1 : ℕ) ∉ internalImage m H then 1 else 0) +
    (if membership m H (m : ℕ) ∉ internalImage m H then 1 else 0)

private theorem boundary_labels_outside (m : ℕ) (hm : 5 ≤ m)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (four : (fullImage m H).card = 4) (z : Pair) (nonzero : z ≠ 0)
    (internal : internalImage m H = {0, z}) :
    membership m H (1 : ℕ) ≠ 0 ∧ membership m H (1 : ℕ) ≠ z ∧
    membership m H (m : ℕ) ≠ 0 ∧ membership m H (m : ℕ) ≠ z ∧
    membership m H (1 : ℕ) ≠ membership m H (m : ℕ) := by
  classical
  have regions := image_regions m hm H inside
  rw [internal] at regions
  have bound (x y : Pair) : (insert x (insert y ({0} : Finset Pair))).card ≤ 3 :=
    Finset.card_le_three
  constructor
  · intro eq
    have small := bound (membership m H (m : ℕ)) z
    have same : fullImage m H = {membership m H (m : ℕ), z, 0} := by
      rw [regions, eq]; ext q; simp; tauto
    rw [← same, four] at small; omega
  constructor
  · intro eq
    have small := bound (membership m H (m : ℕ)) z
    have same : fullImage m H = {membership m H (m : ℕ), z, 0} := by
      rw [regions, eq]; ext q; simp; tauto
    rw [← same, four] at small; omega
  constructor
  · intro eq
    have small := bound (membership m H (1 : ℕ)) z
    have same : fullImage m H = {membership m H (1 : ℕ), z, 0} := by
      rw [regions, eq]; ext q; simp; tauto
    rw [← same, four] at small; omega
  constructor
  · intro eq
    have small := bound (membership m H (1 : ℕ)) z
    have same : fullImage m H = {membership m H (1 : ℕ), z, 0} := by
      rw [regions, eq]; ext q; simp; tauto
    rw [← same, four] at small; omega
  · intro eq
    have small := bound (membership m H (m : ℕ)) z
    have same : fullImage m H = {membership m H (m : ℕ), z, 0} := by
      rw [regions, eq]; ext q; simp; tauto
    rw [← same, four] at small; omega

private theorem multiplicity_boundary (m : ℕ) (hm : 5 ≤ m)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (z : Pair) (nonzero : z ≠ 0) (absent : z ∉ internalImage m H) :
    FirstWindowBoundaryFourLabels.multiplicity m H z = (if membership m H (1 : ℕ) = z then 1 else 0) +
      (if membership m H (m : ℕ) = z then 1 else 0) := by
  classical
  have boundaryDistinct : (1 : Phase m) ≠ (m : ℕ) := by
    intro eq
    have vals := congrArg (fun j : Phase m => j.val) eq
    have vOne : (1 : Phase m).val = 1 := by
      simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (a := 1) (by omega : 1 < 2 * m - 2 + 1)
    rw [vOne, ZMod.val_natCast_of_lt (by omega)] at vals
    omega
  have phases : (Finset.univ.filter (fun j : Phase m => membership m H j = z)) =
      (if membership m H (1 : ℕ) = z then {(1 : Phase m)} else ∅) ∪
      (if membership m H (m : ℕ) = z then {((m : ℕ) : Phase m)} else ∅) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    by_cases one : j = (1 : ℕ)
    · subst j; simp; split_ifs <;> simp_all [boundaryDistinct, Nat.cast_one]
    by_cases last : j = (m : ℕ)
    · subst j; simp; split_ifs <;> simp_all [boundaryDistinct, Nat.cast_one]
    have oneVal : j.val ≠ 1 := by
      intro e; exact one (ZMod.val_injective _ (e.trans (ZMod.val_natCast_of_lt (by omega)).symm))
    have lastVal : j.val ≠ m := by
      intro e; exact last (ZMod.val_injective _ (e.trans (ZMod.val_natCast_of_lt (by omega)).symm))
    have no : membership m H j ≠ z := by
      intro eq
      by_cases mid : 2 ≤ j.val ∧ j.val < m
      · exact absent (Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨by simp, mid⟩, eq⟩)
      · have zero : membership m H j = 0 := (membership_zero m H j).mpr (by
          intro mem; rcases Finset.mem_union.mp mem with mem | mem <;>
            have := inside _ _ mem <;> omega)
        exact nonzero (eq.symm.trans zero)
    split_ifs <;> simp_all
  unfold FirstWindowBoundaryFourLabels.multiplicity
  rw [phases]
  split_ifs <;> simp [boundaryDistinct, Ne.symm boundaryDistinct]

private theorem multiplicity_internal (m : ℕ) (hm : 5 ≤ m)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (z : Pair) (nonzero : z ≠ 0)
    (left : membership m H (1 : ℕ) ≠ z) (right : membership m H (m : ℕ) ≠ z) :
    FirstWindowBoundaryFourLabels.multiplicity m H z = (internalFiber m H z).card := by
  classical
  unfold FirstWindowBoundaryFourLabels.multiplicity
  apply Finset.card_bij (fun j _ => j.val)
  · intro j hj
    have label := (Finset.mem_filter.mp hj).2
    have mid : 2 ≤ j.val ∧ j.val < m := by
      by_contra no
      by_cases one : j.val = 1
      · have eq : j = (1 : ℕ) := ZMod.val_injective _
          (one.trans (ZMod.val_natCast_of_lt (by omega)).symm)
        exact left (by simpa [eq] using label)
      by_cases last : j.val = m
      · have eq : j = (m : ℕ) := ZMod.val_injective _
          (last.trans (ZMod.val_natCast_of_lt (by omega)).symm)
        exact right (by simpa [eq] using label)
      have zero : membership m H j = 0 := (membership_zero m H j).mpr (by
        intro mem; rcases Finset.mem_union.mp mem with mem | mem <;>
          have := inside _ _ mem <;> omega)
      exact nonzero (label.symm.trans zero)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr mid, by
      simpa only [ZMod.natCast_zmod_val] using label⟩
  · intro j hj l hl eq; exact ZMod.val_injective _ eq
  · intro h hh
    have pair := Finset.mem_filter.mp hh
    have bounds := Finset.mem_Ico.mp pair.1
    have val : ((h : ℕ) : Phase m).val = h := ZMod.val_natCast_of_lt (by omega)
    exact ⟨(h : ℕ), Finset.mem_filter.mpr ⟨by simp, pair.2⟩, val⟩

private theorem base_internal_parity {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v)
    (four : (fullImage m H).card = 4) (z : Pair) (nonzero : z ≠ 0)
    (internal : internalImage m H = {0, z}) :
    piFour m H ↔ Odd (internalFiber m H z).card := by
  classical
  let x := membership m H (1 : ℕ)
  let y := membership m H (m : ℕ)
  obtain ⟨x0, xz, y0, yz, xy⟩ := boundary_labels_outside m hm H inside four z nonzero internal
  simp only [Nat.cast_one] at x0 xz xy
  have xout : x ∉ internalImage m H := by simp [internal, x, Nat.cast_one, x0, xz]
  have yout : y ∉ internalImage m H := by simp [internal, y, y0, yz]
  have mx : FirstWindowBoundaryFourLabels.multiplicity m H x = 1 := by
    rw [multiplicity_boundary m hm H inside x x0 xout]
    simp [x, y, Nat.cast_one, Ne.symm xy]
  have my : FirstWindowBoundaryFourLabels.multiplicity m H y = 1 := by
    rw [multiplicity_boundary m hm H inside y y0 yout]
    simp [x, y, Nat.cast_one, xy]
  have mz := multiplicity_internal m hm H inside z nonzero xz yz
  have outlier := (original_first_window_four_label_compatibility
    m hm alphabet H inside A B distinct f target four).1
  have pi : piFour m H ↔ pivot m H = 0 := by
    unfold piFour
    rw [internal]
    constructor
    · intro pair; exact pair.2 (by simp)
    · intro eq
      refine ⟨?_, fun _ => eq⟩
      rw [eq]
      have subset : ({0, z} : Finset Pair).erase 0 ⊆ {z} := by
        intro q hq
        have mem := Finset.mem_erase.mp hq
        rcases Finset.mem_insert.mp mem.2 with eq | mem
        · exact (mem.1 eq).elim
        · exact mem
      exact (Finset.card_le_card subset).trans (by simp)
  rw [pi, ← ZMod.natCast_eq_one_iff_odd, ← mz]
  constructor
  · intro eq
    have law := (outlier 0).mpr eq
    have baseZero : (FirstWindowBoundaryFourLabels.multiplicity m H 0 : ZMod 2) = 0 := by
      have diff := law x x0
      rw [mx, Nat.cast_one] at diff
      exact (by decide : ∀ a : ZMod 2, (1 : ZMod 2) ≠ a → a = 0) _ diff
    have diff := law z nonzero
    rw [baseZero] at diff
    exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ diff
  · intro odd
    have full : fullImage m H = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa [ZMod.card] using four)
    have member : pivot m H ∈ fullImage m H := by rw [full]; simp
    rw [image_regions m hm H inside, internal] at member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with eq | eq | eq | eq | eq
    · exact eq
    · have diff := (outlier x).mpr eq y (Ne.symm xy)
      simp [mx, my] at diff
    · have diff := (outlier y).mpr eq x xy
      simp [mx, my] at diff
    · exact eq
    · have diff := (outlier z).mpr eq x xz
      simp [mx, odd] at diff

private theorem exterior_parity (m : ℕ) (hm : 5 ≤ m)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (base : (0 : Pair) ∉ internalImage m H) :
    ((Finset.univ.filter (fun j : Phase m => membership m H j ∉ internalImage m H)).card : ZMod 2) =
      (boundaryParity m H : ZMod 2) := by
  classical
  let K := internalImage m H
  let left : ZMod 2 := if membership m H (1 : ℕ) ∉ K then 1 else 0
  let right : ZMod 2 := if membership m H (m : ℕ) ∉ K then 1 else 0
  have valOne : (1 : Phase m).val = 1 := by
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (a := 1) (by omega : 1 < 2 * m - 2 + 1)
  have profile (j : Phase m) :
      (if membership m H j ∉ K then (1 : ZMod 2) else 0) =
      1 - supportRow (Finset.Icc 1 m) j.val +
        left * supportRow {1} j.val + right * supportRow {m} j.val := by
    by_cases one : j.val = 1
    · have eq : j = (1 : ℕ) := ZMod.val_injective _
        (one.trans (ZMod.val_natCast_of_lt (by omega)).symm)
      simp [eq, left, supportRow, valOne,
        show (1 : ℕ) ≠ m by omega, show 1 ≤ m by omega]
    by_cases last : j.val = m
    · have eq : j = (m : ℕ) := ZMod.val_injective _
        (last.trans (ZMod.val_natCast_of_lt (by omega)).symm)
      simp [eq, right, supportRow, ZMod.val_natCast_of_lt (by omega : m < 2 * m - 2 + 1),
        show m ≠ 1 by omega, show 1 ≤ m by omega]
    by_cases mid : 2 ≤ j.val ∧ j.val < m
    · have mem : membership m H j ∈ K := Finset.mem_image.mpr
        ⟨j, Finset.mem_filter.mpr ⟨by simp, mid⟩, rfl⟩
      simp [mem, supportRow, one, last, show 1 ≤ j.val by omega, show j.val ≤ m by omega]
    · have zero : membership m H j = 0 := (membership_zero m H j).mpr (by
        intro mem; rcases Finset.mem_union.mp mem with mem | mem <;>
          have := inside _ _ mem <;> omega)
      simp [zero, K, base, supportRow, one, last, show ¬ (1 ≤ j.val ∧ j.val ≤ m) by omega]
  have count : (∑ j : Phase m, if membership m H j ∉ K then (1 : ZMod 2) else 0) =
      ((Finset.univ.filter (fun j : Phase m => membership m H j ∉ K)).card : ZMod 2) := by
    rw [← Finset.sum_filter]
    simp
  have total : ((2 * m - 2 + 1 : ℕ) : ZMod 2) = 1 := by
    rw [Nat.cast_add, Nat.cast_sub (by omega : 2 ≤ 2 * m), Nat.cast_mul]
    simp only [Nat.cast_ofNat, Nat.cast_one, show (2 : ZMod 2) = 0 by decide, zero_mul, sub_zero, add_zero, zero_add]
  have onesum := phase_support_sum m {1} (by intro h hh; simp only [Finset.mem_singleton] at hh; omega)
  have lastsum := phase_support_sum m {m} (by intro h hh; simp only [Finset.mem_singleton] at hh; omega)
  have interval := phase_support_sum m (Finset.Icc 1 m) (by intro h hh; have := Finset.mem_Icc.mp hh; omega)
  have sum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => profile j)
  rw [count] at sum
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    onesum, lastsum, interval, Finset.card_singleton, Nat.cast_one, mul_one,
    Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one,
    total, Nat.card_Icc, show m + 1 - 1 = m by omega] at sum
  rw [sum]
  unfold boundaryParity left right K
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ m)]
  split_ifs <;> simp only [Nat.cast_one, Nat.cast_zero, ZMod.neg_eq_self_mod_two, sub_eq_add_neg] <;> ring

private theorem base_absent_parity {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v)
    (four : (fullImage m H).card = 4) (two : (internalImage m H).card = 2)
    (base : (0 : Pair) ∉ internalImage m H) :
    piFour m H ↔ Even (boundaryParity m H) := by
  classical
  let K := internalImage m H
  let C : Finset Pair := Finset.univ \ K
  have cardC : C.card = 2 := by
    rw [Finset.card_sdiff]
    simp [K, two, ZMod.card]
  have baseC : (0 : Pair) ∈ C := by simp [C, K, base]
  have erase : (C.erase 0).card = 1 := by have := Finset.card_erase_add_one baseC; omega
  obtain ⟨z, single⟩ := Finset.card_eq_one.mp erase
  have complement : C = {0, z} := by rw [← Finset.insert_erase baseC, single]
  have nonzero : z ≠ 0 := by
    have mem : z ∈ C.erase 0 := by simp [single]
    exact (Finset.mem_erase.mp mem).1
  have zC : z ∈ C := by rw [complement]; simp
  have zK : z ∉ K := (Finset.mem_sdiff.mp zC).2
  have phases : Finset.univ.filter (fun j : Phase m => membership m H j ∉ K) =
      (Finset.univ.filter (fun j : Phase m => membership m H j = 0)) ∪
      (Finset.univ.filter (fun j : Phase m => membership m H j = z)) := by
    ext j
    have member : membership m H j ∉ K ↔ membership m H j ∈ C := by simp [C]
    simp [member, complement]
  have disjoint : Disjoint
      (Finset.univ.filter (fun j : Phase m => membership m H j = 0))
      (Finset.univ.filter (fun j : Phase m => membership m H j = z)) := by
    apply Finset.disjoint_left.mpr
    intro j a b
    exact nonzero ((Finset.mem_filter.mp b).2.symm.trans (Finset.mem_filter.mp a).2)
  have parity : ((FirstWindowBoundaryFourLabels.multiplicity m H 0 : ℕ) : ZMod 2) +
      (FirstWindowBoundaryFourLabels.multiplicity m H z : ZMod 2) =
        (boundaryParity m H : ZMod 2) := by
    have total := exterior_parity m hm H inside base
    rw [phases, Finset.card_union_of_disjoint disjoint, Nat.cast_add] at total
    exact total
  have pi : piFour m H ↔ pivot m H ∈ K := by
    unfold piFour
    simp only [base, false_implies, and_true]
    by_cases mem : pivot m H ∈ K
    · have card := Finset.card_erase_add_one mem
      constructor
      · intro _; exact mem
      · intro _; change (K.erase (pivot m H)).card ≤ 1; dsimp [K] at card ⊢; omega
    · simp [K] at mem
      simp [Finset.erase_eq_of_notMem mem, two, mem, K]
  have outlier := (original_first_window_four_label_compatibility
    m hm alphabet H inside A B distinct f target four).1
  have equal : pivot m H ∈ K ↔ (FirstWindowBoundaryFourLabels.multiplicity m H 0 : ZMod 2) =
      (FirstWindowBoundaryFourLabels.multiplicity m H z : ZMod 2) := by
    constructor
    · intro mem
      have d0 : (0 : Pair) ≠ pivot m H := by intro eq; exact base (by simpa [K, eq] using mem)
      have dz : z ≠ pivot m H := by intro eq; exact zK (eq.symm ▸ mem)
      have law := (outlier (pivot m H)).mpr rfl
      exact (by decide : ∀ a b c : ZMod 2, a ≠ c → b ≠ c → a = b) _ _ _ (law 0 d0) (law z dz)
    · intro eq
      by_contra outside
      have mem : pivot m H ∈ C := by simp [C, outside]
      rw [complement] at mem
      rcases Finset.mem_insert.mp mem with d0 | dz
      · exact ((outlier 0).mpr d0 z nonzero) eq.symm
      · have dz := Finset.mem_singleton.mp dz
        exact ((outlier z).mpr dz 0 (Ne.symm nonzero)) eq
  rw [pi, equal, ← ZMod.natCast_eq_zero_iff_even, ← parity]
  exact (by decide : ∀ a b : ZMod 2, a = b ↔ a + b = 0) _ _

def presetCost (m : ℕ) (H : ZMod 2 → Finset ℕ) : ℕ := by
  classical
  exact if (fullImage m H).card = 1 then 0
  else if (fullImage m H).card = 2 then binaryCost (H 0 ∪ H 1)
  else if (fullImage m H).card = 3 then (if piThree m H then 2 else 3)
  else if (internalImage m H).card = 1 then 2
  else if 3 ≤ (internalImage m H).card then 3
  else if piFour m H then 2 else 3

private theorem one_block_image_bound {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v)
    (feasible : OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 1) :
    (fullImage m H).card ≤ 2 := by
  classical
  obtain ⟨stream, stop, _, _, correct⟩ := feasible
  have refines (p q : Phase m) (charges : firstCharge m stream p = firstCharge m stream q) :
      membership m H p = membership m H q := by
    have scalar (v : ZMod 2) : supportRow (H v) p.val = supportRow (H v) q.val := by
      have fiber : FiberCorrect m hm alphabet f v 1 (presetSelector stream stop) := by
        intro history
        dsimp only
        intro observed
        obtain ⟨c, bound, success⟩ := correct history
        rw [observed] at success
        exact ⟨c, bound, success⟩
      have native (j : Phase m) := OwnPathCharges.native_fiber (2 * m - 2) m
        (by omega) (by omega) alphabet f v 1 _ fiber (-j) 0 (by omega)
        (by rw [FourLabelPaidFeedback.coprime m hm]; exact one_dvd _)
      obtain ⟨c, _, ex⟩ := native p
      obtain ⟨c', _, ey⟩ := native q
      have safe : runAdmissible (2 * m - 2 - 1) (2 * m - 2 - 1 - 0) m (stream 0) = true := by
        apply runAdmissible_eq_true_of_length_le <;> omega
      have same := OwnPathCharges.charge_separates (2 * m - 2) m (by omega)
        (presetSelector stream stop) 1 v (-p) (-q) 0 (by omega) (some v) [] _ _ c c' ex ey (by
          intro t ht
          have te : t = 0 := by omega
          subst t
          cases chosen : stop (some v) [] with
          | some label => simp [OwnPathCharges.ownCharge, presetSelector, chosen]
          | none =>
            simp only [OwnPathCharges.ownCharge, presetSelector, chosen, List.length_nil]
            simp only [Nat.sub_zero] at safe ⊢
            rw [if_pos safe, if_pos safe]
            exact charges)
      rw [target v p 0 (by omega), target v q 0 (by omega)] at same
      by_cases a : p.val ∈ H v <;> by_cases b : q.val ∈ H v
      · simp [supportRow, a, b]
      · simp only [if_pos a, if_neg b] at same
        exact (distinct v same.symm).elim
      · simp only [if_neg a, if_pos b] at same
        exact (distinct v same).elim
      · simp [supportRow, a, b]
    exact Prod.ext (scalar 0) (scalar 1)
  let pick (z : Pair) (hz : z ∈ fullImage m H) : Phase m :=
    Classical.choose (Finset.mem_image.mp hz)
  have picked (z : Pair) (hz : z ∈ fullImage m H) : membership m H (pick z hz) = z :=
    (Classical.choose_spec (Finset.mem_image.mp hz)).2
  let select (z : Pair) : ZMod 2 :=
    if hz : z ∈ fullImage m H then firstCharge m stream (pick z hz) else 0
  have inj : Set.InjOn select (fullImage m H) := by
    intro z hz w hw same
    change z ∈ fullImage m H at hz
    change w ∈ fullImage m H at hw
    dsimp only [select] at same
    rw [dif_pos hz, dif_pos hw] at same
    exact (picked z hz).symm.trans ((refines _ _ same).trans (picked w hw))
  have bound := Finset.card_le_card_of_injOn select
    (t := Finset.univ) (by intro z hz; exact Finset.mem_univ _) inj
  simpa using bound

private theorem binary_join_attains {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v)
    (small : (fullImage m H).card = 1 ∨ (fullImage m H).card = 2) :
    OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f (binaryCost (H 0 ∪ H 1)) := by
  classical
  have supports : ∀ v : ZMod 2, H v = ∅ ∨ H v = H 0 ∪ H 1 := by
    rcases small with one | two
    · have empty := (fullImage_one m hm H inside).mp one
      intro v
      have values : v = 0 ∨ v = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) v
      rcases values with rfl | rfl <;> simp [empty]
    · exact (fullImage_two m hm H inside two).choose_spec.2.2.2.1
  let label (v b : ZMod 2) : Y :=
    if H v = ∅ then A v else if b = 0 then A v else B v
  apply (original_first_window_binary_stream m hm alphabet (H 0 ∪ H 1)
    (by intro h hh; rcases Finset.mem_union.mp hh with hh | hh <;> exact inside _ h hh)
    f label ?_).1
  intro v j s hs
  rw [target v j s hs]
  by_cases empty : H v = ∅
  · simp [label, empty]
  · have eq : H v = H 0 ∪ H 1 := (supports v).resolve_left empty
    dsimp only [label]
    rw [if_neg empty, eq]
    by_cases mem : j.val ∈ H 0 ∪ H 1 <;> simp [supportRow, mem]

def PresetBitFeasible {Y : Type u} (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (f : Option (LiveRecord (2 * m - 2)) → Y) (b : ℕ) : Prop :=
  ∃ (stream : ℕ → Fin m → Bool)
    (stop : Option (ZMod 2) → NarrowWindowCost.Archive m → Option Y),
    FullPositiveWindowPrice.SelectorLegal (2 * m - 2) alphabet (presetSelector stream stop) ∧
    stop none [] = some (f none) ∧
    ∀ history : List (AllowedBlock (2 * m - 2) m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      ∃ issued, PaidTrace (presetSelector stream stop) (NarrowWindowCost.output (2 * m - 2) (by omega) w)
        (OriginalRecord (2 * m - 2) (by omega) w) [] issued (f (OriginalRecord (2 * m - 2) (by omega) w)) ∧
        (archiveWords issued).length ≤ b

private theorem optimal_paid_traces {Y : Type u} (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (f : Option (LiveRecord (2 * m - 2)) → Y) (c : ℕ)
    (attain : OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f c)
    (least : ∀ d, OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f d → c ≤ d) :
    (∀ b, PresetBitFeasible m hm alphabet f b ↔ m * c ≤ b) ∧
    ∃ (stream : ℕ → Fin m → Bool)
      (stop : Option (ZMod 2) → NarrowWindowCost.Archive m → Option Y),
      FullPositiveWindowPrice.SelectorLegal (2 * m - 2) alphabet (presetSelector stream stop) ∧
      stop none [] = some (f none) ∧
      (∀ history : List (AllowedBlock (2 * m - 2) m alphabet),
        let w := history.flatMap (fun a => List.ofFn a.val)
        ∃ issued, PaidTrace (presetSelector stream stop) (NarrowWindowCost.output (2 * m - 2) (by omega) w)
          (OriginalRecord (2 * m - 2) (by omega) w) [] issued (f (OriginalRecord (2 * m - 2) (by omega) w)) ∧
          issued.length ≤ c ∧ (archiveWords issued).length = m * issued.length) ∧
      ∃ (history : List (AllowedBlock (2 * m - 2) m alphabet)) (issued : NarrowWindowCost.Archive m),
        let w := history.flatMap (fun a => List.ofFn a.val)
        PaidTrace (presetSelector stream stop) (NarrowWindowCost.output (2 * m - 2) (by omega) w)
          (OriginalRecord (2 * m - 2) (by omega) w) [] issued (f (OriginalRecord (2 * m - 2) (by omega) w)) ∧
        issued.length = c ∧ (archiveWords issued).length = m * c := by
  classical
  obtain ⟨stream, stop, legal, bottom, success⟩ := attain
  have traces (history : List (AllowedBlock (2 * m - 2) m alphabet)) :
      let w := history.flatMap (fun a => List.ofFn a.val)
      ∃ issued, PaidTrace (presetSelector stream stop) (NarrowWindowCost.output (2 * m - 2) (by omega) w)
        (OriginalRecord (2 * m - 2) (by omega) w) [] issued (f (OriginalRecord (2 * m - 2) (by omega) w)) ∧
        issued.length ≤ c ∧ (archiveWords issued).length = m * issued.length := by
    intro w
    obtain ⟨d, bound, execution⟩ := success history
    rw [execute_paid_trace _ m (by omega)] at execution
    obtain ⟨issued, traced, count, _⟩ := execution
    exact ⟨issued, traced, count ▸ bound, by rw [archive_length, Nat.mul_comm]⟩
  constructor
  · intro b
    constructor
    · rintro ⟨words, stopping, lawful, root, bitTraces⟩
      have feasible : OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f (b / m) := by
        refine ⟨words, stopping, lawful, root, ?_⟩
        intro history w
        obtain ⟨issued, traced, bits⟩ := bitTraces history
        rw [archive_length, Nat.mul_comm] at bits
        have bound : issued.length ≤ b / m := (Nat.le_div_iff_mul_le (by omega)).mpr
          (by simpa [Nat.mul_comm] using bits)
        refine ⟨issued.length, bound, ?_⟩
        rw [execute_paid_trace _ m (by omega)]
        exact ⟨issued, traced, rfl, bound⟩
      have bound := least _ feasible
      exact (Nat.le_div_iff_mul_le (by omega)).mp bound |> fun h => by simpa [Nat.mul_comm] using h
    · intro bound
      refine ⟨stream, stop, legal, bottom, ?_⟩
      intro history w
      obtain ⟨issued, traced, count, bits⟩ := traces history
      exact ⟨issued, traced, by rw [bits]; exact (Nat.mul_le_mul_left m count).trans bound⟩
  · refine ⟨stream, stop, legal, bottom, traces, ?_⟩
    by_cases zero : c = 0
    · obtain ⟨issued, traced, bound, bits⟩ := traces []
      refine ⟨[], issued, traced, by omega, ?_⟩
      rw [bits]; congr 1; omega
    · by_contra no
      have smaller : OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f (c - 1) := by
        refine ⟨stream, stop, legal, bottom, ?_⟩
        intro history w
        obtain ⟨issued, traced, bound, bits⟩ := traces history
        have notEqual : issued.length ≠ c := by
          intro eq
          exact no ⟨history, issued, traced, eq, by simpa [eq] using bits⟩
        have strict : issued.length ≤ c - 1 := by omega
        refine ⟨issued.length, strict, ?_⟩
        rw [execute_paid_trace _ m (by omega)]
        exact ⟨issued, traced, rfl, strict⟩
      have bad := least (c - 1) smaller
      omega

/-- One common literal stream has the exact complete-original first-window price.
The image is counted once per phase; the remembered value is used only to stop and decode. -/
theorem original_first_window_preset_price {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v) :
    GlobalPresetPrice (2 * m - 2) m (by omega) alphabet f = (presetCost m H : ℕ∞) ∧
    (∀ d, OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f d ↔ presetCost m H ≤ d) ∧
    ((fullImage m H).card = 1 ↔ H 0 = ∅ ∧ H 1 = ∅) ∧
    ((fullImage m H).card = 2 →
      ∃ z : Pair, z ≠ 0 ∧ fullImage m H = {0, z} ∧
        (∀ j : Phase m, membership m H j = if j.val ∈ H 0 ∪ H 1 then z else 0) ∧
        (∀ v : ZMod 2, H v = ∅ ∨ H v = H 0 ∪ H 1) ∧
        ∃ v : ZMod 2, H v = H 0 ∪ H 1) ∧
    ((fullImage m H).card = 4 →
      ((internalImage m H).card = 1 → piFour m H) ∧
      (3 ≤ (internalImage m H).card → ¬ piFour m H) ∧
      (∀ z : Pair, z ≠ 0 → internalImage m H = {0, z} →
        (piFour m H ↔ Odd (internalFiber m H z).card)) ∧
      ((internalImage m H).card = 2 → (0 : Pair) ∉ internalImage m H →
        (piFour m H ↔ Even (boundaryParity m H)))) ∧
    (∀ b, PresetBitFeasible m hm alphabet f b ↔ m * presetCost m H ≤ b) ∧
    ∃ (stream : ℕ → Fin m → Bool)
      (stop : Option (ZMod 2) → NarrowWindowCost.Archive m → Option Y),
      FullPositiveWindowPrice.SelectorLegal (2 * m - 2) alphabet (presetSelector stream stop) ∧
      stop none [] = some (f none) ∧
      (∀ history : List (AllowedBlock (2 * m - 2) m alphabet),
        let w := history.flatMap (fun a => List.ofFn a.val)
        ∃ issued, PaidTrace (presetSelector stream stop) (NarrowWindowCost.output (2 * m - 2) (by omega) w)
          (OriginalRecord (2 * m - 2) (by omega) w) [] issued (f (OriginalRecord (2 * m - 2) (by omega) w)) ∧
          issued.length ≤ presetCost m H ∧ (archiveWords issued).length = m * issued.length) ∧
      ∃ (history : List (AllowedBlock (2 * m - 2) m alphabet)) (issued : NarrowWindowCost.Archive m),
        let w := history.flatMap (fun a => List.ofFn a.val)
        PaidTrace (presetSelector stream stop) (NarrowWindowCost.output (2 * m - 2) (by omega) w)
          (OriginalRecord (2 * m - 2) (by omega) w) [] issued (f (OriginalRecord (2 * m - 2) (by omega) w)) ∧
        issued.length = presetCost m H ∧ (archiveWords issued).length = m * presetCost m H := by
  classical
  have npos : 1 ≤ (fullImage m H).card := by
    have base : (0 : Pair) ∈ fullImage m H := by rw [image_regions m hm H inside]; simp
    exact Finset.card_pos.mpr ⟨0, base⟩
  have nbound : (fullImage m H).card ≤ 4 := by
    simpa [ZMod.card] using Finset.card_le_univ (fullImage m H)
  have upperThree : OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 3 := by
    let label (v : ZMod 2) (z : Pair) : Y :=
      if v = 0 then (if z.1 = 0 then A v else B v) else (if z.2 = 0 then A v else B v)
    apply (original_first_window_three_block_stream m hm alphabet f (membership m H)
      (by intro j out; exact (membership_zero m H j).mpr (by
        intro mem; rcases Finset.mem_union.mp mem with mem | mem <;> exact out (inside _ _ mem)))
      label ?_).1
    intro v j s hs
    rw [target v j s hs]
    have values : v = 0 ∨ v = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) v
    rcases values with rfl | rfl <;> simp [label, membership, supportRow]
  have fourCost (four : (fullImage m H).card = 4) :
      presetCost m H = if piFour m H then 2 else 3 := by
    have extremes := original_first_window_table_extremes m hm alphabet H inside A B distinct f target four
    unfold presetCost
    simp only [four, show (4 : ℕ) ≠ 1 by omega, show (4 : ℕ) ≠ 2 by omega,
      show (4 : ℕ) ≠ 3 by omega, if_false]
    by_cases one : (internalImage m H).card = 1
    · simp [one, extremes.2.1 one]
    · by_cases large : 3 ≤ (internalImage m H).card
      · simp [one, large, extremes.2.2 large]
      · simp [one, large]
  have attain : OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f (presetCost m H) := by
    by_cases one : (fullImage m H).card = 1
    · have empty := (fullImage_one m hm H inside).mp one
      simpa [presetCost, one, binaryCost, empty] using
        binary_join_attains m hm alphabet H inside A B f target (Or.inl one)
    by_cases two : (fullImage m H).card = 2
    · simpa [presetCost, one, two] using
        binary_join_attains m hm alphabet H inside A B f target (Or.inr two)
    by_cases three : (fullImage m H).card = 3
    · have compat := (original_first_window_three_label_compatibility m hm alphabet H inside A B distinct f target three).1
      by_cases admitted : piThree m H
      · simpa [presetCost, one, two, three, admitted] using compat.mpr admitted
      · simpa [presetCost, one, two, three, admitted] using upperThree
    · have four : (fullImage m H).card = 4 := by omega
      rw [fourCost four]
      by_cases admitted : piFour m H
      · rw [if_pos admitted]
        exact (original_first_window_four_label_compatibility m hm alphabet H inside A B distinct f target four).2.1.mpr admitted
      · simpa [admitted] using upperThree
  have least (d : ℕ) (feasible : OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f d) :
      presetCost m H ≤ d := by
    by_cases one : (fullImage m H).card = 1
    · simp [presetCost, one]
    by_cases two : (fullImage m H).card = 2
    · obtain ⟨z, _, _, _, _, v, eq⟩ := fullImage_two m hm H inside two
      have adaptive := preset_inclusion _ _ (by omega) alphabet f d feasible
      have bound := ((FirstWindowBoundaryAdaptive.original_first_window_adaptive_price
        m hm alphabet H inside A B distinct f target).2.1 d).mp adaptive
      have vc : v = 0 ∨ v = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) v
      have own : binaryCost (H v) ≤ d := by
        rcases vc with rfl | rfl
        · exact (le_max_left _ _).trans bound
        · exact (le_max_right _ _).trans bound
      simpa [presetCost, one, two, eq] using own
    have lower : 2 ≤ d := by
      by_contra small
      have oneFee := preset_monotone _ _ (by omega) alphabet f d 1 (by omega) feasible
      have image := one_block_image_bound m hm alphabet H inside A B distinct f target oneFee
      omega
    by_cases three : (fullImage m H).card = 3
    · by_cases admitted : piThree m H
      · simpa [presetCost, one, two, three, admitted] using lower
      · have notTwo := (original_first_window_three_label_compatibility m hm alphabet H inside A B distinct f target three).1.not.mpr admitted
        have more : 3 ≤ d := by
          by_contra small
          exact notTwo (preset_monotone _ _ (by omega) alphabet f d 2 (by omega) feasible)
        simpa [presetCost, one, two, three, admitted] using more
    · have four : (fullImage m H).card = 4 := by omega
      rw [fourCost four]
      by_cases admitted : piFour m H
      · simpa [admitted] using lower
      · have notTwo := (original_first_window_four_label_compatibility m hm alphabet H inside A B distinct f target four).2.1.not.mpr admitted
        have more : 3 ≤ d := by
          by_contra small
          exact notTwo (preset_monotone _ _ (by omega) alphabet f d 2 (by omega) feasible)
        simpa [admitted] using more
  refine ⟨FullPositiveWindowPrice.price_exact _ _ attain least, ?_,
    fullImage_one m hm H inside, fullImage_two m hm H inside, ?_,
    optimal_paid_traces m hm alphabet f _ attain least⟩
  · intro d
    exact ⟨least d, fun bound => preset_monotone _ _ (by omega) alphabet f _ d bound attain⟩
  · intro four
    have extremes := original_first_window_table_extremes m hm alphabet H inside A B distinct f target four
    exact ⟨extremes.2.1, extremes.2.2,
      fun z nonzero internal => base_internal_parity m hm alphabet H inside A B distinct f target four z nonzero internal,
      fun two base => base_absent_parity m hm alphabet H inside A B distinct f target four two base⟩

#print axioms original_first_window_preset_price
#print axioms original_first_window_table_extremes
end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryPrice
