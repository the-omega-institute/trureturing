/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryFourLabels
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryFourLabels
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Phase-once four-label pivots select safe common physical boundary streams. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCompatibility
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryFourLabels
open D5.S0.Tower.DBonacci.Names
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells WindowChargeInverse PhysicalWindowDecoder
open OriginalNarrowCost OriginalAcquiredTrace OriginalExecutionBridge DonorCorrection
open FirstWindowBoundaryAttainment FirstWindowBoundaryCodes FirstWindowBoundaryCompatibility GlobalPresetObstruction
open scoped BigOperators

/-- Each phase contributes once, independently of its histories and inherited tails. -/
def multiplicity (m : ℕ) (H : ZMod 2 → Finset ℕ) (z : Pair) : ℕ :=
  (Finset.univ.filter (fun j : Phase m => membership m H j = z)).card

def pivot (m : ℕ) (H : ZMod 2 → Finset ℕ) : Pair := ∑ j, membership m H j

def piFour (m : ℕ) (H : ZMod 2 → Finset ℕ) : Prop :=
  ((internalImage m H).erase (pivot m H)).card ≤ 1 ∧
    ((0 : Pair) ∈ internalImage m H → pivot m H = 0)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem permutation_odd_sum : ∀ (g : Pair → Pair), Function.Bijective g →
    ∀ (w : Pair → ZMod 2), (∑ z, w z) = 1 →
    g (∑ z, w z • z) = ∑ z, w z • g z := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 4096 in
private theorem normalized_selection : ∀ (b : Pair → Bool) (d x y : Pair),
    let K := Finset.univ.filter (fun z => b z = true)

    insert 0 (insert x (insert y K)) = Finset.univ →
    (K.erase d).card ≤ 1 → (0 ∈ K → d = 0) →
    ∃ g : Pair → Pair, Function.Bijective g ∧ g d = 0 ∧ (g 0).1 = 0 ∧
      (∀ z ∈ K, (g z).2 = 0) ∧
      ((g y).2 = 0 ∨ (g 0).2 = 1 ∨ (g y).1 = 0) := by
  dsimp only
  decide

private theorem total_parity (m : ℕ) (hm : 5 ≤ m) :
    ((2 * m - 2 + 1 : ℕ) : ZMod 2) = 1 := by
  rw [Nat.cast_add, Nat.cast_sub (by omega : 2 ≤ 2 * m), Nat.cast_mul,
    show ((2 : ℕ) : ZMod 2) = 0 by decide]
  simp

private theorem multiplicity_total (m : ℕ) (hm : 5 ≤ m) (H : ZMod 2 → Finset ℕ) :
    (∑ z : Pair, (multiplicity m H z : ZMod 2)) = 1 := by
  have fibers := Finset.sum_fiberwise' (Finset.univ : Finset (Phase m))
    (membership m H) (fun _ => (1 : ZMod 2))
  simpa [multiplicity, Finset.sum_const, nsmul_eq_mul, ZMod.card, total_parity m hm] using fibers

private theorem multiplicity_sum (m : ℕ) (H : ZMod 2 → Finset ℕ) (g : Pair → Pair) :
    (∑ z : Pair, (multiplicity m H z : ZMod 2) • g z) =
      ∑ j : Phase m, g (membership m H j) := by
  have fibers := Finset.sum_fiberwise' (Finset.univ : Finset (Phase m)) (membership m H) g
  simpa only [Finset.sum_const, multiplicity, Nat.cast_smul_eq_nsmul] using fibers

private theorem pivot_sum (m : ℕ) (hm : 5 ≤ m) (H : ZMod 2 → Finset ℕ)
    (g : Pair → Pair) (bijective : Function.Bijective g) :
    (∑ j, g (membership m H j)) = g (pivot m H) := by
  have law := permutation_odd_sum g bijective (fun z => (multiplicity m H z : ZMod 2))
    (multiplicity_total m hm H)
  rw [show (∑ z : Pair, (multiplicity m H z : ZMod 2) • z) = pivot m H from
    multiplicity_sum m H (fun z => z), multiplicity_sum m H g] at law
  exact law.symm

set_option maxRecDepth 4096 in
private theorem parity_outlier : ∀ (w : Pair → ZMod 2), (∑ z, w z) = 1 →
    ∀ d : Pair, (∀ z, z ≠ d → w z ≠ w d) ↔ (∑ z, w z • z) = d := by
  decide

private theorem pivot_multiplicity (m : ℕ) (hm : 5 ≤ m) (H : ZMod 2 → Finset ℕ) :
    ∀ d : Pair, (∀ z, z ≠ d →
      (multiplicity m H z : ZMod 2) ≠ (multiplicity m H d : ZMod 2)) ↔ pivot m H = d := by
  intro d
  have law := parity_outlier (fun z => (multiplicity m H z : ZMod 2))
    (multiplicity_total m hm H) d
  rw [show (∑ z : Pair, (multiplicity m H z : ZMod 2) • z) = pivot m H from
    multiplicity_sum m H (fun z => z)] at law
  exact law

private theorem outside_label (m : ℕ) (H : ZMod 2 → Finset ℕ)
    (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (j : Phase m) (out : ¬ (1 ≤ j.val ∧ j.val ≤ m)) : membership m H j = 0 := by
  have absent (v : ZMod 2) : j.val ∉ H v := fun mem => out (inside v j.val mem)
  simp [membership, supportRow, absent]

theorem image_regions (m : ℕ) (hm : 5 ≤ m) (H : ZMod 2 → Finset ℕ)
    (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m) :
    fullImage m H = insert 0 (insert (membership m H (1 : ℕ))
      (insert (membership m H (m : ℕ)) (internalImage m H))) := by
  classical
  apply Finset.Subset.antisymm
  · intro z mem
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp mem
    by_cases one : j.val = 1
    · have eq : j = (1 : ℕ) := ZMod.val_injective _
        (one.trans (ZMod.val_natCast_of_lt (by omega)).symm)
      simp [eq]
    by_cases last : j.val = m
    · have eq : j = (m : ℕ) := ZMod.val_injective _
        (last.trans (ZMod.val_natCast_of_lt (by omega)).symm)
      simp [eq]
    by_cases mid : 2 ≤ j.val ∧ j.val < m
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, mid⟩, rfl⟩)))
    · rw [outside_label m H inside j (by omega)]; simp
  · intro z mem
    simp only [Finset.mem_insert] at mem
    rcases mem with rfl | rfl | rfl | mem
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, outside_label m H inside 0 (by simp)⟩
    · exact Finset.mem_image.mpr ⟨(1 : ℕ), Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨(m : ℕ), Finset.mem_univ _, rfl⟩
    · obtain ⟨j, _, eq⟩ := Finset.mem_image.mp mem
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, eq⟩

private theorem saturated_codes (m : ℕ) (H : ZMod 2 → Finset ℕ)
    (four : (fullImage m H).card = 4) (code : Phase m → Pair)
    (refines : ∀ p q, code p = code q → membership m H p = membership m H q) :
    ∃ g : Pair → Pair, Function.Bijective g ∧ ∀ j, code j = g (membership m H j) := by
  classical
  have full : fullImage m H = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa [ZMod.card] using four)
  have onto : Function.Surjective (membership m H) := by
    intro z
    have mem : z ∈ fullImage m H := by rw [full]; simp
    obtain ⟨j, _, eq⟩ := Finset.mem_image.mp mem
    exact ⟨j, eq⟩
  let rep (z : Pair) := Classical.choose (onto z)
  have represented (z : Pair) : membership m H (rep z) = z := Classical.choose_spec (onto z)
  let g (z : Pair) := code (rep z)
  have inj : Function.Injective g := by
    intro z w same
    exact (represented z).symm.trans ((refines _ _ same).trans (represented w))
  have bijective : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).mpr ⟨inj, rfl⟩
  refine ⟨g, bijective, ?_⟩
  intro j
  obtain ⟨z, eq⟩ := bijective.2 (code j)
  have label := (represented z).symm.trans (refines (rep z) j eq)
  exact eq.symm.trans (congrArg g label)

private theorem four_necessary {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v)
    (four : (fullImage m H).card = 4)
    (feasible : OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2) : piFour m H := by
  classical
  have full : fullImage m H = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa [ZMod.card] using four)
  have nonempty : (H 0).Nonempty := by
    have mem : (1, 0) ∈ fullImage m H := by rw [full]; simp
    obtain ⟨j, _, eq⟩ := Finset.mem_image.mp mem
    have first := congrArg Prod.fst eq
    by_cases hj : j.val ∈ H 0
    · exact ⟨j.val, hj⟩
    · simp [membership, supportRow, hj] at first
  obtain ⟨stream, stop, _, root, blind, evenA, evenB, refines, _⟩ :=
    (original_first_window_boundary_rows m hm alphabet H inside A B distinct f target).1 feasible
  let code (j : Phase m) : Pair := (firstCharge m stream j, secondCharge m stream j)
  obtain ⟨g, bijective, codes⟩ := saturated_codes m H four code (by
    intro p q same; exact refines p q (congrArg Prod.fst same) (congrArg Prod.snd same))
  have zeroSum : (∑ j, g (membership m H j)) = 0 := by
    simp_rw [← codes]
    apply Prod.ext <;> simp [code, Prod.fst_sum, Prod.snd_sum, evenA, evenB]
  have pivotZero : g (pivot m H) = 0 := (pivot_sum m hm H g bijective).symm.trans zeroSum
  have internal (z : Pair) (hz : z ∈ internalImage m H) : (g z).2 = 0 := by
    obtain ⟨j, mem, eq⟩ := Finset.mem_image.mp hz
    have bounds := (Finset.mem_filter.mp mem).2
    rw [← eq, ← codes]
    exact blind j bounds.1 bounds.2
  have atZero : (g 0).1 = 0 := by
    have label : membership m H 0 = 0 := outside_label m H inside 0 (by simp)
    rw [← label, ← codes]
    exact (root nonempty).2.2 0 (by simp)
  have uniqueZero (z : Pair) (first : (g z).1 = 0) (second : (g z).2 = 0) : z = pivot m H :=
    bijective.1 ((Prod.ext first second).trans pivotZero.symm)
  have oneCode (z : Pair) (hz : z ∈ (internalImage m H).erase (pivot m H)) : g z = (1, 0) := by
    have mem := Finset.mem_erase.mp hz
    have second := internal z mem.2
    have first : (g z).1 = 1 := by
      have ne : (g z).1 ≠ 0 := fun eq => mem.1 (uniqueZero z eq second)
      have binary : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
      exact binary _ ne
    exact Prod.ext first second
  refine ⟨?_, ?_⟩
  · have sub : (internalImage m H).erase (pivot m H) ⊆
        ({Classical.choose (bijective.2 (1, 0))} : Finset Pair) := by
      intro z hz
      apply Finset.mem_singleton.mpr
      exact bijective.1 ((oneCode z hz).trans (Classical.choose_spec (bijective.2 (1, 0))).symm)
    exact (Finset.card_le_card sub).trans (by simp)
  · intro base
    exact (uniqueZero 0 atZero (internal 0 base)).symm

theorem phase_support_sum (m : ℕ) (H : Finset ℕ)
    (inside : ∀ h ∈ H, h ≤ 2 * m - 2) :
    (∑ j : Phase m, supportRow H j.val) = (H.card : ZMod 2) := by
  let e : Fin (2 * m - 2 + 1) ≃ Phase m := (ZMod.finEquiv _).toEquiv
  rw [← e.sum_comp]
  have val (j : Fin (2 * m - 2 + 1)) : (e j).val = j.val := rfl
  simp only [val]
  rw [Fin.sum_univ_eq_sum_range, support_sum (2 * m - 2) H inside]

private theorem normalized_physical_rows (m : ℕ) (hm : 5 ≤ m)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (g : Pair → Pair) (bijective : Function.Bijective g)
    (pivotZero : g (pivot m H) = 0) (baseZero : (g 0).1 = 0)
    (internal : ∀ z ∈ internalImage m H, (g z).2 = 0)
    (seam : (g (membership m H (m : ℕ))).2 = 0 ∨
      (g 0).2 = 1 ∨ (g (membership m H (m : ℕ))).1 = 0) :
    ∃ (S : Finset ℕ) (a : BaseAssignment),
      S = (Finset.Ico 2 m).filter (fun h => (g (membership m H (h : ℕ))).1 = 1) ∧
      a = ⟨0, (g 0).2, 0, g (membership m H (1 : ℕ)), g (membership m H (m : ℕ))⟩ ∧
      (∀ h ∈ S, 2 ≤ h ∧ h < m) ∧
      (S.card : ZMod 2) + a.flip * (m : ℕ) + a.left.1 + a.right.1 = 0 ∧
      a.exterior * ((m : ZMod 2) + 1) + a.donor + a.left.2 + a.right.2 = 0 ∧
      (a.right.2 = 0 ∨ a.exterior + a.donor = 1 ∨ a.right.1 = 0) ∧
      ∀ j, baseCode m S a j = g (membership m H j) := by
  classical
  let S := (Finset.Ico 2 m).filter (fun h => (g (membership m H (h : ℕ))).1 = 1)
  let a : BaseAssignment :=
    ⟨0, (g 0).2, 0, g (membership m H (1 : ℕ)), g (membership m H (m : ℕ))⟩
  have Sinside : ∀ h ∈ S, 2 ≤ h ∧ h < m := by
    intro h hh; exact Finset.mem_Ico.mp (Finset.mem_filter.mp hh).1
  have vOne : (1 : Phase m).val = 1 := by
    simpa using (ZMod.val_natCast_of_lt (a := 1) (by omega : 1 < 2 * m - 2 + 1))
  have noOne : 1 ∉ S := by intro h; have := Sinside 1 h; omega
  have noLast : m ∉ S := by intro h; have := Sinside m h; omega
  have atOne (j : Phase m) (one : j.val = 1) : j = (1 : ℕ) :=
    ZMod.val_injective _ (one.trans (ZMod.val_natCast_of_lt (by omega)).symm)
  have atLast (j : Phase m) (last : j.val = m) : j = (m : ℕ) :=
    ZMod.val_injective _ (last.trans (ZMod.val_natCast_of_lt (by omega)).symm)
  have internalZero (j : Phase m) (mid : 2 ≤ j.val ∧ j.val < m) :
      (g (membership m H j)).2 = 0 := internal _
    (Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, mid⟩, rfl⟩)
  have subsetBit (j : Phase m) (mid : 2 ≤ j.val ∧ j.val < m) :
      supportRow S j.val = (g (membership m H j)).1 := by
    have cast : ((j.val : ℕ) : Phase m) = j := ZMod.natCast_zmod_val j
    have binary : ∀ z : ZMod 2, (if z = 1 then 1 else 0) = z := by decide
    simpa [supportRow, S, mid, cast] using binary (g (membership m H j)).1
  have firstProfile (j : Phase m) : (g (membership m H j)).1 =
      supportRow S j.val + a.left.1 * supportRow {1} j.val + a.right.1 * supportRow {m} j.val := by
    by_cases one : j.val = 1
    · rw [atOne j one]
      simp [a, supportRow, noOne, vOne, show (1 : ℕ) ≠ m by omega]
    by_cases last : j.val = m
    · rw [atLast j last]
      simp [a, supportRow, noLast, show ((m : ℕ) : Phase m).val = m from
        ZMod.val_natCast_of_lt (by omega), show m ≠ 1 by omega]
    by_cases mid : 2 ≤ j.val ∧ j.val < m
    · simp [supportRow, one, last, ← subsetBit j mid]
    · have absent : j.val ∉ S := by intro mem; have := Sinside j.val mem; omega
      rw [outside_label m H inside j (by omega), baseZero]
      simp [supportRow, absent, one, last]
  have secondProfile (j : Phase m) : (g (membership m H j)).2 =
      a.exterior * (1 - supportRow (Finset.Icc 1 m) j.val) +
        a.left.2 * supportRow {1} j.val + a.right.2 * supportRow {m} j.val := by
    by_cases one : j.val = 1
    · rw [atOne j one]
      simp [a, supportRow, vOne, show (1 : ℕ) ≠ m by omega, show 1 ≤ m by omega]
    by_cases last : j.val = m
    · rw [atLast j last]
      simp [a, supportRow, show ((m : ℕ) : Phase m).val = m from
        ZMod.val_natCast_of_lt (by omega), show m ≠ 1 by omega, show 1 ≤ m by omega]
    by_cases mid : 2 ≤ j.val ∧ j.val < m
    · rw [internalZero j mid]
      simp [supportRow, one, last, show 1 ≤ j.val by omega, show j.val ≤ m by omega]
    · rw [outside_label m H inside j (by omega)]
      simp [a, supportRow, one, last, show ¬ (1 ≤ j.val ∧ j.val ≤ m) by omega]
  have total : (∑ j, g (membership m H j)) = 0 := (pivot_sum m hm H g bijective).trans pivotZero
  have firstSum := congrArg Prod.fst total
  have secondSum := congrArg Prod.snd total
  simp only [Prod.fst_sum, Prod.snd_sum, Prod.fst_zero, Prod.snd_zero] at firstSum secondSum
  simp_rw [firstProfile] at firstSum
  simp_rw [secondProfile] at secondSum
  have ssum := phase_support_sum m S (by intro h hh; have := Sinside h hh; omega)
  have onesum := phase_support_sum m {1} (by intro h hh; simp at hh; omega)
  have lastsum := phase_support_sum m {m} (by intro h hh; simp at hh; omega)
  have bsum := phase_support_sum m (Finset.Icc 1 m) (by intro h hh; simp at hh; omega)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ssum, onesum, lastsum,
    Finset.card_singleton, Nat.cast_one, mul_one] at firstSum
  have rm : (1 : ZMod 2) - (m : ℕ) = (m : ℕ) + 1 := by
    simp only [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]; ring
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    onesum, lastsum, bsum, Finset.card_singleton, Nat.cast_one, mul_one,
    Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
    total_parity m hm, Nat.card_Icc, show m + 1 - 1 = m by omega, rm] at secondSum
  refine ⟨S, a, rfl, rfl, Sinside, by simpa [a] using firstSum,
    by simpa [a] using secondSum, by simpa [a] using seam, ?_⟩
  intro j
  unfold baseCode
  split_ifs with one last mid donor
  · exact congrArg g (congrArg (membership m H) (atOne j one)).symm
  · exact congrArg g (congrArg (membership m H) (atLast j last)).symm
  · exact Prod.ext (by simpa [a] using subsetBit j mid) (by simpa using (internalZero j mid).symm)
  all_goals
    rw [outside_label m H inside j (by omega)]
    apply Prod.ext <;> simp [a, baseZero]

private theorem four_attainment {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v)
    (four : (fullImage m H).card = 4) (admitted : piFour m H) :
    ∃ (g : Pair → Pair) (S : Finset ℕ) (a : BaseAssignment),
      Function.Bijective g ∧ g (pivot m H) = 0 ∧ (g 0).1 = 0 ∧
      (∀ z ∈ internalImage m H, (g z).2 = 0) ∧
      S = (Finset.Ico 2 m).filter (fun h => (g (membership m H (h : ℕ))).1 = 1) ∧
      a = ⟨0, (g 0).2, 0, g (membership m H (1 : ℕ)), g (membership m H (m : ℕ))⟩ ∧
      (∀ h ∈ S, 2 ≤ h ∧ h < m) ∧
      (S.card : ZMod 2) + a.flip * (m : ℕ) + a.left.1 + a.right.1 = 0 ∧
      a.exterior * ((m : ZMod 2) + 1) + a.donor + a.left.2 + a.right.2 = 0 ∧
      (a.right.2 = 0 ∨ a.exterior + a.donor = 1 ∨ a.right.1 = 0) ∧
      (∀ j, baseCode m S a j = g (membership m H j)) ∧
      (baseWords m S a).length = 2 ∧
      OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2 ∧
      ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
        endpointDifferences (some v)
          ((scriptArchive (baseWords m S a) (some ⟨v, -j, s⟩)).map Prod.snd) =
          [some (g (membership m H j)).1, some (g (membership m H j)).2] ∧
        (scriptArchive (baseWords m S a) (some ⟨v, -j, s⟩)).length = 2 ∧
        ((scriptArchive (baseWords m S a) (some ⟨v, -j, s⟩)).flatMap
          (fun b => List.ofFn b.1)).length = 2 * m := by
  classical
  have full : fullImage m H = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa [ZMod.card] using four)
  have regions := image_regions m hm H inside
  rw [full] at regions
  have encoded : Finset.univ.filter (fun z => decide (z ∈ internalImage m H) = true) = internalImage m H := by
    ext z; simp
  have selection := normalized_selection (fun z => decide (z ∈ internalImage m H)) (pivot m H)
    (membership m H (1 : ℕ)) (membership m H (m : ℕ))
  simp only [encoded] at selection
  obtain ⟨g, bijective, pivotZero, baseZero, internal, seam⟩ := selection regions.symm admitted.1 admitted.2
  obtain ⟨S, a, subset, assignment, Sinside, first, second, safe, codes⟩ :=
    normalized_physical_rows m hm H inside g bijective pivotZero baseZero internal seam
  have refines (p q : Phase m) (same : baseCode m S a p = baseCode m S a q) :
      membership m H p = membership m H q := by
    rw [codes p, codes q] at same
    exact bijective.1 same
  let label (v : ZMod 2) (z : Pair) : Y :=
    if v = 0 then (if z.1 = 0 then A v else B v) else (if z.2 = 0 then A v else B v)
  have labels (v : ZMod 2) (j : Phase m) (s : ℕ) (hs : s < 2 * m - 2) :
      f (some ⟨v, -j, s⟩) = label v (membership m H j) := by
    rw [target v j s hs]
    have vc : v = 0 ∨ v = 1 := by decide +revert
    rcases vc with rfl | rfl <;> simp [label, membership, supportRow]
  let decode (v : ZMod 2) (ar : NarrowWindowCost.Archive m) : Y :=
    if h : ∃ j, [some (baseCode m S a j).1, some (baseCode m S a j).2] =
        endpointDifferences (some v) (ar.map Prod.snd)
    then label v (membership m H (Classical.choose h)) else f none
  have feasible : OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2 := by
    change OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f (baseWords m S a).length
    apply script_global_preset (2 * m - 2) m (by omega) (by omega) alphabet f _ decode
    intro v phase s hs
    have readings := base_script_code m hm S Sinside a first second safe v (-phase) s hs
    simp only [neg_neg] at readings
    have existsPhase : ∃ j, [some (baseCode m S a j).1, some (baseCode m S a j).2] =
        endpointDifferences (some v) ((scriptArchive (baseWords m S a) (some ⟨v, phase, s⟩)).map Prod.snd) :=
      ⟨-phase, readings.symm⟩
    dsimp only [decode]
    rw [dif_pos existsPhase]
    have same := (Classical.choose_spec existsPhase).trans readings
    simp only [List.cons.injEq, Option.some.injEq] at same
    rw [refines _ _ (Prod.ext same.1 same.2.1)]
    simpa only [neg_neg] using (labels v (-phase) s hs).symm
  refine ⟨g, S, a, bijective, pivotZero, baseZero, internal, subset, assignment,
    Sinside, first, second, safe, codes, rfl, feasible, ?_⟩
  intro v j s hs
  refine ⟨by rw [← codes]; exact base_script_code m hm S Sinside a first second safe v j s hs, ?_, ?_⟩
  · simp [baseWords, scriptArchive]
  · change (archiveWords (scriptArchive (baseWords m S a) (some ⟨v, -j, s⟩))).length = _
    rw [archive_length]
    simp [baseWords, scriptArchive]

/-- The phase-once parity pivot gives the full saturated four-label compatibility
relation and a normalized common stream safe on the original inherited-tail prior. -/
theorem original_first_window_four_label_compatibility {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v)
    (four : (fullImage m H).card = 4) :
    (∀ d : Pair, (∀ z, z ≠ d →
      (multiplicity m H z : ZMod 2) ≠ (multiplicity m H d : ZMod 2)) ↔ pivot m H = d) ∧
    (OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2 ↔ piFour m H) ∧
    (piFour m H →
    ∃ (g : Pair → Pair) (S : Finset ℕ) (a : BaseAssignment),
      Function.Bijective g ∧ g (pivot m H) = 0 ∧ (g 0).1 = 0 ∧
      (∀ z ∈ internalImage m H, (g z).2 = 0) ∧
      S = (Finset.Ico 2 m).filter (fun h => (g (membership m H (h : ℕ))).1 = 1) ∧
      a = ⟨0, (g 0).2, 0, g (membership m H (1 : ℕ)), g (membership m H (m : ℕ))⟩ ∧
      (∀ h ∈ S, 2 ≤ h ∧ h < m) ∧
      (S.card : ZMod 2) + a.flip * (m : ℕ) + a.left.1 + a.right.1 = 0 ∧
      a.exterior * ((m : ZMod 2) + 1) + a.donor + a.left.2 + a.right.2 = 0 ∧
      (a.right.2 = 0 ∨ a.exterior + a.donor = 1 ∨ a.right.1 = 0) ∧
      (∀ j, baseCode m S a j = g (membership m H j)) ∧
      (baseWords m S a).length = 2 ∧
      OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2 ∧
      ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
        endpointDifferences (some v)
          ((scriptArchive (baseWords m S a) (some ⟨v, -j, s⟩)).map Prod.snd) =
          [some (g (membership m H j)).1, some (g (membership m H j)).2] ∧
        (scriptArchive (baseWords m S a) (some ⟨v, -j, s⟩)).length = 2 ∧
        ((scriptArchive (baseWords m S a) (some ⟨v, -j, s⟩)).flatMap
          (fun b => List.ofFn b.1)).length = 2 * m) := by
  refine ⟨pivot_multiplicity m hm H, ⟨four_necessary m hm alphabet H inside A B distinct f target four, ?_⟩,
    four_attainment m hm alphabet H inside A B distinct f target four⟩
  intro admitted
  obtain ⟨g, S, a, _, _, _, _, _, _, _, _, _, _, _, _, feasible, _⟩ :=
    four_attainment m hm alphabet H inside A B distinct f target four admitted
  exact feasible

#print axioms original_first_window_four_label_compatibility

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryFourLabels
