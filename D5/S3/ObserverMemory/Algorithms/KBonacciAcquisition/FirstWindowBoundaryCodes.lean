/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryCodes
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryCodes
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Original two-block rows refine both fibres and homogeneous internal labels have safe common inverses. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes
open D5.S0.Tower.DBonacci.Names
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells WindowChargeInverse PhysicalWindowDecoder
open OriginalNarrowCost OriginalAcquiredTrace OriginalExecutionBridge DonorCorrection
open FirstWindowBoundaryAttainment GlobalPresetObstruction
open scoped BigOperators

/-- Membership is ordered by the two remembered free values, not by output-label identity. -/
def membership (m : ℕ) (H : ZMod 2 → Finset ℕ) (j : Phase m) : Pair :=
  (supportRow (H 0) j.val, supportRow (H 1) j.val)

def internalPhases (m : ℕ) : Finset (Phase m) :=
  Finset.univ.filter (fun j => 2 ≤ j.val ∧ j.val < m)

def internalImage (m : ℕ) (H : ZMod 2 → Finset ℕ) : Finset Pair :=
  (internalPhases m).image (membership m H)

/-- Rows of the actual first and second scheduled moving windows. A scheduled
row on a stopped source is a proof profile, not an acquired observation. -/
def firstCharge (m : ℕ) (stream : ℕ → Fin m → Bool) (j : Phase m) : ZMod 2 :=
  wordIncrement (2 * m - 2) (-j) (stream 0)
def secondCharge (m : ℕ) (stream : ℕ → Fin m → Bool) (j : Phase m) : ZMod 2 :=
  wordIncrement (2 * m - 2) (-j + (m : ℕ)) (stream 1)

private theorem necessary_rows {Y : Type u} (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v)
    (feasible : OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2) :
    ∃ (stream : ℕ → Fin m → Bool)
      (stop : Option (ZMod 2) → NarrowWindowCost.Archive m → Option Y),
      (∀ v, FiberCorrect m hm alphabet f v 2 (presetSelector stream stop)) ∧
      ((H 0).Nonempty → stop (some 0) [] = none ∧ stream 0 ⟨0, by omega⟩ = false ∧
        ∀ j, ¬ (1 ≤ j.val ∧ j.val ≤ m) → firstCharge m stream j = 0) ∧
      (∀ j, 2 ≤ j.val → j.val < m → secondCharge m stream j = 0) ∧
      (∑ j, firstCharge m stream j) = 0 ∧ (∑ j, secondCharge m stream j) = 0 ∧
      (∀ p q, firstCharge m stream p = firstCharge m stream q →
        secondCharge m stream p = secondCharge m stream q → membership m H p = membership m H q) ∧
      (internalImage m H).card ≤ 2 := by
  classical
  obtain ⟨stream, stop, _, _, correct⟩ := feasible
  have fiber (v : ZMod 2) : FiberCorrect m hm alphabet f v 2 (presetSelector stream stop) := by
    intro history
    dsimp only
    intro hv
    obtain ⟨c, bound, ex⟩ := correct history
    rw [hv] at ex
    exact ⟨c, bound, ex⟩
  have native (v : ZMod 2) (j : Phase m) (s : ℕ) (hs : s < 2 * m - 2) :
      ∃ c, NativeExecute (presetSelector stream stop) 2 (some ⟨v, -j, s⟩) (some v) [] =
        some ((if j.val ∈ H v then B v else A v), c) := by
    obtain ⟨c, _, ex⟩ := OwnPathCharges.native_fiber (2 * m - 2) m (by omega)
      (by omega) alphabet f v 2 _ (fiber v) (-j) s hs
      (by rw [FourLabelPaidFeedback.coprime m hm]; exact one_dvd _)
    rw [target v j s hs] at ex
    exact ⟨c, ex⟩
  have refines (p q : Phase m) (ha : firstCharge m stream p = firstCharge m stream q)
      (hb : secondCharge m stream p = secondCharge m stream q) : membership m H p = membership m H q := by
    have scalar (v : ZMod 2) : supportRow (H v) p.val = supportRow (H v) q.val := by
      obtain ⟨c, ex⟩ := native v p 0 (by omega)
      obtain ⟨c', ey⟩ := native v q 0 (by omega)
      have same := native_two_same (2 * m - 2) m (by omega) stream stop v (-p) (-q) 0 (by omega) ha hb
      rw [ex, ey] at same
      have labels := (Prod.mk.inj (Option.some.inj same)).1
      by_cases hp : p.val ∈ H v <;> by_cases hq : q.val ∈ H v
      · simp [supportRow, hp, hq]
      · rw [if_pos hp, if_neg hq] at labels
        exact (distinct v labels.symm).elim
      · rw [if_neg hp, if_pos hq] at labels
        exact (distinct v labels).elim
      · simp [supportRow, hp, hq]
    exact Prod.ext (scalar 0) (scalar 1)
  have blind (j : Phase m) (lo : 2 ≤ j.val) (hi : j.val < m) : secondCharge m stream j = 0 :=
    second_charge_blind m hm (stream 1) j lo hi
  have internalBound : (internalImage m H).card ≤ 2 := by
    let pick (z : Pair) (hz : z ∈ internalImage m H) : Phase m :=
      Classical.choose (Finset.mem_image.mp hz)
    have picked (z : Pair) (hz : z ∈ internalImage m H) :
        pick z hz ∈ internalPhases m ∧ membership m H (pick z hz) = z :=
      Classical.choose_spec (Finset.mem_image.mp hz)
    let select (z : Pair) : ZMod 2 :=
      if hz : z ∈ internalImage m H then firstCharge m stream (pick z hz) else 0
    have inj : Set.InjOn select (internalImage m H) := by
      intro z hz w hw same
      change z ∈ internalImage m H at hz
      change w ∈ internalImage m H at hw
      dsimp only [select] at same
      rw [dif_pos hz, dif_pos hw] at same
      have zj := Finset.mem_filter.mp (picked z hz).1
      have wj := Finset.mem_filter.mp (picked w hw).1
      have eq := refines _ _ same ((blind _ zj.2.1 zj.2.2).trans (blind _ wj.2.1 wj.2.2).symm)
      exact (picked z hz).2.symm.trans (eq.trans (picked w hw).2)
    have bound := Finset.card_le_card_of_injOn select
      (t := Finset.univ) (by intro z hz; exact Finset.mem_univ _) inj
    simpa using bound
  refine ⟨stream, stop, fiber, ?_, blind,
    by simpa [firstCharge] using charge_even (2 * m - 2) m (by omega) 0 (stream 0),
    by simpa [secondCharge] using charge_even (2 * m - 2) m (by omega) (m : ℕ) (stream 1), refines, internalBound⟩
  intro nonempty
  obtain ⟨h, hmem⟩ := nonempty
  have hb := inside 0 h hmem
  have hval : ((h : ℕ) : Phase m).val = h := ZMod.val_natCast_of_lt (by omega)
  have zero : 0 ∉ H 0 := by intro hz; have := inside 0 0 hz; omega
  let table (j : Phase m) : Y := if j.val ∈ H 0 then B 0 else A 0
  have nonconstant : ¬ ∃ y, ∀ j, table j = y := by
    rintro ⟨y, same⟩
    have eq := (same 0).trans (same (h : ℕ)).symm
    simp only [table, ZMod.val_zero, if_neg zero, hval, if_pos hmem] at eq
    exact distinct 0 eq
  have root : stop (some 0) [] = none := by
    cases chosen : stop (some 0) [] with
    | none => rfl
    | some label =>
      apply False.elim
      apply nonconstant
      refine ⟨label, ?_⟩
      intro j
      obtain ⟨c, ex⟩ := native 0 j 0 (by omega)
      simp only [native_succ, presetSelector, chosen] at ex
      exact (Prod.mk.inj (Option.some.inj ex)).1.symm
  have head : stream 0 ⟨0, by omega⟩ = false :=
    OwnPathCharges.root_zero (2 * m - 2) m (by omega) (by omega) table
      (presetSelector stream stop) 2 (native 0) nonconstant (stream 0)
      (by simp [presetSelector, root])
  refine ⟨root, head, ?_⟩
  intro j outside
  rw [firstCharge, increment_derivative (2 * m - 2) (by omega) m (by omega)]
  by_cases z : j.val = 0
  · simp [z, extendedBit, bitScalar, head, show 0 < m by omega]
  · have large : m < j.val := by omega
    simp [extendedBit, z, show ¬ j.val < m by omega, show ¬ j.val - 1 < m by omega]

/-- The two ordered inverse rows for a homogeneous internal image. -/
def homogeneousRoot (m : ℕ) : Finset ℕ :=
  if Odd m then Finset.Ico 1 m else {1, m}
def homogeneousSecond (m : ℕ) : Finset ℕ :=
  if Odd m then {0, m} else Finset.Icc 1 m

def homogeneousWords (m : ℕ) : List (Fin m → Bool) :=
  [prefixWord m (supportRow (homogeneousRoot m)),
   prefixWord m (supportRow (homogeneousSecond m))]

def homogeneousCode (m : ℕ) (j : Phase m) : List (Option (ZMod 2)) :=
  if Odd m then
    [some (if 1 ≤ j.val ∧ j.val < m then 1 else 0),
     some (if j.val = 1 ∨ j.val = m then 1 else 0)]
  else [some (if j.val = 1 ∨ j.val = m then 1 else 0),
    some (if j.val = m ∨ (2 ≤ j.val ∧ j.val < m) then 0 else 1)]

private theorem homogeneous_even (m : ℕ) (hm : 5 ≤ m) :
    (∑ h ∈ Finset.range (m + 1), supportRow (homogeneousRoot m) h) = 0 ∧
    (∑ h ∈ Finset.range (m + 1), supportRow (homogeneousSecond m) h) = 0 ∧
    supportRow (homogeneousRoot m) 0 = 0 := by
  classical
  have rootInside : ∀ h ∈ homogeneousRoot m, h ≤ m := by
    intro h hh
    unfold homogeneousRoot at hh
    split_ifs at hh <;> simp_all <;> omega
  have secondInside : ∀ h ∈ homogeneousSecond m, h ≤ m := by
    intro h hh
    unfold homogeneousSecond at hh
    split_ifs at hh <;> simp_all <;> omega
  rw [support_sum m _ rootInside, support_sum m _ secondInside]
  by_cases odd : Odd m
  · have rootCard : (homogeneousRoot m).card = m - 1 := by simp [homogeneousRoot, odd]
    have secondCard : (homogeneousSecond m).card = 2 := by
      simp [homogeneousSecond, odd, show (0 : ℕ) ≠ m by omega]
    have even : Even (m - 1) := by
      obtain ⟨n, hn⟩ := odd
      exact ⟨n, by omega⟩
    rw [rootCard, secondCard]
    refine ⟨even.natCast_zmod_two, by decide, ?_⟩
    simp [supportRow, homogeneousRoot, odd]
  · have rootCard : (homogeneousRoot m).card = 2 := by
      simp [homogeneousRoot, odd, show (1 : ℕ) ≠ m by omega]
    have secondCard : (homogeneousSecond m).card = m := by
      simp [homogeneousSecond, odd]
    have even : Even m := Nat.not_odd_iff_even.mp odd
    rw [rootCard, secondCard]
    refine ⟨by decide, even.natCast_zmod_two, ?_⟩
    simp [supportRow, homogeneousRoot, odd, show (0 : ℕ) ≠ m by omega]

private theorem homogeneous_charges (m : ℕ) (hm : 5 ≤ m) (j : Phase m) :
    [some (windowCharge (2 * m - 2) m (supportRow (homogeneousRoot m)) j),
     some (windowCharge (2 * m - 2) m (supportRow (homogeneousSecond m)) (j - (m : ℕ)))] =
      homogeneousCode m j := by
  have shift := shift_value m m hm (by omega) j
  have bound := ZMod.val_lt j
  have first : windowCharge (2 * m - 2) m (supportRow (homogeneousRoot m)) j =
      if Odd m then (if 1 ≤ j.val ∧ j.val < m then 1 else 0)
      else (if j.val = 1 ∨ j.val = m then 1 else 0) := by
    unfold windowCharge homogeneousRoot supportRow
    by_cases odd : Odd m <;> simp only [odd, if_true, if_false, Finset.mem_Ico,
      Finset.mem_insert, Finset.mem_singleton] <;> split_ifs <;> simp_all <;> omega
  have second : windowCharge (2 * m - 2) m (supportRow (homogeneousSecond m)) (j - (m : ℕ)) =
      if Odd m then (if j.val = 1 ∨ j.val = m then 1 else 0)
      else (if j.val = m ∨ (2 ≤ j.val ∧ j.val < m) then 0 else 1) := by
    unfold windowCharge
    rw [shift]
    unfold homogeneousSecond supportRow
    by_cases odd : Odd m <;> by_cases large : m ≤ j.val <;>
      simp only [odd, large, if_true, if_false, Finset.mem_Icc,
        Finset.mem_insert, Finset.mem_singleton] <;>
      split_ifs <;> simp_all <;> omega
  rw [first, second]
  unfold homogeneousCode
  split_ifs <;> rfl

private theorem homogeneous_script_code (m : ℕ) (hm : 5 ≤ m)
    (v : ZMod 2) (j : Phase m) (s : ℕ) (hs : s < 2 * m - 2) :
    endpointDifferences (some v)
      ((scriptArchive (homogeneousWords m) (some ⟨v, -j, s⟩)).map Prod.snd) =
      homogeneousCode m j := by
  obtain ⟨rootSum, secondSum, rootZero⟩ := homogeneous_even m hm
  obtain ⟨rootInv, rootHead, rootLast, _⟩ := short_window_charge_inverse
    (2 * m - 2) (by omega) m (by omega) (by omega) (supportRow (homogeneousRoot m)) rootSum
  obtain ⟨secondInv, secondHead, _, _⟩ := short_window_charge_inverse
    (2 * m - 2) (by omega) m (by omega) (by omega) (supportRow (homogeneousSecond m)) secondSum
  have headZero := rootHead.mpr rootZero
  obtain ⟨rootStep, rootTail⟩ := short_safe_execution (2 * m - 2) (by omega) m (by omega)
    (by omega) (prefixWord m (supportRow (homogeneousRoot m))) v (-j) s hs (Or.inr headZero)
  have incoming : tailAfter 0 (prefixWord m (supportRow (homogeneousRoot m))) = 0 ∨
      prefixWord m (supportRow (homogeneousSecond m)) ⟨0, by omega⟩ = false := by
    by_cases odd : Odd m
    · left
      have lastZero := rootLast.mpr (by simp [homogeneousRoot, supportRow, odd])
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      cases hn
      exact last_false_tail n _ 0 lastZero
    · right
      exact secondHead.mpr (by simp [homogeneousSecond, supportRow, odd])
  have secondStep := (short_safe_execution (2 * m - 2) (by omega) m (by omega) (by omega)
    (prefixWord m (supportRow (homogeneousSecond m)))
    (v + wordIncrement (2 * m - 2) (-j) (prefixWord m (supportRow (homogeneousRoot m))))
    (-j + (m : ℕ)) _ rootTail incoming).1
  have eq : -j + (m : ℕ) = -(j - (m : ℕ)) := by ring
  simp only [homogeneousWords, scriptArchive, rootStep, secondStep, endpointReading,
    List.map_cons, List.map_nil, endpointDifferences, Option.map_some]
  rw [eq, rootInv, secondInv]
  convert homogeneous_charges m hm j using 1 <;> simp [endpointDifferences]

theorem homogeneous_separates (m : ℕ) (hm : 5 ≤ m) (table : Phase m → Pair)
    (outside : ∀ j, ¬ (1 ≤ j.val ∧ j.val ≤ m) → table j = 0)
    (homogeneous : ∀ p q, 2 ≤ p.val → p.val < m → 2 ≤ q.val → q.val < m → table p = table q)
    (j l : Phase m) (same : homogeneousCode m j = homogeneousCode m l) : table j = table l := by
  have regions : (j.val = 1 ↔ l.val = 1) ∧ (j.val = m ↔ l.val = m) ∧
      ((2 ≤ j.val ∧ j.val < m) ↔ (2 ≤ l.val ∧ l.val < m)) := by
    unfold homogeneousCode at same
    by_cases odd : Odd m <;> simp only [odd, if_true, if_false, List.cons.injEq,
      Option.some.injEq] at same <;>
      rcases same with ⟨a, b, _⟩ <;>
      split_ifs at a b <;> simp_all <;> omega
  by_cases one : j.val = 1
  · exact congrArg table (ZMod.val_injective _ (one.trans (regions.1.mp one).symm))
  by_cases last : j.val = m
  · exact congrArg table (ZMod.val_injective _ (last.trans (regions.2.1.mp last).symm))
  by_cases internal : 2 ≤ j.val ∧ j.val < m
  · exact homogeneous j l internal.1 internal.2 (regions.2.2.mp internal).1 (regions.2.2.mp internal).2
  · have lOne : l.val ≠ 1 := fun h => one (regions.1.mpr h)
    have lLast : l.val ≠ m := fun h => last (regions.2.1.mpr h)
    have lInternal : ¬ (2 ≤ l.val ∧ l.val < m) := fun h => internal (regions.2.2.mpr h)
    exact (outside j (by omega)).trans (outside l (by omega)).symm

/-- Actual shared two-row refinement, the internal-image obstruction, and the
safe two-block inverse stream whenever the internal membership image is one label. -/
theorem original_first_window_boundary_rows {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v) :
    (OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2 →
      ∃ (stream : ℕ → Fin m → Bool)
        (stop : Option (ZMod 2) → NarrowWindowCost.Archive m → Option Y),
        (∀ v, FiberCorrect m hm alphabet f v 2 (presetSelector stream stop)) ∧
        ((H 0).Nonempty → stop (some 0) [] = none ∧ stream 0 ⟨0, by omega⟩ = false ∧
          ∀ j, ¬ (1 ≤ j.val ∧ j.val ≤ m) → firstCharge m stream j = 0) ∧
        (∀ j, 2 ≤ j.val → j.val < m → secondCharge m stream j = 0) ∧
        (∑ j, firstCharge m stream j) = 0 ∧ (∑ j, secondCharge m stream j) = 0 ∧
        (∀ p q, firstCharge m stream p = firstCharge m stream q →
          secondCharge m stream p = secondCharge m stream q → membership m H p = membership m H q) ∧
        (internalImage m H).card ≤ 2) ∧
    (homogeneousWords m).length = 2 ∧
    ((internalImage m H).card = 1 →
      OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2 ∧
      ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
        endpointDifferences (some v)
          ((scriptArchive (homogeneousWords m) (some ⟨v, -j, s⟩)).map Prod.snd) = homogeneousCode m j ∧
        (scriptArchive (homogeneousWords m) (some ⟨v, -j, s⟩)).length = 2 ∧
        ((scriptArchive (homogeneousWords m) (some ⟨v, -j, s⟩)).flatMap
          (fun a => List.ofFn a.1)).length = 2 * m) := by
  classical
  refine ⟨necessary_rows m hm alphabet H inside A B distinct f target, rfl, ?_⟩
  intro internalOne
  have outside (j : Phase m) (hj : ¬ (1 ≤ j.val ∧ j.val ≤ m)) : membership m H j = 0 := by
    have absent (v : ZMod 2) : j.val ∉ H v := by
      intro mem
      exact hj (inside v j.val mem)
    simp [membership, supportRow, absent]
  have homogeneous (p q : Phase m) (plo : 2 ≤ p.val) (phi : p.val < m)
      (qlo : 2 ≤ q.val) (qhi : q.val < m) : membership m H p = membership m H q := by
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp internalOne
    have mem (j : Phase m) (lo : 2 ≤ j.val) (hi : j.val < m) : membership m H j ∈ internalImage m H :=
      Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, lo, hi⟩, rfl⟩
    have pe := mem p plo phi
    have qe := mem q qlo qhi
    rw [hz, Finset.mem_singleton] at pe qe
    exact pe.trans qe.symm
  let label (v : ZMod 2) (z : Pair) : Y :=
    if v = 0 then (if z.1 = 0 then A v else B v) else (if z.2 = 0 then A v else B v)
  have labels (v : ZMod 2) (j : Phase m) (s : ℕ) (hs : s < 2 * m - 2) :
      f (some ⟨v, -j, s⟩) = label v (membership m H j) := by
    rw [target v j s hs]
    have vc : v = 0 ∨ v = 1 := by
      fin_cases v
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases vc with rfl | rfl <;> simp [label, membership, supportRow]
  let decode (v : ZMod 2) (ar : NarrowWindowCost.Archive m) : Y :=
    if h : ∃ j, homogeneousCode m j = endpointDifferences (some v) (ar.map Prod.snd)
    then label v (membership m H (Classical.choose h)) else f none
  have feasible : OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2 := by
    have count : (homogeneousWords m).length = 2 := rfl
    change OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f (homogeneousWords m).length
    apply script_global_preset (2 * m - 2) m (by omega) (by omega) alphabet f (homogeneousWords m) decode
    intro v phase s hs
    have readings := homogeneous_script_code m hm v (-phase) s hs
    simp only [neg_neg] at readings
    have existsPhase : ∃ j, homogeneousCode m j = endpointDifferences (some v)
        ((scriptArchive (homogeneousWords m) (some ⟨v, phase, s⟩)).map Prod.snd) :=
      ⟨-phase, readings.symm⟩
    dsimp only [decode]
    rw [dif_pos existsPhase]
    have separated := homogeneous_separates m hm (membership m H) outside homogeneous _ (-phase)
      ((Classical.choose_spec existsPhase).trans readings)
    rw [separated]
    simpa only [neg_neg] using (labels v (-phase) s hs).symm
  refine ⟨feasible, ?_⟩
  intro v j s hs
  refine ⟨homogeneous_script_code m hm v j s hs, ?_, ?_⟩
  · simp [homogeneousWords, scriptArchive]
  · change (archiveWords (scriptArchive (homogeneousWords m) (some ⟨v, -j, s⟩))).length = _
    rw [archive_length]
    simp [homogeneousWords, scriptArchive]

#print axioms original_first_window_boundary_rows

/-- The full image counts actual phases, independently of their realizing histories. -/
def fullImage (m : ℕ) (H : ZMod 2 → Finset ℕ) : Finset Pair :=
  Finset.univ.image (membership m H)

private def threeClass (x y : Fin 3) (i : Fin 5) : Fin 3 :=
  if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 2 else if i = 3 then x else y

private def threeCode (flip : ZMod 2) (left right : Pair) (i : Fin 5) : Pair :=
  if i = 0 then (0, 1) else if i = 1 then (flip, 0)
  else if i = 2 then (flip + 1, 0) else if i = 3 then left else right

/-- Boundary codes may split a repeated label; only unequal labels must separate. -/
private theorem three_selection : ∀ (e t : ZMod 2) (x y : Fin 3),
    e = 1 ∨ x ≠ 0 ∨ y ≠ 0 →
    ∃ (flip : ZMod 2) (left right : Pair),
      t + flip * e + left.1 + right.1 = 0 ∧
      e + 1 + left.2 + right.2 = 0 ∧
      ∀ i j, threeCode flip left right i = threeCode flip left right j →
        threeClass x y i = threeClass x y j := by
  decide

/-- The first row occupies B and the second occupies R and the two boundaries.
The offset one of the second path is the actual exterior phase m+1. -/
def nonbaseRoot (m : ℕ) (S : Finset ℕ) (flip : ZMod 2) (left right : Pair)
    (h : ℕ) : ZMod 2 :=
  supportRow S h + flip * supportRow (Finset.Ico 2 m) h +
    left.1 * supportRow {1} h + right.1 * supportRow {m} h

def nonbaseSecond (m : ℕ) (left right : Pair) (h : ℕ) : ZMod 2 :=
  supportRow (Finset.Ico 1 m) h + right.2 * supportRow {0} h +
    left.2 * supportRow {m} h

def nonbaseWords (m : ℕ) (S : Finset ℕ) (flip : ZMod 2) (left right : Pair) :
    List (Fin m → Bool) :=
  [prefixWord m (nonbaseRoot m S flip left right), prefixWord m (nonbaseSecond m left right)]

def nonbaseCode (m : ℕ) (S : Finset ℕ) (flip : ZMod 2) (left right : Pair)
    (j : Phase m) : Pair :=
  if j.val = 1 then left else if j.val = m then right
  else if 2 ≤ j.val ∧ j.val < m then (supportRow S j.val + flip, 0) else (0, 1)

theorem nonbase_even (m : ℕ) (hm : 5 ≤ m) (S : Finset ℕ)
    (inside : ∀ h ∈ S, 2 ≤ h ∧ h < m) (flip : ZMod 2) (left right : Pair)
    (first : (S.card : ZMod 2) + flip * (m : ℕ) + left.1 + right.1 = 0)
    (second : (m : ZMod 2) + 1 + left.2 + right.2 = 0) :
    (∑ h ∈ Finset.range (m + 1), nonbaseRoot m S flip left right h) = 0 ∧
    (∑ h ∈ Finset.range (m + 1), nonbaseSecond m left right h) = 0 ∧
    nonbaseRoot m S flip left right 0 = 0 := by
  have ssum := support_sum m S (by intro h hh; have := inside h hh; omega)
  have usum := support_sum m (Finset.Ico 2 m) (by intro h hh; simp at hh; omega)
  have rsum := support_sum m (Finset.Ico 1 m) (by intro h hh; simp at hh; omega)
  have onesum := support_sum m {1} (by intro h hh; simp at hh; omega)
  have lastsum := support_sum m {m} (by intro h hh; simp at hh; omega)
  have zerosum := support_sum m {0} (by intro h hh; simp at hh; omega)
  have um : ((m - 2 : ℕ) : ZMod 2) = (m : ℕ) := by
    rw [Nat.cast_sub (by omega : 2 ≤ m)]
    rw [show ((2 : ℕ) : ZMod 2) = 0 by decide, sub_zero]
  have rm : ((m - 1 : ℕ) : ZMod 2) = (m : ℕ) + 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    simp only [Nat.cast_one, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  have absent : 0 ∉ S := by intro mem; have := inside 0 mem; omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [nonbaseRoot, Finset.sum_add_distrib, ← Finset.mul_sum,
      ssum, usum, onesum, lastsum, Nat.card_Ico, Finset.card_singleton,
      Nat.cast_one, mul_one, um]
    exact first
  · simp only [nonbaseSecond, Finset.sum_add_distrib, ← Finset.mul_sum,
      rsum, zerosum, lastsum, Nat.card_Ico, Finset.card_singleton,
      Nat.cast_one, mul_one, rm]
    simpa only [add_assoc, add_comm, add_left_comm] using second
  · simp [nonbaseRoot, supportRow, absent, show (0 : ℕ) ≠ m by omega]

theorem nonbase_charges (m : ℕ) (hm : 5 ≤ m) (S : Finset ℕ)
    (inside : ∀ h ∈ S, 2 ≤ h ∧ h < m) (flip : ZMod 2) (left right : Pair)
    (j : Phase m) :
    (windowCharge (2 * m - 2) m (nonbaseRoot m S flip left right) j,
     windowCharge (2 * m - 2) m (nonbaseSecond m left right) (j - (m : ℕ))) =
      nonbaseCode m S flip left right j := by
  have shift := shift_value m m hm (by omega) j
  have bound := ZMod.val_lt j
  have absent (h : ℕ) (hh : ¬ (2 ≤ h ∧ h < m)) : h ∉ S :=
    fun mem => hh (inside h mem)
  have oneAbsent : 1 ∉ S := absent 1 (by omega)
  have lastAbsent : m ∉ S := absent m (by omega)
  apply Prod.ext
  · by_cases one : j.val = 1
    · simp [windowCharge, nonbaseRoot, nonbaseCode, one, supportRow, oneAbsent,
        show (1 : ℕ) ≠ m by omega, show 1 ≤ m by omega]
    · by_cases last : j.val = m
      · simp [windowCharge, nonbaseRoot, nonbaseCode, one, last, supportRow, lastAbsent, show m ≠ 1 by omega]
      · by_cases mid : 2 ≤ j.val ∧ j.val < m
        · simp [windowCharge, nonbaseRoot, nonbaseCode, one, last, mid, supportRow,
            show j.val ≤ m by omega, add_comm]
        · have noS := absent j.val mid
          simp [windowCharge, nonbaseRoot, nonbaseCode, one, last, mid, supportRow, noS]
  · by_cases one : j.val = 1
    · have localVal : (j - (m : ℕ)).val = m := by rw [shift, if_neg (by omega)]; omega
      simp [windowCharge, localVal, nonbaseSecond, nonbaseCode, one, supportRow,
        show m ≠ 0 by omega]
    · by_cases last : j.val = m
      · have localVal : (j - (m : ℕ)).val = 0 := by rw [shift, if_pos (by omega)]; omega
        simp [windowCharge, localVal, nonbaseSecond, nonbaseCode, last, supportRow,
          show (0 : ℕ) ≠ m by omega, show m ≠ 1 by omega]
      · by_cases mid : 2 ≤ j.val ∧ j.val < m
        · have large : m < (j - (m : ℕ)).val := by rw [shift, if_neg (by omega)]; omega
          simp [windowCharge, nonbaseCode, one, last, mid, show ¬ (j - (m : ℕ)).val ≤ m by omega]
        · have localVal : 1 ≤ (j - (m : ℕ)).val ∧ (j - (m : ℕ)).val < m := by
            rw [shift]
            split_ifs <;> omega
          simp [windowCharge, nonbaseSecond, nonbaseCode, one, last, mid, supportRow,
            localVal, show (j - (m : ℕ)).val ≤ m by omega,
            show (j - (m : ℕ)).val ≠ 0 by omega, show (j - (m : ℕ)).val ≠ m by omega]

private theorem nonbase_script_code (m : ℕ) (hm : 5 ≤ m) (S : Finset ℕ)
    (inside : ∀ h ∈ S, 2 ≤ h ∧ h < m) (flip : ZMod 2) (left right : Pair)
    (first : (S.card : ZMod 2) + flip * (m : ℕ) + left.1 + right.1 = 0)
    (second : (m : ZMod 2) + 1 + left.2 + right.2 = 0)
    (v : ZMod 2) (j : Phase m) (s : ℕ) (hs : s < 2 * m - 2) :
    endpointDifferences (some v)
      ((scriptArchive (nonbaseWords m S flip left right) (some ⟨v, -j, s⟩)).map Prod.snd) =
      [some (nonbaseCode m S flip left right j).1, some (nonbaseCode m S flip left right j).2] := by
  obtain ⟨rootSum, secondSum, rootZero⟩ := nonbase_even m hm S inside flip left right first second
  obtain ⟨rootInv, rootHead, _, _⟩ := short_window_charge_inverse
    (2 * m - 2) (by omega) m (by omega) (by omega) _ rootSum
  obtain ⟨secondInv, secondHead, _, _⟩ := short_window_charge_inverse
    (2 * m - 2) (by omega) m (by omega) (by omega) _ secondSum
  have headZero := rootHead.mpr rootZero
  obtain ⟨rootStep, rootTail⟩ := InternalZeroSafety.internal_zero_execution
    (2 * m - 2) (by omega) m (by omega) _ ⟨0, by omega⟩ headZero v (-j) s hs (Or.inr headZero)
  have tailBound : tailAfter 0 (prefixWord m (nonbaseRoot m S flip left right)) < 2 * m - 2 := by
    change tailAfter 0 (prefixWord m (nonbaseRoot m S flip left right)) ≤ m - 1 at rootTail
    omega
  have secondStep := by
    show runBits (2 * m - 2) (prefixWord m (nonbaseSecond m left right))
      (some ⟨v + wordIncrement (2 * m - 2) (-j) (prefixWord m (nonbaseRoot m S flip left right)),
        -j + (m : ℕ), tailAfter 0 (prefixWord m (nonbaseRoot m S flip left right))⟩) =
      some ⟨v + wordIncrement (2 * m - 2) (-j) (prefixWord m (nonbaseRoot m S flip left right)) +
        wordIncrement (2 * m - 2) (-j + (m : ℕ)) (prefixWord m (nonbaseSecond m left right)),
        -j + (m : ℕ) + (m : ℕ), tailAfter 0 (prefixWord m (nonbaseSecond m left right))⟩
    by_cases clear : right.2 = 0
    · have head := secondHead.mpr (by simp [nonbaseSecond, supportRow, clear, show (0 : ℕ) ≠ m by omega])
      exact (short_safe_execution (2 * m - 2) (by omega) m (by omega) (by omega) _ _ _ _ tailBound (Or.inr head)).1
    · have one : right.2 = 1 := by
        have bound := ZMod.val_lt right.2
        have nonzero := (ZMod.val_ne_zero right.2).mpr clear
        exact ZMod.val_injective 2 (by change _ = 1; omega)
      have marked : prefixWord m (nonbaseSecond m left right) ⟨1, by omega⟩ = false := by
        simp [prefixWord, Finset.sum_range_succ, nonbaseSecond, supportRow, one,
          show (0 : ℕ) ≠ m by omega, show (1 : ℕ) ≠ m by omega, show 1 < m by omega, CharTwo.add_self_eq_zero]
      exact (InternalZeroSafety.internal_zero_execution (2 * m - 2) (by omega) m (by omega)
        _ ⟨1, by omega⟩ marked _ _ _ tailBound
        (Or.inl (by change tailAfter 0 (prefixWord m (nonbaseRoot m S flip left right)) + 1 < 2 * m - 2; omega))).1
  have eq : -j + (m : ℕ) = -(j - (m : ℕ)) := by ring
  simp only [nonbaseWords, scriptArchive, rootStep, secondStep, endpointReading,
    List.map_cons, List.map_nil, endpointDifferences, Option.map_some]
  rw [eq, rootInv, secondInv]
  have charges := nonbase_charges m hm S inside flip left right j
  have a := congrArg Prod.fst charges
  have b := congrArg Prod.snd charges
  simp only [Prod.fst, Prod.snd] at a b
  rw [a, b]
  simp [endpointDifferences]

def classIndex (X z : Pair) : Fin 3 :=
  if z = 0 then 0 else if z = X then 1 else 2
def classLabel (X Y : Pair) (i : Fin 3) : Pair :=
  if i = 0 then 0 else if i = 1 then X else Y

theorem class_restore (X Y z : Pair) (Xzero : X ≠ 0) (Yzero : Y ≠ 0)
    (different : X ≠ Y) (member : z = 0 ∨ z = X ∨ z = Y) :
    classLabel X Y (classIndex X z) = z := by
  rcases member with rfl | rfl | rfl <;> simp [classIndex, classLabel, Xzero, Yzero, different.symm]

private theorem nonbase_necessary {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v)
    (two : (internalImage m H).card = 2)
    (nonbase : (0 : Pair) ∉ internalImage m H)
    (feasible : OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2) :
    Odd m ∨ membership m H (1 : ℕ) ≠ 0 ∨ membership m H (m : ℕ) ≠ 0 := by
  classical
  by_cases one : membership m H (1 : ℕ) ≠ 0
  · exact Or.inr (Or.inl one)
  by_cases last : membership m H (m : ℕ) ≠ 0
  · exact Or.inr (Or.inr last)
  have oneZero : membership m H (1 : ℕ) = 0 := not_ne_iff.mp one
  have lastZero : membership m H (m : ℕ) = 0 := not_ne_iff.mp last
  obtain ⟨stream, stop, _, _, blind, _, evenB, refines, _⟩ :=
    (original_first_window_boundary_rows m hm alphabet H inside A B distinct f target).1 feasible
  obtain ⟨X, Z, different, image⟩ := Finset.card_eq_two.mp two
  have xmem : X ∈ internalImage m H := by simp [image]
  have zmem : Z ∈ internalImage m H := by simp [image]
  have Xzero : X ≠ 0 := fun eq => nonbase (eq ▸ xmem)
  have Zzero : Z ≠ 0 := fun eq => nonbase (eq ▸ zmem)
  obtain ⟨p, pInternal, pLabel⟩ := Finset.mem_image.mp xmem
  obtain ⟨q, qInternal, qLabel⟩ := Finset.mem_image.mp zmem
  have pp := (Finset.mem_filter.mp pInternal).2
  have qq := (Finset.mem_filter.mp qInternal).2
  have pb := blind p pp.1 pp.2
  have qb := blind q qq.1 qq.2
  have differentCharge : firstCharge m stream p ≠ firstCharge m stream q := by
    intro same
    exact different (pLabel.symm.trans ((refines p q same (pb.trans qb.symm)).trans qLabel))
  have complete : ∀ (a b c : ZMod 2), a ≠ b → c = a ∨ c = b := by decide
  have base (j : Phase m) (out : ¬ (2 ≤ j.val ∧ j.val < m)) : membership m H j = 0 := by
    by_cases atOne : j.val = 1
    · have phase : j = (1 : ℕ) := ZMod.val_injective _
        (atOne.trans (ZMod.val_natCast_of_lt (by omega)).symm)
      simpa only [phase] using oneZero
    by_cases atLast : j.val = m
    · have phase : j = (m : ℕ) := ZMod.val_injective _
        (atLast.trans (ZMod.val_natCast_of_lt (by omega)).symm)
      simpa only [phase] using lastZero
    have absent (v : ZMod 2) : j.val ∉ H v := by
      intro mem
      have := inside v j.val mem
      omega
    simp [membership, supportRow, absent]
  have charges (j : Phase m) : secondCharge m stream j =
      1 - supportRow (Finset.Ico 2 m) j.val := by
    by_cases mid : 2 ≤ j.val ∧ j.val < m
    · simpa [supportRow, mid] using blind j mid.1 mid.2
    · have notZero : secondCharge m stream j ≠ 0 := by
        intro zero
        rcases complete _ _ (firstCharge m stream j) differentCharge with same | same
        · have bad := refines j p same (zero.trans pb.symm)
          rw [base j mid, pLabel] at bad
          exact Xzero bad.symm
        · have bad := refines j q same (zero.trans qb.symm)
          rw [base j mid, qLabel] at bad
          exact Zzero bad.symm
      have val := ZMod.val_lt (secondCharge m stream j)
      have nonzero := (ZMod.val_ne_zero _).mpr notZero
      have chargeOne : secondCharge m stream j = 1 := ZMod.val_injective 2 (by change _ = 1; omega)
      simpa [supportRow, mid] using chargeOne
  have total : (∑ j : Phase m, supportRow (Finset.Ico 2 m) j.val) = ((m - 2 : ℕ) : ZMod 2) := by
    let e : Fin (2 * m - 2 + 1) ≃ Phase m := (ZMod.finEquiv _).toEquiv
    rw [← e.sum_comp]
    have val (j : Fin (2 * m - 2 + 1)) : (e j).val = j.val := rfl
    simp only [val]
    rw [Fin.sum_univ_eq_sum_range, support_sum (2 * m - 2) _ (by
      intro h hh; have := Finset.mem_Ico.mp hh; omega), Nat.card_Ico]
  have um : ((m - 2 : ℕ) : ZMod 2) = (m : ℕ) := by
    rw [Nat.cast_sub (by omega : 2 ≤ m), show ((2 : ℕ) : ZMod 2) = 0 by decide, sub_zero]
  have tm : ((2 * m - 2 + 1 : ℕ) : ZMod 2) = 1 := by
    rw [Nat.cast_add, Nat.cast_sub (by omega : 2 ≤ 2 * m), Nat.cast_mul,
      show ((2 : ℕ) : ZMod 2) = 0 by decide]
    simp
  have card : Fintype.card (Phase m) = 2 * m - 2 + 1 := ZMod.card _
  simp_rw [charges] at evenB
  rw [Finset.sum_sub_distrib, total, um] at evenB
  simp only [Finset.sum_const, Finset.card_univ, card, nsmul_eq_mul, mul_one, tm] at evenB
  exact Or.inl (ZMod.natCast_eq_one_iff_odd.mp (sub_eq_zero.mp evenB).symm)

/-- All three-label cases with two nonbase internal labels have an actual common
safe two-block stream precisely on the admitted odd-width or nonbase-boundary slice. -/
theorem original_first_window_nonbase_internal_stream {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : ZMod 2 → Finset ℕ) (inside : ∀ v h, h ∈ H v → 1 ≤ h ∧ h ≤ m)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j.val ∈ H v then B v else A v)
    (three : (fullImage m H).card = 3) (two : (internalImage m H).card = 2)
    (nonbase : (0 : Pair) ∉ internalImage m H)
    :
    (OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2 →
      Odd m ∨ membership m H (1 : ℕ) ≠ 0 ∨ membership m H (m : ℕ) ≠ 0) ∧
    ((Odd m ∨ membership m H (1 : ℕ) ≠ 0 ∨ membership m H (m : ℕ) ≠ 0) →
    ∃ (S : Finset ℕ) (flip : ZMod 2) (left right : Pair),
      (∀ h ∈ S, 2 ≤ h ∧ h < m) ∧
      (S.card : ZMod 2) + flip * (m : ℕ) + left.1 + right.1 = 0 ∧
      (m : ZMod 2) + 1 + left.2 + right.2 = 0 ∧
      (nonbaseWords m S flip left right).length = 2 ∧
      (∀ p q, nonbaseCode m S flip left right p = nonbaseCode m S flip left right q →
        membership m H p = membership m H q) ∧
      OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2 ∧
      ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
        endpointDifferences (some v)
          ((scriptArchive (nonbaseWords m S flip left right) (some ⟨v, -j, s⟩)).map Prod.snd) =
          [some (nonbaseCode m S flip left right j).1, some (nonbaseCode m S flip left right j).2] ∧
        (scriptArchive (nonbaseWords m S flip left right) (some ⟨v, -j, s⟩)).length = 2 ∧
        ((scriptArchive (nonbaseWords m S flip left right) (some ⟨v, -j, s⟩)).flatMap
          (fun a => List.ofFn a.1)).length = 2 * m) := by
  classical
  refine ⟨nonbase_necessary m hm alphabet H inside A B distinct f target two nonbase, ?_⟩
  intro admitted
  obtain ⟨X, Z, different, image⟩ := Finset.card_eq_two.mp two
  have Xzero : X ≠ 0 := by intro eq; apply nonbase; simp [image, eq]
  have Zzero : Z ≠ 0 := by intro eq; apply nonbase; simp [image, eq]
  have outside (j : Phase m) (hj : ¬ (1 ≤ j.val ∧ j.val ≤ m)) : membership m H j = 0 := by
    have absent (v : ZMod 2) : j.val ∉ H v := fun mem => hj (inside v j.val mem)
    simp [membership, supportRow, absent]
  have subset : insert (0 : Pair) (internalImage m H) ⊆ fullImage m H := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, outside 0 (by simp)⟩
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have full : fullImage m H = insert 0 (internalImage m H) :=
    (Finset.eq_of_subset_of_card_le subset (by rw [Finset.card_insert_of_notMem nonbase, two, three])).symm
  have member (j : Phase m) : membership m H j = 0 ∨ membership m H j = X ∨ membership m H j = Z := by
    have mem : membership m H j ∈ fullImage m H := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    simpa [full, image] using mem
  have internal (j : Phase m) (lo : 2 ≤ j.val) (hi : j.val < m) :
      membership m H j = X ∨ membership m H j = Z := by
    have mem : membership m H j ∈ internalImage m H :=
      Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, lo, hi⟩, rfl⟩
    simpa [image] using mem
  let S := (Finset.Ico 2 m).filter (fun h => membership m H (h : ℕ) = Z)
  have Sinside : ∀ h ∈ S, 2 ≤ h ∧ h < m := by
    intro h hh
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hh).1
  let x := classIndex X (membership m H (1 : ℕ))
  let y := classIndex X (membership m H (m : ℕ))
  have allowed : (m : ZMod 2) = 1 ∨ x ≠ 0 ∨ y ≠ 0 := by
    rcases admitted with odd | a | b
    · exact Or.inl odd.natCast_zmod_two
    · right; left; dsimp [x, classIndex]; rw [if_neg a]; split_ifs <;> decide
    · right; right; dsimp [y, classIndex]; rw [if_neg b]; split_ifs <;> decide
  obtain ⟨flip, left, right, first, second, separates⟩ := three_selection (m : ℕ) S.card x y allowed
  let role (j : Phase m) : Fin 5 :=
    if j.val = 1 then 3 else if j.val = m then 4
    else if 2 ≤ j.val ∧ j.val < m then (if membership m H j = X then 1 else 2) else 0
  have roleLabel (j : Phase m) : classLabel X Z (threeClass x y (role j)) = membership m H j := by
    have atOne : j.val = 1 → j = (1 : ℕ) := fun eq =>
      ZMod.val_injective _ (eq.trans (ZMod.val_natCast_of_lt (by omega)).symm)
    have atLast : j.val = m → j = (m : ℕ) := fun eq =>
      ZMod.val_injective _ (eq.trans (ZMod.val_natCast_of_lt (by omega)).symm)
    dsimp only [role]
    split_ifs with one last mid isX
    · have samePhase := atOne one
      subst j
      simpa [threeClass, x] using class_restore X Z _ Xzero Zzero different (member (1 : ℕ))
    · have samePhase := atLast last
      subst j
      simpa [threeClass, y] using class_restore X Z _ Xzero Zzero different (member (m : ℕ))
    · simp [threeClass, classLabel, isX]
    · have isZ := (internal j mid.1 mid.2).resolve_left isX
      simp [threeClass, classLabel, isZ]
    · have base := outside j (by omega)
      simp [threeClass, classLabel, base]
  have roleCode (j : Phase m) : nonbaseCode m S flip left right j = threeCode flip left right (role j) := by
    have cast : ((j.val : ℕ) : Phase m) = j := ZMod.natCast_zmod_val j
    unfold nonbaseCode
    dsimp only [role]
    split_ifs with one last mid isX
    · rfl
    · rfl
    · have notZ : membership m H j ≠ Z := by rw [isX]; exact different
      simp [threeCode, supportRow, S, cast, notZ, add_comm]
    · have isZ := (internal j mid.1 mid.2).resolve_left isX
      simp [threeCode, supportRow, S, cast, mid, isZ, add_comm]
    · rfl
  have refines (p q : Phase m) (same : nonbaseCode m S flip left right p = nonbaseCode m S flip left right q) :
      membership m H p = membership m H q := by
    rw [roleCode p, roleCode q] at same
    exact (roleLabel p).symm.trans ((congrArg (classLabel X Z) (separates _ _ same)).trans (roleLabel q))
  let label (v : ZMod 2) (z : Pair) : Y :=
    if v = 0 then (if z.1 = 0 then A v else B v) else (if z.2 = 0 then A v else B v)
  have labels (v : ZMod 2) (j : Phase m) (s : ℕ) (hs : s < 2 * m - 2) :
      f (some ⟨v, -j, s⟩) = label v (membership m H j) := by
    rw [target v j s hs]
    have vc : v = 0 ∨ v = 1 := by
      fin_cases v
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases vc with rfl | rfl <;> simp [label, membership, supportRow]
  let decode (v : ZMod 2) (ar : NarrowWindowCost.Archive m) : Y :=
    if h : ∃ j, [some (nonbaseCode m S flip left right j).1, some (nonbaseCode m S flip left right j).2] =
        endpointDifferences (some v) (ar.map Prod.snd)
    then label v (membership m H (Classical.choose h)) else f none
  have feasible : OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 2 := by
    change OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f (nonbaseWords m S flip left right).length
    apply script_global_preset (2 * m - 2) m (by omega) (by omega) alphabet f _ decode
    intro v phase s hs
    have readings := nonbase_script_code m hm S Sinside flip left right first second v (-phase) s hs
    simp only [neg_neg] at readings
    have existsPhase : ∃ j, [some (nonbaseCode m S flip left right j).1, some (nonbaseCode m S flip left right j).2] =
        endpointDifferences (some v) ((scriptArchive (nonbaseWords m S flip left right) (some ⟨v, phase, s⟩)).map Prod.snd) :=
      ⟨-phase, readings.symm⟩
    dsimp only [decode]
    rw [dif_pos existsPhase]
    have same := (Classical.choose_spec existsPhase).trans readings
    simp only [List.cons.injEq, Option.some.injEq] at same
    rw [refines _ _ (Prod.ext same.1 same.2.1)]
    simpa only [neg_neg] using (labels v (-phase) s hs).symm
  refine ⟨S, flip, left, right, Sinside, first, second, rfl, refines, feasible, ?_⟩
  intro v j s hs
  refine ⟨nonbase_script_code m hm S Sinside flip left right first second v j s hs, ?_, ?_⟩
  · simp [nonbaseWords, scriptArchive]
  · change (archiveWords (scriptArchive (nonbaseWords m S flip left right) (some ⟨v, -j, s⟩))).length = _
    rw [archive_length]
    simp [nonbaseWords, scriptArchive]

#print axioms original_first_window_nonbase_internal_stream

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryCodes
