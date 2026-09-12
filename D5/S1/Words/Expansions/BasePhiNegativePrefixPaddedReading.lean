/- GID: D5/S1/Words/Expansions/BasePhiNegativePrefixPaddedReading
   generality: I
   mirror-B: D5/B/S1/Words/Expansions/BasePhiNegativePrefixPaddedReading
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Words/Expansions/BasePhiNegativePrefixPaddedReading.claim; result=D5/S1/Words/Expansions/BasePhiNegativePrefixPaddedReading.result; claim=D5/S1/Words/Expansions/BasePhiNegativePrefixPaddedReading.claim
   digest: Zero padding merges prefixes 01 and 010; the depth reading differs at 2, 3, 4. -/

import D5.S1.Words.Expansions.BasePhiNegativePrefixTridentSupport

namespace D5.S1.Words.Expansions.BasePhiNegativePrefixPaddedReading

open D5.S0.Carrier D5.S1.Scale
open D5.S1.Words.Expansions.BasePhiNegative
open D5.S1.Words.Expansions.BasePhiCanonicalExpansion
open D5.X_Frontier.BasePhiNegativePrefixTrident
open scoped BigOperators symmDiff

noncomputable section

/-- Agreement after extending a finite negative tail by zeros. -/
abbrev PaddedPrefixOccurs (expansion : BasePhiNegativeExpansion)
    (w : List Bool) (N : Nat) : Prop :=
  ∀ i : Fin w.length, negativeDigit expansion N i.1 = w.get i

def paddedOccurrenceSet (expansion : BasePhiNegativeExpansion) (w : List Bool) : Set Nat :=
  {N | 0 < N ∧ PaddedPrefixOccurs expansion w N}

private theorem forced_zero (e : BasePhiNegativeExpansion) (N k : Nat)
    (h : negativeDigit e N k = true) : negativeDigit e N (k + 1) = false := by
  have hlast : e.digit N (-((k + 1 : Nat) : Int)) = 1 := of_decide_eq_true h
  have hnext : e.digit N (-((k + 1 + 1 : Nat) : Int)) ≠ 1 := by
    intro hone
    have hz := e.canonical N _ hone
    rw [show -((k + 1 + 1 : Nat) : Int) + 1 = -((k + 1 : Nat) : Int) by omega] at hz
    omega
  have hz : e.digit N (-((k + 1 + 1 : Nat) : Int)) = 0 := by
    have := e.binary N (-((k + 1 + 1 : Nat) : Int))
    omega
  change decide (e.digit N (-((k + 1 + 1 : Nat) : Int)) = 1) = false
  rw [hz]
  rfl

theorem paddedPrefixOccurs_append_false_iff
    (expansion : BasePhiNegativeExpansion) (w : List Bool) (hw : w ≠ [])
    (hlast : w.getLast hw = true) (N : Nat) :
    PaddedPrefixOccurs expansion w N ↔ PaddedPrefixOccurs expansion (w ++ [false]) N := by
  have hlen : 0 < w.length := List.length_pos_iff.mpr hw
  constructor
  · intro h i
    by_cases hi : i.val < w.length
    · simpa only [List.get_eq_getElem, List.getElem_append_left hi] using h ⟨i.val, hi⟩
    · have heq : i.val = w.length := by have := i.isLt; simp at this; omega
      have ht : negativeDigit expansion N (w.length - 1) = true := by
        simpa only [List.get_eq_getElem, ← List.getLast_eq_getElem hw, hlast] using
          h ⟨w.length - 1, by omega⟩
      have hz := forced_zero expansion N (w.length - 1) ht
      simpa [List.get_eq_getElem, heq, List.getElem_append_right, Nat.sub_add_cancel hlen] using hz
  · intro h i
    simpa only [List.get_eq_getElem, List.getElem_append_left i.isLt] using
      h ⟨i.val, by simp only [List.length_append, List.length_singleton]; omega⟩

theorem paddedOccurrenceSet_append_false (expansion : BasePhiNegativeExpansion)
    (w : List Bool) (hw : w ≠ []) (hlast : w.getLast hw = true) :
    paddedOccurrenceSet expansion w = paddedOccurrenceSet expansion (w ++ [false]) := by
  ext N
  exact and_congr_right fun _ => paddedPrefixOccurs_append_false_iff expansion w hw hlast N

theorem paddedOccurrenceSet_prefix01_eq_prefix010 :
    paddedOccurrenceSet canonicalExpansion [false, true] =
      paddedOccurrenceSet canonicalExpansion [false, true, false] :=
  paddedOccurrenceSet_append_false canonicalExpansion [false, true] (by simp) rfl

private abbrev unitPower (i : Int) : GoldenInt := ↑(phiUnit ^ i)

private theorem unitPower_nonneg (k : Nat) : unitPower (k : Int) = phi ^ k := by
  rw [unitPower, zpow_natCast, Units.val_pow_eq_pow_val, coe_phiUnit]

private theorem unitPower_neg_two : unitPower (-2) = ⟨2, -1⟩ := by
  change (↑(phiUnit ^ (-(2 : Nat) : Int)) : GoldenInt) = _
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  change (-conj phi) ^ 2 = _
  ext <;> norm_num [conj, phi, pow_succ]

private theorem unitPower_b (i : Int) (hi : 0 ≤ i) :
    (unitPower i).b = (Nat.fib i.toNat : Int) := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hi
  rw [unitPower_nonneg]
  simpa using golden_phi_pow_b_eq_fib_index k

private theorem value_small (d : Int →₀ Nat)
    (hs : d.support ⊆ ({-2, 0, 1, 2} : Finset Int)) :
    basePhiValue d = (d (-2) : GoldenInt) * ⟨2, -1⟩ +
      (d 0 : GoldenInt) + (d 1 : GoldenInt) * phi + (d 2 : GoldenInt) * phi ^ 2 := by
  unfold basePhiValue
  rw [Finset.sum_subset hs (by intro i _ hi; simp [Finsupp.notMem_support_iff.mp hi])]
  change (∑ i ∈ ({-2, 0, 1, 2} : Finset Int), (d i : GoldenInt) * unitPower i) = _
  simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
    Finset.mem_singleton, OfNat.ofNat_ne_zero, neg_eq_zero, not_false_eq_true,
    show (-2 : Int) ≠ 1 by omega, show (-2 : Int) ≠ 2 by omega,
    show (0 : Int) ≠ 1 by omega, show (0 : Int) ≠ 2 by omega,
    show (1 : Int) ≠ 2 by omega, or_self, unitPower_neg_two]
  rw [show unitPower 0 = 1 by simp [unitPower],
    show unitPower 1 = phi by simp [unitPower],
    show unitPower 2 = phi ^ 2 by simpa using unitPower_nonneg 2]
  ring

/-- The Fibonacci coefficient equation excludes every exponent at least three. -/
private theorem shallow_classification (e : BasePhiNegativeExpansion) (N : Nat)
    (hn : ∀ i : Int, i < 0 → e.digit N i = if i = -2 then 1 else 0) :
    N = 2 ∨ N = 3 ∨ N = 4 := by
  classical
  let d := e.digit N
  let s := d.support.erase (-2)
  let b : GoldenInt →+ Int :=
    { toFun := GoldenInt.b, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hm : (-2 : Int) ∈ d.support := by simp [Finsupp.mem_support_iff, d, hn]
  have hnonneg (i : Int) (hi : i ∈ s) : 0 ≤ i := by
    have hm' := Finset.mem_erase.mp hi
    by_contra h
    have hz := hn i (by omega)
    simp only [if_neg hm'.1] at hz
    exact Finsupp.mem_support_iff.mp hm'.2 hz
  have heq : ∑ i ∈ s, (d i : Int) * (Nat.fib i.toNat : Int) = 1 := by
    have hv := congrArg b (e.value_equation N)
    change b (∑ i ∈ d.support, (d i : GoldenInt) * unitPower i) = 0 at hv
    rw [← Finset.sum_erase_add _ _ hm, map_add, map_sum] at hv
    have he : ∀ i ∈ s, b ((d i : GoldenInt) * unitPower i) =
        (d i : Int) * (Nat.fib i.toNat : Int) := by
      intro i hi
      simp [b, unitPower_b i (hnonneg i hi)]
    have hsum := Finset.sum_congr rfl he
    change (∑ i ∈ s, b ((d i : GoldenInt) * unitPower i)) +
      b ((d (-2) : GoldenInt) * unitPower (-2)) = 0 at hv
    rw [hsum] at hv
    have hd : d (-2) = 1 := hn (-2) (by omega)
    simp [hd, unitPower_neg_two, b] at hv
    omega
  have hs : d.support ⊆ ({-2, 0, 1, 2} : Finset Int) := by
    intro i hi
    by_cases hm2 : i = -2
    · simp [hm2]
    have his : i ∈ s := Finset.mem_erase.mpr ⟨hm2, hi⟩
    have hi0 := hnonneg i his
    have hbound := Finset.single_le_sum
      (fun j (_ : j ∈ s) => mul_nonneg (Int.natCast_nonneg (d j))
        (Int.natCast_nonneg (Nat.fib j.toNat))) his
    rw [heq] at hbound
    have hone : d i = 1 := by
      have hle : d i ≤ 1 := e.binary N i
      have := Finsupp.mem_support_iff.mp hi
      omega
    have hi3 : i < 3 := by
      by_contra h
      have hf := Nat.fib_mono (show 3 ≤ i.toNat by omega)
      norm_num [hone] at hbound
      norm_num at hf
      omega
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hv := e.value_equation N
  rw [value_small _ hs] at hv
  have hd : e.digit N (-2) = 1 := hn (-2) (by omega)
  have ha := congrArg GoldenInt.a hv
  have hb := congrArg GoldenInt.b hv
  norm_num [hd, phi_sq, d] at ha hb
  have h0 := e.binary N 0
  have h1 := e.binary N 1
  have h2 := e.binary N 2
  have hc := e.canonical N 0
  norm_num at hc
  omega

private theorem short_digits (a c : Nat) (ha : a ≤ 1) (hc : c ≤ 1)
    (hac : c = 0 → a = 0) (i : Int) :
    canonicalExpansion.digit (2 + a + c) i =
      if i = -2 then 1 else if i = 0 then a else if i = 1 then 1 - c
      else if i = 2 then c else 0 := by
  classical
  let d : Int →₀ Nat := Finsupp.single (-2) 1 + Finsupp.single 0 a +
    Finsupp.single 1 (1 - c) + Finsupp.single 2 c
  have hd (j : Int) : d j = if j = -2 then 1 else if j = 0 then a
      else if j = 1 then 1 - c else if j = 2 then c else 0 := by
    simp only [d, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> omega
  have hb (j : Int) : d j ≤ 1 := by rw [hd]; split_ifs <;> omega
  have hk (j : Int) (hj : d j = 1) : d (j + 1) = 0 := by
    rw [hd] at hj ⊢
    split_ifs at * <;> omega
  have hs : d.support ⊆ ({-2, 0, 1, 2} : Finset Int) := by
    intro j hj
    by_contra h
    have hz : d j = 0 := by simp_all
    exact Finsupp.mem_support_iff.mp hj hz
  have hv : basePhiValue d = (2 + a + c : Nat) := by
    rw [value_small _ hs]
    ext <;> norm_num [hd, phi_sq, show (2 : GoldenInt).a = 2 from rfl,
      show (2 : GoldenInt).b = 0 from rfl] <;> omega
  obtain ⟨_, _, hu⟩ := basePhiExpansion_existsUnique (2 + a + c)
  have he := (hu (canonicalExpansion.digit _) ⟨canonicalExpansion.binary _,
    canonicalExpansion.canonical _, canonicalExpansion.value_equation _⟩).trans
    (hu d ⟨hb, hk, hv⟩).symm
  rw [he, hd]

private theorem small_tail (N : Nat) (hN : N = 2 ∨ N = 3 ∨ N = 4) :
    ∀ i : Int, i < 0 → canonicalExpansion.digit N i = if i = -2 then 1 else 0 := by
  intro i hi
  rcases hN with rfl | rfl | rfl
  · simpa [show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega] using
      short_digits 0 0 (by omega) (by omega) (by omega) i
  · simpa [show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega] using
      short_digits 0 1 (by omega) (by omega) (by omega) i
  · simpa [show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega] using
      short_digits 1 1 (by omega) (by omega) (by omega) i

private theorem difference_iff (N : Nat) :
    N ∈ occurrenceSet canonicalExpansion [false, true] \
      occurrenceSet canonicalExpansion [false, true, false] ↔
    0 < N ∧ ∀ i : Int, i < 0 → canonicalExpansion.digit N i =
      if i = -2 then 1 else 0 := by
  constructor
  · rintro ⟨h01, hn010⟩
    have hpad : PaddedPrefixOccurs canonicalExpansion [false, true, false] N :=
      (paddedPrefixOccurs_append_false_iff canonicalExpansion [false, true]
        (by simp) rfl N).mp h01.2.2
    have hdepth : ¬reachesNegativeDepth canonicalExpansion N 3 :=
      fun h => hn010 ⟨h01.1, h, hpad⟩
    have h0 := h01.2.2 ⟨0, by simp⟩
    have h1 := h01.2.2 ⟨1, by simp⟩
    simp [negativeDigit] at h0 h1
    refine ⟨h01.1, fun i hi => ?_⟩
    by_cases hi2 : i = -2
    · simpa [hi2] using h1
    rw [if_neg hi2]
    by_cases hi1 : i = -1
    · subst i
      have := canonicalExpansion.binary N (-1)
      omega
    · by_contra hz
      exact hdepth ⟨by omega, i, Finsupp.mem_support_iff.mpr hz, by omega⟩
  · rintro ⟨hpos, hn⟩
    refine ⟨⟨hpos, ⟨by decide, -2, ?_, by norm_num⟩, ?_⟩, ?_⟩
    · simp [Finsupp.mem_support_iff, hn]
    · intro i
      fin_cases i <;> simp [negativeDigit, hn]
    · rintro ⟨_, ⟨_, i, hi, hle⟩, _⟩
      have hz := hn i (by simp at hle; omega)
      have hi2 : i ≠ -2 := by simp at hle; omega
      simp only [if_neg hi2] at hz
      exact Finsupp.mem_support_iff.mp hi hz

theorem occurrenceSet_prefix01_sdiff_prefix010 :
    occurrenceSet canonicalExpansion [false, true] \
      occurrenceSet canonicalExpansion [false, true, false] = {2, 3, 4} := by
  ext N
  rw [difference_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · exact fun h => shallow_classification canonicalExpansion N h.2
  · intro h
    exact ⟨by rcases h with rfl | rfl | rfl <;> omega, small_tail N h⟩

private theorem prefix010_subset_prefix01 :
    occurrenceSet canonicalExpansion [false, true, false] ⊆
      occurrenceSet canonicalExpansion [false, true] := by
  intro N h
  refine ⟨h.1, ⟨by decide, ?_⟩,
    (paddedPrefixOccurs_append_false_iff canonicalExpansion [false, true]
      (by simp) rfl N).mpr h.2.2⟩
  obtain ⟨i, hi, hdepth⟩ := h.2.1.2
  exact ⟨i, hi, by change i ≤ -3 at hdepth; change i ≤ -2; omega⟩

theorem occurrenceSet_prefix01_symmDiff_prefix010 :
    occurrenceSet canonicalExpansion [false, true] ∆
      occurrenceSet canonicalExpansion [false, true, false] = {2, 3, 4} := by
  rw [symmDiff_of_ge prefix010_subset_prefix01, occurrenceSet_prefix01_sdiff_prefix010]

def claim : Prop :=
  occurrenceSet canonicalExpansion [false, true] =
    occurrenceSet canonicalExpansion [false, true, false]

theorem result : Not claim := by
  intro h
  have he := occurrenceSet_prefix01_sdiff_prefix010
  rw [show occurrenceSet canonicalExpansion [false, true] =
    occurrenceSet canonicalExpansion [false, true, false] from h, Set.sdiff_self] at he
  have : 2 ∈ ({2, 3, 4} : Set Nat) := by simp
  rw [← he] at this
  exact this

def PaddedCore (w : List Bool) : Set Nat :=
  {q | fiberStart q ∧ PaddedPrefixOccurs canonicalExpansion w q}

theorem two_mem_paddedCore010 : 2 ∈ PaddedCore [false, true, false] := by
  have ht := small_tail 2 (Or.inl rfl)
  have hdiff := (difference_iff 2).mpr ⟨by omega, ht⟩
  refine ⟨⟨⟨by omega, fun _ => rfl⟩, ?_⟩, ?_⟩
  · intro M hM
    have hm : ∀ i : Int, i < 0 → canonicalExpansion.digit M i =
        if i = -2 then 1 else 0 := by
      intro i hi
      let k := (-i).toNat - 1
      have hk : -((k + 1 : Nat) : Int) = i := by dsimp [k]; omega
      have hb := hM.2 k
      simp only [negativeDigit, hk] at hb
      have htwo := ht i hi
      have hbM := canonicalExpansion.binary M i
      by_cases hi2 : i = -2 <;> simp_all <;> omega
    have hc := shallow_classification canonicalExpansion M hm
    omega
  · exact (paddedPrefixOccurs_append_false_iff canonicalExpansion [false, true]
      (by simp) rfl 2).mp hdiff.1.2.2

#print axioms PaddedPrefixOccurs
#print axioms paddedOccurrenceSet
#print axioms paddedPrefixOccurs_append_false_iff
#print axioms paddedOccurrenceSet_append_false
#print axioms paddedOccurrenceSet_prefix01_eq_prefix010
#print axioms occurrenceSet_prefix01_sdiff_prefix010
#print axioms occurrenceSet_prefix01_symmDiff_prefix010
#print axioms claim
#print axioms result
#print axioms PaddedCore
#print axioms two_mem_paddedCore010

end
end D5.S1.Words.Expansions.BasePhiNegativePrefixPaddedReading
