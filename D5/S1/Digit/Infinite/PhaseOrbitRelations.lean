/- GID: D5/S1/Digit/Infinite/PhaseOrbitRelations
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/PhaseOrbitRelations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Eventual merging of legal streams agrees with circle rotation orbits and phase fibres, with exact merging times at negative phases. -/

import D5.S1.Digit.Infinite.MultiplierObstruction
import D5.S1.Digit.Infinite.InfiniteSuccessorFibres
import D5.S1.Digit.Carry.SuccessorShortest
import Mathlib.Topology.DenseEmbedding
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Data.Set.Countable

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.PhaseOrbitRelations

open D5.S1.Digit.Infinite.SuccessorContinuity
open D5.S1.Digit.Infinite.InfiniteSuccessorFibres
open D5.S1.Digit.Infinite.SignedSeriesRange
open D5.S1.Digit.Infinite.SignedSeriesFibres
open D5.S1.Digit.Infinite.MultiplierObstruction
open D5.S1.Digit.GoldenBase4AutomataOracle
open D5.S1.Digit D5.S1.Digit.Carry.Successor
open D5.S1.Digit.Carry.SuccessorShortest
open scoped Topology

/-- The successor as a self-map of the legal digit streams. -/
noncomputable def T (x : LegalDigits) : LegalDigits := ⟨next x.val, next_fibres.1 x⟩

/-- Two circle points belong to the same rotation orbit. -/
def ER (t s : AddCircle (1 : ℝ)) : Prop :=
  ∃ k : ℤ, s = t + k • (Real.goldenRatio : AddCircle (1 : ℝ))

/-- Two legal streams have equal successor iterates at possibly different times. -/
def ET (x y : LegalDigits) : Prop := ∃ m n : ℕ, T^[m] x = T^[n] y

/-- Two legal streams have equal successor iterates at the same time. -/
def ST (x y : LegalDigits) : Prop := ∃ k : ℕ, T^[k] x = T^[k] y

/-- Two legal streams have the same phase on the circle. -/
def QH (x y : LegalDigits) : Prop := phase x = phase y

set_option maxHeartbeats 800000 in
/-- The eventual-merging relations correspond to rotation orbits and phase fibres. Both orbit
relations are countable Borel equivalence relations. Distinct streams of phase minus j times the
rotation angle merge at the zero row after exactly j successor steps, for every positive j. -/
theorem phase_orbit_relations :
    Equivalence ER ∧ Equivalence ET ∧
    (∀ t, Set.Countable {s | ER t s}) ∧
    (∀ x, Set.Countable {y | ET x y}) ∧
    MeasurableSet {p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) | ER p.1 p.2} ∧
    @MeasurableSet (LegalDigits × LegalDigits) (borel (LegalDigits × LegalDigits))
      {p | ET p.1 p.2} ∧
    (∀ x y, ET x y ↔ ER (phase x) (phase y)) ∧
    (∀ x y, ST x y ↔ phase x = phase y) ∧
    (∀ j : ℕ, 1 ≤ j → ∀ x y : LegalDigits,
      phase x = -(j • (Real.goldenRatio : AddCircle (1 : ℝ))) →
      phase y = -(j • (Real.goldenRatio : AddCircle (1 : ℝ))) →
      T^[j] x = zRow 0 ∧ T^[j] y = zRow 0 ∧
      (x ≠ y → ∀ i < j, T^[i] x ≠ T^[i] y)) := by
  classical
  let c : AddCircle (1 : ℝ) := Real.goldenRatio
  let gamma (n : ℕ) : AddCircle (1 : ℝ) := (n : ℝ) * Real.goldenRatio
  have row_zero : (zRow 0).val = fun _ => false := by
    funext j
    simp [zRow, zeckendorfBit, D5.S0.Conventions.wdigits]

  have successor_binding (n : ℕ) : next (zRow n).val = (zRow (n + 1)).val := by
    classical
    have raw_mem (m i : ℕ) :
        i ∈ (rawOfZeckendorf (Nat.zeckendorf m)).support ↔ i + 2 ∈ Nat.zeckendorf m := by
      conv_rhs => rw [← rawToZeckendorf_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf m)]
      simp [rawToZeckendorf, Finsupp.mem_toMultiset]
    have row_mem (m i : ℕ) :
        (zRow m).val i = true ↔ i ∈ (rawOfZeckendorf (Nat.zeckendorf m)).support := by
      rw [raw_mem]
      change decide (zeckendorfBit m i = 1) = true ↔ _
      simp only [decide_eq_true_eq]
      by_cases h : i + 2 ∈ Nat.zeckendorf m <;>
        simp [zeckendorfBit, D5.S0.Conventions.wdigits, h]
    let r := rawOfZeckendorf (Nat.zeckendorf n)
    let s := rawOfZeckendorf (Nat.zeckendorf (n + 1))
    let offset := if r 0 = 1 then 0 else 1
    let k := alternatingLength n
    let erased := prefixSet offset k
    let inserted := carriedIndex offset k
    have hc : CanonicalRaw r := canonicalRaw_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf n)
    have all := successor_erasure_and_shortest n
    change (∀ j < k, r (prefixIndex offset j) = 1) ∧
      r (prefixIndex offset k) = 0 ∧
      (r 0 = 0 → r 1 = 0 → k = 0) ∧
      erased ⊆ r.support ∧ erased.card = k ∧ inserted ∉ r.support ∧
      s.support = (r.support \ erased) ∪ {inserted} ∧ _ at all
    have bits := all.1
    have gap := all.2.1
    have fresh := all.2.2.2.2.2.1
    have support := all.2.2.2.2.2.2.1
    have offs : offset = 0 ∨ offset = 1 := by dsimp [offset]; split <;> simp
    have positive : offset = 0 → 0 < k := by
      intro ho
      have hz : r 0 = 1 := by
        by_contra hz
        simp [offset, hz] at ho
      by_contra hk
      have hk0 : k = 0 := by omega
      simpa [ho, hk0, prefixIndex, hz] using gap
    have covered (i : ℕ) (hi : i < inserted) :
        (∃ t < k, i = prefixIndex offset t) ∨
        (∃ t < k, i + 1 = prefixIndex offset t) := by
      have imod := Nat.mod_lt i (by decide : 0 < 2)
      have imod' := Nat.mod_lt (i + 1) (by decide : 0 < 2)
      rcases offs with ho | ho
      · have hp := positive ho
        dsimp [inserted, carriedIndex, prefixIndex] at hi
        simp only [ho] at hi ⊢
        by_cases he : i % 2 = 0
        · exact Or.inl ⟨i / 2, by omega, by dsimp [prefixIndex]; omega⟩
        · exact Or.inr ⟨(i + 1) / 2, by omega, by dsimp [prefixIndex]; omega⟩
      · dsimp [inserted, carriedIndex, prefixIndex] at hi
        simp only [ho] at hi ⊢
        by_cases he : i % 2 = 1
        · exact Or.inl ⟨i / 2, by omega, by dsimp [prefixIndex]; omega⟩
        · exact Or.inr ⟨(i + 1) / 2, by omega, by dsimp [prefixIndex]; omega⟩
    have first_pair : (zRow n).val inserted = false ∧ (zRow n).val (inserted + 1) = false := by
      have hi : inserted + 1 = prefixIndex offset k := by
        rcases offs with ho | ho
        · have hp := positive ho
          dsimp [inserted, carriedIndex, prefixIndex]
          omega
        · dsimp [inserted, carriedIndex, prefixIndex]
          omega
      constructor
      · apply Bool.eq_false_iff.mpr
        intro h
        exact fresh ((row_mem n inserted).mp h)
      · apply Bool.eq_false_iff.mpr
        intro h
        have hr := (row_mem n (inserted + 1)).mp h
        have hne := Finsupp.mem_support_iff.mp hr
        exact hne (hi ▸ gap)
    have lower (i : ℕ) (hi : i < inserted) :
        ¬ ((zRow n).val i = false ∧ (zRow n).val (i + 1) = false) := by
      intro h
      rcases covered i hi with ⟨t, ht, he⟩ | ⟨t, ht, he⟩
      · have hm : i ∈ r.support := Finsupp.mem_support_iff.mpr (by rw [he, bits t ht]; decide)
        have hone := (row_mem n i).mpr hm
        simp [hone] at h
      · have hm : i + 1 ∈ r.support := Finsupp.mem_support_iff.mpr (by rw [he, bits t ht]; decide)
        have hone := (row_mem n (i + 1)).mpr hm
        simp [hone] at h
    have exists_pair : ∃ j, (zRow n).val j = false ∧ (zRow n).val (j + 1) = false :=
      ⟨inserted, first_pair⟩
    have first : Nat.find exists_pair = inserted := (Nat.find_eq_iff exists_pair).mpr ⟨first_pair, lower⟩
    have erased_lt (i : ℕ) (hi : i ∈ erased) : i < inserted := by
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
      have htk := Finset.mem_range.mp ht
      dsimp [inserted, carriedIndex, prefixIndex]
      rcases offs with ho | ho <;> omega
    have old_low_erased (i : ℕ) (hi : i < inserted) (hm : i ∈ r.support) : i ∈ erased := by
      rcases covered i hi with ⟨t, ht, he⟩ | ⟨t, ht, he⟩
      · exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, he.symm⟩
      · have hone : r i = 1 := by
          have := hc.1 i
          have := Finsupp.mem_support_iff.mp hm
          omega
        have hz := hc.2 i hone
        have hh : r (i + 1) = 1 := he ▸ bits t ht
        omega
    funext i
    simp only [next, dif_pos exists_pair, first]
    have hs : (zRow (n + 1)).val i = true ↔ i ∈ (r.support \ erased) ∪ {inserted} := by
      rw [row_mem]
      exact support ▸ Iff.rfl
    by_cases hi : i < inserted
    · simp only [if_pos hi]
      apply Eq.symm
      apply Bool.eq_false_iff.mpr
      intro h
      have hm := hs.mp h
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton] at hm
      rcases hm with ⟨hm, he⟩ | he
      · exact he (old_low_erased i hi hm)
      · omega
    · simp only [if_neg hi]
      by_cases he : i = inserted
      · simp only [if_pos he]
        exact (hs.mpr (Finset.mem_union_right _ (Finset.mem_singleton.mpr he))).symm
      · simp only [if_neg he]
        have hne : i ∉ erased := fun hm => hi (erased_lt i hm)
        have equiv : (zRow n).val i = true ↔ (zRow (n + 1)).val i = true := by
          rw [hs, row_mem]
          simp [hne, he, r]
        cases h0 : (zRow n).val i <;> cases h1 : (zRow (n + 1)).val i <;> simp_all

  have density_binding : DenseRange zRow := by
    classical
    have raw_mem (m i : ℕ) :
        i ∈ (rawOfZeckendorf (Nat.zeckendorf m)).support ↔ i + 2 ∈ Nat.zeckendorf m := by
      conv_rhs => rw [← rawToZeckendorf_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf m)]
      simp [rawToZeckendorf, Finsupp.mem_toMultiset]
    have row_mem (m i : ℕ) :
        (zRow m).val i = true ↔ i ∈ (rawOfZeckendorf (Nat.zeckendorf m)).support := by
      rw [raw_mem]
      change decide (zeckendorfBit m i = 1) = true ↔ _
      simp only [decide_eq_true_eq]
      by_cases h : i + 2 ∈ Nat.zeckendorf m <;>
        simp [zeckendorfBit, D5.S0.Conventions.wdigits, h]

    intro x
    let R (L : ℕ) : RawDigits := Finsupp.onFinset (Finset.range L)
      (fun i => if i < L ∧ x.val i = true then 1 else 0)
      (by intro i hi; by_contra h; simp only [Finset.mem_range] at h; simp [h] at hi)
    have canonical (L : ℕ) : CanonicalRaw (R L) := by
      constructor
      · intro i
        change (if i < L ∧ x.val i = true then 1 else 0) ≤ 1
        split <;> omega
      · intro i hi
        change (if i < L ∧ x.val i = true then 1 else 0) = 1 at hi
        have hxi : x.val i = true := by split at hi <;> simp_all
        have hn : x.val (i + 1) ≠ true := fun h => x.property i ⟨hxi, h⟩
        change (if i + 1 < L ∧ x.val (i + 1) = true then 1 else 0) = 0
        simp [hn]
    have reencode (L : ℕ) : rawOfZeckendorf (Nat.zeckendorf (rawValue (R L))) = R L := by
      rw [← rawToZeckendorf_eq_zeckendorf (canonical L), rawOfZeckendorf_rawToZeckendorf]
    have prefix_agree (L i : ℕ) (hi : i < L) : (zRow (rawValue (R L))).val i = x.val i := by
      have hm := row_mem (rawValue (R L)) i
      rw [reencode L, Finsupp.mem_support_iff] at hm
      change ((zRow (rawValue (R L))).val i = true ↔
        (if i < L ∧ x.val i = true then 1 else 0) ≠ 0) at hm
      simp only [hi, true_and] at hm
      cases hx : x.val i <;> cases hz : (zRow (rawValue (R L))).val i <;> simp_all
    have htendsto : Filter.Tendsto (fun L => zRow (rawValue (R L))) Filter.atTop (𝓝 x) := by
      apply tendsto_subtype_rng.mpr
      apply tendsto_pi_nhds.mpr
      intro i
      apply tendsto_nhds_of_eventually_eq
      exact (Filter.eventually_gt_atTop i).mono fun L hL => prefix_agree L i hL
    exact mem_closure_of_tendsto htendsto
      (Filter.Eventually.of_forall fun L => Set.mem_range_self (rawValue (R L)))

  have t_continuous : Continuous T :=
    infinite_successor_continuous.subtype_mk (fun x => next_fibres.1 x)

  have t_row (n : ℕ) : T (zRow n) = zRow (n + 1) :=
    Subtype.ext (successor_binding n)

  have coefficient (j : ℕ) :
      (-1 : ℝ) ^ (j + 1) * alpha ^ (j + 2) =
      Real.goldenRatio * (Nat.fib (j + 2) : ℝ) - (Nat.fib (j + 3) : ℝ) := by
    have e := Real.fib_succ_sub_goldenRatio_mul_fib (j + 2)
    have hc : Real.goldenConj = -alpha := by
      dsimp [alpha]
      have hi := Real.inv_goldenRatio
      linarith [hi]
    have hsign : (-alpha) ^ (j + 2) =
        -((-1 : ℝ) ^ (j + 1) * alpha ^ (j + 2)) := by
      rw [neg_eq_neg_one_mul, mul_pow]
      simp only [show j + 2 = (j + 1) + 1 by omega, pow_succ]
      ring
    rw [hc, hsign] at e
    have hi : j + 2 + 1 = j + 3 := by omega
    rw [hi] at e
    linarith

  have value_row (n : ℕ) : ∃ k : ℤ,
      signedValue (zRow n) = (n : ℝ) * Real.goldenRatio - k := by
    classical
    let R := rawOfZeckendorf (Nat.zeckendorf n)
    have hc := canonicalRaw_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf n)
    have hm (i : ℕ) : i ∈ R.support ↔ i + 2 ∈ Nat.zeckendorf n := by
      dsimp [R]
      conv_rhs => rw [← rawToZeckendorf_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf n)]
      simp [rawToZeckendorf, Finsupp.mem_toMultiset]
    have bit (i : ℕ) : (if (zRow n).val i then (1 : ℝ) else 0) = R i := by
      have hb := hc.1 i
      change R i ≤ 1 at hb
      have hm' := hm i
      rw [Finsupp.mem_support_iff] at hm'
      by_cases hi : i + 2 ∈ Nat.zeckendorf n
      · have hr : R i = 1 := by have := hm'.mpr hi; omega
        simp [zRow, zeckendorfBit, D5.S0.Conventions.wdigits, hi, hr]
      · have hr : R i = 0 := by simpa using mt hm'.mp hi
        simp [zRow, zeckendorfBit, D5.S0.Conventions.wdigits, hi, hr]
    have hn : rawValue R = n := by
      rw [rawValue_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf n), Nat.sum_zeckendorf_fib]
    refine ⟨(∑ j ∈ R.support, (R j : ℤ) * (Nat.fib (j + 3) : ℤ)), ?_⟩
    rw [signedValue]
    simp_rw [bit]
    rw [tsum_eq_sum (s := R.support) (fun j hj => by simp [Finsupp.notMem_support_iff.mp hj])]
    simp_rw [coefficient]
    rw [← hn]
    simp only [rawValue, Finsupp.sum, D5.S0.Conventions.wValue, Int.cast_natCast,
      Nat.cast_sum, Nat.cast_mul, Int.cast_sum, Int.cast_mul, Int.cast_natCast, Finset.sum_mul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring

  have phase_row (n : ℕ) : phase (zRow n) = gamma n := by
    obtain ⟨k, hk⟩ := value_row n
    have zeroK : ((k : ℝ) : AddCircle (1 : ℝ)) = 0 :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨k, by simp⟩
    simp only [phase, gamma, hk, AddCircle.coe_sub, zeroK, sub_zero]

  have value_continuous : Continuous signedValue := by
    have hp : 0 < alpha := inv_pos.mpr Real.goldenRatio_pos
    have hlt : alpha < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
    apply continuous_tsum
    · intro j
      apply continuous_const.mul
      exact (continuous_of_discreteTopology : Continuous (fun b : Bool => if b then (1 : ℝ) else 0)).comp
        ((continuous_apply j).comp continuous_subtype_val)
    · exact (summable_geometric_of_lt_one hp.le hlt).mul_right (alpha ^ 2)
    · intro j x
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow]
      simp only [abs_neg, abs_one, one_pow, one_mul, abs_of_pos hp]
      cases x.val j <;> simp [pow_add, mul_nonneg (pow_nonneg hp.le j) (sq_nonneg alpha)]

  have h_continuous : Continuous phase :=
    (AddCircle.continuous_mk' (1 : ℝ)).comp value_continuous

  have semiconjugacy : ∀ x, phase (T x) = phase x + (Real.goldenRatio : AddCircle (1 : ℝ)) := by
    have he : (fun x => phase (T x)) = (fun x => phase x + (Real.goldenRatio : AddCircle (1 : ℝ))) := by
      apply density_binding.equalizer (h_continuous.comp t_continuous)
        (h_continuous.add continuous_const)
      funext n
      change phase (T (zRow n)) = phase (zRow n) + _
      rw [t_row, phase_row, phase_row]
      simp [gamma, add_nsmul]
    exact congrFun he

  have seam_negative_phase (w : List Block) :
      ∃ k : ℕ, 2 ≤ k ∧ ((seam w : ℝ) : AddCircle (1 : ℝ)) =
        (((-(k : ℝ) * Real.goldenRatio) : ℝ) : AddCircle (1 : ℝ)) := by
    classical
    let N : ℕ := ∑ j ∈ Finset.range (len w),
      if (digitsOf w)[j]?.getD false then Nat.fib (j + 2) else 0
    let J : ℕ := ∑ j ∈ Finset.range (len w),
      if (digitsOf w)[j]?.getD false then Nat.fib (j + 3) else 0
    have hsum : (∑ j ∈ Finset.range (len w), Nat.fib (j + 2)) + 2 =
        Nat.fib (len w + 3) := by
      have ht := Nat.fib_succ_eq_succ_sum (len w + 2)
      have hs : (∑ j ∈ Finset.range (len w + 2), Nat.fib j) =
          1 + ∑ j ∈ Finset.range (len w), Nat.fib (j + 2) := by
        simpa [Finset.sum_range_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (Finset.sum_range_add Nat.fib 2 (len w))
      rw [hs] at ht
      calc
        (∑ j ∈ Finset.range (len w), Nat.fib (j + 2)) + 2 =
            (1 + ∑ j ∈ Finset.range (len w), Nat.fib (j + 2)) + 1 := by omega
        _ = Nat.fib (len w + 2 + 1) := ht.symm
        _ = Nat.fib (len w + 3) := rfl
    have hN : N ≤ ∑ j ∈ Finset.range (len w), Nat.fib (j + 2) := by
      apply Finset.sum_le_sum
      intro j _
      split <;> omega
    have hNk : N + 2 ≤ Nat.fib (len w + 3) := by omega
    let k := Nat.fib (len w + 3) - N
    have hk : 2 ≤ k := by dsimp [k]; omega
    have hreal : (Nat.fib (len w + 3) : ℝ) = (N : ℝ) + (k : ℝ) := by
      exact_mod_cast (show Nat.fib (len w + 3) = N + k by dsimp [k]; omega)
    have hS : S w = Real.goldenRatio * (N : ℝ) - (J : ℝ) := by
      dsimp [S, N, J]
      simp_rw [coefficient]
      push_cast
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      cases h : (digitsOf w)[j]?.getD false <;> simp [h]
    have hq : r ^ len w * q =
        -(Real.goldenRatio * (Nat.fib (len w + 3) : ℝ) - (Nat.fib (len w + 4) : ℝ)) := by
      have h := coefficient (len w + 1)
      have he : r ^ len w * q =
          -((-1 : ℝ) ^ (len w + 1 + 1) * alpha ^ (len w + 1 + 2)) := by
        dsimp [r, q]
        rw [neg_eq_neg_one_mul alpha, mul_pow]
        simp only [pow_add, pow_one]
        ring
      simpa only [Nat.add_assoc] using he.trans (congrArg Neg.neg h)
    have hs : seam w = -(k : ℝ) * Real.goldenRatio +
        ((Nat.fib (len w + 4) : ℤ) - (J : ℤ) : ℤ) := by
      dsimp [seam, f]
      rw [hS, hq, hreal]
      push_cast
      ring
    refine ⟨k, hk, ?_⟩
    have hz : ((((Nat.fib (len w + 4) : ℤ) - (J : ℤ) : ℤ) : ℝ) :
        AddCircle (1 : ℝ)) = 0 :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
        ⟨(Nat.fib (len w + 4) : ℤ) - (J : ℤ), by simp⟩
    rw [hs, AddCircle.coe_add, hz, add_zero]

  have phase_unique_of_avoids (c : AddCircle (1 : ℝ))
      (havoid : ∀ k : ℕ, 1 ≤ k → c ≠
        (((-(k : ℝ) * Real.goldenRatio) : ℝ) : AddCircle (1 : ℝ))) :
      ∃! x : LegalDigits, phase x = c := by
    have haid : a = 1 - Real.goldenRatio := by
      dsimp [a, alpha]
      rw [Real.inv_goldenRatio]
      linarith [Real.goldenRatio_add_goldenConj]
    have hba : b = a + 1 := by
      dsimp [b, a, alpha]
      rw [Real.inv_goldenRatio]
      nlinarith [Real.goldenConj_sq]
    have hone : ((1 : ℝ) : AddCircle (1 : ℝ)) = 0 :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨1, by simp⟩
    have hap : (a : AddCircle (1 : ℝ)) = ((-Real.goldenRatio : ℝ) : AddCircle (1 : ℝ)) := by
      rw [haid, AddCircle.coe_sub, hone, zero_sub, AddCircle.coe_neg]
    have hbp : (b : AddCircle (1 : ℝ)) = ((-Real.goldenRatio : ℝ) : AddCircle (1 : ℝ)) := by
      rw [hba, AddCircle.coe_add, hone, add_zero, hap]
    have he : c ≠ ((-Real.goldenRatio : ℝ) : AddCircle (1 : ℝ)) := by
      simpa using havoid 1 (by omega)
    let t := AddCircle.equivIco (1 : ℝ) a c
    have htc : ((t.val : ℝ) : AddCircle (1 : ℝ)) = c := AddCircle.coe_equivIco
    have hti : t.val ∈ Set.Ioo a b := by
      refine ⟨lt_of_le_of_ne t.property.1 ?_, ?_⟩
      · intro ht
        exact he (htc.symm.trans (ht ▸ hap))
      · simpa [hba] using t.property.2
    have hns : t.val ∉ Set.range seam := by
      rintro ⟨w, hw⟩
      obtain ⟨k, hk, hphase⟩ := seam_negative_phase w
      exact havoid k (by omega) (htc.symm.trans (hw ▸ hphase))
    obtain ⟨x, hx, hunique⟩ := signed_series_fibres.2.2 t.val
      ⟨hti.1.le, hti.2.le⟩ hns
    refine ⟨x, ?_, ?_⟩
    · exact (congrArg (fun s : ℝ => (s : AddCircle (1 : ℝ))) hx).trans htc
    · intro y hy
      apply hunique y
      have hbounds : signedValue y ∈ Set.Icc a b := by
        rw [← signed_series_range.1]
        exact Set.mem_range_self y
      have hlt : signedValue y < b := by
        refine lt_of_le_of_ne hbounds.2 ?_
        intro hb
        exact he (hy.symm.trans ((congrArg (fun s : ℝ => (s : AddCircle (1 : ℝ))) hb).trans hbp))
      exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
        (show signedValue y ∈ Set.Ico a (a + 1) from ⟨hbounds.1, hba ▸ hlt⟩)
        t.property).mp (hy.trans htc.symm)

  have natural_phase_avoids (n k : ℕ) (hk : 1 ≤ k) :
      gamma n ≠ (((-(k : ℝ) * Real.goldenRatio) : ℝ) : AddCircle (1 : ℝ)) := by
    intro he
    have hz : ((((n + k : ℕ) : ℝ) * Real.goldenRatio : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      rw [Nat.cast_add, add_mul, AddCircle.coe_add]
      change gamma n + _ = 0
      rw [he]
      simp [neg_mul]
    obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
    have hi := Real.goldenRatio_irrational.natCast_mul (show n + k ≠ 0 by omega)
    exact hi.ne_int z (by simpa using hz.symm)

  have natural_phase_fibre (n : ℕ) (x : LegalDigits) : phase x = gamma n ↔ x = zRow n := by
    obtain ⟨y, hy, huniq⟩ := phase_unique_of_avoids (gamma n) (natural_phase_avoids n)
    constructor
    · intro hx
      exact (huniq x hx).trans (huniq (zRow n) (phase_row n)).symm
    · rintro rfl
      exact phase_row n

  have phase_fibre_alternatives (c : AddCircle (1 : ℝ)) :
      (∃! x : LegalDigits, phase x = c) ∨
      (∃ x y : LegalDigits, x ≠ y ∧ ∀ z : LegalDigits, phase z = c ↔ z = x ∨ z = y) := by
    classical
    have hba : b = a + 1 := by
      dsimp [b, a, alpha]
      rw [Real.inv_goldenRatio]
      nlinarith [Real.goldenConj_sq]
    have hone : ((1 : ℝ) : AddCircle (1 : ℝ)) = 0 :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨1, by simp⟩
    have hab : (b : AddCircle (1 : ℝ)) = (a : AddCircle (1 : ℝ)) := by
      rw [hba, AddCircle.coe_add, hone, add_zero]
    have ha : a ∈ Set.Ico a (a + 1) := ⟨le_rfl, by linarith⟩
    have hbounds (z : LegalDigits) : signedValue z ∈ Set.Icc a b := by
      rw [← signed_series_range.1]
      exact Set.mem_range_self z
    let t := AddCircle.equivIco (1 : ℝ) a c
    have htc : ((t.val : ℝ) : AddCircle (1 : ℝ)) = c := AddCircle.coe_equivIco
    by_cases hta : t.val = a
    · have hca : c = (a : AddCircle (1 : ℝ)) := htc.symm.trans (congrArg _ hta)
      right
      refine ⟨u, v, ?_, ?_⟩
      · intro h
        have := congrArg (fun z : LegalDigits => z.val 0) h
        simp [u, v] at this
      · intro z
        constructor
        · intro hz
          have hs : signedValue z = a ∨ signedValue z = b := by
            by_cases hb : signedValue z = b
            · exact Or.inr hb
            · left
              apply (AddCircle.coe_eq_coe_iff_of_mem_Ico
                (show signedValue z ∈ Set.Ico a (a + 1) from
                  ⟨(hbounds z).1, hba ▸ (lt_of_le_of_ne (hbounds z).2 hb)⟩) ha).mp
              exact hz.trans hca
          exact hs.imp ((signed_series_range.2.1 z).mp) ((signed_series_range.2.2 z).mp)
        · rintro (rfl | rfl)
          · change ((signedValue u : ℝ) : AddCircle (1 : ℝ)) = c
            rw [(signed_series_range.2.1 u).mpr rfl, ← hca]
          · change ((signedValue v : ℝ) : AddCircle (1 : ℝ)) = c
            rw [(signed_series_range.2.2 v).mpr rfl, hab, ← hca]
    · have hti : t.val ∈ Set.Ioo a b :=
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm hta), by simpa only [hba] using t.property.2⟩
      have hcb : c ≠ (b : AddCircle (1 : ℝ)) := by
        intro h
        exact hta ((AddCircle.coe_eq_coe_iff_of_mem_Ico t.property ha).mp
          (htc.trans (h.trans hab)))
      have repr (z : LegalDigits) : phase z = c ↔ signedValue z = t.val := by
        constructor
        · intro hz
          have hb : signedValue z ≠ b := by
            intro hb
            exact hcb (hz.symm.trans (congrArg (fun s : ℝ => (s : AddCircle (1 : ℝ))) hb))
          exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
            (show signedValue z ∈ Set.Ico a (a + 1) from
              ⟨(hbounds z).1, hba ▸ (lt_of_le_of_ne (hbounds z).2 hb)⟩) t.property).mp
            (hz.trans htc.symm)
        · intro hz
          exact (congrArg (fun s : ℝ => (s : AddCircle (1 : ℝ))) hz).trans htc
      by_cases hs : t.val ∈ Set.range seam
      · obtain ⟨w, hw⟩ := hs
        right
        refine ⟨leftStream w, rightStream w, (signed_series_fibres.1 w).1, ?_⟩
        intro z
        rw [repr, ← hw]
        exact (signed_series_fibres.1 w).2 z
      · left
        obtain ⟨x, hx, huniq⟩ := signed_series_fibres.2.2 _ ⟨hti.1.le, hti.2.le⟩ hs
        exact ⟨x, (repr x).mpr hx, fun z hz => huniq z ((repr z).mp hz)⟩

  have phase_iterate (h : ℕ) (x : LegalDigits) : phase (T^[h] x) = phase x + h • c := by
    have hs : Function.Semiconj phase T (· + c) := semiconjugacy
    simpa only [add_right_iterate] using hs.iterate_right h x

  have merge_at_negative (j : ℕ) (x : LegalDigits) (hx : phase x = -(j • c)) :
      T^[j] x = zRow 0 := by
    apply (natural_phase_fibre 0 _).mp
    rw [phase_iterate, hx, neg_add_cancel]
    simp [gamma]

  have same_phase_sync (x y : LegalDigits) : ST x y ↔ phase x = phase y := by
    classical
    constructor
    · rintro ⟨m, hm⟩
      have h := congrArg phase hm
      rw [phase_iterate, phase_iterate] at h
      exact add_right_cancel h
    · intro hxy
      by_cases he : ∃ j : ℕ, 1 ≤ j ∧ phase x = -(j • c)
      · obtain ⟨j, hj, hx⟩ := he
        exact ⟨j, (merge_at_negative j x hx).trans
          (merge_at_negative j y (hxy ▸ hx)).symm⟩
      · have ha : ∀ j : ℕ, 1 ≤ j → phase x ≠
            (((-(j : ℝ) * Real.goldenRatio) : ℝ) : (AddCircle (1 : ℝ))) := by
          intro j hj hx
          apply he
          refine ⟨j, hj, ?_⟩
          rw [hx]
          simp only [c, ← AddCircle.coe_nsmul, nsmul_eq_mul, neg_mul, AddCircle.coe_neg]
        obtain ⟨z, hz, hu⟩ := phase_unique_of_avoids (phase x) ha
        exact ⟨0, (hu x rfl).trans (hu y hxy.symm).symm⟩

  have reflect_before_zero (x y : LegalDigits) (i : ℕ)
      (avoid : ∀ k, 0 < k → k ≤ i → T^[k] x ≠ zRow 0)
      (he : T^[i] x = T^[i] y) : x = y := by
    induction i with
    | zero => exact he
    | succ i ih =>
      apply ih (fun k hk hki => avoid k hk (by omega))
      have ht : T (T^[i] x) = T (T^[i] y) := by
        simpa only [Function.iterate_succ_apply'] using he
      have hn : (T (T^[i] x)).val ≠ (fun _ => false) := by
        intro hn
        have hez : T (T^[i] x) = zRow 0 := Subtype.ext (hn.trans row_zero.symm)
        apply avoid (i+1) (by omega) le_rfl
        simpa only [Function.iterate_succ_apply'] using hez
      obtain ⟨z, hz, hu⟩ := next_fibres.2.2.2 (T (T^[i] x)) hn
      exact (hu (T^[i] x) rfl).trans
        (hu (T^[i] y) (congrArg Subtype.val ht.symm)).symm

  have no_earlier_merge (j : ℕ) (x y : LegalDigits)
      (hx : phase x = -(j • c)) (hne : x ≠ y) (i : ℕ) (hi : i < j) :
      T^[i] x ≠ T^[i] y := by
    intro he
    apply hne
    apply reflect_before_zero x y i _ he
    intro k hk hki hz
    have hp : phase (T^[k] x) = 0 := by rw [hz, phase_row]; simp [gamma]
    rw [phase_iterate, hx] at hp
    have hkj : k ≤ j := by omega
    have hh : j • c = (j-k) • c + k • c := by
      rw [← add_nsmul, Nat.sub_add_cancel hkj]
    rw [hh] at hp
    have hd : -((j-k) • c) = 0 := by
      calc
        -((j-k) • c) = -((j-k) • c + k • c) + k • c := by abel
        _ = 0 := hp
    have bad := natural_phase_avoids 0 (j-k) (by omega)
    apply bad
    simp only [gamma, Nat.cast_zero, zero_mul, AddCircle.coe_zero]
    simpa only [c, ← AddCircle.coe_nsmul, nsmul_eq_mul, ← AddCircle.coe_neg,
      neg_mul] using hd.symm

  have async_iff_phase_orbit (x y : LegalDigits) : ET x y ↔ ER (phase x) (phase y) := by
    constructor
    · rintro ⟨m,n,he⟩
      refine ⟨(m : ℤ)-(n : ℤ), ?_⟩
      have hp := congrArg phase he
      rw [phase_iterate, phase_iterate] at hp
      have hs : phase y + n • c = (phase x + ((m : ℤ)-(n : ℤ)) • c) + n • c := by
        rw [← hp]
        simp only [sub_zsmul, natCast_zsmul]
        abel
      exact add_right_cancel hs
    · rintro ⟨k,hk⟩
      cases k with
      | ofNat k =>
        have hp : phase (T^[k] x) = phase y := by
          rw [phase_iterate, hk]
          simp [c]
        obtain ⟨m,hm⟩ := (same_phase_sync (T^[k] x) y).mpr hp
        exact ⟨m+k,m,by simpa only [Function.iterate_add_apply] using hm⟩
      | negSucc k =>
        have hp : phase x = phase (T^[k+1] y) := by
          rw [phase_iterate, hk]
          simp only [negSucc_zsmul]
          abel
        obtain ⟨m,hm⟩ := (same_phase_sync x (T^[k+1] y)).mpr hp
        exact ⟨m,m+(k+1),by simpa only [Function.iterate_add_apply] using hm⟩

  have er_equivalence : Equivalence ER := by
    refine ⟨?_, ?_, ?_⟩
    · intro t
      exact ⟨0, by simp⟩
    · intro t s h
      obtain ⟨k, hk⟩ := h
      refine ⟨-k, ?_⟩
      rw [hk, neg_zsmul]
      abel
    · intro t s u hts hsu
      obtain ⟨k, hk⟩ := hts
      obtain ⟨l, hl⟩ := hsu
      refine ⟨k + l, ?_⟩
      rw [hl, hk, add_zsmul, add_assoc]
  have er_countable (t : AddCircle (1 : ℝ)) : Set.Countable {s | ER t s} := by
    have he : {s | ER t s} = Set.range (fun k : ℤ => t + k • c) := by
      ext s
      simp only [ER, Set.mem_ofPred_eq, Set.mem_range]
      exact exists_congr fun k => eq_comm
    rw [he]
    exact Set.countable_range _
  have phase_countable (t : AddCircle (1 : ℝ)) : (phase ⁻¹' {t}).Countable := by
    rcases phase_fibre_alternatives t with ⟨x, hx, hu⟩ | ⟨x, y, hne, hf⟩
    · apply (Set.countable_singleton x).mono
      intro y hy
      exact hu y hy
    · apply (Set.toFinite ({x, y} : Set LegalDigits)).countable.mono
      intro z hz
      exact (hf z).mp hz
  have et_countable (x : LegalDigits) : Set.Countable {y | ET x y} := by
    have hp : (phase ⁻¹' {t | ER (phase x) t}).Countable := by
      convert (er_countable (phase x)).biUnion (fun t _ => phase_countable t) using 1
      ext y
      simp
    convert hp using 1
    ext y
    exact async_iff_phase_orbit x y
  have er_borel :
      MeasurableSet {p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) | ER p.1 p.2} := by
    have he : {p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) | ER p.1 p.2} =
        ⋃ k : ℤ, {p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) | p.2 = p.1 + k • c} := by
      ext p
      simp [ER, c]
    rw [he]
    apply MeasurableSet.iUnion
    intro k
    exact (isClosed_eq continuous_snd (continuous_fst.add continuous_const)).measurableSet
  have et_borel :
      @MeasurableSet (LegalDigits × LegalDigits) (borel (LegalDigits × LegalDigits))
        {p | ET p.1 p.2} := by
    letI : MeasurableSpace (LegalDigits × LegalDigits) := borel (LegalDigits × LegalDigits)
    haveI : BorelSpace (LegalDigits × LegalDigits) := ⟨rfl⟩
    have he : {p : LegalDigits × LegalDigits | ET p.1 p.2} =
        ⋃ m : ℕ, ⋃ n : ℕ, {p : LegalDigits × LegalDigits | T^[m] p.1 = T^[n] p.2} := by
      ext p
      simp [ET]
    rw [he]
    apply MeasurableSet.iUnion
    intro m
    apply MeasurableSet.iUnion
    intro n
    exact (isClosed_eq ((t_continuous.iterate m).comp continuous_fst)
      ((t_continuous.iterate n).comp continuous_snd)).measurableSet
  refine ⟨er_equivalence, ?_, er_countable, et_countable, er_borel, et_borel,
    async_iff_phase_orbit, same_phase_sync, ?_⟩
  · have he : ET = fun x y => ER (phase x) (phase y) := by
      funext x y
      exact propext (async_iff_phase_orbit x y)
    rw [he]
    exact er_equivalence.comap phase
  · intro j hj x y hx hy
    exact ⟨merge_at_negative j x hx, merge_at_negative j y hy,
      fun hne i hi => no_earlier_merge j x y hx hne i hi⟩

end D5.S1.Digit.Infinite.PhaseOrbitRelations
