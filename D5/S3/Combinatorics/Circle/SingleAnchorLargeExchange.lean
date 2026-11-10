/- GID: D5/S3/Combinatorics/Circle/SingleAnchorLargeExchange
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/SingleAnchorLargeExchange
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic]
   utility: none
   digest: One actual positive SMALL anchor constructs a complete strict-H three-LARGE exchange. -/
module
public import D5.S3.Combinatorics.Circle.ThreeLargePacketExchange
public import Mathlib.Data.List.Perm.Basic

/-! A reserved physical anchor fills the residual integer crossing gap. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.SingleAnchorLargeExchange
open SourceWidth ExpandingSourcePath MixedSuffixEnergy SmallStepOrdering
open TwoOppositeLargeExchange ThreeLargePacketExchange
open scoped BigOperators

/-- Reserve one actual occurrence, cross with the others, and append that
occurrence exactly when the crossing prefix leaves a positive gap. -/
theorem single_anchor_select {α : Type*} [DecidableEq α]
    (f : α → ℤ) (Pos : List α) (a : α) (m B low : ℤ)
    (ha : a ∈ Pos) (haval : f a = m) (hm : 0 < m)
    (hB : m ≤ B + 1) (hlow : 0 < low)
    (hentry : ∀ i ∈ Pos, 0 < f i ∧ (i ≠ a → f i ≤ m + B + 1))
    (htotal : low ≤ mass f Pos) :
    ∃ R : List α, R.Subperm Pos ∧ low ≤ mass f R ∧ mass f R ≤ low + B := by
  classical
  let O := Pos.erase a
  have hpart : (O ++ [a]).Perm Pos :=
    List.perm_append_comm.trans (List.perm_cons_erase ha).symm
  have hmass : mass f O + m = mass f Pos := by
    simpa only [mass, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, haval]
      using (hpart.map f).sum_eq
  obtain ⟨U,hU,hUlo,hUhi⟩ : ∃ U : List α,
      U.Sublist O ∧ low - m ≤ mass f U ∧ mass f U ≤ low + B := by
    by_cases hl : low ≤ m
    · refine ⟨[], List.nil_sublist _, ?_, ?_⟩ <;>
        simp only [mass, List.map_nil, List.sum_nil] <;> omega
    · have hentryO : ∀ i ∈ O, 0 < f i ∧ f i ≤ (m + B) + 1 := by
        intro i hi
        have hh := hentry i (List.mem_of_mem_erase hi)
        refine ⟨hh.1, ?_⟩
        by_cases hieq : i = a
        · rw [hieq,haval]; omega
        · exact hh.2 hieq
      obtain ⟨U,hU,hlo,hhi⟩ := PositiveSmallReturnExchange.first_crossing
        f O (m + B) (by omega) (low - m) (by omega) hentryO (by omega)
      exact ⟨U,hU,hlo,by omega⟩
  obtain ⟨K,hK,hlo,hhi⟩ : ∃ K : List α,
      K.Sublist [a] ∧ low ≤ mass f U + mass f K ∧
      mass f U + mass f K ≤ low + B := by
    by_cases hu : low ≤ mass f U
    · refine ⟨[], List.nil_sublist _, ?_, ?_⟩ <;>
        simp only [mass, List.map_nil, List.sum_nil, add_zero] <;>
        dsimp only [mass] at * <;> omega
    · refine ⟨[a], List.Sublist.refl _, ?_, ?_⟩ <;>
        simp only [mass, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero, haval] <;>
        dsimp only [mass] at * <;> omega
  refine ⟨U ++ K, (hU.append hK).subperm.trans hpart.subperm, ?_, ?_⟩
  · simpa only [mass, List.map_append, List.sum_append] using hlo
  · simpa only [mass, List.map_append, List.sum_append] using hhi

/-- One actual positive SMALL occurrence supplies the return batch with
integer-sharp anchor and other-entry bounds; no doubling pair is required. -/
theorem actualSource_threeLarge_singleAnchor_exchange_full
    (k t : ℕ) (hk : 3 ≤ k) (p q y zpen z a : Fin k)
    (A T0 T1 T2 E : List (Fin k))
    (hpositive : 0 < s k t p)
    (hnlarge : Q k ≤ |s k t (hit k 1 p)|)
    (hexpand : N k < 3 * |s k t p|)
    (hW : Legal k t (oldWord p y zpen z A T0 T1 T2 E))
    (hpunused : p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hnunused : hit k 1 p ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hqunused : q ∉ oldWord p y zpen z A T0 T1 T2 E)
    (hsmall : ∀ i ∈ smallWord T0 T1 T2 E, |s k t i| < Q k)
    (hylarge : Q k ≤ -s k t y)
    (hzpenlarge : Q k ≤ -s k t zpen)
    (hzlarge : Q k ≤ -s k t z)
    (hzupper : -s k t z ≤ s k t q)
    (hqlarge : Q k ≤ s k t q)
    (hqsmaller : s k t q < s k t p)
    (ha : a ∈ smallWord T0 T1 T2 E)
    (hapositive : 0 < s k t a)
    (haBound : s k t a ≤ (C k - s k t q) + 1)
    (hother : ∀ i ∈ smallWord T0 T1 T2 E,
      i ≠ a → 0 < s k t i →
      s k t i ≤ s k t a + (C k - s k t q) + 1) :
    let n := hit k 1 p
    let x := hit k 2 p
    let W := oldWord p y zpen z A T0 T1 T2 E
    let S := smallWord T0 T1 T2 E
    let e0 := prospective k t p q y zpen W
    ∃ R L : List (Fin k),
      R.Subperm (positive t S) ∧ (L ++ R).Perm S ∧
      (∀ i ∈ R, 0 < s k t i ∧ |s k t i| < Q k) ∧
      (let V := A ++ [p, n] ++ L ++ [z, q]
       let returned := [x, y, zpen] ++ R
       let e := e0 - mass (s k t) R
       Legal k t V ∧ InStrip (s k t) (C k) 0 V ∧
       (∀ j : ℕ, 0 ≤ mass (s k t) (V.take j) ∧
         mass (s k t) (V.take j) ≤ C k) ∧
       Inventory k t W V [p, n, q] returned ∧
       G k t V = G k t W ∧ U V = U W + R.length ∧
       H k t V + 3 ^ (s k t x).natAbs + 3 ^ (s k t y).natAbs +
         3 ^ (s k t zpen).natAbs =
         H k t W + 3 ^ (s k t p).natAbs + 3 ^ (s k t n).natAbs +
           3 ^ (s k t q).natAbs ∧
       H k t V < H k t W ∧ J k t V < J k t W ∧
       mass (s k t) V = e ∧ s k t q ≤ e ∧ e ≤ C k) := by
  apply actualSource_threeLarge_return_exchange_full k t hk p q y zpen z
    A T0 T1 T2 E hpositive hnlarge hexpand hW hpunused hnunused hqunused
    hsmall hylarge hzpenlarge hzlarge hzupper hqlarge hqsmaller
  intro low hlow htotal
  apply single_anchor_select (s k t) (positive t (smallWord T0 T1 T2 E))
    a (s k t a) (C k - s k t q) low
  · simp only [positive, List.mem_filter, decide_eq_true_eq]
    exact ⟨ha,hapositive⟩
  · rfl
  · exact hapositive
  · exact haBound
  · exact hlow
  · intro i hi
    have hm : i ∈ smallWord T0 T1 T2 E ∧ 0 < s k t i := by
      simpa only [positive, List.mem_filter, decide_eq_true_eq] using hi
    exact ⟨hm.2, fun hne => hother i hm.1 hne hm.2⟩
  · exact htotal

#print axioms actualSource_threeLarge_singleAnchor_exchange_full

end D5.S3.Combinatorics.Circle.SingleAnchorLargeExchange
