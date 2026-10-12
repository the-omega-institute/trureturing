/- GID: D5/S3/Estimation/TimeArrow/NativeRectangleEnvironment
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeRectangleEnvironment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Numerical rectangle margins are recovered from the collapsed native history and outside counts. -/

import D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel

open scoped BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
noncomputable section

open private
  D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber.native_departure_word_counts
from D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber

/-- The collapsed history fixes both total signal departure counts. -/
theorem native_signal_count_totals {M q s : ℕ} (S : Support M q)
    (e : Experiment) (o : Obs M s e) [Fintype (Sites s e)] (y : Fiber S e o) :
    (∑ i : {i : Fin M // i ∈ S.val}, count e y.val i.val 1) =
        (signedDepartureBlocks S e o 0).card ∧
      (∑ i : {i : Fin M // i ∈ S.val}, count e y.val i.val (-1)) =
        (signedDepartureBlocks S e o 1).card := by
  classical
  let W := labelBlockEquiv S e o _ _ _ (nativeDepartureEnumeration S e o)
    (fiberLabelEquiv S e o y)
  have hp : (∑ i : {i : Fin M // i ∈ S.val}, count e y.val i.val 1) =
      (D5.S3.Quantum.Entanglement.OccupancyWordSectors.occupation W.1.1).card := by
    rw [← Multiset.sum_count_eq_card (s := univ) (fun _ _ => mem_univ _)]
    exact sum_congr rfl fun i _ => (D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber.native_departure_word_counts S e o y i).1
  have hm : (∑ i : {i : Fin M // i ∈ S.val}, count e y.val i.val (-1)) =
      (D5.S3.Quantum.Entanglement.OccupancyWordSectors.occupation W.1.2).card := by
    rw [← Multiset.sum_count_eq_card (s := univ) (fun _ _ => mem_univ _)]
    exact sum_congr rfl fun i _ => (D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber.native_departure_word_counts S e o y i).2
  simpa only [D5.S3.Quantum.Entanglement.OccupancyWordSectors.occupation_card] using And.intro hp hm

/-- The environment retains membership and all outside signal-row count
pairs; departure totals are already fixed by the collapsed history. -/
def nativeMinimalRectangleReadout {M q s : ℕ} (S : Support M q) (e : Experiment)
    (o : Obs M s e) (k l : ℕ) (y : Fiber S e o) :
    Finset {i : Fin M // i ∈ S.val} × ({i : Fin M // i ∈ S.val} → Option (ℕ × ℕ)) :=
  ((nativeMarginRectangleReadout S e o k l y).1,
    (nativeMarginRectangleReadout S e o k l y).2.1)

/-- Exact information sigma-algebra of the minimal finite readout. -/
def nativeMinimalRectangleSigma {M q s : ℕ} (S : Support M q) (e : Experiment)
    (o : Obs M s e) (k l : ℕ) : MeasurableSpace (Fiber S e o) :=
  MeasurableSpace.comap (nativeMinimalRectangleReadout S e o k l) ⊤

private theorem two_level_count_sum {α : Type*} [Fintype α] [DecidableEq α]
    (V : Finset α) (f : α → ℕ) (k : ℕ)
    (hf : ∀ i ∈ V, f i = k ∨ f i = k + 1) :
    (∑ i, f i) + (V.filter fun i => f i = k).card =
      (∑ i ∈ univ \ V, f i) + V.card * (k + 1) := by
  have hi : (∑ i ∈ V, f i) + (V.filter fun i => f i = k).card =
      V.card * (k + 1) := by
    have hb : (∑ i ∈ V, if f i = k then (1 : ℕ) else 0) =
        (V.filter fun i => f i = k).card := by
      simpa using (sum_boole (R := ℕ) (fun i => f i = k) V)
    rw [← hb, ← sum_add_distrib]
    calc
      _ = ∑ i ∈ V, (k + 1) := by
        apply sum_congr rfl
        intro i hi
        obtain h | h := hf i hi
        · simp [h]
        · have hn : f i ≠ k := by omega
          simp [hn, h]
      _ = _ := by simp
  have ht := sum_sdiff (subset_univ V) (f := f)
  omega

/-- Both margins are determined by the minimal environment. -/
theorem native_minimal_readout_eq_iff {M q s : ℕ} (S : Support M q)
    (e : Experiment) (o : Obs M s e) [Fintype (Sites s e)] (k l : ℕ)
    (y z : Fiber S e o) :
    nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z ↔
      nativeMarginRectangleReadout S e o k l y = nativeMarginRectangleReadout S e o k l z := by
  classical
  constructor
  · intro h
    have hV := congrArg Prod.fst h
    have hout := congrArg Prod.snd h
    change nativeRectangleRows S e o k l y = nativeRectangleRows S e o k l z at hV
    have ho (i : {i : Fin M // i ∈ S.val}) (hi : i ∉ nativeRectangleRows S e o k l y) :
        count e y.val i.val 1 = count e z.val i.val 1 ∧
          count e y.val i.val (-1) = count e z.val i.val (-1) := by
      have hiz : i ∉ nativeRectangleRows S e o k l z := by rwa [← hV]
      have hh := congrFun hout i
      change (if i ∈ nativeRectangleRows S e o k l y then none else
          some (count e y.val i.val 1, count e y.val i.val (-1))) =
        (if i ∈ nativeRectangleRows S e o k l z then none else
          some (count e z.val i.val 1, count e z.val i.val (-1))) at hh
      simpa only [if_neg hi, if_neg hiz, Option.some.injEq, Prod.mk.injEq] using hh
    have hs : (∑ i ∈ univ \ nativeRectangleRows S e o k l y, count e y.val i.val 1) =
        (∑ i ∈ univ \ nativeRectangleRows S e o k l z, count e z.val i.val 1) ∧
      (∑ i ∈ univ \ nativeRectangleRows S e o k l y, count e y.val i.val (-1)) =
        (∑ i ∈ univ \ nativeRectangleRows S e o k l z, count e z.val i.val (-1)) := by
      rw [← hV]
      constructor <;> apply sum_congr rfl <;> intro i hi
      · exact (ho i (mem_sdiff.mp hi).2).1
      · exact (ho i (mem_sdiff.mp hi).2).2
    have hp (v : Fiber S e o) := two_level_count_sum (nativeRectangleRows S e o k l v)
      (fun i => count e v.val i.val 1) k (fun i hi => (mem_filter.mp hi).2.1)
    have hn (v : Fiber S e o) := two_level_count_sum (nativeRectangleRows S e o k l v)
      (fun i => count e v.val i.val (-1)) l (fun i hi => (mem_filter.mp hi).2.2)
    have hty := native_signal_count_totals S e o y
    have htz := native_signal_count_totals S e o z
    have hR : ((nativeRectangleRows S e o k l y).filter
        fun i => count e y.val i.val 1 = k).card =
        ((nativeRectangleRows S e o k l z).filter
        fun i => count e z.val i.val 1 = k).card := by
      rw [hV]
      have hy := hp y
      have hz := hp z
      rw [hty.1, hs.1, hV] at hy
      rw [htz.1] at hz
      omega
    have hU : ((nativeRectangleRows S e o k l y).filter
        fun i => count e y.val i.val (-1) = l).card =
        ((nativeRectangleRows S e o k l z).filter
        fun i => count e z.val i.val (-1) = l).card := by
      rw [hV]
      have hy := hn y
      have hz := hn z
      rw [hty.2, hs.2, hV] at hy
      rw [htz.2] at hz
      omega
    exact Prod.ext hV (Prod.ext hout (Prod.ext hR hU))
  · intro h
    exact congrArg (fun v => (v.1, v.2.1)) h

/-- Omitting numerical margins leaves the native conditioning sigma-algebra
unchanged, because both margins are recoverable on every collapsed fiber. -/
theorem native_rectangle_sigma_eq {M q s : ℕ} (S : Support M q)
    (e : Experiment) (o : Obs M s e) [Fintype (Sites s e)] (k l : ℕ) :
    nativeMinimalRectangleSigma S e o k l = nativeMarginRectangleSigma S e o k l := by
  classical
  apply MeasurableSpace.ext
  intro A
  change (∃ B, @MeasurableSet _ ⊤ B ∧
      (nativeMinimalRectangleReadout S e o k l) ⁻¹' B = A) ↔
    (∃ B, @MeasurableSet _ ⊤ B ∧
      (nativeMarginRectangleReadout S e o k l) ⁻¹' B = A)
  constructor
  · rintro ⟨B, _, rfl⟩
    refine ⟨nativeMarginRectangleReadout S e o k l ''
      ((nativeMinimalRectangleReadout S e o k l) ⁻¹' B), MeasurableSpace.measurableSet_top, ?_⟩
    ext y
    constructor
    · rintro ⟨z, hz, hzy⟩
      have he := (native_minimal_readout_eq_iff S e o k l z y).mpr hzy
      change nativeMinimalRectangleReadout S e o k l y ∈ B
      rwa [← he]
    · intro hy
      exact ⟨y, hy, rfl⟩
  · rintro ⟨B, _, rfl⟩
    refine ⟨nativeMinimalRectangleReadout S e o k l ''
      ((nativeMarginRectangleReadout S e o k l) ⁻¹' B), MeasurableSpace.measurableSet_top, ?_⟩
    ext y
    constructor
    · rintro ⟨z, hz, hzy⟩
      have he := (native_minimal_readout_eq_iff S e o k l z y).mp hzy
      change nativeMarginRectangleReadout S e o k l y ∈ B
      rwa [← he]
    · intro hy
      exact ⟨y, hy, rfl⟩

open private
  D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel.native_four_cell_conditional_law
from D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel

/-- On an attained minimal environment, the original pair/path A count has
an exact hypergeometric law. All departure-total side conditions are derived
from the reference native history, rather than assumed. -/
private theorem native_minimal_four_cell_law {M q s : ℕ} (S : Support M q)
    (r : ℝ) (e : Experiment) (o : Obs M s e) [Fintype (Sites s e)]
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (k l : ℕ) (z : Fiber S e o) (t : ℕ) :
    letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
    let V := nativeRectangleRows S e o k l z
    let R := (V.filter fun i => count e z.val i.val 1 = k).card
    let U := (V.filter fun i => count e z.val i.val (-1) = l).card
    let Env := univ.filter fun y : Fiber S e o =>
      nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z
    conditionalFiberMass S r e o (Env.filter fun y => nativeRectangleACount S e o k l y = t) /
      conditionalFiberMass S r e o Env =
        if t ≤ U then ((R.choose t : ℝ) * ((V.card - R).choose (U - t) : ℝ)) /
          (V.card.choose U : ℝ) else 0 := by
  classical
  letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
  dsimp only
  let V := nativeRectangleRows S e o k l z
  let R := (V.filter fun i => count e z.val i.val 1 = k).card
  let U := (V.filter fun i => count e z.val i.val (-1) = l).card
  let outsideP := fun i : {i : Fin M // i ∈ S.val} => count e z.val i.val 1
  let outsideM := fun i : {i : Fin M // i ∈ S.val} => count e z.val i.val (-1)
  have hR : R ≤ V.card := card_filter_le V _
  have hU : U ≤ V.card := card_filter_le V _
  have hp := two_level_count_sum V outsideP k
    (fun i hi => (mem_filter.mp hi).2.1)
  have hn := two_level_count_sum V outsideM l
    (fun i hi => (mem_filter.mp hi).2.2)
  rw [(native_signal_count_totals S e o z).1] at hp
  rw [(native_signal_count_totals S e o z).2] at hn
  have hpos : (∑ i ∈ univ \ V, outsideP i) + R * k + (V.card - R) * (k + 1) =
      (signedDepartureBlocks S e o 0).card := by
    change (signedDepartureBlocks S e o 0).card + R = _ at hp
    nlinarith [Nat.sub_add_cancel hR]
  have hneg : (∑ i ∈ univ \ V, outsideM i) + U * l + (V.card - U) * (l + 1) =
      (signedDepartureBlocks S e o 1).card := by
    change (signedDepartureBlocks S e o 1).card + U = _ at hn
    nlinarith [Nat.sub_add_cancel hU]
  have hout : ∀ i ∉ V, ¬ ((outsideP i = k ∨ outsideP i = k + 1) ∧
      (outsideM i = l ∨ outsideM i = l + 1)) := by
    intro i hi
    exact fun h => hi (mem_filter.mpr ⟨mem_univ _, h⟩)
  have he : (univ.filter fun y : Fiber S e o =>
      nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z) =
    (univ.filter fun y : Fiber S e o => nativeMarginRectangleReadout S e o k l y =
      (V, (fun i => if i ∈ V then none else some (outsideP i, outsideM i)), R, U)) := by
    ext y
    simp only [mem_filter, mem_univ, true_and,
      native_minimal_readout_eq_iff S e o k l y z]
    rfl
  rw [he]
  exact (D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel.native_four_cell_conditional_law
    S r e o hq hqm hr hr1 ha ha1 V outsideP outsideM k l R U t
      hpos hneg hR hU hout).1

end
end D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
