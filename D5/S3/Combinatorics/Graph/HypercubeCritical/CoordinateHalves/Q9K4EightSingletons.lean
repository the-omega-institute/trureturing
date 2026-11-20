/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9K4EightSingletons
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9K4EightSingletons
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The eight-singleton obstruction for the normalized K4 projection at half size 28. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4ZeroCutArithmetic
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5SingletonCutObstructions

/-! The midpoint overlaps of the K4 cuts give the local degree equation on Q5. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4EightSingletons

open Finset
open scoped BigOperators
open BalancedCriticalSpectrum (Q IsBalanced)
local notation "flip" => BalancedCriticalSpectrum.flip
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCubeComponentBoundary (directions regular_directions)
open Q9FourFiberSpectrum (leftProjection fiber_and_signedRow_supported)
open Q9SignedProjection (join fiber signedRow)
open Q9TenPatternIncidence (tenProjection vertexCode midpointCode endpoints midpoint_cut)
open Q9K4CutBalance Q9K4ZeroCutArithmetic
open Q5SingletonCutObstructions (adjacent sameLabelDegree eight_singletons_impossible)
open Q5SharedSixLeaves (degree)
open private label_values nonzero_iff_mem occupied_eq_indicator midpoint_scaled countIf
  singletonSupport_card even_degree star_count_eq_half star_moments label_contributions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4CutBalance
open private occupation_totals half_pairing from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4ZeroCutArithmetic
open private pattern from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThetaProjection
open private flip_join_left flip_join_right from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9SignedProjection
open private flip_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private adjacent_flip degree_eq_count_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5SingletonCutObstructions

private abbrev midpoint (z : Q 9 → ℤ) (y : Q 5) (e : Fin 6) : ℤ :=
  fiber z y (pattern (midpointCode e))

private def incident (i : Fin 4) (e : Fin 6) : Prop :=
  i = (endpoints e).1 ∨ i = (endpoints e).2

private instance (i : Fin 4) (e : Fin 6) : Decidable (incident i e) :=
  inferInstanceAs (Decidable (_ ∨ _))

private def centerProfile (i : Fin 4) (sign : Bool) (j : Fin 4) : ℤ :=
  (if sign then 1 else -1) * (if j = i then 3 else -1)

private def pairedLabels (i k : Fin 4) (sign : Bool) (j : Fin 4) : ℤ :=
  (if sign then 1 else -1) * ((if j = i then 1 else 0) - (if j = k then 1 else 0))

private theorem singleton_data {z : Q 9 → ℤ}
    (ht : ∀ y, LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y))
    (y : Q 5) :
    ∃ (i : Fin 4) (sign : Bool), oddCount z y = 3 →
      (∀ j, cScaled z j y = centerProfile i sign j) ∧
      ((∀ j, evenLabel z j y = 0) ∨
        ∃ k, k ≠ i ∧ ∀ j, evenLabel z j y = pairedLabels i k sign j) := by
  rcases ht y with ⟨_, h, _⟩ | ⟨i, sign, _, hc, ha⟩ | ⟨h, _⟩
  · exact ⟨0, false, fun hh => by omega⟩
  · exact ⟨i, sign, fun _ => ⟨hc, ha⟩⟩
  · exact ⟨0, false, fun hh => by omega⟩

private theorem midpoint_occupation {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hP : leftProjection C = tenProjection)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    (hrow : ∀ u, signedRow z u = 3 * z u) (y : Q 5) (e : Fin 6) :
    occupied (midpoint z y e) =
      countIf (cScaled z (endpoints e).1 y ≠ cScaled z (endpoints e).2 y) := by
  have hs (x : Q 4) (hx : x ∉ tenProjection) :=
    fiber_and_signedRow_supported hz hrow y (hP.symm ▸ hx)
  have hunit (j : Fin 6) : |midpoint z y j| ≤ 1 := by
    rcases label_values hu hz (join (pattern (midpointCode j)) y) with h | h | h <;>
      change |z (join (pattern (midpointCode j)) y)| ≤ 1 <;> norm_num [h]
  have hm := midpoint_scaled e
    (midpoint_cut (fun x hx => (hs x hx).1) (fun x hx => (hs x hx).2) hunit).1
  have hzero : midpoint z y e = 0 ↔ cScaled z (endpoints e).1 y = cScaled z (endpoints e).2 y :=
    ⟨fun h => by change 4 * midpoint z y e = _ at hm; omega,
      fun h => by change 4 * midpoint z y e = _ at hm; omega⟩
  by_cases he : midpoint z y e = 0
  · simp [occupied, countIf, he, hzero.mp he]
  · have hn : cScaled z (endpoints e).1 y ≠ cScaled z (endpoints e).2 y :=
      fun hc => he (hzero.mpr hc)
    simp [occupied, countIf, he, hn]

private theorem center_profile_table :
    (∀ i sign j, |centerProfile i sign j| = 3 ↔ j = i) ∧
    (∀ i sign e,
      (centerProfile i sign (endpoints e).1 ≠ centerProfile i sign (endpoints e).2) ↔
        incident i e) ∧
    (∀ i k sign, k ≠ i → pairedLabels i k sign i * centerProfile i sign i = 3) := by
  decide +kernel

private theorem singleton_overlap : ∀ i j : Fin 4,
    (∑ e, countIf (incident i e) * countIf (incident j e)) = 1 + 2 * countIf (j = i) := by
  decide +kernel

private theorem balanced_overlap : ∀ (i : Fin 4) (side : Fin 4 → Bool),
    (∑ e, countIf (side (endpoints e).1 ≠ side (endpoints e).2)) = 4 →
      (∑ e, countIf (incident i e) *
        countIf (side (endpoints e).1 ≠ side (endpoints e).2)) = 2 := by
  decide +kernel

private theorem singleton_horizontal : ∀ (i k : Fin 4) (sign : Bool), k ≠ i →
    (∑ e, countIf (incident i e) *
      (occupied (pairedLabels i k sign (endpoints e).1) +
        occupied (pairedLabels i k sign (endpoints e).2))) = 4 := by
  decide +kernel

private theorem midpoint_neighbors : ∀ e : Fin 6,
    ((univ.filter fun d : Fin 4 => flip (pattern (midpointCode e)) d ∈ tenProjection).image
      (flip (pattern (midpointCode e)))) =
      {pattern (vertexCode (endpoints e).1), pattern (vertexCode (endpoints e).2)} ∧
    pattern (vertexCode (endpoints e).1) ≠ pattern (vertexCode (endpoints e).2) := by
  decide +kernel

open Classical in
private theorem midpoint_vertical {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    {y : Q 5} {e : Fin 6} (hm : midpoint z y e ≠ 0)
    (hout : ∀ x ∉ tenProjection, fiber z y x = 0) :
    (∑ d : Fin 5, occupied (midpoint z (flip y d) e)) =
      3 - (occupied (evenLabel z (endpoints e).1 y) +
        occupied (evenLabel z (endpoints e).2 y)) := by
  let x := pattern (midpointCode e)
  have hp : join x y ∈ C := (nonzero_iff_mem hu hz _).mp hm
  have hdeg : (∑ d : Fin 9, occupied (z (flip (join x y) d))) = 3 := by
    simp only [occupied_eq_indicator hu hz, sum_boole]
    change ((directions C (join x y)).card : ℤ) = 3
    rw [regular_directions C hreg hp]
    rfl
  rw [Fin.sum_univ_add (a := 4) (b := 5)] at hdeg
  simp only [flip_join_left, flip_join_right] at hdeg
  let D := univ.filter fun d : Fin 4 => flip x d ∈ tenProjection
  have hhor : (∑ d : Fin 4, occupied (fiber z y (flip x d))) =
      occupied (evenLabel z (endpoints e).1 y) + occupied (evenLabel z (endpoints e).2 y) := by
    rw [← sum_subset (filter_subset _ _) (s₁ := D) (fun d _ hd => by
      have hn : flip x d ∉ tenProjection := fun h => hd (mem_filter.mpr ⟨mem_univ _, h⟩)
      simp [hout _ hn, occupied])]
    rw [← sum_image (s := D) (g := flip x) (f := fun v => occupied (fiber z y v))
      (flip_injective x).injOn]
    rw [(midpoint_neighbors e).1, sum_insert (by simpa only [mem_singleton] using
      (midpoint_neighbors e).2), sum_singleton]
    rfl
  change (∑ d : Fin 4, occupied (fiber z y (flip x d))) +
    (∑ d : Fin 5, occupied (midpoint z (flip y d) e)) = 3 at hdeg
  omega

private theorem suffix_flip (x : BitVec 5) (d : Fin 5) :
    cubeBitVec 5 (x ^^^ BitVec.twoPow 5 d.val) = flip (cubeBitVec 5 x) d := by
  have hp : ∀ i : Fin 5, BitVec.twoPow 5 i.val = BitVec.ofNat 5 (2 ^ i.val) := by
    decide +kernel
  rw [hp, cubeBitVec_xor_single]
  rfl

private theorem degree_as_sum (T : Finset (BitVec 5)) (x : BitVec 5) :
    (degree T x : ℤ) = ∑ d : Fin 5, countIf (x ^^^ BitVec.twoPow 5 d.val ∈ T) := by
  rw [degree_eq_count_directions]
  simp [countIf, sum_boole]

local instance : Fintype (BitVec 5) :=
  Fintype.ofEquiv (Fin 32) {
    toFun := BitVec.ofFin (w := 5)
    invFun := BitVec.toFin
    left_inv := by intro x; rfl
    right_inv := by intro x; cases x; rfl }

private theorem label_moment_bound {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hP : leftProjection C = tenProjection)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    (hrow : ∀ u, signedRow z u = 3 * z u)
    (hrows : ∀ i y, signedRow (evenLabel z i) y = 3 * evenLabel z i y - cScaled z i y ∧
      signedRow (cScaled z i) y = 4 * evenLabel z i y - 3 * cScaled z i y)
    (ht : ∀ y, LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y))
    (hodd : (∑ y, oddCount z y) = 48 - zeroCutOccupation z)
    (hzero : zeroCutOccupation z = 8) (hs : singletons z = 8)
    (hhalves : ∀ i, (C.filter fun u => u ((starAxis i).castAdd 5) = decide (i ≠ 0)).card = 28)
    (i : Fin 4) : 4 * singletonCenters z i ≤ 12 + activeCenters z i := by
  have hhalf : (∑ y, starCount z i y) = 28 := by
    rw [star_count_eq_half hP hu hz i, hhalves]
    rfl
  have hlinear := sum_congr (s₁ := (univ : Finset (Q 5))) rfl
    (fun y _ => (star_moments hP hu hz hrow i y).1)
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, hhalf, hodd] at hlinear
  change 2 * (28 - labelCount z i) =
    48 - zeroCutOccupation z - singletons z + 4 * singletonCenters z i at hlinear
  have hpair := half_pairing hP hu hz hrow hrows ht hodd i
  rw [hhalf, hzero] at hpair
  have hcount : activeCenters z i + activePartners z i + activeBalanced z i ≤ labelCount z i := by
    unfold activeCenters activePartners activeBalanced labelCount
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_le_sum
    intro y _
    by_cases ho : oddCount z y = 0
    · rcases ht y with ⟨hc, _, _⟩ | ⟨_, _, h, _⟩ | ⟨h, _⟩
      · have hci : cScaled z i y = 0 := hc i
        simp [ho, hci, countIf, occupied]
        split <;> omega
      · omega
      · omega
    · exact (label_contributions (i := i) (ht y) (fun h => (ho h).elim)).2.1.ge
  have hpartner : 0 ≤ activePartners z i :=
    sum_nonneg (fun _ _ => by unfold occupied countIf; split <;> split <;> omega)
  omega

open Classical in
/-- Eight singleton cuts cannot occur in the half-28, eight-zero-occupation K4 case. -/
theorem eight_singletons_impossible_of_half_twenty_eight {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hsize : C.card = 72)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hP : leftProjection C = tenProjection)
    (hhalves : ∀ i, (C.filter fun u => u ((starAxis i).castAdd 5) = decide (i ≠ 0)).card = 28)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    (hrow : ∀ u, signedRow z u = 3 * z u)
    (hrows : ∀ i y, signedRow (evenLabel z i) y = 3 * evenLabel z i y - cScaled z i y ∧
      signedRow (cScaled z i) y = 4 * evenLabel z i y - 3 * cScaled z i y)
    (ht : ∀ y, LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y))
    (hzero : zeroCutOccupation z = 8) (hs : singletons z = 8) : False := by
  let S := singletonSupport z
  let B := univ.filter fun x : BitVec 5 => oddCount z (cubeBitVec 5 x) = 4
  have hS (x : BitVec 5) : x ∈ S ↔ oddCount z (cubeBitVec 5 x) = 3 := by
    simp [S, singletonSupport]
  have hB (x : BitVec 5) : x ∈ B ↔ oddCount z (cubeBitVec 5 x) = 4 := by simp [B]
  have hSCard : S.card = 8 := by
    have h := singletonSupport_card z
    change (S.card : ℤ) = singletons z at h
    omega
  have hdis : Disjoint S B := disjoint_left.mpr fun x hx hx' =>
    by have := (hS x).mp hx; have := (hB x).mp hx'; omega
  obtain ⟨_, _, hodd, _⟩ := occupation_totals hsize hreg hb hP hu hz hrow
    (fun i y => (hrows i y).1) ht
  have hcutCount : 3 * singletons z + 4 * balancedCuts z = ∑ y, oddCount z y := by
    have hlocalCount (y : Q 5) :
        3 * countIf (oddCount z y = 3) + 4 * countIf (oddCount z y = 4) = oddCount z y := by
      rcases ht y with ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨h, _⟩ <;> norm_num [h, countIf]
    have h := sum_congr (s₁ := (univ : Finset (Q 5))) rfl (fun y _ => hlocalCount y)
    simpa only [sum_add_distrib, ← mul_sum, singletons, balancedCuts] using h
  have hBCard : B.card = 4 := by
    have h := Fintype.sum_equiv (cubeBitVec 5)
      (fun x => countIf (oddCount z (cubeBitVec 5 x) = 4))
      (fun y => countIf (oddCount z y = 4)) (fun _ => rfl)
    have hcast : (B.card : ℤ) = balancedCuts z := by
      simpa only [B, balancedCuts, countIf, sum_boole] using h
    omega
  have hpar := singleton_support_neighborParity
    (singleton_parity_rows (fun i y => label_values hu hz (join (pattern (vertexCode i)) y))
      hrows ht).2
  choose label sign hdata using fun x : BitVec 5 => singleton_data ht (cubeBitVec 5 x)
  let a (x : BitVec 5) (i : Fin 4) := evenLabel z i (cubeBitVec 5 x)
  let active (x : BitVec 5) : Bool := decide (a x (label x) ≠ 0)
  have hcenter (x : BitVec 5) (hx : x ∈ S) (i : Fin 4) :
      cScaled z i (cubeBitVec 5 x) = centerProfile (label x) (sign x) i :=
    (hdata x ((hS x).mp hx)).1 i
  have hchosen (x : BitVec 5) (hx : x ∈ S) (e : Fin 6) :
      occupied (midpoint z (cubeBitVec 5 x) e) = countIf (incident (label x) e) := by
    rw [midpoint_occupation hP hu hz hrow, hcenter x hx, hcenter x hx]
    simp only [center_profile_table.2.1]
  have hlocal₀ (x : BitVec 5) (hx : x ∈ S) :
      (∑ d : Fin 5, ∑ e, occupied (midpoint z (cubeBitVec 5 x) e) *
        occupied (midpoint z (flip (cubeBitVec 5 x) d) e)) =
      if active x then 5 else 9 := by
    rw [sum_comm]
    have hm (e : Fin 6) :
        (∑ d : Fin 5, occupied (midpoint z (cubeBitVec 5 x) e) *
          occupied (midpoint z (flip (cubeBitVec 5 x) d) e)) =
        occupied (midpoint z (cubeBitVec 5 x) e) *
          (3 - (occupied (a x (endpoints e).1) + occupied (a x (endpoints e).2))) := by
      rw [← mul_sum]
      by_cases he : midpoint z (cubeBitVec 5 x) e = 0
      · simp [he, occupied]
      · rw [midpoint_vertical hreg hu hz he (fun v hv =>
          (fiber_and_signedRow_supported hz hrow _ (hP.symm ▸ hv)).1)]
    rw [sum_congr rfl (fun e _ => hm e)]
    simp only [mul_sub, sum_sub_distrib, ← sum_mul]
    change oddCount z (cubeBitVec 5 x) * 3 - _ = _
    rw [(hS x).mp hx]
    rcases (hdata x ((hS x).mp hx)).2 with ha | ⟨k, hk, ha⟩
    · change ∀ j, a x j = 0 at ha
      simp [ha, occupied, active]
    · change ∀ j, a x j = pairedLabels (label x) k (sign x) j at ha
      have hne : a x (label x) ≠ 0 := by
        have hprod := center_profile_table.2.2 (label x) k (sign x) hk
        rw [← ha] at hprod
        intro h
        simp [h] at hprod
      have hax : active x = true := by simpa only [active, decide_eq_true_eq] using hne
      simp only [hax, ite_true, hchosen x hx, ha]
      rw [singleton_horizontal _ _ _ hk]
      decide
  have hoverlap (x : BitVec 5) (hx : x ∈ S) (w : BitVec 5) :
      (∑ e, occupied (midpoint z (cubeBitVec 5 x) e) * occupied (midpoint z (cubeBitVec 5 w) e)) =
        countIf (w ∈ S) + 2 * countIf (w ∈ S ∧ label w = label x) + 2 * countIf (w ∈ B) := by
    simp only [hchosen x hx]
    by_cases hw : w ∈ S
    · have hnot : w ∉ B := disjoint_left.mp hdis hw
      simp only [hchosen w hw, hw, hnot, true_and, countIf, ite_true, ite_false, mul_zero, add_zero]
      exact singleton_overlap _ _
    · by_cases hwB : w ∈ B
      · have ho := (hB w).mp hwB
        have hvals : ∀ i, cScaled z i (cubeBitVec 5 w) = 2 ∨
            cScaled z i (cubeBitVec 5 w) = -2 := by
          rcases ht (cubeBitVec 5 w) with ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, hc, _⟩
          · omega
          · omega
          · exact hc
        let side (i : Fin 4) := decide (cScaled z i (cubeBitVec 5 w) = 2)
        have hocc (e : Fin 6) : occupied (midpoint z (cubeBitVec 5 w) e) =
            countIf (side (endpoints e).1 ≠ side (endpoints e).2) := by
          rw [midpoint_occupation hP hu hz hrow]
          rcases hvals (endpoints e).1 with h₁ | h₁ <;>
            rcases hvals (endpoints e).2 with h₂ | h₂ <;> norm_num [side, h₁, h₂, countIf]
        change (∑ e, occupied (midpoint z (cubeBitVec 5 w) e)) = 4 at ho
        simp only [hocc] at ho
        simpa [hocc, hw, hwB, countIf] using balanced_overlap (label x) side ho
      · have hvals : ∀ i, cScaled z i (cubeBitVec 5 w) = 0 := by
          rcases ht (cubeBitVec 5 w) with ⟨hc, _, _⟩ | ⟨_, _, h, _⟩ | ⟨h, _⟩
          · exact hc
          · exact (hw ((hS w).mpr h)).elim
          · exact (hwB ((hB w).mpr h)).elim
        simp [midpoint_occupation hP hu hz hrow, hvals, countIf, hw, hwB]
  refine eight_singletons_impossible (label := label) (active := active)
    hSCard hBCard hdis hpar (fun x hx => ?_)
    (fun x hx w hw hadj hax haw heq => ?_) (fun i => ?_)
  · have h := hlocal₀ x hx
    simp only [← suffix_flip, hoverlap x hx, sum_add_distrib, ← mul_sum] at h
    have hmem (w : BitVec 5) : (w ∈ S ∧ label w = label x) ↔
        w ∈ (S.filter fun v => label v = label x) := by simp
    simp only [hmem, ← degree_as_sum] at h
    change (degree S x : ℤ) + 2 * (sameLabelDegree S label x : ℤ) +
      2 * (degree B x : ℤ) = _ at h
    cases hact : active x <;> simp only [hact, Bool.false_eq_true, ite_false, ite_true] at h ⊢ <;>
      exact_mod_cast h
  · obtain ⟨d, rfl⟩ := (adjacent_flip x w).mp hadj
    have hn : a x (label x) ≠ 0 := of_decide_eq_true hax
    have hn' : a (x ^^^ BitVec.twoPow 5 d.val) (label x) ≠ 0 := by
      rw [heq]
      exact of_decide_eq_true haw
    have hproduct : a x (label x) * cScaled z (label x) (cubeBitVec 5 x) = 3 := by
      rcases (hdata x ((hS x).mp hx)).2 with ha | ⟨k, hk, ha⟩
      · exact (hn (ha _)).elim
      · rw [hcenter x hx, show a x (label x) = _ from ha _]
        exact center_profile_table.2.2 _ _ _ hk
    have hd := even_degree hreg hu hz hrow (fun i y => (hrows i y).1)
      (label x) (cubeBitVec 5 x) hn
    change evenVerticalDegree z (label x) (cubeBitVec 5 x) = _ at hd
    rw [show evenLabel z (label x) (cubeBitVec 5 x) = a x (label x) from rfl, hproduct] at hd
    have hle := single_le_sum (f := fun j => occupied (evenLabel z (label x)
      (flip (cubeBitVec 5 x) j))) (fun j _ => by unfold occupied; split <;> omega) (mem_univ d)
    change occupied (evenLabel z (label x) (flip (cubeBitVec 5 x) d)) ≤
      evenVerticalDegree z (label x) (cubeBitVec 5 x) at hle
    rw [← suffix_flip, hd] at hle
    change occupied (a (x ^^^ BitVec.twoPow 5 d.val) (label x)) ≤ _ at hle
    simp [occupied, hn'] at hle
  · have hc (x : BitVec 5) : (|cScaled z i (cubeBitVec 5 x)| = 3) ↔
        x ∈ S ∧ label x = i := by
      by_cases hx : x ∈ S
      · simp [hx, hcenter x hx, center_profile_table.1, eq_comm]
      · have hne : oddCount z (cubeBitVec 5 x) ≠ 3 := fun h => hx ((hS x).mpr h)
        rcases ht (cubeBitVec 5 x) with ⟨hc, _, _⟩ | ⟨_, _, h, _⟩ | ⟨_, hc, _⟩
        · have hci : cScaled z i (cubeBitVec 5 x) = 0 := hc i
          norm_num [hci, hx]
        · exact (hne h).elim
        · rcases hc i with hi | hi <;> norm_num [hi, hx]
    have hsCard : singletonCenters z i = ((S.filter fun x => label x = i).card : ℤ) := by
      rw [singletonCenters, ← Fintype.sum_equiv (cubeBitVec 5) _ _ (fun _ => rfl)]
      have hfilter : (univ.filter fun x => x ∈ S ∧ label x = i) =
          S.filter (fun x => label x = i) := by ext x; simp
      have hsum := sum_congr (s₁ := (univ : Finset (BitVec 5))) rfl (fun x _ => show
          countIf (|cScaled z i (cubeBitVec 5 x)| = 3) =
            countIf (x ∈ S ∧ label x = i) from by
          by_cases h : x ∈ S ∧ label x = i <;> simp [hc, h, countIf])
      simpa only [countIf, sum_boole, hfilter] using hsum
    have hmCard : activeCenters z i =
        ((S.filter fun x => label x = i ∧ active x = true).card : ℤ) := by
      rw [activeCenters, ← Fintype.sum_equiv (cubeBitVec 5) _ _ (fun _ => rfl)]
      have hterm (x : BitVec 5) :
          occupied (a x i) * countIf (|cScaled z i (cubeBitVec 5 x)| = 3) =
            countIf (x ∈ S ∧ label x = i ∧ active x = true) := by
        by_cases he : label x = i
        · by_cases hx : x ∈ S <;> by_cases hn : a x i = 0 <;>
            simp [hc, countIf, occupied, active, he, hx, hn]
        · simp [hc, countIf, he]
      change (∑ x, occupied (a x i) * countIf (|cScaled z i (cubeBitVec 5 x)| = 3)) = _
      have hfilter : (univ.filter fun x => x ∈ S ∧ label x = i ∧ active x = true) =
          S.filter (fun x => label x = i ∧ active x = true) := by ext x; simp
      have hsum := sum_congr (s₁ := (univ : Finset (BitVec 5))) rfl (fun x _ => hterm x)
      simpa only [countIf, sum_boole, hfilter] using hsum
    have h := label_moment_bound hP hu hz hrow hrows ht hodd hzero hs hhalves i
    rw [hsCard, hmCard] at h
    exact_mod_cast h

#check eight_singletons_impossible_of_half_twenty_eight
#print axioms eight_singletons_impossible_of_half_twenty_eight

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4EightSingletons
