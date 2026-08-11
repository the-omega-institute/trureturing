/- GID: D5/S1/Words/ReturnWords/GoldenReturnItinerary
   generality: I
   mirror-B: none(waiver:formal-kernel-return-itinerary-rigidity)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive-length golden return words are rigid at a fixed length. -/

import D5.S1.Words.ReturnWords.GoldenArcFirstReturn

namespace D5.S1.Words

open Set
open GoldenArcFirstReturnInternal

private theorem adjacent_golden_occurrences_iff {n : Nat} {w : List Bool} {i j : Nat} :
    AdjacentGoldenOccurrences n w i j ↔
      i < j ∧ goldenFactor n i = w ∧ goldenFactor n j = w ∧
        (Finset.Ioo i j).filter (fun k => goldenFactor n k = w) = ∅ := by
  change decide (i < j ∧ goldenFactor n i = w ∧ goldenFactor n j = w ∧
    (Finset.Ioo i j).filter (fun k => goldenFactor n k = w) = ∅) = true ↔ _
  simp

private theorem golden_cylinder_rank_eq_endpoint_count (n i : Nat) :
    goldenCylinderRank n i =
      ((goldenCylinderEndpointSet n).filter fun x => x ≤ goldenPhase i).card := by
  rfl

private theorem golden_endpoint_fract_ne_zero (m : Nat) :
    Int.fract (((m + 1 : Nat) : Real) * goldenMechanicalSlope) ≠ 0 := by
  rw [Int.fract_ne_zero_iff]
  rintro ⟨z, hz⟩
  have hi : Irrational (((m + 1 : Nat) : Real) * goldenMechanicalSlope) :=
    golden_mechanical_slope_irrational.natCast_mul (Nat.succ_ne_zero m)
  exact hi.ne_int z hz.symm

private theorem golden_endpoint_eq_backward_displacement (m : Nat) :
    goldenCylinderEndpoint m = backwardDisplacement goldenMechanicalSlope (m + 1) := by
  calc
    goldenCylinderEndpoint m =
        1 - Int.fract (((m + 1 : Nat) : Real) * goldenMechanicalSlope) := rfl
    _ = Int.fract (-(((m + 1 : Nat) : Real) * goldenMechanicalSlope)) :=
      (Int.fract_neg (golden_endpoint_fract_ne_zero m)).symm
    _ = backwardDisplacement goldenMechanicalSlope (m + 1) := by
      rw [backwardDisplacement]
      congr 1
      push_cast
      ring

private theorem golden_phase_add (i d : Nat) :
    goldenPhase (i + d) =
      Int.fract (goldenPhase i + (d : Real) * goldenMechanicalSlope) := by
  rw [goldenPhase, goldenPhase]
  have harg : (((i + d + 1 : Nat) : Real) * goldenMechanicalSlope) =
      (((i + 1 : Nat) : Real) * goldenMechanicalSlope) +
        (d : Real) * goldenMechanicalSlope := by
    push_cast
    ring
  rw [harg]
  conv_lhs =>
    enter [1, 1]
    rw [← Int.floor_add_fract (((i + 1 : Nat) : Real) * goldenMechanicalSlope)]
  rw [add_assoc, Int.fract_intCast_add]

private theorem golden_phase_ne_endpoint (i m : Nat) :
    goldenPhase i ≠ goldenCylinderEndpoint m := by
  rw [goldenPhase, golden_endpoint_eq_backward_displacement, backwardDisplacement]
  intro h
  obtain ⟨z, hz⟩ := Int.fract_eq_fract.mp h
  have hi : Irrational ((((i + 1) + (m + 1) : Nat) : Real) * goldenMechanicalSlope) :=
    golden_mechanical_slope_irrational.natCast_mul (by omega)
  apply hi.ne_int z
  push_cast at hz ⊢
  rw [← hz]
  ring

private theorem rotation_cut_orbit_index (alpha : Real) (N : Nat)
    [Fact (Irrational alpha)] [NeZero N] {j : Fin (N + 1)} (hj : j < Fin.last N) :
    ∃ u < N, rotationCut alpha N j = backwardDisplacement alpha u := by
  have hjlt : rotationCut alpha N j < 1 := by
    calc
      rotationCut alpha N j < rotationCut alpha N (Fin.last N) :=
        (rotationCut alpha N).strictMono hj
      _ = 1 := rotation_cut_last alpha N
  have hjmem : rotationCut alpha N j ∈ rotationCutSet alpha N := by
    exact Finset.orderEmbOfFin_mem _ _ _
  rw [rotationCutSet, Finset.mem_insert] at hjmem
  rcases hjmem with hone | horbit
  · rw [hone] at hjlt
    exact (lt_irrefl (1 : Real) hjlt).elim
  · rw [D5.S1.Recurrence.RotationOrbitGapsPartition.rotationOrbit,
      Finset.mem_image] at horbit
    obtain ⟨u, hu, heq⟩ := horbit
    exact ⟨u, Finset.mem_range.mp hu, by simpa [backwardDisplacement] using heq.symm⟩

private theorem fract_translate_between_backward_cuts (alpha x c t : Real) (k u : Nat)
    (hku : u ≤ k) (hc : c = backwardDisplacement alpha k)
    (ht : t = backwardDisplacement alpha u)
    (hlower : 0 ≤ t + (x - c)) (hupper : t + (x - c) < 1) :
    Int.fract (x + ((k - u : Nat) : Real) * alpha) = t + (x - c) := by
  rw [Int.fract_eq_iff]
  refine ⟨hlower, hupper, ?_⟩
  let z : Int := ⌊(u : Real) * (-alpha)⌋ - ⌊(k : Real) * (-alpha)⌋
  refine ⟨z, ?_⟩
  rw [hc, ht, backwardDisplacement, backwardDisplacement]
  dsimp [z]
  rw [Int.cast_sub, ← Int.self_sub_fract ((u : Real) * (-alpha)),
    ← Int.self_sub_fract ((k : Real) * (-alpha))]
  rw [Nat.cast_sub hku]
  ring

private theorem golden_cylinder_rank_lt_succ (n i : Nat) :
    goldenCylinderRank n i < n + 1 := by
  rw [golden_cylinder_rank_eq_endpoint_count]
  apply Nat.lt_succ_of_le
  calc
    ((goldenCylinderEndpointSet n).filter fun x => x ≤ goldenPhase i).card ≤
        (goldenCylinderEndpointSet n).card := Finset.card_filter_le _ _
    _ ≤ (Finset.range n).card := Finset.card_image_le
    _ = n := Finset.card_range n

private theorem selected_endpoints_eq_of_rank_eq {n i j : Nat}
    (h : goldenCylinderRank n i = goldenCylinderRank n j) :
    (goldenCylinderEndpointSet n).filter (fun x => x ≤ goldenPhase i) =
      (goldenCylinderEndpointSet n).filter (fun x => x ≤ goldenPhase j) := by
  rcases le_total (goldenPhase i) (goldenPhase j) with hij | hji
  · apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hx.2.trans hij⟩
    · simpa [golden_cylinder_rank_eq_endpoint_count] using h.ge
  · symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hx.2.trans hji⟩
    · simpa [golden_cylinder_rank_eq_endpoint_count] using h.le

private theorem exists_endpoint_strictly_between_of_rank_ne {d i j : Nat}
    (hphase : goldenPhase i < goldenPhase j)
    (hrank : goldenCylinderRank d i ≠ goldenCylinderRank d j) :
    ∃ m < d, goldenPhase i < goldenCylinderEndpoint m ∧
      goldenCylinderEndpoint m < goldenPhase j := by
  let si := (goldenCylinderEndpointSet d).filter (fun x => x ≤ goldenPhase i)
  let sj := (goldenCylinderEndpointSet d).filter (fun x => x ≤ goldenPhase j)
  have hsubset : si ⊆ sj := by
    intro x hx
    simp only [si, sj, Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.trans hphase.le⟩
  have hsets : si ≠ sj := by
    intro hsets
    apply hrank
    rw [golden_cylinder_rank_eq_endpoint_count,
      golden_cylinder_rank_eq_endpoint_count]
    exact congrArg Finset.card hsets
  have hnotSubset : ¬(↑sj : Set Real) ⊆ (↑si : Set Real) := by
    intro hreverse
    apply hsets
    apply Finset.Subset.antisymm hsubset
    intro x hx
    exact hreverse hx
  obtain ⟨c, hcj, hci⟩ := Set.not_subset.mp hnotSubset
  have hcj' : c ∈ goldenCylinderEndpointSet d ∧ c ≤ goldenPhase j := by
    simpa [sj] using hcj
  have hci' : ¬(c ∈ goldenCylinderEndpointSet d ∧ c ≤ goldenPhase i) := by
    simpa [si] using hci
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hcj'.1
  refine ⟨m, Finset.mem_range.mp hm, ?_, ?_⟩
  · exact lt_of_not_ge fun hle => hci' ⟨Finset.mem_image.mpr ⟨m, hm, rfl⟩, hle⟩
  · exact lt_of_le_of_ne hcj'.2 (golden_phase_ne_endpoint j m).symm

private theorem golden_phase_translate_between_cuts {i k u : Nat} {c t : Real}
    (hku : u ≤ k) (hc : c = backwardDisplacement goldenMechanicalSlope k)
    (ht : t = backwardDisplacement goldenMechanicalSlope u)
    (hlower : 0 ≤ t + (goldenPhase i - c))
    (hupper : t + (goldenPhase i - c) < 1) :
    goldenPhase (i + (k - u)) = t + (goldenPhase i - c) := by
  rw [golden_phase_add]
  exact fract_translate_between_backward_cuts goldenMechanicalSlope (goldenPhase i) c t k u
    hku hc ht hlower hupper

private theorem golden_cylinder_rank_eq_of_common_avoidance_of_phase_lt
    {n d i j : Nat} (hn : 0 < n)
    (hstart : goldenCylinderRank n i = goldenCylinderRank n j)
    (hifirst : ∀ e, 0 < e → e < d →
      goldenCylinderRank n (i + e) ≠ goldenCylinderRank n i)
    (hjfirst : ∀ e, 0 < e → e < d →
      goldenCylinderRank n (j + e) ≠ goldenCylinderRank n j)
    (hphase : goldenPhase i < goldenPhase j) :
    goldenCylinderRank d i = goldenCylinderRank d j := by
  by_contra hrank
  obtain ⟨m, hm, hleftOfCut, hcutRight⟩ :=
    exists_endpoint_strictly_between_of_rank_ne hphase hrank
  let c := goldenCylinderEndpoint m
  change goldenPhase i < c at hleftOfCut
  change c < goldenPhase j at hcutRight
  have hmn : n ≤ m := by
    by_contra hnot
    have hmold : m < n := Nat.lt_of_not_ge hnot
    have hselected := selected_endpoints_eq_of_rank_eq hstart
    have hmemj : c ∈
        (goldenCylinderEndpointSet n).filter (fun x => x ≤ goldenPhase j) := by
      refine Finset.mem_filter.mpr ⟨?_, hcutRight.le⟩
      exact Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hmold, rfl⟩
    rw [← hselected] at hmemj
    exact (not_le_of_gt hleftOfCut) (Finset.mem_filter.mp hmemj).2
  let r : Fin (n + 1) := ⟨goldenCylinderRank n i, golden_cylinder_rank_lt_succ n i⟩
  have hiArc : goldenPhase i ∈
      rotationGapArc goldenMechanicalSlope (n + 1) r := by
    apply (golden_cylinder_rank_iff_mem_rotation_gap_arc n i r).mp
    rfl
  have hjArc : goldenPhase j ∈
      rotationGapArc goldenMechanicalSlope (n + 1) r := by
    apply (golden_cylinder_rank_iff_mem_rotation_gap_arc n j r).mp
    exact hstart.symm
  let a := rotationCut goldenMechanicalSlope (n + 1) r.castSucc
  let b := rotationCut goldenMechanicalSlope (n + 1) r.succ
  change a ≤ goldenPhase i ∧ goldenPhase i < b at hiArc
  change a ≤ goldenPhase j ∧ goldenPhase j < b at hjArc
  have ha0 : 0 ≤ a := by
    calc
      0 = rotationCut goldenMechanicalSlope (n + 1) 0 :=
        (rotation_cut_zero goldenMechanicalSlope (n + 1)).symm
      _ ≤ a := (rotationCut goldenMechanicalSlope (n + 1)).monotone (by simp)
  have hb1 : b ≤ 1 := by
    calc
      b ≤ rotationCut goldenMechanicalSlope (n + 1) (Fin.last (n + 1)) :=
        (rotationCut goldenMechanicalSlope (n + 1)).monotone (Fin.le_last _)
      _ = 1 := rotation_cut_last goldenMechanicalSlope (n + 1)
  have hleftIndex : r.castSucc < Fin.last (n + 1) := by
    apply Fin.mk_lt_mk.mpr
    exact r.isLt
  obtain ⟨u, hu, hleft⟩ :=
    rotation_cut_orbit_index goldenMechanicalSlope (n + 1) hleftIndex
  have ha : a = backwardDisplacement goldenMechanicalSlope u := by
    exact hleft
  let k := m + 1
  have hc : c = backwardDisplacement goldenMechanicalSlope k := by
    dsimp [c, k]
    exact golden_endpoint_eq_backward_displacement m
  have hk_le_d : k ≤ d := by dsimp [k]; omega
  have hN_le_k : n + 1 ≤ k := by dsimp [k]; omega
  have hu_lt_k : u < k := lt_of_lt_of_le hu hN_le_k
  let e := k - u
  have hepos : 0 < e := by dsimp [e]; omega
  have hele : e ≤ d := by dsimp [e]; omega
  have htargetRight : a + (goldenPhase j - c) < b := by
    linarith [hiArc.1, hleftOfCut, hjArc.2]
  have hyTranslate :
      goldenPhase (j + e) = a + (goldenPhase j - c) := by
    apply golden_phase_translate_between_cuts hu_lt_k.le hc ha
    · linarith [ha0, hcutRight]
    · linarith [htargetRight, hb1]
  have hyEarlyArc : goldenPhase (j + e) ∈
      rotationGapArc goldenMechanicalSlope (n + 1) r := by
    change a ≤ goldenPhase (j + e) ∧ goldenPhase (j + e) < b
    rw [hyTranslate]
    exact ⟨by linarith [hcutRight], htargetRight⟩
  have hyEarlyRank : goldenCylinderRank n (j + e) = goldenCylinderRank n j := by
    calc
      goldenCylinderRank n (j + e) = r.val :=
        (golden_cylinder_rank_iff_mem_rotation_gap_arc n (j + e) r).mpr hyEarlyArc
      _ = goldenCylinderRank n i := rfl
      _ = goldenCylinderRank n j := hstart
  by_cases he_lt : e < d
  · exact (hjfirst e hepos he_lt) hyEarlyRank
  have he_eq : e = d := by omega
  have hu0 : u = 0 := by dsimp [e] at he_eq; omega
  have hk_eq : k = d := by dsimp [e] at he_eq; omega
  have ha_eq_zero : a = 0 := by simp [ha, hu0, backwardDisplacement]
  have hrzero : r.castSucc = (0 : Fin ((n + 1) + 1)) := by
    apply (rotationCut goldenMechanicalSlope (n + 1)).injective
    change a = rotationCut goldenMechanicalSlope (n + 1) 0
    rw [rotation_cut_zero]
    exact ha_eq_zero
  have hrval : r.val = 0 := by
    have := congrArg Fin.val hrzero
    simpa using this
  have hrightIndex : r.succ < Fin.last (n + 1) := by
    apply Fin.mk_lt_mk.mpr
    change r.val + 1 < n + 1
    rw [hrval]
    omega
  obtain ⟨v, hv, hright⟩ :=
    rotation_cut_orbit_index goldenMechanicalSlope (n + 1) hrightIndex
  have hb : b = backwardDisplacement goldenMechanicalSlope v := by
    exact hright
  have hvpos : 0 < v := by
    by_contra hnot
    have hv0 : v = 0 := Nat.eq_zero_of_not_pos hnot
    have hab : a < b :=
      (rotationCut goldenMechanicalSlope (n + 1)).strictMono r.castSucc_lt_succ
    rw [ha, hb, hu0, hv0] at hab
    exact (lt_irrefl _ hab)
  have hv_lt_k : v < k := lt_of_lt_of_le hv hN_le_k
  let e' := k - v
  have he'pos : 0 < e' := by dsimp [e']; omega
  have he'lt : e' < d := by dsimp [e']; omega
  have htargetLeft : a < b + (goldenPhase i - c) := by
    linarith [hiArc.1, hleftOfCut, hcutRight, hjArc.2]
  have hxTranslate :
      goldenPhase (i + e') = b + (goldenPhase i - c) := by
    apply golden_phase_translate_between_cuts hv_lt_k.le hc hb
    · linarith [ha0, htargetLeft]
    · linarith [hleftOfCut, hb1]
  have hxEarlyArc : goldenPhase (i + e') ∈
      rotationGapArc goldenMechanicalSlope (n + 1) r := by
    change a ≤ goldenPhase (i + e') ∧ goldenPhase (i + e') < b
    rw [hxTranslate]
    exact ⟨htargetLeft.le, by linarith [hleftOfCut]⟩
  have hxEarlyRank : goldenCylinderRank n (i + e') = goldenCylinderRank n i := by
    calc
      goldenCylinderRank n (i + e') = r.val :=
        (golden_cylinder_rank_iff_mem_rotation_gap_arc n (i + e') r).mpr hxEarlyArc
      _ = goldenCylinderRank n i := rfl
  exact (hifirst e' he'pos he'lt) hxEarlyRank

private theorem golden_cylinder_rank_eq_of_phase_eq (n : Nat) {i j : Nat}
    (hphase : goldenPhase i = goldenPhase j) :
    goldenCylinderRank n i = goldenCylinderRank n j := by
  rw [golden_cylinder_rank_eq_endpoint_count,
    golden_cylinder_rank_eq_endpoint_count, hphase]

private theorem rank_avoids_between_adjacent {n : Nat} {w : List Bool} {i j e : Nat}
    (hadj : AdjacentGoldenOccurrences n w i j) (hepos : 0 < e) (helt : e < j - i) :
    goldenCylinderRank n (i + e) ≠ goldenCylinderRank n i := by
  have hs := adjacent_golden_occurrences_iff.mp hadj
  intro hrank
  have hfactor : goldenFactor n (i + e) = w :=
    ((golden_factor_eq_iff_cylinder_rank_eq n (i + e) i).mpr hrank).trans hs.2.1
  have hmem : i + e ∈ (Finset.Ioo i j).filter (fun k => goldenFactor n k = w) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨by omega, by omega⟩, hfactor⟩
  rw [hs.2.2.2] at hmem
  simp at hmem

/-- Positive-length golden return words of the same length are equal. -/
theorem golden_return_word_eq_of_length_eq {n : Nat} (hn : 0 < n)
    {w r s : List Bool} (hr : r ∈ goldenReturnWords n w)
    (hs : s ∈ goldenReturnWords n w) (h : r.length = s.length) : r = s := by
  obtain ⟨i, j, hadj, rfl⟩ := hr
  obtain ⟨i', j', hadj', rfl⟩ := hs
  have hgap : j - i = j' - i' := by simpa [goldenFactor] using h
  have hstart : goldenCylinderRank n i = goldenCylinderRank n i' := by
    apply (golden_factor_eq_iff_cylinder_rank_eq n i i').mp
    have hi := (adjacent_golden_occurrences_iff.mp hadj).2.1
    have hi' := (adjacent_golden_occurrences_iff.mp hadj').2.1
    exact hi.trans hi'.symm
  have hfirst : ∀ e, 0 < e → e < j - i →
      goldenCylinderRank n (i + e) ≠ goldenCylinderRank n i := by
    intro e hepos helt
    exact rank_avoids_between_adjacent hadj hepos helt
  have hfirst' : ∀ e, 0 < e → e < j - i →
      goldenCylinderRank n (i' + e) ≠ goldenCylinderRank n i' := by
    intro e hepos helt
    exact rank_avoids_between_adjacent hadj' hepos (by omega)
  have hrank : goldenCylinderRank (j - i) i = goldenCylinderRank (j - i) i' := by
    rcases lt_trichotomy (goldenPhase i) (goldenPhase i') with hlt | heq | hgt
    · exact golden_cylinder_rank_eq_of_common_avoidance_of_phase_lt hn hstart hfirst
        hfirst' hlt
    · exact golden_cylinder_rank_eq_of_phase_eq (j - i) heq
    · exact (golden_cylinder_rank_eq_of_common_avoidance_of_phase_lt hn hstart.symm
        hfirst' hfirst hgt).symm
  rw [← hgap]
  exact (golden_factor_eq_iff_cylinder_rank_eq (j - i) i i').mpr hrank

/-- Length is injective on return words to a positive-length golden factor. -/
theorem golden_return_words_length_injOn {n : Nat} (hn : 0 < n) (w : List Bool) :
    Set.InjOn List.length (goldenReturnWords n w) := by
  intro r hr s hs hlength
  exact golden_return_word_eq_of_length_eq hn hr hs hlength


#print axioms golden_return_word_eq_of_length_eq
#print axioms golden_return_words_length_injOn

end D5.S1.Words

