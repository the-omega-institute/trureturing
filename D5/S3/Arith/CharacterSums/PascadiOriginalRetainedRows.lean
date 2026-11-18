/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalRetainedRows
   generality: G
   mirror-B: none(waiver:actual-retained-row-realization)
   mirror-E: none(waiver:open-original-total-count)
   anchors: []
   utility: none
   digest: Actual original row fibers are bijective to their integer-coordinate endpoint records. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalDyadicRecords
import D5.S3.Arith.CharacterSums.PascadiOriginalChartPieces

/-! The parameter set is exactly the middle-column image of the original
integer rows. Coordinates are chosen only in the actual occupied lattices;
neither a counting bound nor a row-to-record injection is supplied. -/

open scoped BigOperators

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

private def latticeCoordinates {c : ℕ} {t w : ℤ}
    (B : MiddleBasis c t w) (z : Coordinate) : Coordinate :=
  Classical.epsilon fun u => physical B.R B.V u = z

private theorem physical_latticeCoordinates {c : ℕ} {t w : ℤ}
    (B : MiddleBasis c t w) (z : Coordinate) (hz : z ∈ middleLattice c t w) :
    physical B.R B.V (latticeCoordinates B z) = z := by
  unfold latticeCoordinates
  exact Classical.epsilon_spec (p := fun u : Coordinate => physical B.R B.V u = z) (by
    obtain ⟨i, j, hij⟩ := B.decompose z hz
    exact ⟨(i, j), hij⟩)

private theorem word_endpoints_mem {c : ℕ} [NeZero c]
    (a₁ a₂ : ZMod c) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (h : ReturnRows)
    (hword : sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1)
      (h.2 0) (h.1 2) (h.2 1) = scalarReturn (-1)) :
    (originalEndpoints h).1 ∈ middleLattice c (h.2 2) (h.1 2) ∧
      (originalEndpoints h).2 ∈ middleLattice c (h.2 2) (h.1 2) := by
  have heq := (sixReturnWord_minus_iff _ _ _ _ _ _ _ _ ha₁ ha₂).mp hword
  constructor
  · change (c : ℤ) ∣ h.1 2 * h.2 0 - h.2 2 * h.1 0
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa only [Int.cast_sub, Int.cast_mul] using sub_eq_zero.mpr heq.2.2.1
  · change (c : ℤ) ∣ h.1 2 * h.2 1 - h.2 2 * h.1 1
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa only [Int.cast_sub, Int.cast_mul] using sub_eq_zero.mpr heq.2.2.2

private theorem originalRows_recover (R V q : Coordinate)
    (e : Endpoint) (h : ReturnRows)
    (hq : physical R V q = -originalMiddle h)
    (h₁ : physical R V e.1 = (originalEndpoints h).1)
    (h₂ : physical R V e.2 = (originalEndpoints h).2) :
    originalRows R V q e = h := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [originalRows, h₁, h₂, hq, originalEndpoints, originalMiddle]

private theorem originalRows_injective {c : ℕ} {t w : ℤ}
    (B : MiddleBasis c t w) (hc : 0 < c) (q : Coordinate) :
    Function.Injective (originalRows B.R B.V q) := by
  intro e e' he
  apply Prod.ext
  · apply B.coordinates_unique hc
    apply Prod.ext
    · simpa [originalRows] using
        congrArg (fun h : ReturnRows => h.1 0) he
    · simpa [originalRows] using
        congrArg (fun h : ReturnRows => h.2 0) he
  · apply B.coordinates_unique hc
    apply Prod.ext
    · simpa [originalRows] using
        congrArg (fun h : ReturnRows => h.1 1) he
    · simpa [originalRows] using
        congrArg (fun h : ReturnRows => h.2 1) he

/-- Realize every actual retained row in its occupied reduced middle chart.
The endpoint sets are images of the original integer fibers. Decoding is
injective, its image is exactly the original fiber, and the total cardinality
is therefore unchanged. A basis is required only for an occupied middle pair. -/
theorem actual_retained_rows_realization (c : ℕ) [NeZero c]
    (X Y : ℝ) (a₁ a₂ : ZMod c) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (T : Finset ReturnRows)
    (B : ∀ wt : Coordinate, wt ∈ T.image originalMiddle →
      ReducedMiddleBasis c wt.2 wt.1 X Y)
    (hbox : ∀ h ∈ T, ∀ i, |(h.1 i : ℝ)| ≤ X ∧ |(h.2 i : ℝ)| ≤ Y)
    (hword : ∀ h ∈ T, sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1)
      (h.2 0) (h.1 2) (h.2 1) = scalarReturn (-1))
    (hunit : ∀ h ∈ T, IsUnit (h.1 2 : ZMod c) ∧ IsUnit (h.2 2 : ZMod c))
    (hendunit : ∀ h ∈ T, IsUnit (h.1 0 : ZMod c) ∧ IsUnit (h.1 1 : ZMod c)) :
    ∃ (q : Coordinate → Coordinate) (RV : Coordinate → Coordinate × Coordinate)
      (E : Coordinate → Finset Endpoint),
      (∀ wt (hw : wt ∈ T.image originalMiddle),
        RV wt = ((B wt hw).R, (B wt hw).V)) ∧
      (∀ wt ∈ T.image originalMiddle, wt ∈ literalBox X Y) ∧
      (∀ wt ∈ T.image originalMiddle, physical (RV wt).1 (RV wt).2 (q wt) = -wt) ∧
      (∀ wt ∈ T.image originalMiddle,
        IsUnit (wt.2 : ZMod c) ∧ IsUnit (wt.1 : ZMod c)) ∧
      (∀ wt ∈ T.image originalMiddle,
        (E wt).image (originalRows (RV wt).1 (RV wt).2 (q wt)) =
          T.filter fun h => originalMiddle h = wt) ∧
      (∀ wt ∈ T.image originalMiddle,
        Function.Injective (originalRows (RV wt).1 (RV wt).2 (q wt))) ∧
      (∀ wt ∈ T.image originalMiddle, ∀ e ∈ E wt,
        WordSolution c a₁ a₂ (RV wt).1 (RV wt).2 (q wt) e) ∧
      (∀ wt ∈ T.image originalMiddle, ∀ e ∈ E wt,
        IsUnit ((physical (RV wt).1 (RV wt).2 e.1).1 : ZMod c) ∧
        IsUnit ((physical (RV wt).1 (RV wt).2 e.2).1 : ZMod c)) ∧
      (∀ wt ∈ T.image originalMiddle, ∀ e ∈ E wt,
        physical (RV wt).1 (RV wt).2 e.1 ∈ literalBox X Y ∧
        physical (RV wt).1 (RV wt).2 e.2 ∈ literalBox X Y) ∧
      T.card = ∑ wt ∈ T.image originalMiddle, (E wt).card := by
  classical
  let s := T.image originalMiddle
  let RV : Coordinate → Coordinate × Coordinate := fun wt =>
    if hw : wt ∈ s then ((B wt hw).R, (B wt hw).V) else (0, 0)
  let q : Coordinate → Coordinate := fun wt =>
    if hw : wt ∈ s then Classical.choose (B wt hw).toMiddleBasis.anchor_coordinates else 0
  let code : Coordinate → ReturnRows → Endpoint := fun wt h =>
    if hw : wt ∈ s then
      (latticeCoordinates (B wt hw).toMiddleBasis (originalEndpoints h).1,
        latticeCoordinates (B wt hw).toMiddleBasis (originalEndpoints h).2)
    else 0
  let E : Coordinate → Finset Endpoint := fun wt =>
    (T.filter fun h => originalMiddle h = wt).image (code wt)
  have hRV (wt : Coordinate) (hw : wt ∈ s) :
      RV wt = ((B wt hw).R, (B wt hw).V) := by simp only [RV, dif_pos hw]
  have hq (wt : Coordinate) (hw : wt ∈ s) :
      physical (RV wt).1 (RV wt).2 (q wt) = -wt := by
    calc
      physical (RV wt).1 (RV wt).2 (q wt) = (-wt.1, -wt.2) := by
        simpa only [RV, q, dif_pos hw] using
          Classical.choose_spec (B wt hw).toMiddleBasis.anchor_coordinates
      _ = -wt := Prod.ext rfl rfl
  have hcode (wt : Coordinate) (hw : wt ∈ s) (h : ReturnRows)
      (hh : h ∈ T.filter fun h => originalMiddle h = wt) :
      physical (RV wt).1 (RV wt).2 (code wt h).1 = (originalEndpoints h).1 ∧
      physical (RV wt).1 (RV wt).2 (code wt h).2 = (originalEndpoints h).2 ∧
      originalRows (RV wt).1 (RV wt).2 (q wt) (code wt h) = h := by
    obtain ⟨hT, hm⟩ := Finset.mem_filter.mp hh
    have hm₁ : h.1 2 = wt.1 := congrArg Prod.fst hm
    have hm₂ : h.2 2 = wt.2 := congrArg Prod.snd hm
    have hlats := word_endpoints_mem a₁ a₂ ha₁ ha₂ h (hword h hT)
    have hl₁ : (originalEndpoints h).1 ∈ middleLattice c wt.2 wt.1 := by
      simpa only [hm₁, hm₂] using hlats.1
    have hl₂ : (originalEndpoints h).2 ∈ middleLattice c wt.2 wt.1 := by
      simpa only [hm₁, hm₂] using hlats.2
    have he₁ : physical (RV wt).1 (RV wt).2 (code wt h).1 =
        (originalEndpoints h).1 := by
      simpa only [RV, code, dif_pos hw] using
        physical_latticeCoordinates (B wt hw).toMiddleBasis _ hl₁
    have he₂ : physical (RV wt).1 (RV wt).2 (code wt h).2 =
        (originalEndpoints h).2 := by
      simpa only [RV, code, dif_pos hw] using
        physical_latticeCoordinates (B wt hw).toMiddleBasis _ hl₂
    refine ⟨he₁, he₂, originalRows_recover _ _ _ _ _ ?_ he₁ he₂⟩
    rw [hq wt hw, hm]
  have hdecode (wt : Coordinate) (hw : wt ∈ s) :
      Function.Injective (originalRows (RV wt).1 (RV wt).2 (q wt)) := by
    simpa only [RV, dif_pos hw] using
      originalRows_injective (B wt hw).toMiddleBasis (NeZero.pos c) (q wt)
  have himage (wt : Coordinate) (hw : wt ∈ s) :
      (E wt).image (originalRows (RV wt).1 (RV wt).2 (q wt)) =
        T.filter fun h => originalMiddle h = wt := by
    apply Finset.ext
    intro h
    constructor
    · intro hh
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hh
      obtain ⟨h', hh', rfl⟩ := Finset.mem_image.mp he
      simpa only [(hcode wt hw h' hh').2.2] using hh'
    · intro hh
      exact Finset.mem_image.mpr ⟨code wt h,
        Finset.mem_image.mpr ⟨h, hh, rfl⟩, (hcode wt hw h hh).2.2⟩
  have hfiber (wt : Coordinate) (hw : wt ∈ s) :
      (T.filter fun h => originalMiddle h = wt).card = (E wt).card := by
    rw [← himage wt hw, Finset.card_image_of_injective _ (hdecode wt hw)]
  have hcount : T.card = ∑ wt ∈ s, (E wt).card := by
    rw [Finset.card_eq_sum_card_image originalMiddle T]
    exact Finset.sum_congr rfl hfiber
  refine ⟨q, RV, E, hRV, ?_, hq, ?_, himage, hdecode, ?_, ?_, ?_, hcount⟩
  · intro wt hw
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hw
    exact hbox h hh 2
  · intro wt hw
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨(hunit h hh).2, (hunit h hh).1⟩
  · intro wt hw e he
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp he
    simpa only [WordSolution, (hcode wt hw h hh).2.2] using
      hword h (Finset.mem_filter.mp hh).1
  · intro wt hw e he
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp he
    rw [(hcode wt hw h hh).1, (hcode wt hw h hh).2.1]
    exact hendunit h (Finset.mem_filter.mp hh).1
  · intro wt hw e he
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp he
    rw [(hcode wt hw h hh).1, (hcode wt hw h hh).2.1]
    exact ⟨hbox h (Finset.mem_filter.mp hh).1 0,
      hbox h (Finset.mem_filter.mp hh).1 1⟩

/-- The dyadic retained bound now counts the literal original ReturnRows.
All record incidences and their cardinalities are constructed from those rows;
only the long-chart and unit-shortest-vector restrictions remain explicit. -/
theorem actual_retained_rows_dyadic_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (X Y H : ℝ)
      (a₁ a₂ : ZMod (p^3)) (T : Finset ReturnRows)
      (B : ∀ wt : Coordinate, wt ∈ T.image originalMiddle →
        ReducedMiddleBasis (p^3) wt.2 wt.1 X Y),
      0 < X → X ≤ Y → 3*Y < (p : ℝ)^2 → 0 < H → H^2 = X*Y →
      IsUnit a₁ → IsUnit a₂ →
      (∀ h ∈ T, ∀ i, |(h.1 i : ℝ)| ≤ X ∧ |(h.2 i : ℝ)| ≤ Y) →
      (∀ h ∈ T, sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1)
        (h.2 0) (h.1 2) (h.2 1) = scalarReturn (-1)) →
      (∀ h ∈ T, IsUnit (h.1 2 : ZMod (p^3)) ∧ IsUnit (h.2 2 : ZMod (p^3))) →
      (∀ h ∈ T, IsUnit (h.1 0 : ZMod (p^3)) ∧ IsUnit (h.1 1 : ZMod (p^3))) →
      (∀ wt (hw : wt ∈ T.image originalMiddle),
        (p^3 : ℝ)^2 < (X*Y)*weightedSq X Y (B wt hw).R) →
      (∀ wt (hw : wt ∈ T.image originalMiddle), IsUnit ((B wt hw).R.1 : ZMod (p^3))) →
      ∃ (q : Coordinate → Coordinate) (RV : Coordinate → Coordinate × Coordinate)
        (E : Coordinate → Finset Endpoint),
        (∀ wt (hw : wt ∈ T.image originalMiddle),
          RV wt = ((B wt hw).R, (B wt hw).V)) ∧
        (∀ wt ∈ T.image originalMiddle, physical (RV wt).1 (RV wt).2 (q wt) = -wt) ∧
        (∀ wt ∈ T.image originalMiddle,
          (E wt).image (originalRows (RV wt).1 (RV wt).2 (q wt)) =
            T.filter fun h => originalMiddle h = wt) ∧
        (∀ wt ∈ T.image originalMiddle,
          Function.Injective (originalRows (RV wt).1 (RV wt).2 (q wt))) ∧
        (∀ wt ∈ T.image originalMiddle, ∀ e ∈ E wt,
          WordSolution (p^3) a₁ a₂ (RV wt).1 (RV wt).2 (q wt) e) ∧
        (∀ wt ∈ T.image originalMiddle, ∀ e ∈ E wt,
          IsUnit ((physical (RV wt).1 (RV wt).2 e.1).1 : ZMod (p^3)) ∧
          IsUnit ((physical (RV wt).1 (RV wt).2 e.2).1 : ZMod (p^3))) ∧
        (∀ wt ∈ T.image originalMiddle, ∀ e ∈ E wt,
          physical (RV wt).1 (RV wt).2 e.1 ∈ literalBox X Y ∧
          physical (RV wt).1 (RV wt).2 e.2 ∈ literalBox X Y) ∧
        T.card = (∑ wt ∈ T.image originalMiddle, (E wt).card) ∧
        (T.card : ℝ) ≤
          2*(∑ wt ∈ T.image originalMiddle,
            (actualRecordBadDegree p (q wt) (RV wt).1 (RV wt).2 (E wt) : ℝ)) +
          Real.sqrt (((T.image originalMiddle).card : ℝ)*C*(p : ℝ)^ε*
            (X*Y/(p : ℝ)^3)^5*(1+Real.log (2*p)/Real.log 2)) := by
  classical
  obtain ⟨C, hC, hdyadic⟩ := actual_dyadic_retained_endpoint_count ε hε
  refine ⟨C, hC, ?_⟩
  intro p hp X Y H a₁ a₂ T B hX hXY hsmall hH hHsq ha₁ ha₂
    hbox hword hunit hendunit hlong hr
  letI : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨q, RV, E, hRV, hsbox, hanchor, hsunit, himage, hinj, heword,
      heunit, hebox, hcount⟩ :=
    actual_retained_rows_realization (p^3) X Y a₁ a₂ ha₁ ha₂ T B
      hbox hword hunit hendunit
  refine ⟨q, RV, E, hRV, hanchor, himage, hinj, heword, heunit, hebox, hcount, ?_⟩
  have hred : ∀ wt ∈ T.image originalMiddle,
      ∃ B' : ReducedMiddleBasis (p^3) wt.2 wt.1 X Y,
        B'.R = (RV wt).1 ∧ B'.V = (RV wt).2 := by
    intro wt hw
    refine ⟨B wt hw, ?_, ?_⟩ <;> rw [hRV wt hw]
  have hlong' : ∀ wt ∈ T.image originalMiddle,
      (p^3 : ℝ)^2 < (X*Y)*weightedSq X Y (RV wt).1 := by
    intro wt hw
    rw [hRV wt hw]
    exact hlong wt hw
  have hr' : ∀ wt ∈ T.image originalMiddle,
      IsUnit ((RV wt).1.1 : ZMod (p^3)) := by
    intro wt hw
    rw [hRV wt hw]
    exact hr wt hw
  have hh := hdyadic p hp X Y H a₁ a₂ q RV (T.image originalMiddle) E
    hX hXY hsmall hH hHsq ha₁ ha₂ hsbox hred hanchor hlong' hr'
      hsunit heword heunit hebox
  have hcountR : (T.card : ℝ) =
      ∑ wt ∈ T.image originalMiddle, ((E wt).card : ℝ) := by exact_mod_cast hcount
  rw [hcountR]
  exact hh

end
end D5.S3.Arith.CharacterSums.Original
