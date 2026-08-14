/- GID: D5/S1/Words/Mechanical/MechanicalUniformRecurrence
   generality: G
   mirror-B: D5/B/S1/Words/Mechanical/MechanicalUniformRecurrence
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   digest: Every factor of an irrational lower mechanical word returns with uniformly bounded gaps. -/

import D5.S1.Words.Mechanical.MechanicalFactorComplexity
import Mathlib.Topology.Instances.AddCircle.Real

namespace D5.S1.Words.Mechanical.MechanicalUniformRecurrence

open Set

private noncomputable def mechanicalBreakpoint (alpha : Real) (m : Nat) : Real :=
  1 - Int.fract (((m + 1 : Nat) : Real) * alpha)

private noncomputable def mechanicalBreakpoints (alpha : Real) (n : Nat) : Finset Real :=
  (Finset.range n).image (mechanicalBreakpoint alpha)

private noncomputable def mechanicalPhase (alpha rho : Real) (i : Nat) : Real :=
  Int.fract (rho + (i : Real) * alpha)

private theorem fract_mul_alpha_ne_zero {alpha : Real} (halpha : Irrational alpha) (m : Nat) :
    Int.fract (((m + 1 : Nat) : Real) * alpha) ≠ 0 := by
  rw [Int.fract_ne_zero_iff]
  rintro ⟨z, hz⟩
  have hi : Irrational (((m + 1 : Nat) : Real) * alpha) :=
    halpha.natCast_mul (Nat.succ_ne_zero m)
  exact hi.ne_int z hz.symm

private theorem mechanicalBreakpoint_mem_Ioo {alpha : Real} (halpha : Irrational alpha)
    (m : Nat) : mechanicalBreakpoint alpha m ∈ Ioo (0 : Real) 1 := by
  have hnonneg := Int.fract_nonneg (((m + 1 : Nat) : Real) * alpha)
  have hlt := Int.fract_lt_one (((m + 1 : Nat) : Real) * alpha)
  have hne := fract_mul_alpha_ne_zero halpha m
  have hpos : 0 < Int.fract (((m + 1 : Nat) : Real) * alpha) :=
    lt_of_le_of_ne hnonneg (Ne.symm hne)
  simp only [mechanicalBreakpoint, mem_Ioo]
  constructor <;> linarith

private theorem floor_add_sub_floor (x t : Real) :
    ⌊x + t⌋ - ⌊x⌋ = ⌊Int.fract x + t⌋ := by
  have hx : (⌊x⌋ : Real) + (Int.fract x + t) = x + t := by
    calc
      (⌊x⌋ : Real) + (Int.fract x + t) = ((⌊x⌋ : Real) + Int.fract x) + t := by ring
      _ = x + t := by rw [Int.floor_add_fract]
  rw [← hx, Int.floor_intCast_add]
  omega

private theorem floor_fract_add_indicator (x t : Real) :
    ⌊Int.fract x + t⌋ = ⌊t⌋ + if 1 - Int.fract t ≤ Int.fract x then 1 else 0 := by
  have hdecomp : (⌊t⌋ : Real) + (Int.fract x + Int.fract t) = Int.fract x + t := by
    calc
      (⌊t⌋ : Real) + (Int.fract x + Int.fract t) =
          Int.fract x + ((⌊t⌋ : Real) + Int.fract t) := by ring
      _ = Int.fract x + t := by rw [Int.floor_add_fract]
  rw [← hdecomp, Int.floor_intCast_add]
  congr 1
  by_cases h : 1 - Int.fract t ≤ Int.fract x
  · rw [if_pos h, Int.floor_eq_iff]
    norm_num
    constructor
    · linarith
    · linarith [Int.fract_lt_one x, Int.fract_lt_one t]
  · rw [if_neg h, Int.floor_eq_iff]
    norm_num
    constructor
    · linarith [Int.fract_nonneg x, Int.fract_nonneg t]
    · linarith [Int.fract_lt_one x, Int.fract_nonneg t, lt_of_not_ge h]

private theorem mechanical_window_count_eq_indicator {alpha rho : Real}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) (i m : Nat) :
    (lowerMechanicalWindowTrueCount alpha rho i (m + 1) : Int) =
      ⌊(((m + 1 : Nat) : Real) * alpha)⌋ +
        if mechanicalBreakpoint alpha m ≤ mechanicalPhase alpha rho i then 1 else 0 := by
  rw [lowerMechanicalWindowTrueCount_eq_floor halpha0 halpha1]
  have hend : rho + ((i + (m + 1) : Nat) : Real) * alpha =
      (rho + (i : Real) * alpha) + (((m + 1 : Nat) : Real) * alpha) := by
    push_cast
    ring
  rw [hend, floor_add_sub_floor, floor_fract_add_indicator]
  rfl

private theorem mechanical_window_count_succ {alpha rho : Real} (i m : Nat) :
    lowerMechanicalWindowTrueCount alpha rho i (m + 1) =
      lowerMechanicalWindowTrueCount alpha rho i m +
        if lowerMechanicalWord alpha rho (i + m) = true then 1 else 0 := by
  classical
  unfold lowerMechanicalWindowTrueCount
  rw [Finset.range_add_one, Finset.filter_insert]
  have hm : m ∉ (Finset.range m).filter
      (fun k => lowerMechanicalWord alpha rho (i + k) = true) := by
    simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_irrefl, false_and,
      not_false_eq_true]
  by_cases h : lowerMechanicalWord alpha rho (i + m) = true
  · rw [if_pos h, Finset.card_insert_of_notMem hm, if_pos h]
  · rw [if_neg h, if_neg h, Nat.add_zero]

private theorem factor_eq_of_breakpoint_sides_eq {alpha rho : Real}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) {n i j : Nat}
    (hside : ∀ m < n, mechanicalBreakpoint alpha m ≤ mechanicalPhase alpha rho i ↔
      mechanicalBreakpoint alpha m ≤ mechanicalPhase alpha rho j) :
    lowerMechanicalFactor alpha rho n i = lowerMechanicalFactor alpha rho n j := by
  have hcounts (r : Nat) (hr : r ≤ n) :
      lowerMechanicalWindowTrueCount alpha rho i r =
        lowerMechanicalWindowTrueCount alpha rho j r := by
    rcases r with _ | m
    · simp [lowerMechanicalWindowTrueCount]
    · have hm : m < n := by omega
      rw [← Nat.cast_inj (R := Int), mechanical_window_count_eq_indicator halpha0 halpha1,
        mechanical_window_count_eq_indicator halpha0 halpha1]
      by_cases hi : mechanicalBreakpoint alpha m ≤ mechanicalPhase alpha rho i
      · simp [hi, (hside m hm).mp hi]
      · have hj : ¬mechanicalBreakpoint alpha m ≤ mechanicalPhase alpha rho j :=
          fun hj => hi ((hside m hm).mpr hj)
        rw [if_neg hi, if_neg hj]
  unfold lowerMechanicalFactor
  congr 1
  funext k
  have hbase := hcounts k k.isLt.le
  have hnext := hcounts (k + 1) (Nat.succ_le_of_lt k.isLt)
  rw [mechanical_window_count_succ, mechanical_window_count_succ] at hnext
  have hindicator : (if lowerMechanicalWord alpha rho (i + k) = true then 1 else 0) =
      if lowerMechanicalWord alpha rho (j + k) = true then 1 else 0 := by omega
  by_cases hi : lowerMechanicalWord alpha rho (i + k) = true
  · have hj : lowerMechanicalWord alpha rho (j + k) = true := by
      by_contra hj
      simp only [if_pos hi, if_neg hj] at hindicator
      omega
    exact hi.trans hj.symm
  · have hj : ¬lowerMechanicalWord alpha rho (j + k) = true := by
      intro hj
      simp only [if_neg hi, if_pos hj] at hindicator
      omega
    rw [Bool.eq_false_of_not_eq_true hi, Bool.eq_false_of_not_eq_true hj]

private theorem exists_right_stable_interval {alpha x : Real} (halpha : Irrational alpha)
    (hx1 : x < 1) (n : Nat) :
    ∃ b, x < b ∧ b ≤ 1 ∧ ∀ {y}, y ∈ Ioo x b → ∀ m < n,
      (mechanicalBreakpoint alpha m ≤ x ↔ mechanicalBreakpoint alpha m ≤ y) := by
  classical
  let points := mechanicalBreakpoints alpha n
  let above := points.filter (x < ·)
  by_cases habove : above.Nonempty
  · let c := above.min' habove
    have hcAbove : c ∈ above := above.min'_mem habove
    have hxc : x < c := (Finset.mem_filter.mp hcAbove).2
    have hcPoints : c ∈ points := (Finset.mem_filter.mp hcAbove).1
    have hc1 : c < 1 := by
      obtain ⟨m, _, hmc⟩ := Finset.mem_image.mp hcPoints
      rw [← hmc]
      exact (mechanicalBreakpoint_mem_Ioo halpha m).2
    refine ⟨(x + c) / 2, by linarith, by linarith, ?_⟩
    intro y hy m hm
    constructor
    · intro hmx
      exact hmx.trans hy.1.le
    · intro hmy
      by_contra hmx
      have hxm : x < mechanicalBreakpoint alpha m := lt_of_not_ge hmx
      have hmPoints : mechanicalBreakpoint alpha m ∈ points :=
        Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hm, rfl⟩
      have hmAbove : mechanicalBreakpoint alpha m ∈ above :=
        Finset.mem_filter.mpr ⟨hmPoints, hxm⟩
      have hcle : c ≤ mechanicalBreakpoint alpha m := above.min'_le _ hmAbove
      have hyc : y < c := hy.2.trans (by linarith)
      exact (not_le_of_gt hyc) (hcle.trans hmy)
  · refine ⟨(x + 1) / 2, by linarith, by linarith, ?_⟩
    intro y hy m hm
    have hmPoints : mechanicalBreakpoint alpha m ∈ points :=
      Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hm, rfl⟩
    have hmx : mechanicalBreakpoint alpha m ≤ x := by
      by_contra hmx
      apply habove
      exact ⟨mechanicalBreakpoint alpha m,
        Finset.mem_filter.mpr ⟨hmPoints, lt_of_not_ge hmx⟩⟩
    exact ⟨fun _ => hmx.trans hy.1.le, fun _ => hmx⟩

private theorem bounded_phase_returns {alpha rho a b : Real} (halpha : Irrational alpha)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ B : Nat, ∀ i : Nat, ∃ q : Nat,
      q ≤ B ∧ mechanicalPhase alpha rho (i + q) ∈ Ioo a b := by
  let step : AddCircle (1 : Real) := (alpha : AddCircle (1 : Real))
  have hz : DenseRange (fun z : Int => z • step) := by
    dsimp [step]
    rw [AddCircle.denseRange_zsmul_coe_iff]
    simpa using halpha
  have hn : DenseRange (fun q : Nat => q • step) := denseRange_zsmul_iff_nsmul.mp hz
  let U : Set (AddCircle (1 : Real)) :=
    ((fun x : Real => (x : AddCircle (1 : Real))) '' Ioo a b)
  have hUopen : IsOpen U := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hUne : U.Nonempty := by
    refine ⟨(((a + b) / 2 : Real) : AddCircle (1 : Real)), (a + b) / 2, ?_, rfl⟩
    constructor <;> linarith
  let V : Nat → Set (AddCircle (1 : Real)) := fun q =>
    {y | y + q • step ∈ U}
  have hVopen : ∀ q, IsOpen (V q) := by
    intro q
    exact IsOpen.preimage (by fun_prop) hUopen
  have hcover : (Set.univ : Set (AddCircle (1 : Real))) ⊆ ⋃ q, V q := by
    intro y _
    let translate : AddCircle (1 : Real) → AddCircle (1 : Real) := fun x => y + x
    have htranslate : Function.Surjective translate := by
      intro z
      exact ⟨z - y, by simp [translate]⟩
    have htranslate_continuous : Continuous translate := by
      dsimp [translate]
      fun_prop
    have htranslated : DenseRange (fun q : Nat => y + q • step) := by
      simpa [translate, Function.comp_def] using
        htranslate.denseRange.comp hn htranslate_continuous
    obtain ⟨q, hq⟩ := htranslated.exists_mem_open hUopen hUne
    exact Set.mem_iUnion.mpr ⟨q, hq⟩
  obtain ⟨t, ht⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (AddCircle (1 : Real)))).elim_finite_subcover
      V hVopen hcover
  refine ⟨t.sup id, fun i => ?_⟩
  let y : AddCircle (1 : Real) :=
    ((rho + (i : Real) * alpha : Real) : AddCircle (1 : Real))
  obtain ⟨q, hqt, hqy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
  have hqBound : q ≤ t.sup id := by
    simpa using (Finset.le_sup (f := id) hqt)
  change y + q • step ∈ U at hqy
  obtain ⟨z, hz, hzy⟩ := hqy
  have hphase_mem : mechanicalPhase alpha rho (i + q) ∈ Ico (0 : Real) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hz_mem : z ∈ Ico (0 : Real) 1 := ⟨(ha.trans_lt hz.1).le, hz.2.trans_le hb⟩
  have hphase_circle :
      ((mechanicalPhase alpha rho (i + q) : Real) : AddCircle (1 : Real)) =
        (z : AddCircle (1 : Real)) := by
    rw [mechanicalPhase, AddCircle.coe_fract]
    simpa [y, step, Nat.cast_add, add_mul, nsmul_eq_mul, add_assoc] using hzy.symm
  have hphase : mechanicalPhase alpha rho (i + q) = z := by
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : Real)) (p := (1 : Real))
      (by simpa only [zero_add] using hphase_mem)
      (by simpa only [zero_add] using hz_mem)).mp
    exact hphase_circle
  exact ⟨q, hqBound, by simpa [hphase] using hz⟩

/-- Every occurring factor of an irrational lower mechanical word has bounded return gaps. -/
theorem lower_mechanical_factor_uniformly_recurrent {alpha rho : Real}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) (halpha_irr : Irrational alpha)
    {n : Nat} {w : List Bool} (hw : w ∈ lowerMechanicalFactorSet alpha rho n) :
    ∃ R : Nat, ∀ i : Nat, ∃ j : Nat, i ≤ j ∧ j + n ≤ i + R ∧
      w = lowerMechanicalFactor alpha rho n j := by
  classical
  obtain ⟨s, hws⟩ := mem_lowerMechanicalFactorSet.mp hw
  let x := mechanicalPhase alpha rho s
  have hx0 : 0 ≤ x := Int.fract_nonneg _
  have hx1 : x < 1 := Int.fract_lt_one _
  obtain ⟨b, hxb, hb1, hstable⟩ :=
    exists_right_stable_interval halpha_irr hx1 n
  obtain ⟨B, hB⟩ := bounded_phase_returns halpha_irr hx0 hxb hb1
  refine ⟨B + n, fun i => ?_⟩
  obtain ⟨q, hqB, hqphase⟩ := hB i
  let j := i + q
  refine ⟨j, by omega, by omega, ?_⟩
  rw [hws]
  apply factor_eq_of_breakpoint_sides_eq halpha0 halpha1
  intro m hm
  simpa [x, j] using hstable hqphase m hm

#print axioms lower_mechanical_factor_uniformly_recurrent

end D5.S1.Words.Mechanical.MechanicalUniformRecurrence
