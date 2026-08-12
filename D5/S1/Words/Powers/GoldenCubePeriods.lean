/- GID: D5/S1/Words/Powers/GoldenCubePeriods
   generality: I
   mirror-B: none(waiver:formal-kernel-cube-period-necessity)
   mirror-E: none(waiver:kernel-small-cases-in-formal-module)
   anchors: []
   digest: Every nonempty golden cube root has Fibonacci length. -/

import D5.S1.Words.Powers.GoldenCubePeriodsSupport

namespace D5.S1.Words.Powers

open D5.S1.Words

/-! ### Golden cube root lengths -/

private theorem goldenFactor_getElem? {n i x : Nat} (hx : x < n) :
    (goldenFactor n i)[x]? = some (goldenWord (i + x)) := by
  rw [goldenFactor, List.getElem?_eq_getElem (by simpa using hx)]
  simp

private theorem cube_block_eq {i : Nat} {u : List Bool}
    (hcube : IsGoldenPowerFactor 3 u i) {t : Nat} (ht : t < 3) :
    goldenFactor u.length (i + t * u.length) = u := by
  apply List.ext_get
  · simp [goldenFactor]
  · intro x hxleft hxright
    have hx : x < u.length := by simpa [goldenFactor] using hxleft
    have hm : t * u.length + x < 3 * u.length := by
      interval_cases t <;> omega
    have hmod : (t * u.length + x) % u.length = x := by
      rw [Nat.mul_comm t u.length, Nat.mul_add_mod, Nat.mod_eq_of_lt hx]
    have hpoint := congrArg (fun w : List Bool => w[t * u.length + x]?) hcube
    rw [goldenFactor_getElem? hm, wordPower_getElem? 3 u _ hm, hmod,
      List.getElem?_eq_getElem hxright] at hpoint
    simp only [List.get_eq_getElem, goldenFactor, List.getElem_ofFn]
    simpa only [Nat.add_assoc] using Option.some.inj hpoint

private theorem overlap_periods {i d : Nat} {u : List Bool} (hdpos : 0 < d)
    (hdlt : d < u.length) (hzero : goldenFactor u.length i = u)
    (hmiddle : goldenFactor u.length (i + d) = u)
    (hnext : goldenFactor u.length (i + u.length) = u) :
    List.HasPeriod u d ∧ List.HasPeriod u (u.length - d) := by
  constructor
  · rw [List.hasPeriod_iff_getElem?]
    intro x hx
    have hx0 : x < u.length := by omega
    have hxd : x + d < u.length := by omega
    have hm := congrArg (fun w : List Bool => w[x]?) hmiddle
    have hz := congrArg (fun w : List Bool => w[x + d]?) hzero
    rw [goldenFactor_getElem? hx0] at hm
    rw [goldenFactor_getElem? hxd] at hz
    calc
      u[x]? = some (goldenWord (i + d + x)) := hm.symm
      _ = some (goldenWord (i + (x + d))) := by
        congr 2
        omega
      _ = u[x + d]? := hz
  · rw [List.hasPeriod_iff_getElem?]
    intro x hx
    have hdle : d ≤ u.length := hdlt.le
    have hcancel : u.length - (u.length - d) = d := by omega
    rw [hcancel] at hx
    have hx0 : x < u.length := by omega
    have hxshift : x + (u.length - d) < u.length := by omega
    have hn := congrArg (fun w : List Bool => w[x]?) hnext
    have hm := congrArg (fun w : List Bool => w[x + (u.length - d)]?) hmiddle
    rw [goldenFactor_getElem? hx0] at hn
    rw [goldenFactor_getElem? hxshift] at hm
    exact hn.symm.trans ((by
      convert hm using 1
      congr 2
      omega))

private theorem wordPower_three_has_period {u : List Bool} {p : Nat}
    (hdvd : p ∣ u.length) (hperiod : List.HasPeriod u p) :
    List.HasPeriod (wordPower 3 u) p := by
  have htwo : List.HasPeriod (u ++ u) p := by
    simpa using List.HasPeriod.take_append p u.length u hdvd le_rfl hperiod
  have hthree : List.HasPeriod (u ++ (u ++ u)) p := by
    simpa using List.HasPeriod.take_append p u.length (u ++ u) hdvd (by simp) htwo
  simpa [wordPower_succ] using hthree

private theorem goldenPeriodic_of_factor_hasPeriod {i L p : Nat}
    (hperiod : List.HasPeriod (goldenFactor L i) p) : GoldenPeriodic i p L := by
  rw [List.hasPeriod_iff_getElem?] at hperiod
  have hperiod' : ∀ x < L - p,
      (goldenFactor L i)[x]? = (goldenFactor L i)[x + p]? := by
    simpa [goldenFactor] using hperiod
  intro q hi hq
  let m := q - i
  have hm : m < L - p := by dsimp [m]; omega
  have hpoint := hperiod' m hm
  have hmL : m < L := by omega
  have hmpL : m + p < L := by omega
  rw [goldenFactor_getElem? hmL, goldenFactor_getElem? hmpL] at hpoint
  dsimp [m] at hpoint
  have hqi : i + (q - i) = q := Nat.add_sub_of_le hi
  have hqip : i + (q - i + p) = q + p := by omega
  simpa only [hqi, hqip] using Option.some.inj hpoint

private theorem cube_no_internal_occurrence {i d : Nat} {u : List Bool}
    (hcube : IsGoldenPowerFactor 3 u i) (hdpos : 0 < d) (hdlt : d < u.length)
    (hmiddle : goldenFactor u.length (i + d) = u) : False := by
  have hzero : goldenFactor u.length i = u := by
    simpa using cube_block_eq hcube (t := 0) (by omega)
  have hnext : goldenFactor u.length (i + u.length) = u := by
    simpa using cube_block_eq hcube (t := 1) (by omega)
  have hperiods := overlap_periods hdpos hdlt hzero hmiddle hnext
  let g := Nat.gcd d (u.length - d)
  have hgperiod : List.HasPeriod u g := by
    apply hperiods.1.gcd hperiods.2
    omega
  have htailpos : 0 < u.length - d := by omega
  have hgpos : 0 < g := by
    exact Nat.gcd_pos_of_pos_left (u.length - d) hdpos
  have hgdvd : g ∣ u.length := by
    have hsum : g ∣ d + (u.length - d) :=
      Nat.dvd_add (Nat.gcd_dvd_left d (u.length - d))
        (Nat.gcd_dvd_right d (u.length - d))
    simpa [Nat.add_sub_of_le hdlt.le] using hsum
  have hgleLeft : g ≤ d := Nat.gcd_le_left (u.length - d) hdpos
  have hgleRight : g ≤ u.length - d := Nat.gcd_le_right d htailpos
  have hpowerPeriod : List.HasPeriod (wordPower 3 u) g :=
    wordPower_three_has_period hgdvd hgperiod
  have hfactorPeriod : List.HasPeriod (goldenFactor (3 * u.length) i) g := by
    rw [hcube]
    exact hpowerPeriod
  have hgolden : GoldenPeriodic i g (3 * u.length) :=
    goldenPeriodic_of_factor_hasPeriod hfactorPeriod
  exact golden_no_periodic g hgpos i (3 * u.length) (by omega) hgolden

private theorem adjacent_golden_occurrences_iff {n : Nat} {w : List Bool} {i j : Nat} :
    AdjacentGoldenOccurrences n w i j ↔
      i < j ∧ goldenFactor n i = w ∧ goldenFactor n j = w ∧
        (Finset.Ioo i j).filter (fun k => goldenFactor n k = w) = ∅ := by
  change decide (i < j ∧ goldenFactor n i = w ∧ goldenFactor n j = w ∧
    (Finset.Ioo i j).filter (fun k => goldenFactor n k = w) = ∅) = true ↔ _
  simp

private theorem cube_first_blocks_adjacent {i : Nat} {u : List Bool} (hu : u ≠ [])
    (hcube : IsGoldenPowerFactor 3 u i) :
    AdjacentGoldenOccurrences u.length u i (i + u.length) := by
  have hlen : 0 < u.length := List.length_pos_of_ne_nil hu
  apply adjacent_golden_occurrences_iff.mpr
  refine ⟨by omega, by simpa using cube_block_eq hcube (t := 0) (by omega),
    by simpa using cube_block_eq hcube (t := 1) (by omega),
    Finset.filter_eq_empty_iff.mpr ?_⟩
  intro k hk hfactor
  have hki := Finset.mem_Ioo.mp hk
  apply cube_no_internal_occurrence hcube (d := k - i) (by omega) (by omega)
  simpa [Nat.add_sub_of_le hki.1.le] using hfactor

private theorem cube_root_length_ne_one {i : Nat} {u : List Bool}
    (hcube : IsGoldenPowerFactor 3 u i) : u.length ≠ 1 := by
  intro hlen
  have hperiod := goldenPeriodic_of_isGoldenPowerFactor hcube
  exact golden_no_periodic 1 (by omega) i 3 (by omega) (by simpa [hlen] using hperiod)

private theorem cube_root_length_ne_two {i : Nat} {u : List Bool}
    (hcube : IsGoldenPowerFactor 3 u i) : u.length ≠ 2 := by
  intro hlen
  have hperiod : GoldenPeriodic i 2 6 := by
    simpa [hlen] using goldenPeriodic_of_isGoldenPowerFactor hcube
  by_cases hi : goldenWord i = true
  · have hi2 : goldenWord (i + 2) = true := by
      rw [← hperiod i le_rfl (by omega)]
      exact hi
    by_cases hi1 : goldenWord (i + 1) = true
    · have hfalse := golden_no_three_true hi hi1
      rw [hi2] at hfalse
      exact Bool.noConfusion hfalse
    · have hi1' : goldenWord (i + 1) = false := by simpa using hi1
      have hi3 : goldenWord (i + 3) = false := by
        rw [← hperiod (i + 1) (by omega) (by omega)]
        exact hi1'
      have hi5 : goldenWord (i + 5) = false := by
        rw [← hperiod (i + 3) (by omega) (by omega)]
        exact hi3
      have hi4 : goldenWord (i + 4) = true := by
        rw [← hperiod (i + 2) (by omega) (by omega)]
        exact hi2
      have hi6 : goldenWord (i + 6) = true := golden_no_two_false hi5
      have hperiod7 : GoldenPeriodic i 2 7 := by
        intro q hq hq2
        by_cases hinside : q + 2 < i + 6
        · exact hperiod q hq hinside
        · have hqeq : q = i + 4 := by omega
          subst q
          exact hi4.trans hi6.symm
      exact golden_no_periodic 2 (by omega) i 7 (by omega) hperiod7
  · have hi' : goldenWord i = false := by simpa using hi
    have hine : i ≠ 0 := by
      intro hizero
      rw [hizero, goldenWord_zero] at hi'
      exact Bool.noConfusion hi'
    obtain ⟨b, rfl⟩ : ∃ b, i = b + 1 := ⟨i - 1, by omega⟩
    have hperiod7 : GoldenPeriodic b 2 7 :=
      goldenPeriodic_shift_left (by omega) hperiod hi'
    exact golden_no_periodic 2 (by omega) b 7 (by omega) hperiod7

/-- Every nonempty root of a golden cube has Fibonacci length. -/
theorem golden_cube_root_length_eq_fib {i : Nat} {u : List Bool}
    (hu : u ≠ []) (hcube : IsGoldenPowerFactor 3 u i) :
    ∃ Q, 4 ≤ Q ∧ u.length = Nat.fib Q := by
  have hadj := cube_first_blocks_adjacent hu hcube
  obtain ⟨Q, hQ, hlength⟩ :=
    GoldenCubePeriodsInternal.golden_adjacent_gap_is_fib hadj
  have hlength' : u.length = Nat.fib Q := by simpa using hlength
  refine ⟨Q, ?_, hlength'⟩
  by_contra hnot
  have hcases : Q = 2 ∨ Q = 3 := by omega
  rcases hcases with rfl | rfl
  · apply cube_root_length_ne_one hcube
    norm_num [Nat.fib] at hlength' ⊢
    exact hlength'
  · apply cube_root_length_ne_two hcube
    norm_num [Nat.fib] at hlength' ⊢
    exact hlength'

#print axioms golden_cube_root_length_eq_fib

end D5.S1.Words.Powers
