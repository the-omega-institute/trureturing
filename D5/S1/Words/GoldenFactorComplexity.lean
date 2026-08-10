/- GID: D5/S1/Words/GoldenFactorComplexity
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:exact-symbolic-factor-complexity)
   anchors: []
   digest: The infinite golden word has exactly n plus one factors of length n. -/

import D5.S1.Words.GoldenBalance
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Data.Finset.Sort

namespace D5.S1.Words

open Set

/-- The length-`n` factor of the infinite golden word starting at `i`. -/
def goldenFactor (n i : Nat) : List Bool :=
  List.ofFn fun k : Fin n => goldenWord (i + k)

/-- The finite set of length-`n` words that occur in the infinite golden word. -/
noncomputable def goldenFactorSet (n : Nat) : Finset (List Bool) := by
  classical
  exact ((Finset.univ : Finset (Fin n → Bool)).filter fun w =>
    ∃ i, List.ofFn w = goldenFactor n i).image List.ofFn

theorem mem_goldenFactorSet {n : Nat} {w : List Bool} :
    w ∈ goldenFactorSet n ↔ ∃ i, w = goldenFactor n i := by
  classical
  simp only [goldenFactorSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact hf
  · rintro ⟨i, rfl⟩
    exact ⟨(fun k : Fin n => goldenWord (i + k)), ⟨i, rfl⟩, rfl⟩

theorem length_eq_of_mem_goldenFactorSet {n : Nat} {w : List Bool}
    (hw : w ∈ goldenFactorSet n) : w.length = n := by
  obtain ⟨i, rfl⟩ := mem_goldenFactorSet.mp hw
  simp [goldenFactor]

private noncomputable def breakpoint (m : Nat) : Real :=
  1 - Int.fract (((m + 1 : Nat) : Real) * goldenMechanicalSlope)
private noncomputable def breakpoints (n : Nat) : Finset Real :=
  (Finset.range n).image breakpoint
private theorem slope_irrational : Irrational goldenMechanicalSlope := by
  exact Real.goldenRatio_irrational.inv
private theorem fract_mul_slope_ne_zero (m : Nat) :
    Int.fract (((m + 1 : Nat) : Real) * goldenMechanicalSlope) ≠ 0 := by
  rw [Int.fract_ne_zero_iff]
  rintro ⟨z, hz⟩
  have hi : Irrational (((m + 1 : Nat) : Real) * goldenMechanicalSlope) :=
    slope_irrational.natCast_mul (Nat.succ_ne_zero m)
  exact hi.ne_int z hz.symm
private theorem breakpoint_mem_Ioo (m : Nat) : breakpoint m ∈ Ioo (0 : Real) 1 := by
  have hnonneg := Int.fract_nonneg (((m + 1 : Nat) : Real) * goldenMechanicalSlope)
  have hlt := Int.fract_lt_one (((m + 1 : Nat) : Real) * goldenMechanicalSlope)
  have hne := fract_mul_slope_ne_zero m
  have hpos : 0 < Int.fract (((m + 1 : Nat) : Real) * goldenMechanicalSlope) :=
    lt_of_le_of_ne hnonneg (Ne.symm hne)
  simp only [breakpoint, mem_Ioo]
  constructor <;> linarith
private theorem breakpoint_injective : Function.Injective breakpoint := by
  intro a b hab
  have hfract : Int.fract (((a + 1 : Nat) : Real) * goldenMechanicalSlope) =
      Int.fract (((b + 1 : Nat) : Real) * goldenMechanicalSlope) := by
    simpa [breakpoint] using congrArg (fun x : Real => 1 - x) hab
  obtain ⟨z, hz⟩ := Int.fract_eq_fract.mp hfract
  by_contra hne
  have hcoeff : (a + 1 : Int) - (b + 1 : Int) ≠ 0 := by omega
  have hi : Irrational ((((a + 1 : Int) - (b + 1 : Int) : Int) : Real) *
      goldenMechanicalSlope) := slope_irrational.intCast_mul hcoeff
  apply hi.ne_int z
  rw [← hz]
  push_cast
  ring
private theorem breakpoints_card (n : Nat) : (breakpoints n).card = n := by
  rw [breakpoints, Finset.card_image_of_injective _ breakpoint_injective, Finset.card_range]
private noncomputable def phase (i : Nat) : Real :=
  Int.fract (((i + 1 : Nat) : Real) * goldenMechanicalSlope)
private theorem exists_phase_mem_Ioo {a b : Real} (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) : ∃ i, phase i ∈ Ioo a b := by
  have hz : DenseRange (fun z : Int =>
      z • ((goldenMechanicalSlope : Real) : AddCircle (1 : Real))) := by
    rw [AddCircle.denseRange_zsmul_coe_iff]
    simpa using slope_irrational
  have hn : DenseRange (fun q : Nat =>
      q • ((goldenMechanicalSlope : Real) : AddCircle (1 : Real))) :=
    denseRange_zsmul_iff_nsmul.mp hz
  let U : Set (AddCircle (1 : Real)) :=
    ((fun x : Real => (x : AddCircle (1 : Real))) '' Ioo a b)
  have hUopen : IsOpen U := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hUne : U.Nonempty := by
    refine ⟨(((a + b) / 2 : Real) : AddCircle (1 : Real)), (a + b) / 2, ?_, rfl⟩
    constructor <;> linarith
  obtain ⟨q, x, hx, hxq⟩ := hn.exists_mem_open hUopen hUne
  have hfract_mem : Int.fract ((q : Real) * goldenMechanicalSlope) ∈ Ico (0 : Real) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hx_mem : x ∈ Ico (0 : Real) 1 := ⟨(ha.trans_lt hx.1).le, hx.2.trans_le hb⟩
  have hfract : Int.fract ((q : Real) * goldenMechanicalSlope) = x := by
    have hfract_mem' : Int.fract ((q : Real) * goldenMechanicalSlope) ∈
        Ico (0 : Real) (0 + 1) := by simpa using hfract_mem
    have hx_mem' : x ∈ Ico (0 : Real) (0 + 1) := by simpa using hx_mem
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : Real))
      hfract_mem' hx_mem').mp
    rw [AddCircle.coe_fract]
    simpa [nsmul_eq_mul] using hxq.symm
  have hq : 0 < q := by
    by_contra hq
    have : q = 0 := Nat.eq_zero_of_not_pos hq
    subst q
    exact (ha.trans_lt hx.1).ne (by simpa using hfract)
  refine ⟨q - 1, ?_⟩
  rw [phase, Nat.sub_add_cancel hq]
  simpa [hfract] using hx
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
    · have : Int.fract x < 1 - Int.fract t := lt_of_not_ge h
      linarith
private theorem window_count_eq_indicator (i m : Nat) :
    (goldenWindowTrueCount i (m + 1) : Int) =
      ⌊(((m + 1 : Nat) : Real) * goldenMechanicalSlope)⌋ +
        if breakpoint m ≤ phase i then 1 else 0 := by
  rw [goldenWindowTrueCount_eq_floor]
  have hend : (((i + (m + 1) + 1 : Nat) : Real) * goldenMechanicalSlope) =
      (((i + 1 : Nat) : Real) * goldenMechanicalSlope) +
        (((m + 1 : Nat) : Real) * goldenMechanicalSlope) := by
    push_cast
    ring
  change ⌊((i + (m + 1) + 1 : Nat) : Real) * goldenMechanicalSlope⌋ -
      ⌊((i + 1 : Nat) : Real) * goldenMechanicalSlope⌋ = _
  rw [hend, floor_add_sub_floor, floor_fract_add_indicator]
  rfl
private theorem window_count_succ (i m : Nat) :
    goldenWindowTrueCount i (m + 1) = goldenWindowTrueCount i m +
      if goldenWord (i + m) = true then 1 else 0 := by
  classical
  by_cases h : goldenWord (i + m) = true <;>
    simp [goldenWindowTrueCount, Finset.range_add_one, Finset.filter_insert, h]
private noncomputable def rank (n i : Nat) : Nat :=
  ((breakpoints n).filter fun x => x ≤ phase i).card
private theorem rank_le (n i : Nat) : rank n i ≤ n := by
  exact (Finset.card_filter_le _ _).trans_eq (breakpoints_card n)
private theorem selected_eq_of_rank_eq {n i j : Nat} (h : rank n i = rank n j) :
    (breakpoints n).filter (fun x => x ≤ phase i) =
      (breakpoints n).filter (fun x => x ≤ phase j) := by
  rcases le_total (phase i) (phase j) with hij | hji
  · apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hx.2.trans hij⟩
    · exact h.ge
  · symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hx.2.trans hji⟩
    · exact h.le
private theorem window_counts_eq_of_selected_eq {n i j m : Nat} (hm : m ≤ n)
    (h : (breakpoints n).filter (fun x => x ≤ phase i) =
      (breakpoints n).filter (fun x => x ≤ phase j)) :
    goldenWindowTrueCount i m = goldenWindowTrueCount j m := by
  rcases m with _ | m
  · simp [goldenWindowTrueCount]
  have hm' : m < n := by omega
  have hmem : breakpoint m ∈ breakpoints n := by
    exact Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hm', rfl⟩
  have hiff : breakpoint m ≤ phase i ↔ breakpoint m ≤ phase j := by
    have := Finset.ext_iff.mp h (breakpoint m)
    simpa [hmem] using this
  rw [← Nat.cast_inj (R := Int), window_count_eq_indicator, window_count_eq_indicator]
  by_cases hi : breakpoint m ≤ phase i
  · have hj := hiff.mp hi
    simp [hi, hj]
  · have hj : ¬breakpoint m ≤ phase j := fun hj => hi (hiff.mpr hj)
    simp [hi, hj]
private theorem factor_eq_of_rank_eq {n i j : Nat} (h : rank n i = rank n j) :
    goldenFactor n i = goldenFactor n j := by
  unfold goldenFactor
  congr 1
  funext k
  have hselected := selected_eq_of_rank_eq h
  have hbase := window_counts_eq_of_selected_eq k.isLt.le hselected
  have hnext := window_counts_eq_of_selected_eq (Nat.succ_le_of_lt k.isLt) hselected
  rw [window_count_succ, window_count_succ] at hnext
  have hindicator : (if goldenWord (i + k) = true then 1 else 0) =
      if goldenWord (j + k) = true then 1 else 0 := by omega
  by_cases hi : goldenWord (i + k) = true <;> by_cases hj : goldenWord (j + k) = true <;>
    simp_all
private theorem window_counts_eq_of_factor_eq {n i j m : Nat} (hm : m ≤ n)
    (h : goldenFactor n i = goldenFactor n j) :
    goldenWindowTrueCount i m = goldenWindowTrueCount j m := by
  have hletters : (fun k : Fin n => goldenWord (i + k)) =
      fun k : Fin n => goldenWord (j + k) := by
    exact List.ofFn_inj.mp h
  unfold goldenWindowTrueCount
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hk, hw⟩
    refine ⟨hk, ?_⟩
    rw [← congrFun hletters ⟨k, hk.trans_le hm⟩]
    exact hw
  · rintro ⟨hk, hw⟩
    refine ⟨hk, ?_⟩
    rw [congrFun hletters ⟨k, hk.trans_le hm⟩]
    exact hw
private theorem selected_eq_of_factor_eq {n i j : Nat}
    (h : goldenFactor n i = goldenFactor n j) :
    (breakpoints n).filter (fun x => x ≤ phase i) =
      (breakpoints n).filter (fun x => x ≤ phase j) := by
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, hxi⟩
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
    have hm' : m + 1 ≤ n := Finset.mem_range.mp hm
    have hc := congrArg (fun q : Nat => (q : Int))
      (window_counts_eq_of_factor_eq hm' h)
    rw [window_count_eq_indicator, window_count_eq_indicator] at hc
    have hxj : breakpoint m ≤ phase j := by
      by_contra hxj
      simp [hxi, hxj] at hc
    exact ⟨Finset.mem_image.mpr ⟨m, hm, rfl⟩, hxj⟩
  · rintro ⟨hx, hxj⟩
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
    have hm' : m + 1 ≤ n := Finset.mem_range.mp hm
    have hc := congrArg (fun q : Nat => (q : Int))
      (window_counts_eq_of_factor_eq hm' h)
    rw [window_count_eq_indicator, window_count_eq_indicator] at hc
    have hxi : breakpoint m ≤ phase i := by
      by_contra hxi
      simp [hxi, hxj] at hc
    exact ⟨Finset.mem_image.mpr ⟨m, hm, rfl⟩, hxi⟩
private theorem rank_eq_of_factor_eq {n i j : Nat}
    (h : goldenFactor n i = goldenFactor n j) : rank n i = rank n j := by
  exact congrArg Finset.card (selected_eq_of_factor_eq h)
private theorem mem_breakpoints_Ioo {n : Nat} {x : Real} (hx : x ∈ breakpoints n) :
    x ∈ Ioo (0 : Real) 1 := by
  obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hx
  exact breakpoint_mem_Ioo m
private theorem rank_eq_of_order_cut {n r i : Nat} (hr : r ≤ n)
    (hcut : ∀ k : Fin n,
      (breakpoints n).orderEmbOfFin (breakpoints_card n) k ≤ phase i ↔ k < r) :
    rank n i = r := by
  let e := (breakpoints n).orderEmbOfFin (breakpoints_card n)
  have heq : (breakpoints n).filter (fun x => x ≤ phase i) =
      (Finset.univ.filter fun k : Fin n => k < r).image e := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hxi⟩
      have hxrange : x ∈ Set.range e := by
        rw [Finset.range_orderEmbOfFin]
        exact hx
      obtain ⟨k, rfl⟩ := hxrange
      exact ⟨k, (hcut k).mp hxi, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem _ _ _, (hcut k).mpr hk⟩
  rw [rank, heq, Finset.card_image_of_injective _ e.injective, Fin.card_filter_val_lt,
    Nat.min_eq_right hr]
private theorem exists_rank_eq (n r : Nat) (hr : r ≤ n) : ∃ i, rank n i = r := by
  rcases n.eq_zero_or_pos with rfl | hn
  · have : r = 0 := by omega
    subst r
    exact ⟨0, by simp [rank, breakpoints]⟩
  let e := (breakpoints n).orderEmbOfFin (breakpoints_card n)
  rcases r.eq_zero_or_pos with rfl | hrpos
  · have he0 : e ⟨0, hn⟩ ∈ Ioo (0 : Real) 1 :=
      mem_breakpoints_Ioo (Finset.orderEmbOfFin_mem _ _ _)
    obtain ⟨i, hi⟩ := exists_phase_mem_Ioo (a := 0) (b := e ⟨0, hn⟩)
      le_rfl he0.1 he0.2.le
    refine ⟨i, rank_eq_of_order_cut (Nat.zero_le n) fun k => ?_⟩
    simp only [Nat.not_lt_zero, iff_false, not_le]
    exact hi.2.trans_le (e.monotone (Fin.mk_le_mk.mpr (Nat.zero_le k.val)))
  · rcases eq_or_lt_of_le hr with rfl | hrlt
    · let last : Fin r := ⟨r - 1, by omega⟩
      have helast : e last ∈ Ioo (0 : Real) 1 :=
        mem_breakpoints_Ioo (Finset.orderEmbOfFin_mem _ _ _)
      obtain ⟨i, hi⟩ := exists_phase_mem_Ioo (a := e last) (b := 1)
        helast.1.le helast.2 le_rfl
      refine ⟨i, rank_eq_of_order_cut le_rfl fun k => ?_⟩
      simp only [Fin.is_lt, iff_true]
      have hklast : k ≤ last := by
        apply Fin.mk_le_mk.mpr
        omega
      exact (e.monotone hklast).trans hi.1.le
    · let lo : Fin n := ⟨r - 1, by omega⟩
      let hiIndex : Fin n := ⟨r, hrlt⟩
      have hlo : e lo ∈ Ioo (0 : Real) 1 :=
        mem_breakpoints_Ioo (Finset.orderEmbOfFin_mem _ _ _)
      have hlt : e lo < e hiIndex := e.strictMono (by simp [lo, hiIndex]; omega)
      have hhi : e hiIndex ∈ Ioo (0 : Real) 1 :=
        mem_breakpoints_Ioo (Finset.orderEmbOfFin_mem _ _ _)
      obtain ⟨i, hphase⟩ := exists_phase_mem_Ioo (a := e lo) (b := e hiIndex)
        hlo.1.le hlt hhi.2.le
      refine ⟨i, rank_eq_of_order_cut hr fun k => ?_⟩
      constructor
      · intro hk
        by_contra hkr
        change ¬k.val < r at hkr
        have hrk : hiIndex ≤ k := by
          apply Fin.mk_le_mk.mpr
          exact Nat.le_of_not_gt hkr
        exact (not_lt_of_ge hk) (hphase.2.trans_le (e.monotone hrk))
      · intro hkr
        change k.val < r at hkr
        have hklo : k ≤ lo := by
          apply Fin.mk_le_mk.mpr
          omega
        exact (e.monotone hklo).trans hphase.1.le

/-- The golden word has exactly `n + 1` distinct factors of length `n`. -/
theorem golden_factor_complexity (n : Nat) : (goldenFactorSet n).card = n + 1 := by
  classical
  let start : (w : ↥(goldenFactorSet n)) → Nat := fun w =>
    Classical.choose (mem_goldenFactorSet.mp w.2)
  have hstart (w : ↥(goldenFactorSet n)) : w.1 = goldenFactor n (start w) :=
    Classical.choose_spec (mem_goldenFactorSet.mp w.2)
  have hupper : (goldenFactorSet n).card ≤ n + 1 := by
    let encode : ↥(goldenFactorSet n) → ↥(Finset.univ : Finset (Fin (n + 1))) := fun w =>
      ⟨⟨rank n (start w), Nat.lt_succ_of_le (rank_le n (start w))⟩, Finset.mem_univ _⟩
    have hencode : Function.Injective encode := by
      intro u v huv
      apply Subtype.ext
      rw [hstart u, hstart v]
      apply factor_eq_of_rank_eq
      simpa [encode] using congrArg (fun x => x.1.1) huv
    simpa using Finset.card_le_card_of_injective hencode
  have hstarts (r : Fin (n + 1)) : ∃ i, rank n i = r :=
    exists_rank_eq n r (Nat.le_of_lt_succ r.isLt)
  let startOfRank (r : Fin (n + 1)) : Nat := Classical.choose (hstarts r)
  have hstartOfRank (r : Fin (n + 1)) : rank n (startOfRank r) = r :=
    Classical.choose_spec (hstarts r)
  have hlower : n + 1 ≤ (goldenFactorSet n).card := by
    let realize : ↥(Finset.univ : Finset (Fin (n + 1))) → ↥(goldenFactorSet n) := fun r =>
      ⟨goldenFactor n (startOfRank r), mem_goldenFactorSet.mpr ⟨startOfRank r, rfl⟩⟩
    have hrealize : Function.Injective realize := by
      intro r s hrs
      apply Subtype.ext
      have hfactors : goldenFactor n (startOfRank r) = goldenFactor n (startOfRank s) :=
        congrArg Subtype.val hrs
      apply Fin.ext
      rw [← hstartOfRank r, ← hstartOfRank s]
      exact rank_eq_of_factor_eq hfactors
    simpa using Finset.card_le_card_of_injective hrealize
  exact Nat.le_antisymm hupper hlower

private def boundedGoldenFactorSet (n starts : Nat) : Finset (List Bool) :=
  (Finset.range starts).image (goldenFactor n)

example : (boundedGoldenFactorSet 1 13).card = 2 := by decide
example : (boundedGoldenFactorSet 2 13).card = 3 := by decide
example : (boundedGoldenFactorSet 3 13).card = 4 := by decide
example : (boundedGoldenFactorSet 4 13).card = 5 := by decide

end D5.S1.Words
