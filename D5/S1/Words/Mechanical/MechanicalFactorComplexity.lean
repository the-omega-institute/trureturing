/- GID: D5/S1/Words/Mechanical/MechanicalFactorComplexity
   generality: G
   mirror-B: D5/B/S1/Words/Mechanical/MechanicalFactorComplexity
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   digest: Every irrational lower mechanical word has exactly n plus one factors of length n. -/
import D5.S1.Words.Mechanical.MechanicalBalance
import Mathlib.Data.Finset.Sort
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
namespace D5.S1.Words.Mechanical
open Set
/-- The length-`n` factor beginning at natural index `i`. -/
noncomputable def lowerMechanicalFactor (alpha rho : Real) (n i : Nat) : List Bool :=
  List.ofFn fun k : Fin n => lowerMechanicalWord alpha rho (i + k)
/-- The finite set of length-`n` factors occurring at natural starting indices. -/
noncomputable def lowerMechanicalFactorSet (alpha rho : Real) (n : Nat) :
    Finset (List Bool) := by
  classical
  exact ((Finset.univ : Finset (Fin n → Bool)).filter fun w =>
    ∃ i, List.ofFn w = lowerMechanicalFactor alpha rho n i).image List.ofFn
theorem mem_lowerMechanicalFactorSet {alpha rho : Real} {n : Nat} {w : List Bool} :
    w ∈ lowerMechanicalFactorSet alpha rho n ↔
      ∃ i, w = lowerMechanicalFactor alpha rho n i := by
  classical
  simp only [lowerMechanicalFactorSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact hf
  · rintro ⟨i, rfl⟩
    exact ⟨(fun k : Fin n => lowerMechanicalWord alpha rho (i + k)), ⟨i, rfl⟩, rfl⟩
private noncomputable def breakpoint (alpha : Real) (m : Nat) : Real :=
  1 - Int.fract (((m + 1 : Nat) : Real) * alpha)
private noncomputable def breakpoints (alpha : Real) (n : Nat) : Finset Real :=
  (Finset.range n).image (breakpoint alpha)
private theorem fract_mul_alpha_ne_zero {alpha : Real} (halpha : Irrational alpha) (m : Nat) :
    Int.fract (((m + 1 : Nat) : Real) * alpha) ≠ 0 := by
  rw [Int.fract_ne_zero_iff]
  rintro ⟨z, hz⟩
  have hi : Irrational (((m + 1 : Nat) : Real) * alpha) :=
    halpha.natCast_mul (Nat.succ_ne_zero m)
  exact hi.ne_int z hz.symm
private theorem breakpoint_mem_Ioo {alpha : Real} (halpha : Irrational alpha) (m : Nat) :
    breakpoint alpha m ∈ Ioo (0 : Real) 1 := by
  have hnonneg := Int.fract_nonneg (((m + 1 : Nat) : Real) * alpha)
  have hlt := Int.fract_lt_one (((m + 1 : Nat) : Real) * alpha)
  have hne := fract_mul_alpha_ne_zero halpha m
  have hpos : 0 < Int.fract (((m + 1 : Nat) : Real) * alpha) :=
    lt_of_le_of_ne hnonneg (Ne.symm hne)
  simp only [breakpoint, mem_Ioo]
  constructor <;> linarith
private theorem breakpoint_injective {alpha : Real} (halpha : Irrational alpha) :
    Function.Injective (breakpoint alpha) := by
  intro a b hab
  have hfract : Int.fract (((a + 1 : Nat) : Real) * alpha) =
      Int.fract (((b + 1 : Nat) : Real) * alpha) := by
    simpa [breakpoint] using congrArg (fun x : Real => 1 - x) hab
  obtain ⟨z, hz⟩ := Int.fract_eq_fract.mp hfract
  by_contra hne
  have hcoeff : (a + 1 : Int) - (b + 1 : Int) ≠ 0 := by omega
  have hi : Irrational ((((a + 1 : Int) - (b + 1 : Int) : Int) : Real) * alpha) :=
    halpha.intCast_mul hcoeff
  apply hi.ne_int z
  rw [← hz]
  push_cast
  ring
private theorem breakpoints_card {alpha : Real} (halpha : Irrational alpha) (n : Nat) :
    (breakpoints alpha n).card = n := by
  rw [breakpoints, Finset.card_image_of_injective _ (breakpoint_injective halpha),
    Finset.card_range]
private noncomputable def phase (alpha rho : Real) (i : Nat) : Real :=
  Int.fract (rho + (i : Real) * alpha)
private theorem exists_phase_mem_Ioo {alpha rho a b : Real} (halpha : Irrational alpha)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ i, phase alpha rho i ∈ Ioo a b := by
  have hz : DenseRange (fun z : Int => z • ((alpha : Real) : AddCircle (1 : Real))) := by
    rw [AddCircle.denseRange_zsmul_coe_iff]
    simpa using halpha
  have hn : DenseRange (fun q : Nat => q • ((alpha : Real) : AddCircle (1 : Real))) :=
    denseRange_zsmul_iff_nsmul.mp hz
  let translate : AddCircle (1 : Real) → AddCircle (1 : Real) :=
    fun x => (rho : AddCircle (1 : Real)) + x
  have htranslate : Function.Surjective translate := by
    intro y
    exact ⟨y - (rho : AddCircle (1 : Real)), by simp [translate]⟩
  have htranslate_continuous : Continuous translate := by
    dsimp [translate]
    fun_prop
  have htranslated : DenseRange (fun q : Nat =>
      (rho : AddCircle (1 : Real)) + q • ((alpha : Real) : AddCircle (1 : Real))) := by
    simpa [translate, Function.comp_def] using
      htranslate.denseRange.comp hn htranslate_continuous
  let U : Set (AddCircle (1 : Real)) :=
    ((fun x : Real => (x : AddCircle (1 : Real))) '' Ioo a b)
  have hUopen : IsOpen U := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hUne : U.Nonempty := by
    refine ⟨(((a + b) / 2 : Real) : AddCircle (1 : Real)), (a + b) / 2, ?_, rfl⟩
    constructor <;> linarith
  obtain ⟨q, x, hx, hxq⟩ := htranslated.exists_mem_open hUopen hUne
  have hfract_mem : Int.fract (rho + (q : Real) * alpha) ∈ Ico (0 : Real) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hx_mem : x ∈ Ico (0 : Real) 1 := ⟨(ha.trans_lt hx.1).le, hx.2.trans_le hb⟩
  have hfract : Int.fract (rho + (q : Real) * alpha) = x := by
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : Real)) (p := (1 : Real))
      (by simpa only [zero_add] using hfract_mem)
      (by simpa only [zero_add] using hx_mem)).mp
    rw [AddCircle.coe_fract]
    simpa [nsmul_eq_mul] using hxq.symm
  exact ⟨q, by simpa [phase, hfract] using hx⟩
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
private theorem window_count_eq_indicator {alpha rho : Real}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) (i m : Nat) :
    (lowerMechanicalWindowTrueCount alpha rho i (m + 1) : Int) =
      ⌊(((m + 1 : Nat) : Real) * alpha)⌋ +
        if breakpoint alpha m ≤ phase alpha rho i then 1 else 0 := by
  rw [lowerMechanicalWindowTrueCount_eq_floor halpha0 halpha1]
  have hend : rho + ((i + (m + 1) : Nat) : Real) * alpha =
      (rho + (i : Real) * alpha) + (((m + 1 : Nat) : Real) * alpha) := by
    push_cast
    ring
  rw [hend, floor_add_sub_floor, floor_fract_add_indicator]
  rfl
private theorem window_count_succ {alpha rho : Real} (i m : Nat) :
    lowerMechanicalWindowTrueCount alpha rho i (m + 1) =
      lowerMechanicalWindowTrueCount alpha rho i m +
        if lowerMechanicalWord alpha rho (i + m) = true then 1 else 0 := by
  classical
  unfold lowerMechanicalWindowTrueCount
  rw [Finset.range_add_one, Finset.filter_insert]
  have hm : m ∉ (Finset.range m).filter
      (fun k => lowerMechanicalWord alpha rho (i + k) = true) := by
    simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_irrefl, false_and, not_false_eq_true]
  by_cases h : lowerMechanicalWord alpha rho (i + m) = true
  · rw [if_pos h, Finset.card_insert_of_notMem hm, if_pos h]
  · rw [if_neg h, if_neg h, Nat.add_zero]
private noncomputable def rank (alpha rho : Real) (n i : Nat) : Nat :=
  ((breakpoints alpha n).filter fun x => x ≤ phase alpha rho i).card
private theorem rank_le {alpha rho : Real} (halpha : Irrational alpha) (n i : Nat) :
    rank alpha rho n i ≤ n := by
  exact (Finset.card_filter_le _ _).trans_eq (breakpoints_card halpha n)
private theorem selected_eq_of_rank_eq {alpha rho : Real} {n i j : Nat}
    (h : rank alpha rho n i = rank alpha rho n j) :
    (breakpoints alpha n).filter (fun x => x ≤ phase alpha rho i) =
      (breakpoints alpha n).filter (fun x => x ≤ phase alpha rho j) := by
  rcases le_total (phase alpha rho i) (phase alpha rho j) with hij | hji
  · apply Finset.eq_of_subset_of_card_le
    · intro x hx
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.trans hij⟩
    · exact h.ge
  · symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.trans hji⟩
    · exact h.le
private theorem window_counts_eq_of_selected_eq {alpha rho : Real}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) {n i j m : Nat} (hm : m ≤ n)
    (h : (breakpoints alpha n).filter (fun x => x ≤ phase alpha rho i) =
      (breakpoints alpha n).filter (fun x => x ≤ phase alpha rho j)) :
    lowerMechanicalWindowTrueCount alpha rho i m =
      lowerMechanicalWindowTrueCount alpha rho j m := by
  rcases m with _ | m
  · simp [lowerMechanicalWindowTrueCount]
  have hm' : m < n := by omega
  have hmem : breakpoint alpha m ∈ breakpoints alpha n :=
    Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hm', rfl⟩
  have hiff : breakpoint alpha m ≤ phase alpha rho i ↔
      breakpoint alpha m ≤ phase alpha rho j := by
    simpa [hmem] using Finset.ext_iff.mp h (breakpoint alpha m)
  rw [← Nat.cast_inj (R := Int), window_count_eq_indicator halpha0 halpha1,
    window_count_eq_indicator halpha0 halpha1]
  by_cases hi : breakpoint alpha m ≤ phase alpha rho i
  · simp [hi, hiff.mp hi]
  · have hj : ¬breakpoint alpha m ≤ phase alpha rho j := fun hj => hi (hiff.mpr hj)
    rw [if_neg hi, if_neg hj]
private theorem factor_eq_of_rank_eq {alpha rho : Real}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) {n i j : Nat}
    (h : rank alpha rho n i = rank alpha rho n j) :
    lowerMechanicalFactor alpha rho n i = lowerMechanicalFactor alpha rho n j := by
  unfold lowerMechanicalFactor
  congr 1
  funext k
  have hs := selected_eq_of_rank_eq h
  have hbase := window_counts_eq_of_selected_eq halpha0 halpha1 k.isLt.le hs
  have hnext := window_counts_eq_of_selected_eq halpha0 halpha1
    (Nat.succ_le_of_lt k.isLt) hs
  rw [window_count_succ, window_count_succ] at hnext
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
private theorem window_counts_eq_of_factor_eq {alpha rho : Real} {n i j m : Nat}
    (hm : m ≤ n)
    (h : lowerMechanicalFactor alpha rho n i = lowerMechanicalFactor alpha rho n j) :
    lowerMechanicalWindowTrueCount alpha rho i m =
      lowerMechanicalWindowTrueCount alpha rho j m := by
  have hletters : (fun k : Fin n => lowerMechanicalWord alpha rho (i + k)) =
      fun k : Fin n => lowerMechanicalWord alpha rho (j + k) := List.ofFn_inj.mp h
  unfold lowerMechanicalWindowTrueCount
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hk, hw⟩
    exact ⟨hk, by rw [← congrFun hletters ⟨k, hk.trans_le hm⟩]; exact hw⟩
  · rintro ⟨hk, hw⟩
    exact ⟨hk, by rw [congrFun hletters ⟨k, hk.trans_le hm⟩]; exact hw⟩
private theorem selected_eq_of_factor_eq {alpha rho : Real}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) {n i j : Nat}
    (h : lowerMechanicalFactor alpha rho n i = lowerMechanicalFactor alpha rho n j) :
    (breakpoints alpha n).filter (fun x => x ≤ phase alpha rho i) =
      (breakpoints alpha n).filter (fun x => x ≤ phase alpha rho j) := by
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, hxi⟩
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
    have hc := congrArg (fun q : Nat => (q : Int))
      (window_counts_eq_of_factor_eq (Finset.mem_range.mp hm) h)
    rw [window_count_eq_indicator halpha0 halpha1,
      window_count_eq_indicator halpha0 halpha1] at hc
    have hxj : breakpoint alpha m ≤ phase alpha rho j := by
      by_contra hxj
      simp [hxi, hxj] at hc
    exact ⟨Finset.mem_image.mpr ⟨m, hm, rfl⟩, hxj⟩
  · rintro ⟨hx, hxj⟩
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
    have hc := congrArg (fun q : Nat => (q : Int))
      (window_counts_eq_of_factor_eq (Finset.mem_range.mp hm) h)
    rw [window_count_eq_indicator halpha0 halpha1,
      window_count_eq_indicator halpha0 halpha1] at hc
    have hxi : breakpoint alpha m ≤ phase alpha rho i := by
      by_contra hxi
      simp [hxi, hxj] at hc
    exact ⟨Finset.mem_image.mpr ⟨m, hm, rfl⟩, hxi⟩
private theorem rank_eq_of_factor_eq {alpha rho : Real}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) {n i j : Nat}
    (h : lowerMechanicalFactor alpha rho n i = lowerMechanicalFactor alpha rho n j) :
    rank alpha rho n i = rank alpha rho n j :=
  congrArg Finset.card (selected_eq_of_factor_eq halpha0 halpha1 h)
private theorem mem_breakpoints_Ioo {alpha : Real} (halpha : Irrational alpha)
    {n : Nat} {x : Real} (hx : x ∈ breakpoints alpha n) : x ∈ Ioo (0 : Real) 1 := by
  obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hx
  exact breakpoint_mem_Ioo halpha m
private theorem rank_eq_of_order_cut {alpha rho : Real} (halpha : Irrational alpha)
    {n r i : Nat} (hr : r ≤ n)
    (hcut : ∀ k : Fin n,
      (breakpoints alpha n).orderEmbOfFin (breakpoints_card halpha n) k ≤
        phase alpha rho i ↔ k < r) :
    rank alpha rho n i = r := by
  let e := (breakpoints alpha n).orderEmbOfFin (breakpoints_card halpha n)
  have heq : (breakpoints alpha n).filter (fun x => x ≤ phase alpha rho i) =
      (Finset.univ.filter fun k : Fin n => k < r).image e := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hxi⟩
      obtain ⟨k, rfl⟩ : x ∈ Set.range e := by
        rw [Finset.range_orderEmbOfFin]
        exact hx
      exact ⟨k, (hcut k).mp hxi, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem _ _ _, (hcut k).mpr hk⟩
  rw [rank, heq, Finset.card_image_of_injective _ e.injective, Fin.card_filter_val_lt,
    Nat.min_eq_right hr]
private theorem exists_rank_eq {alpha rho : Real} (halpha : Irrational alpha)
    (n r : Nat) (hr : r ≤ n) : ∃ i, rank alpha rho n i = r := by
  rcases n.eq_zero_or_pos with rfl | hn
  · have : r = 0 := by omega
    subst r
    exact ⟨0, by simp [rank, breakpoints]⟩
  let e := (breakpoints alpha n).orderEmbOfFin (breakpoints_card halpha n)
  rcases r.eq_zero_or_pos with rfl | hrpos
  · let zero : Fin n := ⟨0, hn⟩
    have hzero : e zero ∈ breakpoints alpha n := by
      exact Finset.orderEmbOfFin_mem (breakpoints alpha n) (breakpoints_card halpha n) zero
    have he0 := mem_breakpoints_Ioo halpha hzero
    obtain ⟨i, hi⟩ := exists_phase_mem_Ioo halpha (a := 0) (b := e ⟨0, hn⟩)
      le_rfl he0.1 he0.2.le
    refine ⟨i, rank_eq_of_order_cut halpha (Nat.zero_le n) fun k => ?_⟩
    simp only [Nat.not_lt_zero, iff_false, not_le]
    exact hi.2.trans_le (e.monotone (Fin.mk_le_mk.mpr (Nat.zero_le k.val)))
  · rcases eq_or_lt_of_le hr with rfl | hrlt
    · let last : Fin r := ⟨r - 1, by omega⟩
      have hlast : e last ∈ breakpoints alpha r := by
        exact Finset.orderEmbOfFin_mem (breakpoints alpha r) (breakpoints_card halpha r) last
      have helast := mem_breakpoints_Ioo halpha hlast
      obtain ⟨i, hi⟩ := exists_phase_mem_Ioo halpha (a := e last) (b := 1)
        helast.1.le helast.2 le_rfl
      refine ⟨i, rank_eq_of_order_cut halpha le_rfl fun k => ?_⟩
      simp only [Fin.is_lt, iff_true]
      exact (e.monotone (Fin.mk_le_mk.mpr (by omega))).trans hi.1.le
    · let lo : Fin n := ⟨r - 1, by omega⟩
      let hiIndex : Fin n := ⟨r, hrlt⟩
      have hlo := mem_breakpoints_Ioo halpha
        (Finset.orderEmbOfFin_mem (breakpoints alpha n) (breakpoints_card halpha n) lo)
      have hhi := mem_breakpoints_Ioo halpha
        (Finset.orderEmbOfFin_mem (breakpoints alpha n) (breakpoints_card halpha n) hiIndex)
      obtain ⟨i, hp⟩ := exists_phase_mem_Ioo halpha (a := e lo) (b := e hiIndex)
        hlo.1.le (e.strictMono (by simp [lo, hiIndex]; omega)) hhi.2.le
      refine ⟨i, rank_eq_of_order_cut halpha hr fun k => ?_⟩
      constructor
      · intro hk
        by_contra hkr
        exact (not_lt_of_ge hk) (hp.2.trans_le (e.monotone (Fin.mk_le_mk.mpr
          (Nat.le_of_not_gt hkr))))
      · intro hkr
        change k.val < r at hkr
        have hklo : k ≤ lo := Fin.mk_le_mk.mpr (by omega)
        exact (e.monotone hklo).trans hp.1.le
/-- Every irrational lower mechanical word has exactly `n + 1` length-`n` factors. -/
theorem lower_mechanical_factor_complexity {alpha rho : Real}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) (halpha_irr : Irrational alpha)
    (n : Nat) :
    (lowerMechanicalFactorSet alpha rho n).card = n + 1 := by
  classical
  let start : (w : ↥(lowerMechanicalFactorSet alpha rho n)) → Nat := fun w =>
    Classical.choose (mem_lowerMechanicalFactorSet.mp w.2)
  have hstart (w : ↥(lowerMechanicalFactorSet alpha rho n)) :
      w.1 = lowerMechanicalFactor alpha rho n (start w) :=
    Classical.choose_spec (mem_lowerMechanicalFactorSet.mp w.2)
  have hupper : (lowerMechanicalFactorSet alpha rho n).card ≤ n + 1 := by
    let encode : ↥(lowerMechanicalFactorSet alpha rho n) →
        ↥(Finset.univ : Finset (Fin (n + 1))) := fun w =>
      ⟨⟨rank alpha rho n (start w), Nat.lt_succ_of_le (rank_le halpha_irr n (start w))⟩,
        Finset.mem_univ _⟩
    have hencode : Function.Injective encode := by
      intro u v huv
      apply Subtype.ext
      rw [hstart u, hstart v]
      apply factor_eq_of_rank_eq halpha0 halpha1
      simpa [encode] using congrArg (fun x => x.1.1) huv
    simpa using Finset.card_le_card_of_injective hencode
  have hstarts (r : Fin (n + 1)) : ∃ i, rank alpha rho n i = r :=
    exists_rank_eq halpha_irr n r (Nat.le_of_lt_succ r.isLt)
  let startOfRank (r : Fin (n + 1)) : Nat := Classical.choose (hstarts r)
  have hstartOfRank (r : Fin (n + 1)) : rank alpha rho n (startOfRank r) = r :=
    Classical.choose_spec (hstarts r)
  have hlower : n + 1 ≤ (lowerMechanicalFactorSet alpha rho n).card := by
    let realize : ↥(Finset.univ : Finset (Fin (n + 1))) →
        ↥(lowerMechanicalFactorSet alpha rho n) := fun r =>
      ⟨lowerMechanicalFactor alpha rho n (startOfRank r),
        mem_lowerMechanicalFactorSet.mpr ⟨startOfRank r, rfl⟩⟩
    have hrealize : Function.Injective realize := by
      intro r s hrs
      apply Subtype.ext
      apply Fin.ext
      rw [← hstartOfRank r, ← hstartOfRank s]
      exact rank_eq_of_factor_eq halpha0 halpha1 (congrArg Subtype.val hrs)
    simpa using Finset.card_le_card_of_injective hrealize
  exact Nat.le_antisymm hupper hlower
private theorem golden_small_cases :
    ∀ n : Fin 5, (lowerMechanicalFactorSet Real.goldenRatio⁻¹ 0 n).card = n + 1 := by
  intro n
  exact lower_mechanical_factor_complexity (rho := 0)
    (inv_nonneg.mpr Real.goldenRatio_pos.le) (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)
    Real.goldenRatio_irrational.inv n
#print axioms lowerMechanicalFactorSet
#print axioms lower_mechanical_factor_complexity
end D5.S1.Words.Mechanical
