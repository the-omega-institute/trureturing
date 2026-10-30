/- GID: D5/S3/Combinatorics/Circle/IsolatedSmallSource
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/IsolatedSmallSource
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic]
   utility: none
   digest: A centered doubling permutation with isolated SMALL labels of one sign admits a full half-strip ordering. -/
import D5.S3.Combinatorics.Circle.SmallStepOrdering
import D5.S3.Combinatorics.Circle.TwoSmallSource
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Chain

/-! # Full inventory ordering for isolated SMALL labels of one sign -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.IsolatedSmallSource
open SourceWidth ExpandingSourcePath
open scoped BigOperators

private def mass {α : Type*} (w : α → ℤ) (L : List α) : ℤ := (L.map w).sum

private theorem mass_flatMap {α β : Type*} (w : β → ℤ) (packet : α → List β)
    (L : List α) : mass w (L.flatMap packet) = (L.map (fun i => mass w (packet i))).sum := by
  induction L with
  | nil => simp [mass]
  | cons i L ih => simp [mass, List.flatMap_cons, List.map_append, List.sum_append, mass] at *; omega

private theorem order_packets {α β : Type*} [DecidableEq α]
    (w : β → ℤ) (packet : α → List β) (tag : α → Prop)
    (N C : ℤ) (hN : 0 < N) (hC : 2 * C = N - 1)
    (fuel : ℕ) (roots : List α) (h : ℤ)
    (hlen : roots.length ≤ fuel)
    (hh : 0 ≤ h) (hwide : 168 * h < 13 * N)
    (hbalance : h + mass w (roots.flatMap packet) = 0)
    (hT : ∀ i ∈ roots, tag i →
      0 ≤ mass w (packet i) ∧ 24 * mass w (packet i) < N ∧
      ∀ v : ℤ, 0 ≤ v → 28 * v < N → InStrip w C v (packet i))
    (hU : ∀ i ∈ roots, ¬tag i →
      mass w (packet i) ≤ 0 ∧ 28 * (-mass w (packet i)) ≤ N ∧
      ∀ v : ℤ, 0 ≤ v → 168 * v < 13 * N →
        0 ≤ v + mass w (packet i) → InStrip w C v (packet i)) :
    ∃ word : List β, word.Perm (roots.flatMap packet) ∧ InStrip w C h word := by
  classical
  induction fuel generalizing roots h with
  | zero =>
    have he : roots = [] := List.length_eq_zero_iff.mp (by omega)
    subst roots
    refine ⟨[], .refl _, ?_⟩
    simp only [List.flatMap_nil, mass, List.map_nil, List.sum_nil, add_zero] at hbalance
    simp only [InStrip]
    constructor <;> omega
  | succ fuel ih =>
    by_cases hempty : roots = []
    · subst roots
      refine ⟨[], .refl _, ?_⟩
      simp only [List.flatMap_nil, mass, List.map_nil, List.sum_nil, add_zero] at hbalance
      simp only [InStrip]
      constructor <;> omega
    have hchoice : ∃ i ∈ roots,
        InStrip w C h (packet i) ∧ 0 ≤ h + mass w (packet i) ∧
        168 * (h + mass w (packet i)) < 13 * N := by
      by_cases hfit : ∃ i ∈ roots, ¬tag i ∧ 0 ≤ h + mass w (packet i)
      · obtain ⟨i, hi, htag, hpay⟩ := hfit
        obtain ⟨hnonpos, _, hs⟩ := hU i hi htag
        exact ⟨i, hi, hs h hh hwide hpay, hpay, by omega⟩
      · have hlow : 28 * h < N := by
          by_cases hu : ∃ i ∈ roots, ¬tag i
          · obtain ⟨i, hi, htag⟩ := hu
            have hfail : h + mass w (packet i) < 0 := by
              by_contra hn
              exact hfit ⟨i, hi, htag, by omega⟩
            have hb := (hU i hi htag).2.1
            omega
          · have hnonneg : ∀ i ∈ roots, 0 ≤ mass w (packet i) := by
              intro i hi
              have ht : tag i := by by_contra hn; exact hu ⟨i, hi, hn⟩
              exact (hT i hi ht).1
            have hs : 0 ≤ mass w (roots.flatMap packet) := by
              rw [mass_flatMap]
              apply List.sum_nonneg
              intro z hz
              obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
              exact hnonneg i hi
            omega
        have hexT : ∃ i ∈ roots, tag i := by
          by_contra ht
          obtain ⟨i, L, rfl⟩ := List.exists_cons_of_ne_nil hempty
          have hall : ∀ j ∈ i :: L, ¬tag j := by
            intro j hj hjt
            exact ht ⟨j, hj, hjt⟩
          have hni := (hU i (by simp) (hall i (by simp))).1
          have hfail : h + mass w (packet i) < 0 := by
            by_contra hn
            exact hfit ⟨i, by simp, hall i (by simp), by omega⟩
          have htail : mass w (L.flatMap packet) ≤ 0 := by
            rw [mass_flatMap]
            calc
              (L.map (fun j => mass w (packet j))).sum ≤
                  (L.map (fun _ => (0 : ℤ))).sum := by
                apply List.sum_le_sum
                intro j hj
                exact (hU j (by simp [hj]) (hall j (by simp [hj]))).1
              _ = 0 := by simp
          simp only [List.flatMap_cons, mass, List.map_append, List.sum_append] at hbalance
          dsimp only [mass] at htail hfail
          omega
        obtain ⟨i, hi, htag⟩ := hexT
        obtain ⟨hnet, hnetbound, hs⟩ := hT i hi htag
        refine ⟨i, hi, hs h hh hlow, by omega, ?_⟩
        omega
    obtain ⟨i, hi, hstrip, hnext, hnextwide⟩ := hchoice
    have hp := List.perm_cons_erase hi
    have hparts := hp.flatMap_right packet
    have hmass := (hparts.map w).sum_eq
    simp only [List.flatMap_cons, List.map_append, List.sum_append] at hmass
    obtain ⟨word, hw, hs⟩ := ih (roots.erase i) (h + mass w (packet i))
      (by have := List.length_erase_add_one hi; omega) hnext hnextwide
      (by dsimp only [mass] at *; omega)
      (fun j hj => hT j (List.mem_of_mem_erase hj))
      (fun j hj => hU j (List.mem_of_mem_erase hj))
    refine ⟨packet i ++ word, ?_, inStrip_append hstrip hs⟩
    exact (List.Perm.append_left _ hw).trans hparts.symm


private def packet {α : Type*} (σ : Equiv.Perm α) (w : α → ℤ) (Q : ℤ)
    (i : α) : List α :=
  if |w (σ (σ i))| < Q then [i, σ (σ i), σ i] else [i, σ i]

private theorem packet_inventory {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (w : α → ℤ) (Q : ℤ) (hQ : 0 < Q)
    (hnonzero : ∀ i, w i ≠ 0)
    (hsmall : ∀ i, |w i| < Q → 0 < w i)
    (hsmallstep : ∀ i, |w i| < Q → Q ≤ w (σ i))
    (hnegative : ∀ i, w i < 0 → 0 < w (σ i))
    (hlarge : ∀ i, Q ≤ w i → w (σ i) < 0) :
    ((Finset.univ.filter (fun i => Q ≤ w i)).toList.flatMap (packet σ w Q)).Perm
      (Finset.univ.toList : List α) := by
  classical
  let roots := (Finset.univ.filter (fun i => Q ≤ w i)).toList
  let owner (x : α) :=
    if Q ≤ w x then x else if w x < 0 then σ.symm x else σ.symm (σ.symm x)
  have hroot (i : α) : i ∈ roots ↔ Q ≤ w i := by simp [roots]
  have howner (i : α) (hi : i ∈ roots) (x : α) (hx : x ∈ packet σ w Q i) :
      owner x = i := by
    have hp := (hroot i).mp hi
    have hn := hlarge i hp
    have hz := hnegative (σ i) hn
    have hnQ : ¬Q ≤ w (σ i) := by omega
    by_cases ht : |w (σ (σ i))| < Q
    · have hzQ : ¬Q ≤ w (σ (σ i)) := by have := abs_lt.mp ht; omega
      simp only [packet, if_pos ht, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · simp [owner, hp]
      · simp [owner, hzQ, show ¬w (σ (σ i)) < 0 by omega]
      · simp [owner, hnQ, hn]
    · simp only [packet, if_neg ht, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · simp [owner, hp]
      · simp [owner, hnQ, hn]
  have hnpacket (i : α) (hi : i ∈ roots) : (packet σ w Q i).Nodup := by
    have hp := (hroot i).mp hi
    have hn := hlarge i hp
    have hz := hnegative (σ i) hn
    have hin : i ≠ σ i := by intro he; rw [← he] at hn; omega
    have hzn : σ (σ i) ≠ σ i := by intro he; rw [he] at hz; omega
    by_cases ht : |w (σ (σ i))| < Q
    · have hiz : i ≠ σ (σ i) := by
        intro he
        have hb := abs_lt.mp ht
        rw [← he] at hb
        omega
      simp [packet, ht, hin, hiz, hzn]
    · simp [packet, ht, hin]
  have hnodup : (roots.flatMap (packet σ w Q)).Nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨hnpacket, ?_⟩
    have hrn : roots.Nodup := Finset.nodup_toList _
    apply List.pairwise_iff_getElem.mpr
    intro a b ha hb hab
    apply List.disjoint_left.mpr
    intro x hxa hxb
    have hi : roots[a] = roots[b] :=
      (howner _ (List.getElem_mem ha) x hxa).symm.trans
        (howner _ (List.getElem_mem hb) x hxb)
    exact (ne_of_lt hab) (hrn.getElem_inj_iff.mp hi)
  have hcomplete (x : α) : x ∈ roots.flatMap (packet σ w Q) := by
    by_cases hxroot : Q ≤ w x
    · apply List.mem_flatMap.mpr
      refine ⟨x, (hroot x).mpr hxroot, ?_⟩
      unfold packet
      split_ifs <;> simp
    · by_cases hxneg : w x < 0
      · let i := σ.symm x
        have histep : σ i = x := σ.apply_symm_apply x
        have hi : Q ≤ w i := by
          by_contra hi
          have hilt : w i < Q := by omega
          by_cases hin : w i < 0
          · have hh := hnegative i hin
            rw [histep] at hh
            omega
          · have hinp : 0 < w i := by have := hnonzero i; omega
            have his : |w i| < Q := by rw [abs_of_pos hinp]; exact hilt
            have hh := hsmallstep i his
            rw [histep] at hh
            omega
        apply List.mem_flatMap.mpr
        refine ⟨i, (hroot i).mpr hi, ?_⟩
        unfold packet
        split_ifs <;> simp [histep]
      · have hxpos : 0 < w x := by have := hnonzero x; omega
        have hxsmall : |w x| < Q := by rw [abs_of_pos hxpos]; omega
        let n := σ.symm x
        let i := σ.symm n
        have hnstep : σ n = x := σ.apply_symm_apply x
        have histep : σ i = n := σ.apply_symm_apply n
        have hnneg : w n < 0 := by
          by_contra hn
          have hnp : 0 < w n := by have := hnonzero n; omega
          by_cases hnr : Q ≤ w n
          · have hh := hlarge n hnr
            rw [hnstep] at hh
            omega
          · have hns : |w n| < Q := by rw [abs_of_pos hnp]; omega
            have hh := hsmallstep n hns
            rw [hnstep] at hh
            have hx := abs_lt.mp hxsmall
            omega
        have hi : Q ≤ w i := by
          by_contra hi
          by_cases hin : w i < 0
          · have hh := hnegative i hin
            rw [histep] at hh
            omega
          · have hip : 0 < w i := by have := hnonzero i; omega
            have his : |w i| < Q := by rw [abs_of_pos hip]; omega
            have hh := hsmallstep i his
            rw [histep] at hh
            omega
        apply List.mem_flatMap.mpr
        refine ⟨i, (hroot i).mpr hi, ?_⟩
        have htwo : σ (σ i) = x := by rw [histep, hnstep]
        simp [packet, htwo, hxsmall]
  apply (List.perm_ext_iff_of_nodup hnodup (Finset.nodup_toList _)).mpr
  intro x
  simp only [Finset.mem_toList, Finset.mem_univ, iff_true]
  exact hcomplete x


private theorem isolated_geometry
    {α : Type*} [Fintype α] [Nonempty α]
    (σ : Equiv.Perm α) (w : α → ℤ) (Q N C : ℤ)
    (hQ : 2 ≤ Q) (hN : N = 4 * Q - 1) (hC : C = 2 * Q - 1)
    (hbound : ∀ i, -C ≤ w i ∧ w i ≤ C)
    (hstep : ∀ i, w (σ i) = doubleStep N (w i))
    (hsmall : ∀ i, |w i| < Q → 0 ≤ w i)
    (hisolated : ∀ i, |w i| < Q → Q ≤ |w (σ i)|) :
    (∀ i, w i ≠ 0) ∧
    (∀ i, |w i| < Q →
      0 < w i ∧ w (σ i) = 2 * w i ∧ 6 * w i < N ∧ N ≤ 7 * w i) ∧
    (∀ i, w i < 0 → Q ≤ -w i ∧ w (σ i) = 2 * w i + N ∧ 0 < w (σ i)) ∧
    (∀ i, Q ≤ w i →
      w (σ i) = 2 * w i - N ∧ w (σ i) < 0 ∧
      w (σ (σ i)) = 4 * w i - N ∧ 0 < w (σ (σ i)) ∧
      2 * N ≤ 7 * w i ∧ 3 * w i ≤ N) := by
  classical
  have hNpos : 0 < N := by omega
  have nonzero (i : α) : w i ≠ 0 := by
    intro hi
    have hs : |w i| < Q := by rw [hi, abs_zero]; omega
    have hz : w (σ i) = 0 := by
      have ht := hstep i
      simp only [hi, doubleStep] at ht
      split_ifs at ht <;> omega
    have hh := hisolated i hs
    rw [hz, abs_zero] at hh
    omega
  have smallPos (i : α) (hi : |w i| < Q) : 0 < w i := by
    have := hsmall i hi
    have := nonzero i
    omega
  have smallStep (i : α) (hi : |w i| < Q) : w (σ i) = 2 * w i := by
    have hb := abs_lt.mp hi
    have ht := hstep i
    rw [doubleStep] at ht
    split_ifs at ht <;> omega
  have negativeStep (i : α) (hi : w i < 0) :
      Q ≤ -w i ∧ w (σ i) = 2 * w i + N ∧ 0 < w (σ i) := by
    have hlarge : Q ≤ -w i := by
      by_contra hh
      have hs : |w i| < Q := by rw [abs_of_neg hi]; omega
      have := hsmall i hs
      omega
    have ht := hstep i
    rw [doubleStep, if_neg (by omega : ¬N < 4 * w i),
      if_pos (by omega : 4 * w i < -N)] at ht
    have hb := hbound i
    exact ⟨hlarge, ht, by omega⟩
  have largeStep (i : α) (hi : Q ≤ w i) :
      w (σ i) = 2 * w i - N ∧ w (σ i) < 0 ∧
      w (σ (σ i)) = 4 * w i - N ∧ 0 < w (σ (σ i)) := by
    have ht := hstep i
    rw [doubleStep, if_pos (by omega : N < 4 * w i)] at ht
    have hb := hbound i
    have hn : w (σ i) < 0 := by omega
    obtain ⟨_, ht2, hp2⟩ := negativeStep (σ i) hn
    exact ⟨ht, hn, by omega, hp2⟩
  obtain ⟨i0, hi0⟩ : ∃ i, 0 < w i := by
    let a : α := Classical.arbitrary α
    by_cases ha : 0 < w a
    · exact ⟨a, ha⟩
    · have hn : w a < 0 := by have := nonzero a; omega
      exact ⟨σ a, (negativeStep a hn).2.2⟩
  let Pos : Finset α := Finset.univ.filter (fun i => 0 < w i)
  have memPos (i : α) : i ∈ Pos ↔ 0 < w i := by simp [Pos]
  have hPos : Pos.Nonempty := ⟨i0, (memPos i0).2 hi0⟩
  obtain ⟨imax, himem, himax⟩ := Pos.exists_max_image w hPos
  have himaxPos : 0 < w imax := (memPos imax).1 himem
  have himaxLarge : Q ≤ w imax := by
    by_contra hh
    have hs : |w imax| < Q := by rw [abs_of_pos himaxPos]; omega
    have ht := smallStep imax hs
    have hnext : 0 < w (σ imax) := by omega
    have hm := himax (σ imax) ((memPos _).2 hnext)
    omega
  obtain ⟨_, _, hmax2, hmax2Pos⟩ := largeStep imax himaxLarge
  have hmax2le := himax (σ (σ imax)) ((memPos _).2 hmax2Pos)
  have hmaxBound : 3 * w imax ≤ N := by omega
  have positiveUpper (i : α) (hi : 0 < w i) : 3 * w i ≤ N := by
    have hm := himax i ((memPos i).2 hi)
    omega
  have smallUpper (i : α) (hi : |w i| < Q) : 6 * w i < N := by
    have hp := smallPos i hi
    have ht := smallStep i hi
    have hnext : 0 < w (σ i) := by omega
    have hu := positiveUpper (σ i) hnext
    omega
  have smallLower (i : α) (hi : |w i| < Q) : N ≤ 7 * w i := by
    let Small : Finset α := Finset.univ.filter (fun j => |w j| < Q)
    have memSmall (j : α) : j ∈ Small ↔ |w j| < Q := by simp [Small]
    have hSmall : Small.Nonempty := ⟨i, (memSmall i).2 hi⟩
    obtain ⟨imin, hm, hmin⟩ := Small.exists_min_image w hSmall
    have hmSmall := (memSmall imin).1 hm
    have hmPos := smallPos imin hmSmall
    have hmStep := smallStep imin hmSmall
    have hmNextPos : 0 < w (σ imin) := by omega
    have hmNextLarge : Q ≤ w (σ imin) := by
      have hh := hisolated imin hmSmall
      rwa [abs_of_pos hmNextPos] at hh
    have minPositive (j : α) (hj : 0 < w j) : w imin ≤ w j := by
      by_cases hs : |w j| < Q
      · exact hmin j ((memSmall j).2 hs)
      · rw [abs_of_pos hj] at hs
        have hb := abs_lt.mp hmSmall
        omega
    obtain ⟨_, _, hthird, hthirdPos⟩ := largeStep (σ imin) hmNextLarge
    have htmin := minPositive (σ (σ (σ imin))) hthirdPos
    have hmi := hmin i ((memSmall i).2 hi)
    omega
  let Roots : Finset α := Finset.univ.filter (fun i => Q ≤ w i)
  have memRoots (i : α) : i ∈ Roots ↔ Q ≤ w i := by simp [Roots]
  have hRoots : Roots.Nonempty := ⟨imax, (memRoots imax).2 himaxLarge⟩
  obtain ⟨rmin, hrmem, hrmin⟩ := Roots.exists_min_image w hRoots
  have hrLarge := (memRoots rmin).1 hrmem
  obtain ⟨_, _, hr2, hr2Pos⟩ := largeStep rmin hrLarge
  have hrootLower : 2 * N ≤ 7 * w rmin := by
    by_cases hs : |w (σ (σ rmin))| < Q
    · have hl := smallLower (σ (σ rmin)) hs
      omega
    · rw [abs_of_pos hr2Pos] at hs
      have hr2Large : Q ≤ w (σ (σ rmin)) := by omega
      have hm := hrmin (σ (σ rmin)) ((memRoots _).2 hr2Large)
      omega
  refine ⟨nonzero, ?_, negativeStep, ?_⟩
  · intro i hi
    exact ⟨smallPos i hi, smallStep i hi, smallUpper i hi, smallLower i hi⟩
  · intro i hi
    obtain ⟨hs, hn, hs2, hp2⟩ := largeStep i hi
    have hm := hrmin i ((memRoots i).2 hi)
    have hp : 0 < w i := by omega
    exact ⟨hs, hn, hs2, hp2, by omega, positiveUpper i hp⟩

private theorem positive_completion {α : Type*} [Fintype α] [Nonempty α]
    (σ : Equiv.Perm α) (w : α → ℤ) (Q N C : ℤ)
    (hQ : 2 ≤ Q) (hN : N = 4 * Q - 1) (hC : C = 2 * Q - 1)
    (hbound : ∀ i, -C ≤ w i ∧ w i ≤ C)
    (hstep : ∀ i, w (σ i) = doubleStep N (w i))
    (hsmall : ∀ i, |w i| < Q → 0 ≤ w i)
    (hisolated : ∀ i, |w i| < Q → Q ≤ |w (σ i)|) :
    ∃ word : List α, word.Perm (Finset.univ.toList : List α) ∧
      InStrip w C 0 word ∧ (word.map w).sum = 0 := by
  classical
  obtain ⟨hnz, hs, hn, hp⟩ := isolated_geometry σ w Q N C hQ hN hC
    hbound hstep hsmall hisolated
  let roots := (Finset.univ.filter (fun i => Q ≤ w i)).toList
  have hroot (i : α) : i ∈ roots ↔ Q ≤ w i := by simp [roots]
  have hpartition := packet_inventory σ w Q (by omega) hnz
    (fun i hi => (hs i hi).1)
    (fun i hi => by
      have hz := (hs i hi).1
      have he := (hs i hi).2.1
      have hh := hisolated i hi
      rw [abs_of_pos (by omega : 0 < w (σ i))] at hh
      exact hh)
    (fun i hi => (hn i hi).2.2)
    (fun i hi => (hp i hi).2.1)
  have hNpos : 0 < N := by omega
  have hhalf : N / 2 = C := by omega
  let potential (i : α) := w i + if w i < 0 then N else 0
  have hpotential (i : α) : potential (σ i) - potential i = w i := by
    have hh := unsigned_step hNpos (show N % 2 = 1 by omega)
      (show -(N / 2) ≤ w i ∧ w i ≤ N / 2 by rw [hhalf]; exact hbound i)
    simpa only [← hstep i, potential] using hh
  have hzero : ∑ i, w i = 0 := by
    have hh : (∑ i, (potential (σ i) - potential i)) = ∑ i, w i :=
      Finset.sum_congr rfl (fun i _ => hpotential i)
    rw [Finset.sum_sub_distrib, Equiv.sum_comp σ potential, sub_self] at hh
    exact hh.symm
  have hmass : mass w (roots.flatMap (packet σ w Q)) = 0 := by
    have he := (hpartition.map w).sum_eq
    simpa [mass, roots, Finset.sum_map_toList, hzero] using he
  have hT (i : α) (hi : i ∈ roots) (ht : |w (σ (σ i))| < Q) :
      0 ≤ mass w (packet σ w Q i) ∧
      24 * mass w (packet σ w Q i) < N ∧
      ∀ v : ℤ, 0 ≤ v → 28 * v < N → InStrip w C v (packet σ w Q i) := by
    obtain ⟨he, hneg, he2, hpos, hlo, hhi⟩ := hp i ((hroot i).mp hi)
    obtain ⟨hrpos, _, hrupper, hrlower⟩ := hs (σ (σ i)) ht
    have hm : mass w (packet σ w Q i) = w i + w (σ (σ i)) + w (σ i) := by
      simp [packet, ht, mass]; ring
    refine ⟨by rw [hm]; omega, by rw [hm]; omega, ?_⟩
    intro v hv hvsmall
    simp only [packet, if_pos ht, InStrip]
    constructor
    · exact hv
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    constructor <;> omega
  have hU (i : α) (hi : i ∈ roots) (ht : ¬|w (σ (σ i))| < Q) :
      mass w (packet σ w Q i) ≤ 0 ∧
      28 * (-mass w (packet σ w Q i)) ≤ N ∧
      ∀ v : ℤ, 0 ≤ v → 168 * v < 13 * N →
        0 ≤ v + mass w (packet σ w Q i) → InStrip w C v (packet σ w Q i) := by
    obtain ⟨he, hneg, he2, hpos, hlo, hhi⟩ := hp i ((hroot i).mp hi)
    have hnextlarge : Q ≤ w (σ (σ i)) := by rw [abs_of_pos hpos] at ht; omega
    have hnextlower := (hp (σ (σ i)) hnextlarge).2.2.2.2.1
    have hm : mass w (packet σ w Q i) = 3 * w i - N := by simp [packet, ht, mass, he]; ring
    refine ⟨by rw [hm]; omega, by rw [hm]; omega, ?_⟩
    intro v hv hvwide hend
    rw [hm] at hend
    simp only [packet, if_neg ht, InStrip]
    constructor
    · exact hv
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    constructor <;> omega
  obtain ⟨word, hw, hstrip⟩ := order_packets w (packet σ w Q)
    (fun i => |w (σ (σ i))| < Q) N C hNpos (by omega)
    roots.length roots 0 (le_refl _) (le_refl _) (by omega)
    (by simpa using hmass) hT hU
  refine ⟨word, hw.trans hpartition, hstrip, ?_⟩
  have he := (hw.map w).sum_eq
  exact he.trans hmass

/-- Every physical occurrence is retained. SMALL labels may be arbitrarily many;
only their common sign and the absence of consecutive SMALL labels are assumed. -/
theorem finite_isolated_small_completion {α : Type*} [Fintype α] [Nonempty α]
    (σ : Equiv.Perm α) (w : α → ℤ) (Q : ℤ) (hQ : 2 ≤ Q)
    (hbound : ∀ i, -(2 * Q - 1) ≤ w i ∧ w i ≤ 2 * Q - 1)
    (hstep : ∀ i, w (σ i) = doubleStep (4 * Q - 1) (w i))
    (hsmall : (∀ i, |w i| < Q → 0 ≤ w i) ∨ (∀ i, |w i| < Q → w i ≤ 0))
    (hisolated : ∀ i, |w i| < Q → Q ≤ |w (σ i)|) :
    ∃ word : List α, word.Perm (Finset.univ.toList : List α) ∧
      InStrip w (2 * Q - 1) 0 word ∧ (word.map w).sum = 0 := by
  classical
  rcases hsmall with hsmall | hsmall
  · exact positive_completion σ w Q (4 * Q - 1) (2 * Q - 1)
      hQ rfl rfl hbound hstep hsmall hisolated
  · obtain ⟨word, hw, hs, hm⟩ := positive_completion σ (fun i => -w i)
      Q (4 * Q - 1) (2 * Q - 1) hQ rfl rfl
      (fun i => by have := hbound i; constructor <;> omega)
      (fun i => by rw [ExpandingSourcePath.doubleStep_neg (by omega), ← hstep i])
      (fun i hi => by have := hsmall i (by simpa using hi); omega)
      (fun i hi => by simpa using hisolated i (by simpa using hi))
    obtain ⟨j, _, hj⟩ := TwoSmallSource.negate_rotation (fun i => -w i)
      (2 * Q - 1) word hs hm
    refine ⟨word.rotate j, (List.rotate_perm word j).trans hw, ?_, ?_⟩
    · apply MixedSuffixEnergy.strip_of_all_prefixes
      intro n
      simpa only [neg_neg, MixedSuffixEnergy.mass, zero_add] using hj n
    · have he := ((List.rotate_perm word j).map w).sum_eq
      have hz : (word.map w).sum = 0 := by
        have hh := sum_neg_map w word
        omega
      exact he.trans hz


/-- Swap precisely the negative/SMALL adjacent pairs of physical labels. -/
private noncomputable def isolatedSwap {α : Type*} (σ : Equiv.Perm α)
    (w : α → ℤ) (Q : ℤ) (i : α) : α :=
  if w i < 0 ∧ |w (σ i)| < Q then σ i
  else if |w i| < Q then σ.symm i else i

/-- The correction on SMALL phases accounts for the adjacent label swap. -/
private noncomputable def isolatedPotential {α : Type*} (σ : Equiv.Perm α)
    (w : α → ℤ) (Q N : ℤ) (i : α) : ℤ :=
  if |w i| < Q then 2 * w i - w (σ.symm i)
  else w i + if w i < 0 then N else 0

private theorem isolated_predecessors {α : Type*}
    (σ : Equiv.Perm α) (w : α → ℤ) (Q : ℤ) (hQ : 0 < Q)
    (hnz : ∀ i, w i ≠ 0)
    (hs : ∀ i, |w i| < Q → 0 < w i ∧ Q ≤ w (σ i))
    (hn : ∀ i, w i < 0 → 0 < w (σ i))
    (hp : ∀ i, Q ≤ w i → w (σ i) < 0) :
    (∀ i, w i < 0 → Q ≤ w (σ.symm i)) ∧
    (∀ i, |w i| < Q → w (σ.symm i) < 0) := by
  have negpred (i : α) (hi : w i < 0) : Q ≤ w (σ.symm i) := by
    by_contra hh
    by_cases ht : w (σ.symm i) < 0
    · have := hn (σ.symm i) ht
      simp only [σ.apply_symm_apply] at this
      omega
    · have hz := hnz (σ.symm i)
      have hpos : 0 < w (σ.symm i) := by omega
      have hsmall : |w (σ.symm i)| < Q := by rw [abs_of_pos hpos]; omega
      have := (hs (σ.symm i) hsmall).2
      simp only [σ.apply_symm_apply] at this
      omega
  refine ⟨negpred, ?_⟩
  intro i hi
  by_contra hh
  have hz := hnz (σ.symm i)
  have hpos : 0 < w (σ.symm i) := by omega
  by_cases ht : Q ≤ w (σ.symm i)
  · have := hp (σ.symm i) ht
    simp only [σ.apply_symm_apply] at this
    have := (hs i hi).1
    omega
  · have ht' : |w (σ.symm i)| < Q := by rw [abs_of_pos hpos]; omega
    have := (hs (σ.symm i) ht').2
    simp only [σ.apply_symm_apply] at this
    have := abs_lt.mp hi
    omega

private theorem isolated_potential_geometry
    {α : Type*} [Fintype α] [Nonempty α]
    (σ : Equiv.Perm α) (w : α → ℤ) (Q N C : ℤ)
    (hQ : 2 ≤ Q) (hN : N = 4 * Q - 1) (hC : C = 2 * Q - 1)
    (hbound : ∀ i, -C ≤ w i ∧ w i ≤ C)
    (hstep : ∀ i, w (σ i) = doubleStep N (w i))
    (hsmall : ∀ i, |w i| < Q → 0 ≤ w i)
    (hisolated : ∀ i, |w i| < Q → Q ≤ |w (σ i)|) :
    ∃ o : α, Q ≤ w o ∧
      (∀ i, isolatedSwap σ w Q (isolatedSwap σ w Q i) = i) ∧
      (∀ i, isolatedPotential σ w Q N (σ i) - isolatedPotential σ w Q N i =
        w (isolatedSwap σ w Q i)) ∧
      (∀ i, 0 ≤ isolatedPotential σ w Q N i - w o ∧
        28 * (isolatedPotential σ w Q N i - w o) < 13 * N) := by
  classical
  obtain ⟨hnz, hs, hn, hp⟩ := isolated_geometry σ w Q N C hQ hN hC
    hbound hstep hsmall hisolated
  have hslarge (i : α) (hi : |w i| < Q) : Q ≤ w (σ i) := by
    have hpos := (hs i hi).1
    have he := (hs i hi).2.1
    have hh := hisolated i hi
    rwa [abs_of_pos (by omega : 0 < w (σ i))] at hh
  obtain ⟨negpred, smallpred⟩ := isolated_predecessors σ w Q (by omega) hnz
    (fun i hi => ⟨(hs i hi).1, hslarge i hi⟩)
    (fun i hi => (hn i hi).2.2) (fun i hi => (hp i hi).2.1)
  have neglarge (i : α) (hi : w i < 0) : ¬|w i| < Q := by
    have := (hn i hi).1
    rw [abs_of_neg hi]
    omega
  have rootlarge (i : α) (hi : Q ≤ w i) : ¬|w i| < Q := by
    rw [abs_of_pos (by omega : 0 < w i)]
    omega
  have hex : ∃ i, Q ≤ w i := by
    let a : α := Classical.arbitrary α
    by_cases ha : Q ≤ w a
    · exact ⟨a, ha⟩
    by_cases hn' : w a < 0
    · exact ⟨σ.symm a, negpred a hn'⟩
    · have hz := hnz a
      have ha' : |w a| < Q := by rw [abs_of_pos (by omega : 0 < w a)]; omega
      exact ⟨σ a, hslarge a ha'⟩
  let roots : Finset α := Finset.univ.filter (fun i => Q ≤ w i)
  obtain ⟨a, ha⟩ := hex
  obtain ⟨o, ho, hmin⟩ := roots.exists_min_image w ⟨a, by simpa [roots] using ha⟩
  have ho' : Q ≤ w o := by simpa [roots] using ho
  have hmin' (i : α) (hi : Q ≤ w i) : w o ≤ w i :=
    hmin i (by simpa [roots] using hi)
  refine ⟨o, ho', ?_, ?_, ?_⟩
  · intro i
    by_cases hi : |w i| < Q
    · have hipos := (hs i hi).1
      have hin := smallpred i hi
      have hinlarge := neglarge (σ.symm i) hin
      simp [isolatedSwap, hi, show ¬w i < 0 by omega, hin]
    · by_cases ht : w i < 0 ∧ |w (σ i)| < Q
      · have hnextpos := (hs (σ i) ht.2).1
        simp [isolatedSwap, ht, show ¬w (σ i) < 0 by omega, ht.2]
      · simp [isolatedSwap, ht, hi]
  · intro i
    by_cases hi : |w i| < Q
    · have hipos := (hs i hi).1
      have hn' := smallpred i hi
      have hnlarge := neglarge (σ.symm i) hn'
      have hsnext := hslarge i hi
      have he := (hs i hi).2.1
      have ht := (hn (σ.symm i) hn').2.1
      simp only [σ.apply_symm_apply] at ht
      simp only [isolatedPotential, if_pos hi, if_neg (rootlarge (σ i) hsnext),
        if_neg (show ¬w (σ i) < 0 by omega), add_zero, isolatedSwap,
        if_neg (show ¬(w i < 0 ∧ |w (σ i)| < Q) by omega)]
      omega
    · by_cases hn' : w i < 0
      · have he := (hn i hn').2.1
        have hnextpos := (hn i hn').2.2
        by_cases ht : |w (σ i)| < Q
        · simp [isolatedPotential, hi, ht, hn', isolatedSwap]
          omega
        · simp only [isolatedPotential, if_neg hi, if_neg ht, if_pos hn',
            if_neg (show ¬w (σ i) < 0 by omega), add_zero, isolatedSwap,
            if_neg (show ¬(w i < 0 ∧ |w (σ i)| < Q) by tauto)]
          omega
      · have hz := hnz i
        have hi' : Q ≤ w i := by rw [abs_of_pos (by omega : 0 < w i)] at hi; omega
        have hnnext := (hp i hi').2.1
        have he := (hp i hi').1
        simp [isolatedPotential, hi, neglarge (σ i) hnnext, hn', hnnext, isolatedSwap]
        omega
  · intro i
    have horoot := hp o ho'
    by_cases hi : |w i| < Q
    · have hn' := smallpred i hi
      have hr := negpred (σ.symm i) hn'
      have hminr := hmin' (σ.symm (σ.symm i)) hr
      have he1 := (hn (σ.symm i) hn').2.1
      have he2 := (hp (σ.symm (σ.symm i)) hr).1
      have hsmall' := hs i hi
      simp only [σ.apply_symm_apply] at he1 he2
      simp only [isolatedPotential, if_pos hi]
      constructor <;> omega
    · by_cases hn' : w i < 0
      · have hr := negpred i hn'
        have hminr := hmin' (σ.symm i) hr
        have he := (hp (σ.symm i) hr)
        simp only [σ.apply_symm_apply] at he
        simp only [isolatedPotential, if_neg hi, if_pos hn']
        constructor <;> omega
      · have hz := hnz i
        have hr : Q ≤ w i := by rw [abs_of_pos (by omega : 0 < w i)] at hi; omega
        have hminr := hmin' i hr
        have he := hp i hr
        simp only [isolatedPotential, if_neg hi, if_neg hn', add_zero]
        constructor <;> omega


/-- Along a physical successor chain, each moved pair has one label of each
size. Removing successive pairs proves the two filtered orders separately. -/
private theorem isolated_swap_chain {α : Type*}
    (σ : Equiv.Perm α) (w : α → ℤ) (Q : ℤ)
    (hsmallpos : ∀ i, |w i| < Q → 0 < w i)
    (hsmallnext : ∀ i, |w i| < Q → ¬|w (σ i)| < Q)
    (hsmallpred : ∀ i, |w i| < Q → w (σ.symm i) < 0)
    (fuel : ℕ) (L : List α) (o : α)
    (hlen : L.length ≤ fuel)
    (hchain : (L ++ [o]).IsChain (fun i j => σ i = j))
    (hstart : ∀ a, L.head? = some a → ¬|w a| < Q)
    (hend : ¬|w o| < Q) :
    (L.map (isolatedSwap σ w Q)).Perm L ∧
      (L.map (isolatedSwap σ w Q)).filter (fun i => decide (Q ≤ |w i|)) =
        L.filter (fun i => decide (Q ≤ |w i|)) ∧
      (L.map (isolatedSwap σ w Q)).filter (fun i => decide (|w i| < Q)) =
        L.filter (fun i => decide (|w i| < Q)) := by
  classical
  induction fuel generalizing L with
  | zero =>
    have : L = [] := List.length_eq_zero_iff.mp (by omega)
    subst L
    simp
  | succ fuel ih =>
    cases L with
    | nil => simp
    | cons a tail =>
      have ha := hstart a rfl
      by_cases ht : w a < 0 ∧ |w (σ a)| < Q
      · cases tail with
        | nil =>
          have he : σ a = o := (List.isChain_cons_cons.mp hchain).1
          exact False.elim (hend (he ▸ ht.2))
        | cons b rest =>
          have hab : σ a = b := (List.isChain_cons_cons.mp hchain).1
          have htail := (List.isChain_cons_cons.mp hchain).2
          have hb : |w b| < Q := hab ▸ ht.2
          have hbpos := hsmallpos b hb
          have hta : isolatedSwap σ w Q a = b := by
            rw [isolatedSwap, if_pos ht, hab]
          have htb : isolatedSwap σ w Q b = a := by
            rw [isolatedSwap,
              if_neg (show ¬(w b < 0 ∧ |w (σ b)| < Q) by omega), if_pos hb,
              ← hab, σ.symm_apply_apply]
          have hrchain : (rest ++ [o]).IsChain (fun i j => σ i = j) := by
            cases rest with
            | nil => simp
            | cons c xs => exact (List.isChain_cons_cons.mp htail).2
          have hrstart : ∀ c, rest.head? = some c → ¬|w c| < Q := by
            intro c hc
            cases rest with
            | nil => simp at hc
            | cons d xs =>
              have hdc : d = c := Option.some.inj hc
              subst c
              have hbd : σ b = d := (List.isChain_cons_cons.mp htail).1
              exact hbd ▸ hsmallnext b hb
          obtain ⟨hrperm, hrlarge, hrsmall⟩ := ih rest (by simp only [List.length_cons] at hlen; omega)
            hrchain hrstart
          refine ⟨?_, ?_, ?_⟩
          · simpa only [List.map_cons, hta, htb] using
              ((hrperm.cons a).cons b).trans (List.Perm.swap a b rest)
          · simp only [List.map_cons, hta, htb, List.filter_cons]
            simp only [show Q ≤ |w a| by omega, show ¬Q ≤ |w b| by omega,
              decide_true, decide_false, Bool.false_eq_true, ite_false, ite_true]
            rw [hrlarge]
          · simp only [List.map_cons, hta, htb, List.filter_cons]
            simp only [ha, hb, decide_true, decide_false, Bool.false_eq_true, ite_false, ite_true]
            rw [hrsmall]
      · have hta : isolatedSwap σ w Q a = a := by simp [isolatedSwap, ht, ha]
        have hrchain : (tail ++ [o]).IsChain (fun i j => σ i = j) := by
          cases tail with
          | nil => simp
          | cons b rest => exact (List.isChain_cons_cons.mp hchain).2
        have hrstart : ∀ b, tail.head? = some b → ¬|w b| < Q := by
          intro b hb
          cases tail with
          | nil => simp at hb
          | cons c rest =>
            have hcb : c = b := Option.some.inj hb
            subst b
            have hac : σ a = c := (List.isChain_cons_cons.mp hchain).1
            intro hc
            have hn := hsmallpred c hc
            rw [← hac, σ.symm_apply_apply] at hn
            exact ht ⟨hn, hac.symm ▸ hc⟩
        obtain ⟨hrperm, hrlarge, hrsmall⟩ := ih tail (by simp only [List.length_cons] at hlen; omega)
          hrchain hrstart
        refine ⟨by simpa only [List.map_cons, hta] using hrperm.cons a, ?_, ?_⟩
        · simp only [List.map_cons, hta, List.filter_cons]
          rw [hrlarge]
        · simp only [List.map_cons, hta, List.filter_cons]
          rw [hrsmall]


private theorem isolated_positive_cycle {k : ℕ} (hk : 0 < k)
    (w : Fin k → ℤ) (Q N C : ℤ)
    (hQ : 2 ≤ Q) (hN : N = 4 * Q - 1) (hC : C = 2 * Q - 1)
    (hbound : ∀ i, -C ≤ w i ∧ w i ≤ C)
    (hstep : ∀ i, w (finRotate k i) = doubleStep N (w i))
    (hsmall : ∀ i, |w i| < Q → 0 ≤ w i)
    (hisolated : ∀ i, |w i| < Q → Q ≤ |w (finRotate k i)|) :
    ∃ L : List (Fin k), L.Perm (List.ofFn (fun i : Fin k => i)) ∧
      (∀ n : ℕ, 0 ≤ ((L.take n).map w).sum ∧
        ((L.take n).map w).sum ≤ C ∧ 28 * ((L.take n).map w).sum < 13 * N) ∧
      (L.map w).sum = 0 ∧
      (L.filter (fun i => decide (Q ≤ |w i|))).IsRotated
        ((List.finRange k).filter (fun i => decide (Q ≤ |w i|))) ∧
      (L.filter (fun i => decide (|w i| < Q))).IsRotated
        ((List.finRange k).filter (fun i => decide (|w i| < Q))) := by
  classical
  letI : NeZero k := ⟨by omega⟩
  let σ := finRotate k
  obtain ⟨o, ho, hinvol, hcob, hb⟩ := isolated_potential_geometry σ w Q N C
    hQ hN hC hbound hstep hsmall hisolated
  let φ := phase hk o
  let τ := isolatedSwap σ w Q
  let P := isolatedPotential σ w Q N
  let base := (List.range k).map φ
  let L := base.map τ
  have hφ (j : ℕ) : σ (φ j) = φ (j + 1) := by
    apply Fin.ext
    simp [σ, φ, phase, finRotate_apply, Fin.val_add, Nat.add_assoc]
  have hφk : φ k = o := by simp [φ, phase, Nat.mod_eq_of_lt o.isLt]
  have hφ0 : φ 0 = o := phase_zero hk o
  have hP0 : P o = w o := by
    have hpos : 0 < w o := by omega
    have hlarge : ¬|w o| < Q := by rw [abs_of_pos hpos]; omega
    simp [P, isolatedPotential, hlarge, show ¬w o < 0 by omega]
  have htel (n : ℕ) : ((List.range n).map (fun j => w (τ (φ j)))).sum = P (φ n) - w o := by
    induction n with
    | zero => simp [hφ0, hP0]
    | succ n ih =>
      have he := hcob (φ n)
      change P (σ (φ n)) - P (φ n) = w (τ (φ n)) at he
      rw [hφ] at he
      simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, add_zero, ih]
      omega
  have hprefix (n : ℕ) : ((L.take n).map w).sum = P (φ (min n k)) - w o := by
    simpa only [L, base, ← List.map_take, List.take_range, List.map_map,
      Function.comp_def] using htel (min n k)
  have htotal : (L.map w).sum = 0 := by
    have hh := htel k
    simpa only [hφk, hP0, sub_self, L, base, List.map_map, Function.comp_def] using hh
  let e : Equiv.Perm (Fin k) := Equiv.addLeft o
  have hbase : base = List.ofFn e := by
    change (List.range k).map φ = List.ofFn e
    rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range]
    simp only [base, List.map_map]
    apply List.map_congr_left
    intro i _
    apply Fin.ext
    rfl
  have hbaserot : base = (List.finRange k).rotate o.val := by
    rw [hbase]
    apply List.ext_getElem
    · simp
    · intro i hi₁ hi₂
      simp only [List.getElem_ofFn, List.getElem_rotate, List.getElem_finRange,
        List.length_ofFn, List.length_rotate, List.length_finRange]
      apply Fin.ext
      simp [e, Fin.val_add, Nat.add_mod, Nat.add_comm]
  let swapEquiv : Equiv.Perm (Fin k) :=
    { toFun := τ, invFun := τ, left_inv := hinvol, right_inv := hinvol }
  have hperm : L.Perm (List.ofFn (fun i : Fin k => i)) := by
    change (base.map swapEquiv).Perm _
    rw [hbase, List.map_ofFn]
    exact (e.ofFn_comp_perm swapEquiv).trans
      (by simpa only [Function.comp_def, id_eq] using
        swapEquiv.ofFn_comp_perm (fun i : Fin k => i))
  obtain ⟨hnz, hs, hn, hp⟩ := isolated_geometry σ w Q N C hQ hN hC
    hbound hstep hsmall hisolated
  have hsnext (i : Fin k) (hi : |w i| < Q) : Q ≤ w (σ i) := by
    have he := (hs i hi).2.1
    have hz := (hs i hi).1
    have hh := hisolated i hi
    rwa [abs_of_pos (by omega : 0 < w (σ i))] at hh
  have hpred := (isolated_predecessors σ w Q (by omega) hnz
    (fun i hi => ⟨(hs i hi).1, hsnext i hi⟩)
    (fun i hi => (hn i hi).2.2) (fun i hi => (hp i hi).2.1)).2
  have holarge : ¬|w o| < Q := by rw [abs_of_pos (by omega : 0 < w o)]; omega
  have hchain : (base ++ [o]).IsChain (fun i j => σ i = j) := by
    have he : base ++ [o] = (List.range (k + 1)).map φ := by
      simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        hφk, base]
    rw [he, List.isChain_iff_getElem]
    intro i hi
    simpa only [List.getElem_map, List.getElem_range] using hφ i
  have hhead : base.head? = some o := by
    simp [base, List.head?_map, List.head?_range, ne_of_gt hk, hφ0]
  obtain ⟨_, hlarge, hsmallorder⟩ := isolated_swap_chain σ w Q
    (fun i hi => (hs i hi).1)
    (fun i hi => by
      have hh := hsnext i hi
      rw [abs_of_pos (by omega : 0 < w (σ i))]
      omega)
    hpred k base o (by simp [base]) hchain
    (fun a ha => by have he := hhead.symm.trans ha; exact Option.some.inj he ▸ holarge)
    holarge
  refine ⟨L, hperm, ?_, htotal, ?_, ?_⟩
  · intro n
    rw [hprefix]
    obtain ⟨hlo, hhi⟩ := hb (φ (min n k))
    change 0 ≤ P (φ (min n k)) - w o at hlo
    change 28 * (P (φ (min n k)) - w o) < 13 * N at hhi
    change 0 ≤ P (φ (min n k)) - w o ∧
      P (φ (min n k)) - w o ≤ C ∧
      28 * (P (φ (min n k)) - w o) < 13 * N
    exact ⟨hlo, by omega, hhi⟩
  · change (base.map τ).filter _ ~r _
    rw [hlarge, hbaserot]
    exact TwoSmallSource.filter_rotate _ _ _
  · change (base.map τ).filter _ ~r _
    rw [hsmallorder, hbaserot]
    exact TwoSmallSource.filter_rotate _ _ _

/-- Isolated native SMALL labels of one weak sign admit a full physical
half-strip word with strict 13/28 margin and both forward cyclic filters.
No assumption on the source's numerical period or SMALL cardinality is used. -/
theorem actualSource_isolated_same_sign_cyclic_completion
    {k : ℕ} (hk : 3 ≤ k) (t : ℕ)
    (hsmall : (∀ i : Fin k, |actualSource k t i| < quarter k → 0 ≤ actualSource k t i) ∨
      (∀ i : Fin k, |actualSource k t i| < quarter k → actualSource k t i ≤ 0))
    (hisolated : ∀ i : Fin k, |actualSource k t i| < quarter k →
      quarter k ≤ |actualSource k t (finRotate k i)|) :
    ∃ L : List (Fin k),
      L.Perm (List.ofFn (fun i : Fin k => i)) ∧
      L.Nodup ∧ L.toFinset = Finset.univ ∧
      InStrip (actualSource k t) (half k) 0 L ∧
      (∀ n : ℕ, 0 ≤ ((L.take n).map (actualSource k t)).sum ∧
        ((L.take n).map (actualSource k t)).sum ≤ half k ∧
        28 * ((L.take n).map (actualSource k t)).sum < 13 * modulus k) ∧
      (L.map (actualSource k t)).sum = 0 ∧
      TwoOppositeLargeExchange.Legal k t L ∧
      (L.filter (fun i => decide (quarter k ≤ |actualSource k t i|))).IsRotated
        ((List.finRange k).filter (fun i => decide (quarter k ≤ |actualSource k t i|))) ∧
      (L.filter (fun i => decide (|actualSource k t i| < quarter k))).IsRotated
        ((List.finRange k).filter (fun i => decide (|actualSource k t i| < quarter k))) := by
  classical
  letI : NeZero k := ⟨by omega⟩
  obtain ⟨hQ, hN, hC, hNpos, hodd⟩ := source_geometry hk
  have hbound (i : Fin k) : -half k ≤ actualSource k t i ∧ actualSource k t i ≤ half k :=
    centered_bounds hNpos hodd _
  have hcycle := (ZeroSumSubsets.source_cycle (by omega : 0 < k) t).2.2
  have hstep (i : Fin k) : actualSource k t (finRotate k i) =
      doubleStep (modulus k) (actualSource k t i) := by
    have he := hcycle i
    unfold doubleStep
    split_ifs at he ⊢ <;> omega
  have hcompletion : ∃ L : List (Fin k),
      L.Perm (List.ofFn (fun i : Fin k => i)) ∧
      (∀ n : ℕ, 0 ≤ ((L.take n).map (actualSource k t)).sum ∧
        ((L.take n).map (actualSource k t)).sum ≤ half k ∧
        28 * ((L.take n).map (actualSource k t)).sum < 13 * modulus k) ∧
      (L.map (actualSource k t)).sum = 0 ∧
      (L.filter (fun i => decide (quarter k ≤ |actualSource k t i|))).IsRotated
        ((List.finRange k).filter (fun i => decide (quarter k ≤ |actualSource k t i|))) ∧
      (L.filter (fun i => decide (|actualSource k t i| < quarter k))).IsRotated
        ((List.finRange k).filter (fun i => decide (|actualSource k t i| < quarter k))) := by
    rcases hsmall with hsmall | hsmall
    · exact isolated_positive_cycle (by omega) (actualSource k t)
        (quarter k) (modulus k) (half k) hQ hN hC hbound hstep hsmall hisolated
    · obtain ⟨L, hp, hb, hz, hlarge, hsmallorder⟩ := isolated_positive_cycle (by omega : 0 < k)
        (fun i => -actualSource k t i) (quarter k) (modulus k) (half k) hQ hN hC
        (fun i => by have := hbound i; constructor <;> omega)
        (fun i => by rw [doubleStep_neg (le_of_lt hNpos), ← hstep i])
        (fun i hi => by have := hsmall i (by simpa only [abs_neg] using hi); omega)
        (fun i hi => by simpa only [abs_neg] using hisolated i (by simpa only [abs_neg] using hi))
      have hs : InStrip (fun i => -actualSource k t i) (half k) 0 L :=
        MixedSuffixEnergy.strip_of_all_prefixes L (fun n => by
          simpa only [MixedSuffixEnergy.mass, zero_add] using ⟨(hb n).1, (hb n).2.1⟩)
      obtain ⟨j, _, hj⟩ := TwoSmallSource.negate_rotation_prefix_bound
        (fun i => -actualSource k t i) (half k) L hs hz
      have htotal : (L.map (actualSource k t)).sum = 0 := by
        rw [sum_neg_map] at hz
        omega
      refine ⟨L.rotate j, (List.rotate_perm L j).trans hp, ?_, ?_, ?_, ?_⟩
      · intro n
        have hprefix := hj n
        have hmargin := (hb j).2.2
        refine ⟨?_, ?_, ?_⟩
        · simpa only [neg_neg] using hprefix.1
        · simpa only [neg_neg] using hprefix.2.1
        · have hstrict : 28 * (((L.rotate j).take n).map
              (fun i => - -actualSource k t i)).sum < 13 * modulus k := by omega
          simpa only [neg_neg] using hstrict
      · exact ((List.rotate_perm L j).map (actualSource k t)).sum_eq.trans htotal
      · exact (TwoSmallSource.filter_rotate _ L j).trans (by simpa only [abs_neg] using hlarge)
      · exact (TwoSmallSource.filter_rotate _ L j).trans (by simpa only [abs_neg] using hsmallorder)
  obtain ⟨L, hp, hb, hz, hlarge, hsmallorder⟩ := hcompletion
  have hn : L.Nodup := hp.nodup_iff.mpr
    (List.nodup_ofFn_ofInjective (f := fun i : Fin k => i) (fun _ _ h => h))
  have hu : L.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    exact List.mem_toFinset.mpr (hp.mem_iff.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩))
  have hs : InStrip (actualSource k t) (half k) 0 L :=
    MixedSuffixEnergy.strip_of_all_prefixes L (fun n => by
      simpa only [MixedSuffixEnergy.mass, zero_add] using ⟨(hb n).1, (hb n).2.1⟩)
  exact ⟨L, hp, hn, hu, hs, hb, hz, TwoOppositeLargeExchange.legal_of_strip hn hs,
    hlarge, hsmallorder⟩

end D5.S3.Combinatorics.Circle.IsolatedSmallSource
