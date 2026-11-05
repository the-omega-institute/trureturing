/- GID: D5/S3/Combinatorics/Circle/ThreeRowScheduler
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeRowScheduler
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical interval cover and consumed attained-mask scheduler. -/
module
import all D5.S3.Combinatorics.Circle.ThreeRowParameters
import D5.S3.Combinatorics.Circle.SourceWidth
import D5.S3.Combinatorics.Circle.ZeroSumSubsets
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 10000000
namespace D5.S3.Combinatorics.Circle.ThreeRowSource
open SourceWidth
open scoped BigOperators
/- SMALL batches at arbitrary legal endpoints. Unlike complete_small_positives,
the final height need not be zero; schedule_rows uses that stronger conclusion.
There is no uniqueness-of-values premise. -/
private theorem small_batch {α : Type*} [DecidableEq α]
    (f : α → ℤ) (B S : ℤ) (hS : 0 ≤ S) (hSB : 2 * S ≤ B)
    (fuel : ℕ) (labels : List α) (h : ℤ) (hlen : labels.length ≤ fuel)
    (hnd : labels.Nodup) (hh : 0 ≤ h ∧ h ≤ B)
    (hend : 0 ≤ h + (labels.map f).sum ∧ h + (labels.map f).sum ≤ B)
    (hsmall : ∀ x ∈ labels, |f x| ≤ S) :
    ∃ word : List α, word.Perm labels ∧ InStrip f B h word := by
  induction fuel generalizing labels h with
  | zero =>
    have he : labels = [] := List.length_eq_zero_iff.mp (by omega)
    subst labels
    exact ⟨[], .refl _, hh⟩
  | succ fuel ih =>
    by_cases he : labels = []
    · subst labels; exact ⟨[], .refl _, hh⟩
    have hstep : ∃ x ∈ labels, 0 ≤ h + f x ∧ h + f x ≤ B := by
      by_contra hnone
      have hn : ∀ x ∈ labels, ¬ (0 ≤ h + f x ∧ h + f x ≤ B) := by
        intro x hx hxfit
        exact hnone ⟨x, hx, hxfit⟩
      by_cases hp : ∃ p ∈ labels, 0 < f p
      · obtain ⟨p, hp, hp0⟩ := hp
        have hpfit := hn p hp
        have hpb := abs_le.mp (hsmall p hp)
        have hover : B < h + f p := by omega
        by_cases hneg : ∃ n ∈ labels, f n < 0
        · obtain ⟨n, hnmem, hn0⟩ := hneg
          have hnfit := hn n hnmem
          have hnb := abs_le.mp (hsmall n hnmem)
          omega
        · have hall : ∀ x ∈ labels, 0 ≤ f x := by
            intro x hx
            by_contra hx0
            exact hneg ⟨x, hx, by omega⟩
          have hle : f p ≤ (labels.map f).sum :=
            List.single_le_sum (by simpa using hall) _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
          omega
      · have hall : ∀ x ∈ labels, f x ≤ 0 := by
          intro x hx
          by_contra hx0
          exact hp ⟨x, hx, by omega⟩
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil labels he
        have hfit := hn x hx
        have hx0 := hall x hx
        have hxsum : (labels.map f).sum ≤ f x := by
          have hs : ((labels.erase x).map f).sum ≤ 0 := by
            simpa using (List.sum_le_sum
              (fun y hy => hall y (List.mem_of_mem_erase hy)))
          have heq := ((List.perm_cons_erase hx).map f).sum_eq
          simp only [List.map_cons, List.sum_cons] at heq
          omega
        omega
    obtain ⟨x, hx, hlo, hhi⟩ := hstep
    have heq := ((List.perm_cons_erase hx).map f).sum_eq
    simp only [List.map_cons, List.sum_cons] at heq
    have hl := List.length_erase_add_one hx
    obtain ⟨word, hw, hs⟩ := ih (labels.erase x) (h + f x) (by omega)
      (hnd.erase x) ⟨hlo, hhi⟩ (by constructor <;> omega)
      (fun y hy => hsmall y (List.mem_of_mem_erase hy))
    exact ⟨x :: word, (hw.cons x).trans (List.perm_cons_erase hx).symm,
      hh.1, hh.2, hs⟩

/- Only the Finset-to-finRange conversion is local; the physical cycle theorem
and its coboundary proof are owned by ZeroSumSubsets. -/
private theorem actual_total (k t : ℕ) (hk : 0 < k) :
    ((List.finRange k).map (actualSource k t)).sum = 0 := by
  rw [← List.sum_toFinset _ (List.nodup_finRange k), List.toFinset_finRange]
  exact (ZeroSumSubsets.source_cycle hk t).2.1

/- A concrete physical interval. Offsets below are original-source positions,
not values or positions in the newly scheduled word. -/
private def segment (k offset len : ℕ) (h : offset + len ≤ k) : List (Fin k) :=
  List.ofFn (fun i : Fin len => ⟨offset + i.val, by omega⟩)

private theorem segment_length (k offset len : ℕ) (h : offset + len ≤ k) :
    (segment k offset len h).length = len := by simp [segment]

private theorem segment_append (k offset u v : ℕ) (h : offset + (u + v) ≤ k) :
    segment k offset u (by omega) ++ segment k (offset + u) v (by omega) =
      segment k offset (u + v) h := by
  apply List.ext_getElem
  · simp [segment]
  · intro i hi hi'
    by_cases hu : i < u
    · rw [List.getElem_append_left (by simpa [segment] using hu)]
      simp only [segment, List.getElem_ofFn]
    · rw [List.getElem_append_right (by simpa [segment] using (show u ≤ i by omega))]
      simp only [segment, List.length_ofFn, List.getElem_ofFn]
      apply Fin.ext
      simp
      omega

private theorem segment_append_any (k offset u v offset' : ℕ)
    (h₁ : offset + u ≤ k) (hoff : offset + u = offset')
    (h₂ : offset' + v ≤ k) :
    segment k offset u h₁ ++ segment k offset' v h₂ =
      segment k offset (u + v) (by omega) := by
  subst offset'
  simpa using (segment_append k offset u v (by omega))

private theorem segment_full (k : ℕ) : segment k 0 k (by omega) = List.finRange k := by
  apply List.ext_getElem <;> simp [segment]

private theorem segment_one (k i : ℕ) (hi : i + 1 ≤ k) :
    segment k i 1 hi = [⟨i, by omega⟩] := by simp [segment, List.ofFn_succ]

/- Positions of every label are explicit, including the last cyclic terminal.
The old positive list is split into its lower bits and its actual top bit. -/
private def physicalRows (J L : ℕ) (hJ : 1 ≤ J) (hL : 1 ≤ L) :
    List (Fin (3 * L + J + 4)) :=
  [⟨0, by omega⟩] ++ segment _ 1 L (by omega) ++
  [⟨L + 1, by omega⟩] ++ segment _ (L + 2) (J - 1) (by omega) ++
  [⟨L + J + 1, by omega⟩, ⟨L + J + 2, by omega⟩] ++
  segment _ (L + J + 3) (L - 1) (by omega) ++
  [⟨2 * L + J + 2, by omega⟩, ⟨2 * L + J + 3, by omega⟩] ++
  segment _ (2 * L + J + 4) (L - 1) (by omega) ++
  [⟨3 * L + J + 3, by omega⟩]

private theorem physical_cover (J L : ℕ) (hJ : 1 ≤ J) (hL : 1 ≤ L) :
    physicalRows J L hJ hL = List.finRange (3 * L + J + 4) := by
  unfold physicalRows
  have htwo (i : ℕ) (hi : i + 2 ≤ 3 * L + J + 4) :
      ([⟨i, by omega⟩, ⟨i + 1, by omega⟩] : List (Fin (3 * L + J + 4))) =
        segment _ i 2 hi := by simp [segment, List.ofFn_succ]
  rw [← segment_one _ 0 (by omega), ← segment_one _ (L + 1) (by omega),
    show ([⟨L + J + 1, by omega⟩, ⟨L + J + 2, by omega⟩] :
      List (Fin (3 * L + J + 4))) = segment _ (L + J + 1) 2 (by omega) from
        htwo _ (by omega),
    show ([⟨2 * L + J + 2, by omega⟩, ⟨2 * L + J + 3, by omega⟩] :
      List (Fin (3 * L + J + 4))) = segment _ (2 * L + J + 2) 2 (by omega) from
        htwo _ (by omega),
    ← segment_one _ (3 * L + J + 3) (by omega)]
  -- Joining from left to right keeps every physical interval and terminal.
  rw [segment_append_any _ 0 1 L 1 (by omega) (by omega) (by omega)]
  rw [segment_append_any _ 0 (1 + L) 1 (L + 1) (by omega) (by omega) (by omega)]
  rw [segment_append_any _ 0 ((1 + L) + 1) (J - 1) (L + 2)
    (by omega) (by omega) (by omega)]
  rw [segment_append_any _ 0 (((1 + L) + 1) + (J - 1)) 2 (L + J + 1)
    (by omega) (by omega) (by omega)]
  rw [segment_append_any _ 0 ((((1 + L) + 1) + (J - 1)) + 2) (L - 1)
    (L + J + 3) (by omega) (by omega) (by omega)]
  rw [segment_append_any _ 0 (((((1 + L) + 1) + (J - 1)) + 2) + (L - 1)) 2
    (2 * L + J + 2) (by omega) (by omega) (by omega)]
  rw [segment_append_any _ 0 ((((((1 + L) + 1) + (J - 1)) + 2) + (L - 1)) + 2)
    (L - 1) (2 * L + J + 4) (by omega) (by omega) (by omega)]
  rw [segment_append_any _ 0 (((((((1 + L) + 1) + (J - 1)) + 2) + (L - 1)) + 2) + (L - 1))
    1 (3 * L + J + 3) (by omega) (by omega) (by omega)]
  have hJ0 : 0 < J := by omega
  have hL0 : 0 < L := by omega
  have hJsub : J - 1 + 1 = J := Nat.sub_add_cancel (by omega)
  have hLsub : L - 1 + 1 = L := Nat.sub_add_cancel (by omega)
  have hJsubZ : ((J - 1 : ℕ) : ℤ) + 1 = J := by exact_mod_cast hJsub
  have hLsubZ : ((L - 1 : ℕ) : ℤ) + 1 = L := by exact_mod_cast hLsub
  convert segment_full (3 * L + J + 4) using 1 <;> congr 1 <;> omega

/- This scheduler's hypotheses are source ROW DATA, not an assumed bounded
word. All mask selections, intermediate heights, complement totals, and
physical consumption are proved here from those data.
-/
private theorem schedule_rows {k : ℕ} (f : Fin k → ℤ)
    (r q n : ℤ) (J L : ℕ)
    (hr : 4 ≤ r) (hq : 2 * r ^ 2 ≤ q)
    (hr2 : 2 * (r / 2) = r) (hq2 : 2 * (q / 2) = q)
    (hn : H r * n = q - r) (hnlo : r ≤ n) (hnhi : n < q)
    (hpowJ : (2 : ℤ) ^ (J - 1) = r / 2)
    (hpowL : (2 : ℤ) ^ L = q) (hpowL1 : (2 : ℤ) ^ (L - 1) = q / 2)
    (p dlabel top parent1 terminal1 parent2 terminal2 : Fin k)
    (oldNeg oldPosLower nextNeg thirdNeg : List (Fin k))
    (hcover : ([p] ++ oldNeg ++ [dlabel] ++ oldPosLower ++ [top, parent1] ++
      nextNeg ++ [terminal1, parent2] ++ thirdNeg ++ [terminal2]).Perm (List.finRange k))
    (hvals : f p = M r q ∧ f dlabel = -D r q ∧ f top = (r / 2) * b r q ∧
      f parent1 = V1 r q ∧ f terminal1 = -W1 r q ∧
      f parent2 = V2 r q ∧ f terminal2 = -W2 r q)
    (hold : Dyadic (fun x => -f x) (a r q) oldNeg)
    (hnext : Dyadic (fun x => -f x) (z1 r q) nextNeg)
    (hthird : Dyadic (fun x => -f x) (z2 r q) thirdNeg)
    (hpos : Dyadic f (b r q) oldPosLower)
    (hlens : oldNeg.length = L ∧ oldPosLower.length = J - 1 ∧
      nextNeg.length = L - 1 ∧ thirdNeg.length = L - 1)
    (hsmall : ∀ x ∈ oldNeg ++ oldPosLower ++ [top] ++ nextNeg ++ thirdNeg,
      |f x| ≤ Q r q - 1)
    (hterminal : 0 ≤ M r q ∧ M r q ≤ C r q ∧
      0 ≤ M r q - D r q ∧ 0 ≤ V2 r q ∧ 0 ≤ W2 r q)
    (hsum : ((List.finRange k).map f).sum = 0) :
    ∃ word : List (Fin k), word.Perm (List.finRange k) ∧
      InStrip f (C r q) 0 word ∧ (word.map f).sum = 0 := by
  classical
  let c := (n + 1) * (2 * q + 1)
  let R := a r q - c - 2 * (r - 1) * delta r q
  let F := R + V1 r q - W1 r q
  let fgate := F - W2 r q + (r / 2) * b r q - (q / 2 - 1) * z2 r q
  obtain ⟨hR0, hRcap, hF0, hFcap, hpoly, hf0, hfG, hclip⟩ :=
    bridge_arithmetic r q n hr hq hr2 hq2 hn
  change 0 < R at hR0
  change R ≤ C r q - V1 r q at hRcap
  change 0 < F at hF0
  change F ≤ C r q at hFcap
  change 0 < fgate at hf0
  change fgate < C r q - V2 r q at hfG
  change W2 r q + fgate < C r q at hclip
  rcases hvals with ⟨hp, hd, ht, hp1, ht1, hp2, ht2⟩
  have hn0 : 0 ≤ n - r := by omega
  have hNmask : (n - r).toNat < 2 ^ oldNeg.length := by
    have he : ((n - r).toNat : ℤ) = n - r := Int.toNat_of_nonneg hn0
    rw [hlens.1]
    exact_mod_cast (show (((n - r).toNat : ℕ) : ℤ) < (2 : ℤ) ^ L by
      rw [he, hpowL]; omega)
  have hv0 : 0 ≤ r - 1 := by omega
  have hVmask : (r - 1).toNat < 2 ^ nextNeg.length := by
    rw [hlens.2.2.1]
    have he : ((r - 1).toNat : ℤ) = r - 1 := Int.toNat_of_nonneg hv0
    exact_mod_cast (show (((r - 1).toNat : ℕ) : ℤ) < (2 : ℤ) ^ (L - 1) by
      rw [he, hpowL1]; nlinarith)
  obtain ⟨aSel, aRest, haPerm, haSum⟩ := dyadic_select hold _ hNmask
  obtain ⟨zSel, zRest, hzPerm, hzSum⟩ := dyadic_select hnext _ hVmask
  rw [sum_neg_map, Int.toNat_of_nonneg hn0] at haSum
  rw [sum_neg_map, Int.toNat_of_nonneg hv0] at hzSum
  have hselSum : ((aSel ++ zSel).map f).sum = -(n - r) * a r q - (r - 1) * z1 r q := by
    simp only [List.map_append, List.sum_append]
    linarith [haSum, hzSum]
  have hstart : M r q - D r q + ((aSel ++ zSel).map f).sum = R := by
    rw [hselSum]
    have hna : M r q - D r q = n * a r q - c := by
      dsimp [c, M, D, a, H] at *
      linear_combination (-4 * q ^ 2) * hn
    rw [hna]
    dsimp [R, z1]
    ring
  have hnegative : ∀ x ∈ oldNeg ++ nextNeg ++ thirdNeg, f x ≤ 0 := by
    have ha0 : 0 ≤ a r q := by unfold a H; nlinarith [sq_nonneg q]
    have hz10 : 0 ≤ z1 r q := by unfold z1 delta; nlinarith
    have hz20 : 0 ≤ z2 r q := by unfold z2 e2; nlinarith
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact neg_nonneg.mp (SourceWidth.dyadic_nonneg ha0 hold x hx)
    · exact neg_nonneg.mp (SourceWidth.dyadic_nonneg hz10 hnext x hx)
    · exact neg_nonneg.mp (SourceWidth.dyadic_nonneg hz20 hthird x hx)
  have hselNeg : ∀ x ∈ aSel ++ zSel, f x ≤ 0 := by
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · have hxold : x ∈ oldNeg := haPerm.mem_iff.mp (by simp [hx])
      exact hnegative x (by simp [hxold])
    · have hxnext : x ∈ nextNeg := hzPerm.mem_iff.mp (by simp [hx])
      exact hnegative x (by simp [hxnext])
  have hD0 : 0 ≤ D r q := by
    have hq0 : 0 ≤ q := by omega
    have ha0 : 0 ≤ a r q := by
      unfold a H
      nlinarith [sq_nonneg q]
    exact mul_nonneg hq0 ha0
  have hz10 : 0 ≤ z1 r q := by
    have hq0 : 0 ≤ q := by omega
    have hr0 : 0 ≤ r := by omega
    have ha0 : 0 ≤ a r q := by
      unfold a H
      nlinarith [sq_nonneg q]
    have hd0 : 0 ≤ (q + r - 1) * (2 * q + 1) := by
      exact mul_nonneg (by omega) (by omega)
    unfold z1
    exact add_nonneg ha0 (mul_nonneg (by norm_num) hd0)
  have hb0 : 0 ≤ b r q := by
    have hq0 : 0 ≤ q := by omega
    have hq1 : 1 ≤ q := by omega
    have hq2ge : q ≤ q ^ 2 := by nlinarith [sq_nonneg (q - 1)]
    have hq3ge : q ^ 2 ≤ q ^ 3 := by
      have hh := mul_le_mul_of_nonneg_left hq2ge hq0
      nlinarith
    unfold b
    nlinarith
  have hV10 : 0 ≤ V1 r q := by
    unfold V1
    exact mul_nonneg (by omega) hb0
  have hW10 : 0 ≤ W1 r q := by
    unfold W1
    exact mul_nonneg (by omega) hz10
  have hmidlow : 0 ≤ R + V1 r q := by
    dsimp [F] at hF0
    omega
  have hMDcap : M r q - D r q ≤ C r q := by omega
  have hRcap' : R + V1 r q ≤ C r q := by omega
  have hfirst : InStrip f (C r q) 0
      ([p, dlabel] ++ aSel ++ zSel ++ [parent1, terminal1]) := by
    have hi : InStrip f (C r q) 0 [p, dlabel] := by
      simp only [InStrip, hp, hd, add_zero, zero_add]
      dsimp [C, Q] at *
      constructor
      · omega
      constructor
      · omega
      constructor
      · omega
      constructor <;> omega
    have hs : InStrip f (C r q) (M r q - D r q) (aSel ++ zSel) :=
      inStrip_nonpos hselNeg (by omega) (by rw [hstart]; omega)
    have hlarge : InStrip f (C r q) R [parent1, terminal1] := by
      simp only [InStrip, hp1, ht1, add_zero, zero_add]
      change 0 < R + V1 r q - W1 r q at hF0
      change R + V1 r q - W1 r q ≤ C r q at hFcap
      constructor
      · omega
      constructor
      · omega
      constructor
      · omega
      constructor <;> omega
    have hmid : InStrip f (C r q)
        (M r q - D r q + ((aSel ++ zSel).map f).sum) [parent1, terminal1] := by
      have hstart' := hstart
      simp only [List.map_append, List.sum_append] at hstart'
      simpa only [List.map_append, List.sum_append] using
        (show InStrip f (C r q)
            (M r q - D r q + ((aSel.map f).sum + (zSel.map f).sum))
            [parent1, terminal1] by rw [hstart']; exact hlarge)
    have htail := inStrip_append hs hmid
    have hright : InStrip f (C r q) (M r q - D r q)
        (aSel ++ zSel ++ [parent1, terminal1]) := htail
    have hcat := inStrip_append hi
      (by simpa [hp, hd, sub_eq_add_neg, zero_add] using hright)
    simpa only [List.append_assoc] using hcat
  have hthirdSum : (thirdNeg.map f).sum = -(q / 2 - 1) * z2 r q := by
    have hh := dyadic_sum hthird
    rw [sum_neg_map, hlens.2.2.2, hpowL1] at hh
    nlinarith
  let mask := [top] ++ thirdNeg
  let rest := aRest ++ zRest ++ oldPosLower
  let staged := [p, dlabel] ++ aSel ++ zSel ++ [parent1, terminal1] ++
    mask ++ [terminal2, parent2] ++ rest
  have hstaged : staged.Perm (List.finRange k) := by
    apply List.Perm.trans (l₂ := [p] ++ oldNeg ++ [dlabel] ++ oldPosLower ++
      [top, parent1] ++ nextNeg ++ [terminal1, parent2] ++ thirdNeg ++ [terminal2])
    · apply List.perm_iff_count.mpr
      intro x
      have ha := haPerm.count_eq x
      have hz := hzPerm.count_eq x
      simp only [staged, mask, rest, List.count_append, List.count_cons, List.count_nil] at *
      omega
    · exact hcover
  have hnd : staged.Nodup := hstaged.nodup_iff.mpr (List.nodup_finRange k)
  have hmasknd : mask.Nodup := by
    have hnd' : (([p, dlabel] ++ aSel ++ zSel ++ [parent1, terminal1]) ++
      (mask ++ ([terminal2, parent2] ++ rest))).Nodup := by
      simpa [staged, List.append_assoc] using hnd
    have hright := (List.nodup_append.mp hnd').2.1
    exact (List.nodup_append.mp hright).1
  have hmaskSmall : ∀ x ∈ mask, |f x| ≤ Q r q - 1 := by
    intro x hx
    apply hsmall x
    simp only [mask, List.mem_append, List.mem_cons, List.mem_singleton] at hx ⊢
    aesop
  have hq0 : 0 ≤ q := by omega
  have hq3 : 0 ≤ q ^ 3 := pow_nonneg hq0 3
  have hq1 : 1 ≤ q := by omega
  have hq3one : 1 ≤ q ^ 3 := by nlinarith
  have hr0 : 0 ≤ r := by omega
  have hprod : 1 ≤ r * q ^ 3 := by
    have hp := mul_le_mul_of_nonneg_left hq3one hr0
    nlinarith [hr]
  have hQ : 0 ≤ Q r q - 1 := by unfold Q; nlinarith
  have hQB : 2 * (Q r q - 1) ≤ C r q := by
    unfold Q C
    ring_nf
    omega
  have hmaskSum : F + (mask.map f).sum = W2 r q + fgate := by
    simp only [mask, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, ht, hthirdSum]
    dsimp [fgate]
    ring
  obtain ⟨maskWord, hmaskPerm, hmaskStrip⟩ := small_batch f (C r q) (Q r q - 1)
    hQ hQB mask.length mask F (le_refl _) hmasknd ⟨hF0.le, hFcap⟩
    (by rw [hmaskSum]; constructor <;> omega) hmaskSmall
  have hpair : InStrip f (C r q) (W2 r q + fgate) [terminal2, parent2] := by
    simp only [InStrip, ht2, hp2, add_zero]
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  let pref := [p, dlabel] ++ aSel ++ zSel ++ [parent1, terminal1] ++
    maskWord ++ [terminal2, parent2]
  have hprefixSum : (pref.map f).sum = V2 r q + fgate := by
    have hm := (hmaskPerm.map f).sum_eq
    simp only [pref, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, hp, hd, hp1, ht1, hp2, ht2] at *
    dsimp [F, R] at *
    omega
  have hprefixStrip : InStrip f (C r q) 0 pref := by
    have hfirstSum : (([p, dlabel] ++ aSel ++ zSel ++ [parent1, terminal1]).map f).sum = F := by
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, hp, hd, hp1, ht1]
      dsimp [F] at *
      simp only [List.map_append, List.sum_append] at hstart
      omega
    have hm := (hmaskPerm.map f).sum_eq
    have hbuilt : InStrip f (C r q) 0
        (([p, dlabel] ++ aSel ++ zSel ++ [parent1, terminal1]) ++
          (maskWord ++ [terminal2, parent2])) := by
      apply inStrip_append hfirst
      rw [zero_add, hfirstSum]
      apply inStrip_append hmaskStrip
      rw [hm, hmaskSum]
      exact hpair
    simpa [pref, List.append_assoc] using hbuilt
  have hnewPerm : (pref ++ rest).Perm (List.finRange k) := by
    apply List.Perm.trans (l₂ := staged)
    · apply List.perm_iff_count.mpr
      intro x
      have hm := hmaskPerm.count_eq x
      simp only [pref, staged, List.count_append] at *
      omega
    · exact hstaged
  have hrestnd : rest.Nodup :=
    (List.nodup_append.mp (hnewPerm.nodup_iff.mpr (List.nodup_finRange k))).2.1
  have haRestSum : (aRest.map f).sum = -((q - 1) - (n - r)) * a r q := by
    have he := (haPerm.map f).sum_eq
    have hs := dyadic_sum hold
    rw [sum_neg_map, hlens.1, hpowL] at hs
    simp only [List.map_append, List.sum_append] at he
    nlinarith [haSum]
  have hzRestSum : (zRest.map f).sum = -(q / 2 - r) * z1 r q := by
    have he := (hzPerm.map f).sum_eq
    have hs := dyadic_sum hnext
    rw [sum_neg_map, hlens.2.2.1, hpowL1] at hs
    simp only [List.map_append, List.sum_append] at he
    nlinarith [hzSum]
  have hposRestSum : (oldPosLower.map f).sum = (r / 2 - 1) * b r q := by
    have hs := dyadic_sum hpos
    simpa only [hlens.2.1, hpowJ] using hs
  have hresidualSigned : (rest.map f).sum = (r / 2 - 1) * b r q -
      (((q - 1) - (n - r)) * a r q + (q / 2 - r) * z1 r q) := by
    simp only [rest, List.map_append, List.sum_append, haRestSum, hzRestSum, hposRestSum]
    ring
  have hrestSum : V2 r q + fgate + (rest.map f).sum = 0 := by
    have he := (hnewPerm.map f).sum_eq
    simp only [List.map_append, List.sum_append, hprefixSum, hsum] at he
    rw [hresidualSigned] at he ⊢
    exact he
  have hrestSmall : ∀ x ∈ rest, |f x| ≤ Q r q - 1 := by
    intro x hx
    apply hsmall x
    simp only [rest, List.mem_append] at hx ⊢
    rcases hx with (hx | hx) | hx
    · have := haPerm.mem_iff.mp (show x ∈ aSel ++ aRest by simp [hx])
      aesop
    · have := hzPerm.mem_iff.mp (show x ∈ zSel ++ zRest by simp [hx])
      aesop
    · aesop
  obtain ⟨tailWord, htailPerm, htailStrip⟩ := small_batch f (C r q) (Q r q - 1)
    hQ hQB rest.length rest (V2 r q + fgate) (le_refl _) hrestnd
    (by constructor <;> omega) (by rw [hrestSum]; constructor <;> omega) hrestSmall
  refine ⟨pref ++ tailWord, ?_, ?_, ?_⟩
  · exact (htailPerm.append_left pref).trans hnewPerm
  · apply inStrip_append hprefixStrip
    simpa [hprefixSum] using htailStrip
  · have ht := (htailPerm.map f).sum_eq
    simp only [List.map_append, List.sum_append, hprefixSum, ht]
    exact hrestSum


end D5.S3.Combinatorics.Circle.ThreeRowSource
