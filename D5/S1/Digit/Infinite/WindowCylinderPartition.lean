/- GID: D5/S1/Digit/Infinite/WindowCylinderPartition
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/WindowCylinderPartition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Completed legal windows parametrize closed affine intervals of exact length that cover the signed value range with disjoint interiors. -/

import D5.S1.Digit.Infinite.WindowSuccessorGraph
import D5.S1.Digit.Infinite.SignedSeriesFibres
import Mathlib.Algebra.Order.Group.Pointwise.Interval

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.WindowCylinderPartition

open D5.S1.Digit.Infinite.SuccessorContinuity
open D5.S1.Digit.Infinite.SignedSeriesRange
open D5.S1.Digit.Infinite.SignedSeriesFibres
open D5.S1.Digit.Infinite.WindowSuccessorGraph
open private prependBlock from D5.S1.Digit.Infinite.SignedSeriesFibres

/-- The real circle with circumference one. -/
abbrev Circle := AddCircle (1 : ℝ)
/-- The negative golden phase indexed by a natural number. -/
noncomputable def E (m : ℕ) : Circle := ((-(m : ℝ) * Real.goldenRatio : ℝ) : Circle)
/-- The Fibonacci value of the digits of a finite return-block word. -/
def wordValue (w : List Block) : ℕ := ∑ j ∈ Finset.range (len w),
  if (digitsOf w)[j]?.getD false then Nat.fib (j + 2) else 0
/-- The natural index of a finite return-block seam. -/
def seamIndex (w : List Block) : ℕ := G (len w + 1) - wordValue w
/-- A return-block word with the specified seam index, or the empty word if none exists. -/
noncomputable def seamWord (m : ℕ) : List Block := by
  classical
  exact if h : ∃ w, seamIndex w = m then Classical.choose h else []
/-- The endpoint stream on the negative side of the indexed circle cut. -/
noncomputable def eMinus (m : ℕ) : LegalDigits :=
  if m ≤ 1 then v else
    if len (seamWord m) % 2 = 0 then rightStream (seamWord m) else leftStream (seamWord m)
/-- The endpoint stream on the positive side of the indexed circle cut. -/
noncomputable def ePlus (m : ℕ) : LegalDigits :=
  if m ≤ 1 then u else
    if len (seamWord m) % 2 = 0 then leftStream (seamWord m) else rightStream (seamWord m)

/-- The window digits completed by a zero exactly when the last digit is one. -/
def completedDigits {L : ℕ} (p : X L) : List (Fin 2) :=
  List.ofFn (fun i => if p.val i then 1 else 0) ++
    if (List.ofFn p.val).getLast?.getD false then [0] else []
/-- The return-block word obtained by decoding the completed window. -/
def c {L : ℕ} (p : X L) : List Block :=
  ((D5.S0.Automata.BinaryZeckendorfBlockSkeleton.decode (completedDigits p)).getD
    ⟨[], .recurrent⟩).blocks
/-- The digit length of the completed window. -/
def d {L : ℕ} (p : X L) : ℕ := L + if (List.ofFn p.val).getLast?.getD false then 1 else 0
/-- The signed golden sum of the window digits. -/
noncomputable def Sp {L : ℕ} (p : X L) : ℝ :=
  ∑ i : Fin L, (-1 : ℝ) ^ (i.val + 1) * alpha ^ (i.val + 2) * (if p.val i then 1 else 0)
/-- The set of legal streams with the specified initial window. -/
def C {L : ℕ} (p : X L) : Set LegalDigits := {x | P L x = p}
/-- The affine interval associated with a completed window. -/
noncomputable def I {L : ℕ} (p : X L) : Set ℝ :=
  (fun t => Sp p + r ^ d p * t) '' Set.Icc a b
/-- The lower real endpoint of a window interval. -/
noncomputable def ell {L : ℕ} (p : X L) : ℝ :=
  min (Sp p + r ^ d p * a) (Sp p + r ^ d p * b)
/-- The upper real endpoint of a window interval. -/
noncomputable def upper {L : ℕ} (p : X L) : ℝ :=
  max (Sp p + r ^ d p * a) (Sp p + r ^ d p * b)
/-- The open circle arc obtained from the interior of a window interval. -/
noncomputable def A {L : ℕ} (p : X L) : Set Circle :=
  (fun t : ℝ => (t : Circle)) '' Set.Ioo (ell p) (upper p)
/-- The negative golden phases indexed from one through the window count. -/
noncomputable def B (L : ℕ) : Set Circle := E '' Set.Icc 1 (G L)
/-- The circle images of the endpoints of all intervals of the specified window length. -/
noncomputable def actualCuts (L : ℕ) : Set Circle :=
  {z | ∃ p : X L, z = ((ell p : ℝ) : Circle) ∨ z = ((upper p : ℝ) : Circle)}

set_option maxHeartbeats 800000 in
/-- Completed legal windows parametrize their cylinders by arbitrary legal tails, and their
signed value intervals have exact positive lengths, cover the range, and have disjoint interiors. -/
theorem window_cylinder_partition :
    ∀ L, 1 ≤ L →
      (Set.univ : Set (X L)).Finite ∧
      (∀ p : X L, signedValue '' C p = I p ∧ I p = Set.Icc (ell p) (upper p) ∧
        upper p - ell p = alpha ^ d p ∧ 0 < alpha ^ d p ∧ alpha ^ d p < 1 ∧
        len (c p) = d p ∧ S (c p) = Sp p ∧ C p = Set.range (prependWord (c p))) ∧
      (⋃ p : X L, I p) = Set.Icc a b ∧
      (∀ p q : X L, p ≠ q → Disjoint (Set.Ioo (ell p) (upper p))
        (Set.Ioo (ell q) (upper q))) := by
  classical
  have hp : 0 < alpha := inv_pos.mpr Real.goldenRatio_pos
  have hlt : alpha < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have ha : alpha ^ 2 + alpha = 1 := by
    dsimp [alpha]
    rw [Real.inv_goldenRatio]
    nlinarith [Real.goldenConj_sq]
  have hab : a < b := by dsimp [a, b]; nlinarith [sq_nonneg alpha]
  have hba : b - a = 1 := by dsimp [a, b]; linarith
  let shift (x : LegalDigits) (n : ℕ) : LegalDigits :=
    ⟨fun j => x.val (j + n), fun j => by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using x.property (j + n)⟩
  let term (x : LegalDigits) (j : ℕ) : ℝ :=
    (-1 : ℝ) ^ (j + 1) * alpha ^ (j + 2) * (if x.val j then 1 else 0)
  have summable_term (x : LegalDigits) : Summable (term x) := by
    apply ((summable_geometric_of_lt_one hp.le hlt).mul_right (alpha ^ 2)).of_norm_bounded
    intro j
    dsimp [term]
    rw [abs_mul, abs_mul, abs_pow, abs_pow]
    simp only [abs_neg, abs_one, one_pow, one_mul, abs_of_pos hp]
    cases x.val j <;> simp [pow_add, mul_nonneg (pow_nonneg hp.le j) (sq_nonneg alpha)]
  have tail_value (x : LegalDigits) (n : ℕ) : signedValue x =
      (∑ j ∈ Finset.range n, term x j) + r ^ n * signedValue (shift x n) := by
    have ht (j : ℕ) : term x (j + n) = r ^ n * term (shift x n) j := by
      simp [term, shift, r, pow_add]
      ring
    change (∑' j, term x j) = _
    rw [← (summable_term x).sum_add_tsum_nat_add n]
    simp_rw [ht]
    rw [tsum_mul_left]
    rfl
  have last_digit {L : ℕ} (p : X L) (hL : 1 ≤ L) :
      (List.ofFn p.val).getLast?.getD false = p.val ⟨L-1, by omega⟩ := by
    rw [List.getLast?_eq_getElem?]
    simp [List.length_ofFn, show L-1 < L by omega]
  have block_prefix (n : ℕ) (x : LegalDigits)
      (hz : 0 < n → x.val (n-1) = false) :
      ∃ w : List Block, len w = n ∧
        ∀ j, j < n → (digitsOf w)[j]?.getD false = x.val j := by
    induction n using Nat.strong_induction_on generalizing x with
    | h n ih =>
      cases n with
      | zero => exact ⟨[],rfl,by omega⟩
      | succ k =>
        cases hx : x.val 0 with
        | false =>
          have ht : 0 < k → (shift x 1).val (k-1) = false := by
            intro hk
            have h := hz (by omega)
            simpa [shift, show k-1+1=k by omega] using h
          obtain ⟨w,hw,hdig⟩ := ih k (by omega) (shift x 1) ht
          refine ⟨.zero :: w, ?_, ?_⟩
          · change (false :: digitsOf w).length = k+1
            simpa [len] using congrArg Nat.succ hw
          · intro j hj
            cases j with
            | zero => simpa [digitsOf, D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand] using hx.symm
            | succ j =>
              simpa [digitsOf, D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand, shift]
                using hdig j (by omega)
        | true =>
          have hk : 0 < k := by
            by_contra h
            have he : k = 0 := by omega
            have ht := hz (by omega)
            simp [he,hx] at ht
          have hx1 : x.val 1 = false := by
            cases hh : x.val 1
            · rfl
            · exact False.elim (x.property 0 ⟨hx,hh⟩)
          have ht : 0 < k-1 → (shift x 2).val (k-1-1) = false := by
            intro hk1
            have h := hz (by omega)
            simpa [shift, show k-1-1+2=k by omega] using h
          obtain ⟨w,hw,hdig⟩ := ih (k-1) (by omega) (shift x 2) ht
          refine ⟨.oneZero :: w, ?_, ?_⟩
          · change (true :: false :: digitsOf w).length = k+1
            simp only [List.length_cons]
            change len w + 1 + 1 = k+1
            omega
          · intro j hj
            cases j with
            | zero => simpa [digitsOf, D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand] using hx.symm
            | succ j =>
              cases j with
              | zero => simpa [digitsOf, D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand] using hx1.symm
              | succ j =>
                simpa [digitsOf, D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand, shift, Nat.add_assoc]
                  using hdig j (by omega)
  have prepend_digits (w : List Block) (y : LegalDigits) (j : ℕ) :
      (prependWord w y).val j = if j < len w then (digitsOf w)[j]?.getD false
        else y.val (j-len w) := by
    induction w generalizing j with
    | nil => simp [prependWord,len,digitsOf,D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand]
    | cons b w ih =>
      cases b with
      | zero =>
        cases j with
        | zero => rfl
        | succ j =>
          simpa [prependWord,prependBlock,len,digitsOf,
            D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand] using ih j
      | oneZero =>
        cases j with
        | zero => rfl
        | succ j =>
          cases j with
          | zero => rfl
          | succ j =>
            simpa [prependWord,prependBlock,len,digitsOf,
              D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand, Nat.add_assoc] using ih j
  have geometry (L : ℕ) (hL : 1 ≤ L) (p : X L) :
      signedValue '' C p = I p ∧ I p = Set.Icc (ell p) (upper p) ∧
      upper p - ell p = alpha ^ d p ∧ 0 < alpha ^ d p ∧ alpha ^ d p < 1 ∧
      len (c p) = d p ∧ S (c p) = Sp p ∧ C p = Set.range (prependWord (c p)) := by
    have hLd : L ≤ d p := by dsimp [d]; split <;> omega
    have hd : d p = L ∨ d p = L+1 := by dsimp [d]; split <;> omega
    have hlast : d p = L ↔ p.val ⟨L-1, by omega⟩ = false := by
      simp only [d, last_digit p hL]
      cases p.val ⟨L-1, by omega⟩ <;> simp
    have hpref (x : LegalDigits) (hx : x ∈ C p) (j : ℕ) (hj : j < L) :
        x.val j = p.val ⟨j,hj⟩ := congrArg (fun z : X L => z.val ⟨j,hj⟩) hx
    have hzero (x : LegalDigits) (hx : x ∈ C p) (he : d p = L+1) : x.val L = false := by
      have hh : p.val ⟨L-1, by omega⟩ = true := by
        cases hh : p.val ⟨L-1, by omega⟩
        · have := hlast.mpr hh; omega
        · rfl
      have ht := hpref x hx (L-1) (by omega)
      have hn := x.property (L-1)
      rw [ht, hh] at hn
      have hl : L-1+1=L := by omega
      rw [hl] at hn
      cases hh : x.val L <;> simp_all
    have hsum (x : LegalDigits) (hx : x ∈ C p) :
        (∑ j ∈ Finset.range (d p), term x j) = Sp p := by
      have hs : (∑ j ∈ Finset.range L, term x j) = Sp p := by
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro j _
        dsimp [term, Sp]
        rw [hpref x hx j j.isLt]
      rcases hd with hd | hd
      · simpa [hd] using hs
      · rw [hd, Finset.sum_range_succ, hs]
        simp [term, hzero x hx hd]
    let join (y : LegalDigits) : LegalDigits :=
      ⟨fun j => if h : j < L then p.val ⟨j,h⟩ else
        if j < d p then false else y.val (j-d p), by
        intro j hj
        by_cases hjL : j < L
        · by_cases hj1L : j+1 < L
          · exact p.property j hj1L ⟨by simpa [hjL] using hj.1,
              by simpa [hj1L] using hj.2⟩
          · have he : j+1 = L := by omega
            by_cases hmore : j+1 < d p
            · simpa [hj1L, hmore] using hj.2
            · have hdL : d p = L := by omega
              have hz := hlast.mp hdL
              have hjm : j = L-1 := by omega
              have hh : p.val ⟨j,hjL⟩ = true := by simpa [hjL] using hj.1
              have : p.val ⟨j,hjL⟩ = false := by simpa [hjm] using hz
              simp_all
        · by_cases hjd : j < d p
          · simpa [hjL, hjd] using hj.1
          · have hj1L : ¬j+1 < L := by omega
            have hj1d : ¬j+1 < d p := by omega
            have he : j+1-d p = (j-d p)+1 := by omega
            apply y.property (j-d p)
            exact ⟨by simpa [hjL, hjd] using hj.1,
              by simpa [hj1L, hj1d, he] using hj.2⟩⟩
    have join_mem (y : LegalDigits) : join y ∈ C p := by
      apply Subtype.ext
      funext j
      simp [P, join]
    have shift_join (y : LegalDigits) : shift (join y) (d p) = y := by
      apply Subtype.ext
      funext j
      simp [shift, join, show ¬j+d p < L by omega, show ¬j+d p < d p by omega]
    have completed_length : (completedDigits p).length = d p := by
      simp only [completedDigits, List.length_append, List.length_ofFn, d]
      split <;> simp
    have completed_bits (j : ℕ) (hj : j < d p) :
        ((completedDigits p).map (fun z => decide (z = 1)))[j]?.getD false = (join u).val j := by
      by_cases hjL : j < L
      · rw [List.getElem?_map]
        simp only [completedDigits]
        rw [List.getElem?_append_left (by simpa using hjL)]
        simp [hjL, join]
      · have he : d p = L+1 := by omega
        have hjE : j = L := by omega
        have hl : (List.ofFn p.val).getLast?.getD false = true := by
          cases h : (List.ofFn p.val).getLast?.getD false
          · simp [d,h] at he
          · rfl
        simp [completedDigits, hl,
          hjE, List.length_ofFn, join, he]
    have last_zero : 0 < d p → (join u).val (d p-1) = false := by
      intro _
      rcases hd with hd | hd
      · rw [hd]
        rw [hpref _ (join_mem u) (L-1) (by omega)]
        exact hlast.mp hd
      · have he : d p-1=L := by omega
        rw [he]
        exact hzero _ (join_mem u) hd
    obtain ⟨w,hwlen,hwbits⟩ := block_prefix (d p) (join u) last_zero
    have hwexpand : D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand w .recurrent =
        completedDigits p := by
      have hb : digitsOf w = (completedDigits p).map (fun z => decide (z = 1)) := by
        apply List.ext_getElem
        · simpa only [List.length_map, completed_length, len] using hwlen
        · intro j hj hj'
          have hjd : j < d p := by change j < len w at hj; omega
          have he := (hwbits j hjd).trans (completed_bits j hjd).symm
          simpa [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj'] using he
      apply (List.map_injective_iff.mpr (show Function.Injective (fun z : Fin 2 => decide (z=1)) from ?_)) hb
      intro s t h
      fin_cases s <;> fin_cases t <;> simp_all
    have hcw : c p = w := by
      have he := D5.S0.Automata.BinaryZeckendorfBlockSkeleton.decode_expand
        (D5.S0.Automata.BinaryZeckendorfBlockSkeleton.BlockCode.mk w .recurrent)
      change D5.S0.Automata.BinaryZeckendorfBlockSkeleton.decode
        (D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand w .recurrent) = some _ at he
      rw [hwexpand] at he
      simp [c,he]
    have hc_len : len (c p) = d p := by simpa [hcw] using hwlen
    have hc_sum : S (c p) = Sp p := by
      rw [← hsum (join u) (join_mem u)]
      unfold S
      rw [hc_len]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range] at hj
      rw [hcw, hwbits j hj]
    have hc_range : C p = Set.range (prependWord (c p)) := by
      ext x
      constructor
      · intro hx
        refine ⟨shift x (d p), ?_⟩
        apply Subtype.ext
        funext j
        rw [prepend_digits, hc_len]
        by_cases hj : j < d p
        · rw [if_pos hj, hcw, hwbits j hj]
          by_cases hjL : j < L
          · rw [hpref _ (join_mem u) j hjL, hpref x hx j hjL]
          · have he : d p = L+1 := by omega
            have hjE : j=L := by omega
            rw [hjE, hzero _ (join_mem u) he, hzero x hx he]
        · rw [if_neg hj]
          change x.val (j-d p+d p) = x.val j
          rw [Nat.sub_add_cancel (by omega)]
      · rintro ⟨y,rfl⟩
        apply Subtype.ext
        funext j
        change (prependWord (c p) y).val j = p.val j
        rw [prepend_digits, hc_len, if_pos (show j.val < d p by omega), hcw,
          hwbits j (by omega), hpref _ (join_mem u) j j.isLt]
    have himage : signedValue '' C p = I p := by
      ext t
      constructor
      · rintro ⟨x,hx,rfl⟩
        refine ⟨signedValue (shift x (d p)), ?_, ?_⟩
        · rw [← signed_series_range.1]
          exact ⟨_,rfl⟩
        · rw [tail_value x (d p), hsum x hx]
      · rintro ⟨s,hs,rfl⟩
        obtain ⟨y,hy⟩ := signed_series_range.1.symm ▸ hs
        refine ⟨join y, join_mem y, ?_⟩
        rw [tail_value, hsum _ (join_mem y), shift_join, hy]
    have hshape : I p = Set.Icc (ell p) (upper p) := by
      rw [I, ← Set.uIcc_of_le hab.le]
      change ((fun t : ℝ => Sp p + t) ∘ (fun t => r ^ d p * t)) '' Set.uIcc a b = _
      rw [Set.image_comp, Set.image_const_mul_uIcc, Set.image_const_add_uIcc]
      rfl
    have hlen : upper p - ell p = alpha ^ d p := by
      change max (Sp p + r ^ d p * a) (Sp p + r ^ d p * b) -
        min (Sp p + r ^ d p * a) (Sp p + r ^ d p * b) = _
      rw [max_sub_min_eq_abs]
      have he : Sp p + r ^ d p * b - (Sp p + r ^ d p * a) = r ^ d p * (b-a) := by ring
      rw [he, abs_mul, abs_pow]
      have hr : |r| = alpha := by simp [r, abs_of_pos hp]
      rw [hr, hba]
      norm_num
    exact ⟨himage,hshape,hlen,pow_pos hp _,pow_lt_one₀ hp.le hlt (by omega), hc_len, hc_sum, hc_range⟩
  have partition (L : ℕ) (hL : 1 ≤ L) :
      (⋃ p : X L, I p) = Set.Icc a b ∧
      (∀ p q : X L, p ≠ q → Disjoint (Set.Ioo (ell p) (upper p))
        (Set.Ioo (ell q) (upper q))) := by
    constructor
    · ext t
      constructor
      · intro ht
        obtain ⟨p,hp⟩ := Set.mem_iUnion.mp ht
        rw [← (geometry L hL p).1] at hp
        obtain ⟨x,_,rfl⟩ := hp
        rw [← signed_series_range.1]
        exact ⟨x,rfl⟩
      · intro ht
        obtain ⟨x,rfl⟩ := signed_series_range.1.symm ▸ ht
        apply Set.mem_iUnion.mpr
        refine ⟨P L x, ?_⟩
        rw [← (geometry L hL (P L x)).1]
        exact ⟨x,rfl,rfl⟩
    · intro p q hpq
      apply Set.disjoint_left.mpr
      intro t htp htq
      have hl : max (ell p) (ell q) < t := max_lt htp.1 htq.1
      have hu : t < min (upper p) (upper q) := lt_min htp.2 htq.2
      have hcount : (Set.Ioo (max (ell p) (ell q)) (min (upper p) (upper q))).Countable := by
        apply (Set.countable_range seam).mono
        intro s hs
        by_contra hns
        have hsp : s ∈ I p := by
          rw [(geometry L hL p).2.1]
          exact ⟨(lt_of_le_of_lt (le_max_left _ _) hs.1).le,
            (lt_of_lt_of_le hs.2 (min_le_left _ _)).le⟩
        have hsq : s ∈ I q := by
          rw [(geometry L hL q).2.1]
          exact ⟨(lt_of_le_of_lt (le_max_right _ _) hs.1).le,
            (lt_of_lt_of_le hs.2 (min_le_right _ _)).le⟩
        rw [← (geometry L hL p).1] at hsp
        rw [← (geometry L hL q).1] at hsq
        obtain ⟨x,hx,hxs⟩ := hsp
        obtain ⟨y,hy,hys⟩ := hsq
        have hbounds : s ∈ Set.Icc a b := by
          rw [← signed_series_range.1]
          exact ⟨x,hxs⟩
        obtain ⟨z,hz,huniq⟩ := signed_series_fibres.2.2 s hbounds hns
        have hxy : x = y := (huniq x hxs).trans (huniq y hys).symm
        exact hpq ((show P L x = p from hx).symm.trans
          ((congrArg (P L) hxy).trans (show P L y = q from hy)))
      exact (not_le_of_gt (hl.trans hu)) (Cardinal.Real.Ioo_countable_iff.mp hcount)
  intro L hL
  have hf : (Set.univ : Set (X L)).Finite := by
    unfold X
    exact Set.toFinite _
  exact ⟨hf,geometry L hL,partition L hL⟩

end D5.S1.Digit.Infinite.WindowCylinderPartition
