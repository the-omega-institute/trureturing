/- GID: D5/S1/Digit/Infinite/WindowCylinderPartition
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/WindowCylinderPartition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Legal windows partition the signed value range into closed affine intervals with exact circle cuts and oriented endpoint fibres. -/

import D5.S1.Digit.Infinite.WindowSuccessorGraph

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.WindowCylinderPartition

open D5.S1.Digit.Infinite.SuccessorContinuity
open D5.S1.Digit.Infinite.SignedSeriesRange
open D5.S1.Digit.Infinite.SignedSeriesFibres
open D5.S1.Digit.Infinite.WindowSuccessorGraph
open D5.S1.Digit.Infinite.MultiplierObstruction (phase)
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
/-- Completed legal windows parametrize closed affine intervals with disjoint interiors.
Their circle cuts are the indexed negative golden phases, with the positive-side stream
at each left endpoint and the negative-side stream at each right endpoint. -/
theorem window_cylinder_partition :
  (∀ m, 2 ≤ m → ∃! w : List Block, seamIndex w = m) ∧
  (∀ m, 1 ≤ m → eMinus m ≠ ePlus m ∧
    ∀ x, D5.S1.Digit.Infinite.MultiplierObstruction.phase x = E m ↔
      x = eMinus m ∨ x = ePlus m) ∧
  (∀ L, 1 ≤ L →
    (Set.univ : Set (X L)).Finite ∧
    (∀ p : X L, len (c p) = d p ∧ S (c p) = Sp p ∧
      C p = Set.range (prependWord (c p)) ∧ signedValue '' C p = I p ∧
      I p = Set.Icc (ell p) (upper p) ∧
      upper p - ell p = alpha ^ d p ∧ 0 < alpha ^ d p ∧ alpha ^ d p < 1) ∧
    (⋃ p : X L, I p) = Set.Icc a b ∧
    (∀ p q : X L, p ≠ q → Disjoint (Set.Ioo (ell p) (upper p))
      (Set.Ioo (ell q) (upper q))) ∧
    actualCuts L = B L ∧
    (∀ p : X L, ∃ i j : ℕ, 1 ≤ i ∧ i ≤ G L ∧ 1 ≤ j ∧ j ≤ G L ∧
      ((ell p : ℝ) : Circle) = E i ∧ ((upper p : ℝ) : Circle) = E j ∧
      C p = D5.S1.Digit.Infinite.MultiplierObstruction.phase ⁻¹' A p ∪
        {ePlus i, eMinus j}) ∧
    (∀ m, 1 ≤ m → (P L (eMinus m) ≠ P L (ePlus m) ↔ m ≤ G L))) := by
  classical
  have hp : 0 < alpha := inv_pos.mpr Real.goldenRatio_pos; have hlt : alpha < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have ha : alpha ^ 2 + alpha = 1 := by dsimp [alpha]; rw [Real.inv_goldenRatio]; nlinarith [Real.goldenConj_sq]
  have hab : a < b := (by dsimp [a, b]; nlinarith [sq_nonneg alpha]); have hba : b - a = 1 := by dsimp [a, b]; linarith
  let shift (x : LegalDigits) (n : ℕ) : LegalDigits := ⟨fun j => x.val (j + n), fun j => by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using x.property (j + n)⟩
  let term (x : LegalDigits) (j : ℕ) : ℝ := (-1 : ℝ) ^ (j + 1) * alpha ^ (j + 2) * (if x.val j then 1 else 0)
  have summable_term (x : LegalDigits) : Summable (term x) := by
    apply ((summable_geometric_of_lt_one hp.le hlt).mul_right (alpha ^ 2)).of_norm_bounded; intro j
    dsimp [term]; rw [abs_mul, abs_mul, abs_pow, abs_pow]
    simp only [abs_neg, abs_one, one_pow, one_mul, abs_of_pos hp]; cases x.val j <;> simp [pow_add, mul_nonneg (pow_nonneg hp.le j) (sq_nonneg alpha)]
  have tail_value (x : LegalDigits) (n : ℕ) : signedValue x = (∑ j ∈ Finset.range n, term x j) + r ^ n * signedValue (shift x n) := by
    have ht (j : ℕ) : term x (j + n) = r ^ n * term (shift x n) j := (by simp [term, shift, r, pow_add]; ring); change (∑' j, term x j) = _
    rw [← (summable_term x).sum_add_tsum_nat_add n]
    simp_rw [ht]
    rw [tsum_mul_left]; rfl
  have last_digit {L : ℕ} (p : X L) (hL : 1 ≤ L) : (List.ofFn p.val).getLast?.getD false = p.val ⟨L-1, by omega⟩ := by rw [List.getLast?_eq_getElem?]; simp [List.length_ofFn, show L-1 < L by omega]
  have block_prefix (n : ℕ) (x : LegalDigits) (hz : 0 < n → x.val (n-1) = false) : ∃ w : List Block, len w = n ∧
        ∀ j, j < n → (digitsOf w)[j]?.getD false = x.val j := by
    induction n using Nat.strong_induction_on generalizing x with
    | h n ih =>
      cases n with
      | zero => exact ⟨[],rfl,by omega⟩
      | succ k =>
        cases hx : x.val 0 with
        | false =>
          have ht : 0 < k → (shift x 1).val (k-1) = false := by intro hk; have h := hz (by omega); simpa [shift, show k-1+1=k by omega] using h
          obtain ⟨w,hw,hdig⟩ := ih k (by omega) (shift x 1) ht; refine ⟨.zero :: w, ?_, ?_⟩
          · change (false :: digitsOf w).length = k+1
            simpa [len] using congrArg Nat.succ hw
          · intro j hj
            cases j with
            | zero => simpa [digitsOf, D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand] using hx.symm
            | succ j =>
              simpa [digitsOf, D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand, shift] using hdig j (by omega)
        | true =>
          have hk : 0 < k := by by_contra h; have he : k = 0 := (by omega); have ht := hz (by omega); simp [he,hx] at ht
          have hx1 : x.val 1 = false := by
            cases hh : x.val 1
            · rfl
            · exact False.elim (x.property 0 ⟨hx,hh⟩)
          have ht : 0 < k-1 → (shift x 2).val (k-1-1) = false := by intro hk1; have h := hz (by omega); simpa [shift, show k-1-1+2=k by omega] using h
          obtain ⟨w,hw,hdig⟩ := ih (k-1) (by omega) (shift x 2) ht; refine ⟨.oneZero :: w, ?_, ?_⟩
          · change (true :: false :: digitsOf w).length = k+1
            simp only [List.length_cons]; change len w + 1 + 1 = k+1; omega
          · intro j hj
            cases j with
            | zero => simpa [digitsOf, D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand] using hx.symm
            | succ j =>
              cases j with
              | zero => simpa [digitsOf, D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand] using hx1.symm
              | succ j =>
                simpa [digitsOf, D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand, shift, Nat.add_assoc] using hdig j (by omega)
  have prepend_digits (w : List Block) (y : LegalDigits) (j : ℕ) : (prependWord w y).val j = if j < len w then (digitsOf w)[j]?.getD false
        else y.val (j-len w) := by
    induction w generalizing j with
    | nil => simp [prependWord,len,digitsOf,D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand]
    | cons b w ih =>
      cases b with
      | zero =>
        cases j with
        | zero => rfl
        | succ j =>
          simpa [prependWord,prependBlock,len,digitsOf, D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand] using ih j
      | oneZero =>
        cases j with
        | zero => rfl
        | succ j =>
          cases j with
          | zero => rfl
          | succ j =>
            simpa [prependWord,prependBlock,len,digitsOf, D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand, Nat.add_assoc] using ih j
  have geometry (L : ℕ) (hL : 1 ≤ L) (p : X L) : signedValue '' C p = I p ∧ I p = Set.Icc (ell p) (upper p) ∧
      upper p - ell p = alpha ^ d p ∧ 0 < alpha ^ d p ∧ alpha ^ d p < 1 ∧
      len (c p) = d p ∧ S (c p) = Sp p ∧ C p = Set.range (prependWord (c p)) := by
    have hLd : L ≤ d p := (by dsimp [d]; split <;> omega); have hd : d p = L ∨ d p = L+1 := by dsimp [d]; split <;> omega
    have hlast : d p = L ↔ p.val ⟨L-1, by omega⟩ = false := by simp only [d, last_digit p hL]; cases p.val ⟨L-1, by omega⟩ <;> simp
    have hpref (x : LegalDigits) (hx : x ∈ C p) (j : ℕ) (hj : j < L) : x.val j = p.val ⟨j,hj⟩ := congrArg (fun z : X L => z.val ⟨j,hj⟩) hx
    have hzero (x : LegalDigits) (hx : x ∈ C p) (he : d p = L+1) : x.val L = false := by
      have hh : p.val ⟨L-1, by omega⟩ = true := by
        cases hh : p.val ⟨L-1, by omega⟩
        · have := hlast.mpr hh; omega
        · rfl
      have ht := hpref x hx (L-1) (by omega); have hn := x.property (L-1); rw [ht, hh] at hn; have hl : L-1+1=L := by omega
      rw [hl] at hn; cases hh : x.val L <;> simp_all
    have hsum (x : LegalDigits) (hx : x ∈ C p) : (∑ j ∈ Finset.range (d p), term x j) = Sp p := by
      have hs : (∑ j ∈ Finset.range L, term x j) = Sp p := by rw [← Fin.sum_univ_eq_sum_range]; apply Finset.sum_congr rfl; intro j _; dsimp [term, Sp]; rw [hpref x hx j j.isLt]
      rcases hd with hd | hd
      · simpa [hd] using hs
      · rw [hd, Finset.sum_range_succ, hs]
        simp [term, hzero x hx hd]
    let join (y : LegalDigits) : LegalDigits := ⟨fun j => if h : j < L then p.val ⟨j,h⟩ else if j < d p then false else y.val (j-d p), by
        intro j hj; by_cases hjL : j < L
        · by_cases hj1L : j+1 < L
          · exact p.property j hj1L ⟨by simpa [hjL] using hj.1, by simpa [hj1L] using hj.2⟩
          · have he : j+1 = L := by omega
            by_cases hmore : j+1 < d p
            · simpa [hj1L, hmore] using hj.2
            · have hdL : d p = L := by omega
              have hz := hlast.mp hdL; have hjm : j = L-1 := by omega
              have hh : p.val ⟨j,hjL⟩ = true := (by simpa [hjL] using hj.1); have : p.val ⟨j,hjL⟩ = false := (by simpa [hjm] using hz); simp_all
        · by_cases hjd : j < d p
          · simpa [hjL, hjd] using hj.1
          · have hj1L : ¬j+1 < L := by omega
            have hj1d : ¬j+1 < d p := (by omega); have he : j+1-d p = (j-d p)+1 := (by omega); apply y.property (j-d p)
            exact ⟨by simpa [hjL, hjd] using hj.1, by simpa [hj1L, hj1d, he] using hj.2⟩⟩
    have join_mem (y : LegalDigits) : join y ∈ C p := by apply Subtype.ext; funext j; simp [P, join]
    have shift_join (y : LegalDigits) : shift (join y) (d p) = y := by apply Subtype.ext; funext j; simp [shift, join, show ¬j+d p < L by omega, show ¬j+d p < d p by omega]
    have completed_length : (completedDigits p).length = d p := by simp only [completedDigits, List.length_append, List.length_ofFn, d]; split <;> simp
    have completed_bits (j : ℕ) (hj : j < d p) : ((completedDigits p).map (fun z => decide (z = 1)))[j]?.getD false = (join u).val j := by
      by_cases hjL : j < L
      · rw [List.getElem?_map]
        simp only [completedDigits]; rw [List.getElem?_append_left (by simpa using hjL)]; simp [hjL, join]
      · have he : d p = L+1 := by omega
        have hjE : j = L := by omega
        have hl : (List.ofFn p.val).getLast?.getD false = true := by
          cases h : (List.ofFn p.val).getLast?.getD false
          · simp [d,h] at he
          · rfl
        simp [completedDigits, hl, hjE, List.length_ofFn, join, he]
    have last_zero : 0 < d p → (join u).val (d p-1) = false := by
      intro _; rcases hd with hd | hd
      · rw [hd]
        rw [hpref _ (join_mem u) (L-1) (by omega)]; exact hlast.mp hd
      · have he : d p-1=L := by omega
        rw [he]; exact hzero _ (join_mem u) hd
    obtain ⟨w,hwlen,hwbits⟩ := block_prefix (d p) (join u) last_zero
    have hwexpand : D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand w .recurrent = completedDigits p := by
      have hb : digitsOf w = (completedDigits p).map (fun z => decide (z = 1)) := by
        apply List.ext_getElem
        · simpa only [List.length_map, completed_length, len] using hwlen
        · intro j hj hj'
          have hjd : j < d p := (by change j < len w at hj; omega); have he := (hwbits j hjd).trans (completed_bits j hjd).symm
          simpa [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj'] using he
      apply (List.map_injective_iff.mpr (show Function.Injective (fun z : Fin 2 => decide (z=1)) from ?_)) hb; intro s t h
      fin_cases s <;> fin_cases t <;> simp_all
    have hcw : c p = w := by
      have he := D5.S0.Automata.BinaryZeckendorfBlockSkeleton.decode_expand (D5.S0.Automata.BinaryZeckendorfBlockSkeleton.BlockCode.mk w .recurrent)
      change D5.S0.Automata.BinaryZeckendorfBlockSkeleton.decode (D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand w .recurrent) = some _ at he
      rw [hwexpand] at he; simp [c,he]
    have hc_len : len (c p) = d p := by simpa [hcw] using hwlen
    have hc_sum : S (c p) = Sp p := by
      rw [← hsum (join u) (join_mem u)]; unfold S; rw [hc_len]; apply Finset.sum_congr rfl
      intro j hj; simp only [Finset.mem_range] at hj; rw [hcw, hwbits j hj]
    have hc_range : C p = Set.range (prependWord (c p)) := by
      ext x; constructor
      · intro hx
        refine ⟨shift x (d p), ?_⟩; apply Subtype.ext; funext j; rw [prepend_digits, hc_len]; by_cases hj : j < d p
        · rw [if_pos hj, hcw, hwbits j hj]
          by_cases hjL : j < L
          · rw [hpref _ (join_mem u) j hjL, hpref x hx j hjL]
          · have he : d p = L+1 := by omega
            have hjE : j=L := (by omega); rw [hjE, hzero _ (join_mem u) he, hzero x hx he]
        · rw [if_neg hj]
          change x.val (j-d p+d p) = x.val j; rw [Nat.sub_add_cancel (by omega)]
      · rintro ⟨y,rfl⟩
        apply Subtype.ext; funext j; change (prependWord (c p) y).val j = p.val j
        rw [prepend_digits, hc_len, if_pos (show j.val < d p by omega), hcw, hwbits j (by omega), hpref _ (join_mem u) j j.isLt]
    have himage : signedValue '' C p = I p := by
      ext t; constructor
      · rintro ⟨x,hx,rfl⟩
        refine ⟨signedValue (shift x (d p)), ?_, ?_⟩
        · rw [← signed_series_range.1]
          exact ⟨_,rfl⟩
        · rw [tail_value x (d p), hsum x hx]
      · rintro ⟨s,hs,rfl⟩
        obtain ⟨y,hy⟩ := signed_series_range.1.symm ▸ hs; refine ⟨join y, join_mem y, ?_⟩; rw [tail_value, hsum _ (join_mem y), shift_join, hy]
    have hshape : I p = Set.Icc (ell p) (upper p) := by
      rw [I, ← Set.uIcc_of_le hab.le]; change ((fun t : ℝ => Sp p + t) ∘ (fun t => r ^ d p * t)) '' Set.uIcc a b = _
      rw [Set.image_comp, Set.image_const_mul_uIcc, Set.image_const_add_uIcc]; rfl
    have hlen : upper p - ell p = alpha ^ d p := by
      change max (Sp p + r ^ d p * a) (Sp p + r ^ d p * b) - min (Sp p + r ^ d p * a) (Sp p + r ^ d p * b) = _; rw [max_sub_min_eq_abs]
      have he : Sp p + r ^ d p * b - (Sp p + r ^ d p * a) = r ^ d p * (b-a) := (by ring); rw [he, abs_mul, abs_pow]
      have hr : |r| = alpha := (by simp [r, abs_of_pos hp]); rw [hr, hba]; norm_num
    exact ⟨himage,hshape,hlen,pow_pos hp _,pow_lt_one₀ hp.le hlt (by omega), hc_len, hc_sum, hc_range⟩
  have partition (L : ℕ) (hL : 1 ≤ L) : (⋃ p : X L, I p) = Set.Icc a b ∧ (∀ p q : X L, p ≠ q → Disjoint (Set.Ioo (ell p) (upper p))
        (Set.Ioo (ell q) (upper q))) := by
    constructor
    · ext t
      constructor
      · intro ht
        obtain ⟨p,hp⟩ := Set.mem_iUnion.mp ht; rw [← (geometry L hL p).1] at hp; obtain ⟨x,_,rfl⟩ := hp; rw [← signed_series_range.1]; exact ⟨x,rfl⟩
      · intro ht
        obtain ⟨x,rfl⟩ := signed_series_range.1.symm ▸ ht; apply Set.mem_iUnion.mpr; refine ⟨P L x, ?_⟩; rw [← (geometry L hL (P L x)).1]
        exact ⟨x,rfl,rfl⟩
    · intro p q hpq
      apply Set.disjoint_left.mpr; intro t htp htq
      have hl : max (ell p) (ell q) < t := max_lt htp.1 htq.1; have hu : t < min (upper p) (upper q) := lt_min htp.2 htq.2
      have hcount : (Set.Ioo (max (ell p) (ell q)) (min (upper p) (upper q))).Countable := by
        apply (Set.countable_range seam).mono; intro s hs; by_contra hns
        have hsp : s ∈ I p := by rw [(geometry L hL p).2.1]; exact ⟨(lt_of_le_of_lt (le_max_left _ _) hs.1).le, (lt_of_lt_of_le hs.2 (min_le_left _ _)).le⟩
        have hsq : s ∈ I q := by rw [(geometry L hL q).2.1]; exact ⟨(lt_of_le_of_lt (le_max_right _ _) hs.1).le, (lt_of_lt_of_le hs.2 (min_le_right _ _)).le⟩
        rw [← (geometry L hL p).1] at hsp; rw [← (geometry L hL q).1] at hsq; obtain ⟨x,hx,hxs⟩ := hsp; obtain ⟨y,hy,hys⟩ := hsq
        have hbounds : s ∈ Set.Icc a b := by rw [← signed_series_range.1]; exact ⟨x,hxs⟩
        obtain ⟨z,hz,huniq⟩ := signed_series_fibres.2.2 s hbounds hns; have hxy : x = y := (huniq x hxs).trans (huniq y hys).symm
        exact hpq ((show P L x = p from hx).symm.trans ((congrArg (P L) hxy).trans (show P L y = q from hy)))
      exact (not_le_of_gt (hl.trans hu)) (Cardinal.Real.Ioo_countable_iff.mp hcount)
  have coefficient (j : ℕ) : (-1 : ℝ) ^ (j + 1) * alpha ^ (j + 2) = Real.goldenRatio * (Nat.fib (j + 2) : ℝ) - (Nat.fib (j + 3) : ℝ) := by
    have e := Real.fib_succ_sub_goldenRatio_mul_fib (j + 2)
    have hc : Real.goldenConj = -alpha := by dsimp [alpha]; have hi := Real.inv_goldenRatio; linarith [hi]
    have hsign : (-alpha) ^ (j + 2) = -((-1 : ℝ) ^ (j + 1) * alpha ^ (j + 2)) := by rw [neg_eq_neg_one_mul, mul_pow]; simp only [show j + 2 = (j + 1) + 1 by omega, pow_succ]; ring
    rw [hc, hsign] at e; have hi : j + 2 + 1 = j + 3 := (by omega); rw [hi] at e; linarith

  have seam_phase (w : List Block) : (seam w : Circle) = E (seamIndex w) := by
    let N : ℕ := ∑ j ∈ Finset.range (len w), if (digitsOf w)[j]?.getD false then Nat.fib (j + 2) else 0
    let J : ℕ := ∑ j ∈ Finset.range (len w), if (digitsOf w)[j]?.getD false then Nat.fib (j + 3) else 0
    have hsum : (∑ j ∈ Finset.range (len w), Nat.fib (j + 2)) + 2 = Nat.fib (len w + 3) := by
      have ht := Nat.fib_succ_eq_succ_sum (len w + 2)
      have hs : (∑ j ∈ Finset.range (len w + 2), Nat.fib j) = 1 + ∑ j ∈ Finset.range (len w), Nat.fib (j + 2) := by simpa [Finset.sum_range_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (Finset.sum_range_add Nat.fib 2 (len w))
      rw [hs] at ht
      calc (∑ j ∈ Finset.range (len w), Nat.fib (j + 2)) + 2 = (1 + ∑ j ∈ Finset.range (len w), Nat.fib (j + 2)) + 1 := by omega
        _ = Nat.fib (len w + 2 + 1) := ht.symm
        _ = Nat.fib (len w + 3) := rfl
    have hN : N ≤ ∑ j ∈ Finset.range (len w), Nat.fib (j + 2) := by apply Finset.sum_le_sum; intro j _; split <;> omega
    have hNk : N + 2 ≤ Nat.fib (len w + 3) := (by omega); let k := Nat.fib (len w + 3) - N
    have hreal : (Nat.fib (len w + 3) : ℝ) = (N : ℝ) + (k : ℝ) := by
      exact_mod_cast (show Nat.fib (len w + 3) = N + k by dsimp [k]; omega)
    have hS : S w = Real.goldenRatio * (N : ℝ) - (J : ℝ) := by
      dsimp [S, N, J]
      simp_rw [coefficient]
      push_cast
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _; cases (digitsOf w)[j]?.getD false <;> simp
    have hq : r ^ len w * q = -(Real.goldenRatio * (Nat.fib (len w + 3) : ℝ) - (Nat.fib (len w + 4) : ℝ)) := by
      have h := coefficient (len w + 1)
      have he : r ^ len w * q = -((-1 : ℝ) ^ (len w + 1 + 1) * alpha ^ (len w + 1 + 2)) := by dsimp [r, q]; rw [neg_eq_neg_one_mul alpha, mul_pow]; simp only [pow_add, pow_one]; ring
      simpa only [Nat.add_assoc] using he.trans (congrArg Neg.neg h)
    have hs : seam w = -(k : ℝ) * Real.goldenRatio + ((Nat.fib (len w + 4) : ℤ) - (J : ℤ) : ℤ) := by dsimp [seam, f]; rw [hS, hq, hreal]; push_cast; ring
    change ((seam w : ℝ) : Circle) = ((-(k : ℝ) * Real.goldenRatio : ℝ) : Circle)
    have hz : ((((Nat.fib (len w + 4) : ℤ) - (J : ℤ) : ℤ) : ℝ) : AddCircle (1 : ℝ)) = 0 := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
        ⟨(Nat.fib (len w + 4) : ℤ) - (J : ℤ), by simp⟩
    rw [hs, AddCircle.coe_add, hz, add_zero]

  have bounds (x : LegalDigits) : signedValue x ∈ Set.Icc a b := by rw [← signed_series_range.1]; exact ⟨x,rfl⟩
  have seam_interior (w : List Block) : seam w ∈ Set.Ioo a b := by
    have hl := ((signed_series_fibres.1 w).2 (leftStream w)).mpr (Or.inl rfl)
    have hr := ((signed_series_fibres.1 w).2 (rightStream w)).mpr (Or.inr rfl); have hb := bounds (leftStream w); rw [hl] at hb
    have hna : seam w ≠ a := by intro h; exact (signed_series_fibres.1 w).1 (((signed_series_range.2.1 _).mp (hl.trans h)).trans ((signed_series_range.2.1 _).mp (hr.trans h)).symm)
    have hnb : seam w ≠ b := by intro h; exact (signed_series_fibres.1 w).1 (((signed_series_range.2.2 _).mp (hl.trans h)).trans ((signed_series_range.2.2 _).mp (hr.trans h)).symm)
    exact ⟨lt_of_le_of_ne hb.1 hna.symm, lt_of_le_of_ne hb.2 hnb⟩
  have index_inj : Function.Injective seamIndex := by
    intro w z he; apply signed_series_fibres.2.1
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (show seam w ∈ Set.Ico a (a+1) from ⟨(seam_interior w).1.le, by linarith [(seam_interior w).2]⟩)
      (show seam z ∈ Set.Ico a (a+1) from ⟨(seam_interior z).1.le, by linarith [(seam_interior z).2]⟩)).mp
    rw [seam_phase, seam_phase, he]
  have value_range (N s : ℕ) (hN : 1 ≤ N) (hs : s < G N) : ∃ x : LegalDigits, V (P N x) = s := by
    by_cases h : s < G N-1
    · obtain ⟨x,hx,_⟩ := ((window_successor_graph N hN).1 s (s+1)).mpr (Or.inl ⟨h,rfl⟩)
      exact ⟨x,hx⟩
    · have he : s = G N-1 := by omega
      obtain ⟨x,hx,_⟩ := ((window_successor_graph N hN).1 s 0).mpr (Or.inr (Or.inl ⟨he,rfl⟩)); exact ⟨x,hx⟩
  let pad (N : ℕ) (p : X N) : LegalDigits := ⟨fun i => if hi : i < N then p.val ⟨i,hi⟩ else false, by
      intro i h; by_cases hi : i+1 < N
      · have hi' : i < N := by omega
        simp only [dif_pos hi, dif_pos hi'] at h; exact p.property i hi h
      · simp only [dif_neg hi, Bool.false_eq_true, and_false] at h⟩
  have value_formula (N : ℕ) (x : LegalDigits) : V (P N x) = ∑ j ∈ Finset.range N, if x.val j then Nat.fib (j+2) else 0 := by
    change (∑ i : Fin N, Nat.fib (i.val+2) * (if x.val i then 1 else 0)) = _
    rw [Fin.sum_univ_eq_sum_range (fun j => Nat.fib (j+2) * (if x.val j then 1 else 0)) N]; apply Finset.sum_congr rfl
    intro j _; cases x.val j <;> simp
  have index_exists (m : ℕ) (hm : 2 ≤ m) : ∃! w : List Block, seamIndex w = m := by
    have hex : ∃ t, m ≤ G (t+1) := by refine ⟨m+2, ?_⟩; have h := Nat.le_fib_self (n := m+5) (by omega); change m ≤ Nat.fib (m+5); omega
    let t := Nat.find hex; have ht : m ≤ G (t+1) := Nat.find_spec hex
    have he : ∃ w : List Block, seamIndex w = m := by
      by_cases ht0 : t = 0
      · have hm2 : m = 2 := by norm_num [ht0,G] at ht; omega
        refine ⟨[],?_⟩; norm_num [seamIndex,wordValue,len,digitsOf, D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand,G,hm2]
      · have htpos : 0 < t := by omega
        have hlow : G t < m := by have h := Nat.find_min hex (show t-1 < t by omega); have he : t-1+1=t := (by omega); rw [he] at h; omega
        have hrec : G (t+1) = G t + G (t-1) := by dsimp [G]; rw [show t-1+2=t+1 by omega]; simpa only [Nat.add_assoc,Nat.reduceAdd] using (Nat.fib_add_two (n := t+1)).trans (Nat.add_comm _ _)
        let N := G (t+1)-m; have hN : N < G (t-1) := (by dsimp [N]; omega); by_cases ht1 : t = 1
        · have hm3 : m = 3 := by norm_num [ht1,G] at ht hlow; omega
          refine ⟨[.zero],?_⟩; norm_num [seamIndex,wordValue,len,digitsOf, D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand,G,hm3]
        · obtain ⟨x,hx⟩ := value_range (t-1) N (by omega) hN
          let y := pad (t-1) (P (t-1) x)
          obtain ⟨w,hw,hwbits⟩ := block_prefix t y (by
            intro _
            simp [y,pad])
          have hv : wordValue w = N := by
            rw [wordValue,hw]; have he : t = (t-1)+1 := (by omega); rw [he,Finset.sum_range_succ]; have hb := hwbits (t-1) (by omega)
            simp only [y,pad,lt_self_iff_false,↓reduceDIte] at hb; rw [hb]
            simp only [Bool.false_eq_true,↓reduceIte,add_zero]; rw [← hx,value_formula]; apply Finset.sum_congr rfl; intro j hj
            have hj' : j < t-1 := Finset.mem_range.mp hj; rw [hwbits j (by omega)]; simp [y,pad,P,hj']
          refine ⟨w,?_⟩; dsimp [seamIndex]; rw [hw,hv]; dsimp [N]; omega
    obtain ⟨w,hw⟩ := he; exact ⟨w,hw,fun z hz => index_inj (hz.trans hw.symm)⟩
  have hone : ((1 : ℝ) : Circle) = 0 := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨1,by simp⟩
  have haid : a = 1-Real.goldenRatio := by dsimp [a,alpha]; rw [Real.inv_goldenRatio]; linarith [Real.goldenRatio_add_goldenConj]
  have hac : (a : Circle) = E 1 := by simp [haid,E,hone]
  have hbc : (b : Circle) = (a : Circle) := by have h : b = a+1 := (by linarith); rw [h,AddCircle.coe_add,hone,add_zero]
  have real_fibre (t : ℝ) (ht : t ∈ Set.Ioo a b) (x : LegalDigits) : phase x = (t : Circle) ↔ signedValue x = t := by
    constructor
    · intro hx
      have hxb : signedValue x ≠ b := by
        intro hb; have he : (t : Circle) = (a : Circle) := by rw [← hx]; change (signedValue x : Circle) = (a : Circle); rw [hb,hbc]
        have he' := (AddCircle.coe_eq_coe_iff_of_mem_Ico (show t ∈ Set.Ico a (a+1) from ⟨ht.1.le,by linarith [ht.2]⟩)
          (show a ∈ Set.Ico a (a+1) from ⟨le_rfl,by linarith⟩)).mp he
        exact (ne_of_gt ht.1) he'
      exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (show signedValue x ∈ Set.Ico a (a+1) from
          ⟨(bounds x).1,by have h := lt_of_le_of_ne (bounds x).2 hxb; linarith⟩)
        (show t ∈ Set.Ico a (a+1) from ⟨ht.1.le,by linarith [ht.2]⟩)).mp hx
    · intro hx
      exact congrArg (fun t : ℝ => (t : Circle)) hx
  have phase_seam (w : List Block) (x : LegalDigits) : phase x = E (seamIndex w) ↔ signedValue x = seam w := by rw [← seam_phase]; exact real_fibre _ (seam_interior w) x
  have seam_word (m : ℕ) (hm : 2 ≤ m) : seamIndex (seamWord m) = m := by have he : ∃ w, seamIndex w = m := (index_exists m hm).exists; simp only [seamWord,dif_pos he]; exact Classical.choose_spec he
  have endpoint_fibres (m : ℕ) (hm : 1 ≤ m) : eMinus m ≠ ePlus m ∧ ∀ x, phase x = E m ↔ x = eMinus m ∨ x = ePlus m := by
    by_cases hm1 : m ≤ 1
    · have hmE : m=1 := by omega
      have hne : v ≠ u := (by intro h; have ht := congrArg (fun x : LegalDigits => x.val 0) h; simp [u,v] at ht); simp only [eMinus,ePlus,if_pos hm1]
      refine ⟨hne,?_⟩; intro x; rw [hmE,← hac]; constructor
      · intro hx
        by_cases hb : signedValue x = b
        · exact Or.inl ((signed_series_range.2.2 x).mp hb)
        · right
          apply (signed_series_range.2.1 x).mp
          exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (show signedValue x ∈ Set.Ico a (a+1) from
              ⟨(bounds x).1,by have h := lt_of_le_of_ne (bounds x).2 hb; linarith⟩)
            (show a ∈ Set.Ico a (a+1) from ⟨le_rfl,by linarith⟩)).mp hx
      · rintro (rfl | rfl)
        · change (signedValue v : Circle) = (a : Circle)
          rw [(signed_series_range.2.2 v).mpr rfl,hbc]
        · change (signedValue u : Circle) = (a : Circle)
          rw [(signed_series_range.2.1 u).mpr rfl]
    · have hwm := seam_word m (by omega)
      have hf (x : LegalDigits) : phase x = E m ↔ x = leftStream (seamWord m) ∨ x = rightStream (seamWord m) := by have hs := phase_seam (seamWord m) x; rw [hwm] at hs; exact hs.trans ((signed_series_fibres.1 (seamWord m)).2 x)
      have hne := (signed_series_fibres.1 (seamWord m)).1; by_cases he : len (seamWord m) % 2 = 0
      · simp only [eMinus,ePlus,if_neg hm1,if_pos he]
        exact ⟨hne.symm,fun x => (hf x).trans or_comm⟩
      · simp only [eMinus,ePlus,if_neg hm1,if_neg he]
        exact ⟨hne,hf⟩
  have value_bound (N : ℕ) (x : LegalDigits) : V (P N x) < G N := by
    by_cases hN : N = 0
    · subst N
      simp [V,G]
    · have hpos : 0 < G N := Nat.fib_pos.mpr (by omega)
      have hb : beta N < G N := by have h1 : 0 < Nat.fib (N+1) := Nat.fib_pos.mpr (by omega); have h2 := Nat.fib_mono (show N+1 ≤ N+2 by omega); dsimp [beta,G]; omega
      have he := ((window_successor_graph N (by omega)).1 (V (P N x)) (V (P N (T x)))).mp ⟨x,rfl,rfl⟩; rcases he with h | h | h <;> omega
  have word_last (w : List Block) : (digitsOf w).getLast?.getD false = false := by
    induction w with
    | nil => rfl
    | cons b w ih =>
      cases w with
      | nil => cases b <;> rfl
      | cons d w =>
        cases b <;> cases d <;>
          simpa [digitsOf,D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand] using ih
  have word_band (w : List Block) (ht : 0 < len w) : G (len w) < seamIndex w ∧ seamIndex w ≤ G (len w+1) := by
    let x := prependWord w u
    have hzero : x.val (len w-1) = false := by rw [prepend_digits,if_pos (show len w-1 < len w by omega)]; have hz := word_last w; rw [List.getLast?_eq_getElem?] at hz; exact hz
    have hv : wordValue w = V (P (len w-1) x) := by
      rw [value_formula]; unfold wordValue; have he : len w = (len w-1)+1 := by omega
      conv_lhs => rw [he,Finset.sum_range_succ]
      have hz : (digitsOf w)[len w-1]?.getD false = false := (by simpa [List.getLast?_eq_getElem?,len] using word_last w); rw [hz]
      simp only [Bool.false_eq_true,↓reduceIte,add_zero]; apply Finset.sum_congr rfl
      intro j hj; have hj' : j < len w := (by have := Finset.mem_range.mp hj; omega); rw [prepend_digits,if_pos hj']
    have hb := value_bound (len w-1) x; rw [← hv] at hb
    have hrec : G (len w+1) = G (len w) + G (len w-1) := by dsimp [G]; rw [show len w-1+2=len w+1 by omega]; simpa only [Nat.add_assoc,Nat.reduceAdd] using (Nat.fib_add_two (n := len w+1)).trans (Nat.add_comm _ _)
    dsimp [seamIndex]; omega
  have gmono : StrictMono G := by apply strictMono_nat_of_lt_succ; intro n; exact Nat.fib_lt_fib_succ (by omega)
  have word_threshold (L : ℕ) (hL : 1 ≤ L) (w : List Block) : seamIndex w ≤ G L ↔ len w < L := by
    by_cases ht : len w = 0
    · have hw : w = [] := by
        cases w with
        | nil => rfl
        | cons b w => cases b <;> simp [len,digitsOf, D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand] at ht
      have hG : 2 ≤ G L := (by have := gmono.monotone hL; norm_num [G] at this ⊢; exact this); subst w
      norm_num [len,digitsOf,D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand, seamIndex,wordValue,G] at hG ⊢; exact ⟨fun _ => hL,fun _ => hG⟩
    · have hb := word_band w (by omega)
      constructor
      · intro h
        by_contra hn; have := gmono.monotone (show L ≤ len w by omega); omega
      · intro h
        exact hb.2.trans (gmono.monotone (by omega))
  have prepend_append (w z : List Block) (x : LegalDigits) : prependWord (w++z) x = prependWord w (prependWord z x) := by
    induction w with
    | nil => rfl
    | cons b w ih => simp only [List.cons_append,prependWord,ih]
  have pair_windows (L : ℕ) (w : List Block) : P L (leftStream w) ≠ P L (rightStream w) ↔ len w < L := by
    constructor
    · intro h
      by_contra hn; apply h; apply Subtype.ext; funext j
      change (leftStream w).val j = (rightStream w).val j; simp only [leftStream,rightStream,prepend_append]
      simp only [prepend_digits,if_pos (show j.val < len w by omega)]
    · intro ht he
      have hd := congrArg (fun p : X L => p.val ⟨len w,ht⟩) he; change (leftStream w).val (len w) = (rightStream w).val (len w) at hd
      simp only [leftStream,rightStream,prepend_append] at hd; simp only [prepend_digits,lt_self_iff_false,↓reduceIte,Nat.sub_self] at hd
      norm_num [len,digitsOf,D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand] at hd
  have endpoint_split (L : ℕ) (hL : 1 ≤ L) (m : ℕ) (hm : 1 ≤ m) : P L (eMinus m) ≠ P L (ePlus m) ↔ m ≤ G L := by
    by_cases hm1 : m ≤ 1
    · have hmE : m=1 := by omega
      have hG : 1 ≤ G L := Nat.fib_pos.mpr (by omega)
      have hne : P L v ≠ P L u := by intro h; have hh := congrArg (fun p : X L => p.val ⟨0,by omega⟩) h; simp [P,u,v] at hh
      simp [eMinus,ePlus,hmE,hG,hne]
    · have hwm := seam_word m (by omega)
      have he : len (seamWord m) < L ↔ m ≤ G L := by have hs := word_threshold L hL (seamWord m); rw [hwm] at hs; exact hs.symm
      by_cases hp : len (seamWord m) % 2 = 0
      · simp only [eMinus,ePlus,if_neg hm1,if_pos hp]
        rw [ne_comm,pair_windows]; exact he
      · simp only [eMinus,ePlus,if_neg hm1,if_neg hp,pair_windows]
        exact he
  have interval_subset (L : ℕ) (hL : 1 ≤ L) (p : X L) : I p ⊆ Set.Icc a b := by rw [← (partition L hL).1]; exact Set.subset_iUnion (fun p : X L => I p) p
  have interval_ends (L : ℕ) (hL : 1 ≤ L) (p : X L) : ell p < upper p ∧ ell p ∈ I p ∧ upper p ∈ I p := by
    have hg := geometry L hL p; have hl : ell p < upper p := by linarith [hg.2.2.1,hg.2.2.2.1]
    rw [hg.2.1]; exact ⟨hl,⟨le_rfl,hl.le⟩,⟨hl.le,le_rfl⟩⟩
  have no_other (L : ℕ) (hL : 1 ≤ L) (p q : X L) (hpq : p ≠ q) : Disjoint (Set.Ioo (ell p) (upper p)) (I q) := by
    apply Set.disjoint_left.mpr; intro t hp hq; rw [(geometry L hL q).2.1] at hq
    have hlt : max (ell p) (ell q) < min (upper p) (upper q) := by
      apply max_lt
      · exact lt_min (interval_ends L hL p).1 (hp.1.trans_le hq.2)
      · exact lt_min (hq.1.trans_lt hp.2) (interval_ends L hL q).1
    obtain ⟨s,hs1,hs2⟩ := exists_between hlt; apply Set.disjoint_left.mp ((partition L hL).2 p q hpq)
    · exact ⟨(le_max_left _ _).trans_lt hs1,hs2.trans_le (min_le_left _ _)⟩
    · exact ⟨(le_max_right _ _).trans_lt hs1,hs2.trans_le (min_le_right _ _)⟩
  have shared_end (L : ℕ) (hL : 1 ≤ L) (p q : X L) (hpq : p ≠ q) (t : ℝ) (hp : t ∈ I p) (hq : t ∈ I q) : t = ell p ∨ t = upper p := by
    by_contra h; push Not at h; have hp' := hp; rw [(geometry L hL p).2.1] at hp'
    exact Set.disjoint_left.mp (no_other L hL p q hpq) ⟨lt_of_le_of_ne hp'.1 h.1.symm,lt_of_le_of_ne hp'.2 h.2⟩ hq
  have boundary_other (L : ℕ) (hL : 1 ≤ L) (p : X L) (t : ℝ) (ht : t=ell p ∨ t=upper p) (ha : a<t) (hb : t<b) : ∃ q : X L, q ≠ p ∧ t ∈ I q := by
    have : Finite (X L) := (by unfold X; infer_instance); let J : Set ℝ := ⋃ q : X L, ⋃ (_ : q ≠ p), I q
    have hJ : IsClosed J := by apply isClosed_iUnion_of_finite; intro q; apply isClosed_iUnion_of_finite; intro _; rw [(geometry L hL q).2.1]; exact isClosed_Icc
    have covers (s : ℝ) (hs : s ∈ Set.Icc a b) (hn : s ∉ I p) : s ∈ J := by
      rw [← (partition L hL).1] at hs; obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hs
      have hqp : q ≠ p := (by rintro rfl; exact hn hq); exact Set.mem_iUnion.mpr ⟨q,Set.mem_iUnion.mpr ⟨hqp,hq⟩⟩
    have htJ : t ∈ J := by
      rcases ht with ht | ht
      · have hsub : Set.Ioo a t ⊆ J := by
          intro s hs; apply covers s ⟨hs.1.le,(hs.2.trans hb).le⟩; rw [(geometry L hL p).2.1]; intro hn; linarith [hn.1,hs.2]
        have htcl : t ∈ closure (Set.Ioo a t) := (by rw [closure_Ioo ha.ne]; exact ⟨ha.le,le_rfl⟩); exact hJ.closure_eq ▸ (closure_mono hsub htcl)
      · have hsub : Set.Ioo t b ⊆ J := by
          intro s hs; apply covers s ⟨(ha.trans hs.1).le,hs.2.le⟩; rw [(geometry L hL p).2.1]; intro hn; linarith [hn.2,hs.1]
        have htcl : t ∈ closure (Set.Ioo t b) := (by rw [closure_Ioo hb.ne]; exact ⟨le_rfl,hb.le⟩); exact hJ.closure_eq ▸ (closure_mono hsub htcl)
    obtain ⟨q,hq⟩ := Set.mem_iUnion.mp htJ; obtain ⟨hne,htq⟩ := Set.mem_iUnion.mp hq; exact ⟨q,hne,htq⟩
  have index_two (w : List Block) : 2 ≤ seamIndex w := by
    by_cases ht : 0 < len w
    · have hb := (word_band w ht).1
      have hg : 0 < G (len w) := Nat.fib_pos.mpr (by omega); omega
    · have hw : w=[] := by
        cases w with
        | nil => rfl
        | cons b w => cases b <;> simp [len,digitsOf, D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand] at ht
      subst w; norm_num [seamIndex,wordValue,len,digitsOf, D5.S0.Automata.BinaryZeckendorfBlockSkeleton.expand,G]
  have cuts (L : ℕ) (hL : 1 ≤ L) : actualCuts L = B L := by
    ext z; constructor
    · rintro ⟨p,hz⟩
      obtain ⟨t,ht,hzt⟩ : ∃ t : ℝ, (t=ell p ∨ t=upper p) ∧ z=(t : Circle) := by
        rcases hz with hz | hz
        · exact ⟨ell p,Or.inl rfl,hz⟩
        · exact ⟨upper p,Or.inr rfl,hz⟩
      have htp : t ∈ I p := by
        rcases ht with rfl | rfl
        · exact (interval_ends L hL p).2.1
        · exact (interval_ends L hL p).2.2
      have htb := interval_subset L hL p htp; by_cases hta : t=a
      · refine ⟨1,⟨le_rfl,?_⟩,?_⟩
        · exact Nat.fib_pos.mpr (by omega)
        · rw [hzt,hta,hac]
      by_cases htb' : t=b
      · refine ⟨1,⟨le_rfl,?_⟩,?_⟩
        · exact Nat.fib_pos.mpr (by omega)
        · rw [hzt,htb',hbc,hac]
      obtain ⟨q,hqp,htq⟩ := boundary_other L hL p t ht (lt_of_le_of_ne htb.1 (fun h => hta h.symm)) (lt_of_le_of_ne htb.2 htb')
      rw [← (geometry L hL p).1] at htp; rw [← (geometry L hL q).1] at htq; obtain ⟨x,hx,hxt⟩ := htp; obtain ⟨y,hy,hyt⟩ := htq
      have hxy : P L x ≠ P L y := by change P L x=p at hx; change P L y=q at hy; rw [hx,hy]; exact hqp.symm
      have hseam : t ∈ Set.range seam := by by_contra hn; obtain ⟨s,_,hu⟩ := signed_series_fibres.2.2 t htb hn; exact hxy (congrArg (P L) ((hu x hxt).trans (hu y hyt).symm))
      obtain ⟨w,hw⟩ := hseam; have hxm : phase x = E (seamIndex w) := by change (signedValue x : Circle) = _; rw [hxt,← hw,seam_phase]
      have hym : phase y = E (seamIndex w) := by change (signedValue y : Circle) = _; rw [hyt,← hw,seam_phase]
      have hxF := (endpoint_fibres _ (by have := index_two w; omega)).2 x |>.mp hxm
      have hyF := (endpoint_fibres _ (by have := index_two w; omega)).2 y |>.mp hym
      have hsplit : P L (eMinus (seamIndex w)) ≠ P L (ePlus (seamIndex w)) := by
        intro he; apply hxy; rcases hxF with hxF | hxF <;> rcases hyF with hyF | hyF
        · exact (congrArg (P L) hxF).trans (congrArg (P L) hyF).symm
        · exact (congrArg (P L) hxF).trans (he.trans (congrArg (P L) hyF).symm)
        · exact (congrArg (P L) hxF).trans (he.symm.trans (congrArg (P L) hyF).symm)
        · exact (congrArg (P L) hxF).trans (congrArg (P L) hyF).symm
      have hm := (endpoint_split L hL _ (by have := index_two w; omega)).mp hsplit; refine ⟨seamIndex w,⟨by have := index_two w; omega,hm⟩,?_⟩
      rw [← seam_phase,hw,hzt]
    · rintro ⟨m,hm,rfl⟩
      by_cases hm1 : m=1
      · let p := P L u
        have hpa : a ∈ I p := by rw [← (geometry L hL p).1]; exact ⟨u,rfl,(signed_series_range.2.1 u).mpr rfl⟩
        have hl := (interval_subset L hL p ((interval_ends L hL p).2.1)).1; have hpa' := hpa
        rw [(geometry L hL p).2.1] at hpa'; have he : ell p = a := le_antisymm hpa'.1 hl; exact ⟨p,Or.inl (by rw [he,hm1,hac])⟩
      · let w := seamWord m
        have hw : seamIndex w=m := seam_word m (by have := hm.1; omega); have hx := (endpoint_fibres m hm.1).2 (eMinus m) |>.mpr (Or.inl rfl)
        have hy := (endpoint_fibres m hm.1).2 (ePlus m) |>.mpr (Or.inr rfl)
        have hxs : signedValue (eMinus m)=seam w := by apply (phase_seam w _).mp; rwa [hw]
        have hys : signedValue (ePlus m)=seam w := by apply (phase_seam w _).mp; rwa [hw]
        have hp : seam w ∈ I (P L (eMinus m)) := by rw [← (geometry L hL _).1]; exact ⟨eMinus m,rfl,hxs⟩
        have hq : seam w ∈ I (P L (ePlus m)) := by rw [← (geometry L hL _).1]; exact ⟨ePlus m,rfl,hys⟩
        have hd := shared_end L hL _ _ ((endpoint_split L hL m hm.1).mpr hm.2) _ hp hq; refine ⟨P L (eMinus m),?_⟩
        have he := seam_phase w; rw [hw] at he; rw [← he]; exact hd.imp (congrArg (fun t : ℝ => (t : Circle))) (congrArg (fun t : ℝ => (t : Circle)))
  have first_side (x : LegalDigits) : (x.val 0 = false → q ≤ signedValue x) ∧ (x.val 0 = true → signedValue x ≤ q) := by
    constructor
    · intro hx
      have hv := tail_value x 1; simp [term,hx,r] at hv; have hu := (bounds (shift x 1)).2; dsimp [b] at hu
      have hmul := mul_le_mul_of_nonpos_left hu (neg_nonpos.mpr hp.le); dsimp [q]; nlinarith
    · intro hx
      have hx1 : x.val 1 = false := by
        cases hh : x.val 1
        · rfl
        · exact False.elim (x.property 0 ⟨hx,hh⟩)
      have hv := tail_value x 2; norm_num [term,hx,hx1,r,Finset.sum_range_succ] at hv; have hu := (bounds (shift x 2)).2; dsimp [b] at hu
      have hmul := mul_le_mul_of_nonneg_left hu (sq_nonneg alpha)
      have he : alpha ^ 4 + alpha ^ 3 = alpha ^ 2 := by nlinarith [congrArg (fun t : ℝ => alpha ^ 2*t) ha, congrArg (fun t : ℝ => alpha*t) ha]
      dsimp [q]; nlinarith
  have real_sides (w : List Block) (x : LegalDigits) (hprefix : ∀ j, j < len w → x.val j = (digitsOf w)[j]?.getD false) : (x.val (len w) = false →
        if len w % 2 = 0 then seam w ≤ signedValue x else signedValue x ≤ seam w) ∧
      (x.val (len w) = true → if len w % 2 = 0 then signedValue x ≤ seam w else seam w ≤ signedValue x) := by
    have hv : signedValue x = S w + r ^ len w * signedValue (shift x (len w)) := by rw [tail_value]; congr 1; apply Finset.sum_congr rfl; intro j hj; dsimp [term]; rw [hprefix j (Finset.mem_range.mp hj)]
    have hr : r ^ len w = if len w % 2 = 0 then alpha ^ len w else -(alpha ^ len w) := by rw [r,neg_eq_neg_one_mul,mul_pow,neg_one_pow_eq_ite]; simp [Nat.even_iff]
    have hf (hx : x.val (len w)=false) : q ≤ signedValue (shift x (len w)) := (first_side (shift x (len w))).1 (by simpa [shift] using hx)
    have ht (hx : x.val (len w)=true) : signedValue (shift x (len w)) ≤ q := (first_side (shift x (len w))).2 (by simpa [shift] using hx)
    by_cases he : len w % 2 = 0
    · have hpow : 0 ≤ r ^ len w := by rw [hr,if_pos he]; exact (pow_pos hp _).le
      simp only [if_pos he]; constructor
      · intro hx
        have h := mul_le_mul_of_nonneg_left (hf hx) hpow; dsimp [seam,f]; linarith
      · intro hx
        have h := mul_le_mul_of_nonneg_left (ht hx) hpow; dsimp [seam,f]; linarith
    · have hpow : r ^ len w ≤ 0 := by rw [hr,if_neg he]; exact neg_nonpos.mpr (pow_pos hp _).le
      simp only [if_neg he]; constructor
      · intro hx
        have h := mul_le_mul_of_nonpos_left (hf hx) hpow; dsimp [seam,f]; linarith
      · intro hx
        have h := mul_le_mul_of_nonpos_left (ht hx) hpow; dsimp [seam,f]; linarith
  have left_side (L : ℕ) (w : List Block) (hL : len w < L) (x : LegalDigits) (hx : P L x = P L (leftStream w)) :
      if len w % 2 = 0 then seam w ≤ signedValue x else signedValue x ≤ seam w := by
    have hpref (j : ℕ) (hj : j < len w) : x.val j = (digitsOf w)[j]?.getD false := by
      have he := congrArg (fun p : X L => p.val ⟨j,by omega⟩) hx; change x.val j = (leftStream w).val j at he
      rw [leftStream,prepend_append,prepend_digits,if_pos hj] at he; exact he
    have hbit : x.val (len w) = false := by
      have he := congrArg (fun p : X L => p.val ⟨len w,hL⟩) hx; change x.val (len w) = (leftStream w).val (len w) at he
      rw [leftStream,prepend_append,prepend_digits,if_neg (lt_irrefl _)] at he; simpa [prependWord,prependBlock] using he
    exact (real_sides w x hpref).1 hbit
  have right_side (L : ℕ) (w : List Block) (hL : len w < L) (x : LegalDigits) (hx : P L x = P L (rightStream w)) :
      if len w % 2 = 0 then signedValue x ≤ seam w else seam w ≤ signedValue x := by
    have hpref (j : ℕ) (hj : j < len w) : x.val j = (digitsOf w)[j]?.getD false := by
      have he := congrArg (fun p : X L => p.val ⟨j,by omega⟩) hx; change x.val j = (rightStream w).val j at he
      rw [rightStream,prepend_append,prepend_digits,if_pos hj] at he; exact he
    have hbit : x.val (len w) = true := by
      have he := congrArg (fun p : X L => p.val ⟨len w,hL⟩) hx; change x.val (len w) = (rightStream w).val (len w) at he
      rw [rightStream,prepend_append,prepend_digits,if_neg (lt_irrefl _)] at he; simpa [prependWord,prependBlock] using he
    exact (real_sides w x hpref).2 hbit
  have oriented_sides (L m : ℕ) (hL : 1 ≤ L) (hm : 2 ≤ m) (hmL : m ≤ G L) (x : LegalDigits) : (P L x = P L (eMinus m) → signedValue x ≤ seam (seamWord m)) ∧
      (P L x = P L (ePlus m) → seam (seamWord m) ≤ signedValue x) := by
    have hw := seam_word m hm; have ht : len (seamWord m) < L := (word_threshold L hL _).mp (by rw [hw]; exact hmL)
    have hm1 : ¬m ≤ 1 := (by omega); by_cases he : len (seamWord m) % 2 = 0
    · simp only [eMinus,ePlus,if_neg hm1,if_pos he]
      exact ⟨fun hx => by simpa [he] using right_side L _ ht x hx, fun hx => by simpa [he] using left_side L _ ht x hx⟩
    · simp only [eMinus,ePlus,if_neg hm1,if_neg he]
      exact ⟨fun hx => by simpa [he] using left_side L _ ht x hx, fun hx => by simpa [he] using right_side L _ ht x hx⟩
  have oriented_formula (L : ℕ) (hL : 1 ≤ L) (p : X L) : ∃ i j : ℕ, 1 ≤ i ∧ i ≤ G L ∧ 1 ≤ j ∧ j ≤ G L ∧ (ell p : Circle)=E i ∧ (upper p : Circle)=E j ∧
        C p = phase ⁻¹' A p ∪ {ePlus i,eMinus j} := by
    have hcutl : (ell p : Circle) ∈ actualCuts L := ⟨p,Or.inl rfl⟩; have hcutr : (upper p : Circle) ∈ actualCuts L := ⟨p,Or.inr rfl⟩
    rw [cuts L hL] at hcutl hcutr; obtain ⟨i,hi,hie⟩ := hcutl
    obtain ⟨j,hj,hje⟩ := hcutr; have hlo := (interval_subset L hL p ((interval_ends L hL p).2.1)).1
    have hhi := (interval_subset L hL p ((interval_ends L hL p).2.2)).2; have hlen := (interval_ends L hL p).1
    have hxl : ell p ∈ signedValue '' C p := (geometry L hL p).1.symm ▸ (interval_ends L hL p).2.1
    have hxr : upper p ∈ signedValue '' C p := (geometry L hL p).1.symm ▸ (interval_ends L hL p).2.2; obtain ⟨xl,hxl,hxlv⟩ := hxl
    obtain ⟨xr,hxr,hxrv⟩ := hxr; have hxli : phase xl=E i := by change (signedValue xl : Circle)=_; rw [hxlv,← hie]
    have hxrj : phase xr=E j := by change (signedValue xr : Circle)=_; rw [hxrv,← hje]
    have left_owner : ePlus i ∈ C p := by
      rcases ((endpoint_fibres i hi.1).2 xl).mp hxli with he | he
      · have hminus : eMinus i ∈ C p := he ▸ hxl
        by_cases hi1 : i ≤ 1
        · have hev : signedValue xl=b := by rw [he,eMinus,if_pos hi1]; exact (signed_series_range.2.2 v).mpr rfl
          exfalso; linarith
        · have hs : seam (seamWord i)=ell p := by
            have hv := (phase_seam (seamWord i) xl).mp (by rwa [seam_word i (by omega)]); exact hv.symm.trans hxlv
          have hb := (oriented_sides L i hL (by omega) hi.2 xr).1 ((show P L xr=p from hxr).trans (show P L (eMinus i)=p from hminus).symm); exfalso
          linarith
      · exact he ▸ hxl
    have right_owner : eMinus j ∈ C p := by
      rcases ((endpoint_fibres j hj.1).2 xr).mp hxrj with he | he
      · exact he ▸ hxr
      · have hplus : ePlus j ∈ C p := he ▸ hxr
        by_cases hj1 : j ≤ 1
        · have heu : signedValue xr=a := by rw [he,ePlus,if_pos hj1]; exact (signed_series_range.2.1 u).mpr rfl
          exfalso; linarith
        · have hs : seam (seamWord j)=upper p := by
            have hv := (phase_seam (seamWord j) xr).mp (by rwa [seam_word j (by omega)]); exact hv.symm.trans hxrv
          have hb := (oriented_sides L j hL (by omega) hj.2 xl).2 ((show P L xl=p from hxl).trans (show P L (ePlus j)=p from hplus).symm); exfalso
          linarith
    have not_left_minus : eMinus i ∉ C p := by intro hx; exact ((endpoint_split L hL i hi.1).mpr hi.2) ((show P L (eMinus i)=p from hx).trans (show P L (ePlus i)=p from left_owner).symm)
    have not_right_plus : ePlus j ∉ C p := by intro hx; exact ((endpoint_split L hL j hj.1).mpr hj.2) ((show P L (eMinus j)=p from right_owner).trans (show P L (ePlus j)=p from hx).symm)
    refine ⟨i,j,hi.1,hi.2,hj.1,hj.2,hie.symm,hje.symm,?_⟩; ext x; constructor
    · intro hx
      have hv : signedValue x ∈ I p := (by rw [← (geometry L hL p).1]; exact ⟨x,hx,rfl⟩); rw [(geometry L hL p).2.1] at hv
      by_cases hl : signedValue x=ell p
      · have hphase : phase x=E i := by change (signedValue x : Circle)=_; rw [hl,← hie]
        rcases ((endpoint_fibres i hi.1).2 x).mp hphase with he | he
        · exact False.elim (not_left_minus (he ▸ hx))
        · exact Or.inr (by simp [he])
      by_cases hr : signedValue x=upper p
      · have hphase : phase x=E j := by change (signedValue x : Circle)=_; rw [hr,← hje]
        rcases ((endpoint_fibres j hj.1).2 x).mp hphase with he | he
        · exact Or.inr (by simp [he])
        · exact False.elim (not_right_plus (he ▸ hx))
      · exact Or.inl ⟨signedValue x, ⟨lt_of_le_of_ne hv.1 (fun h => hl h.symm),lt_of_le_of_ne hv.2 hr⟩,rfl⟩
    · rintro (hx | hx)
      · obtain ⟨t,ht,htx⟩ := hx
        have htI : t ∈ Set.Ioo a b := ⟨hlo.trans_lt ht.1,ht.2.trans_le hhi⟩; have hval : signedValue x=t := (real_fibre t htI x).mp htx.symm
        have hxI : signedValue x ∈ I (P L x) := (by rw [← (geometry L hL (P L x)).1]; exact ⟨x,rfl,rfl⟩); change P L x=p
        by_contra hne; exact Set.disjoint_left.mp (no_other L hL p (P L x) (fun h => hne h.symm)) (hval.symm ▸ ht) hxI
      · simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact left_owner
        · exact right_owner
  refine ⟨index_exists,endpoint_fibres,?_⟩; intro L hL; have hf : (Set.univ : Set (X L)).Finite := by unfold X; exact Set.toFinite _
  refine ⟨hf,?_,(partition L hL).1,(partition L hL).2,cuts L hL,oriented_formula L hL,endpoint_split L hL⟩
  intro p
  obtain ⟨himage,hshape,hlen,hpos,hsmall,hclen,hcsum,hcrange⟩ := geometry L hL p
  exact ⟨hclen,hcsum,hcrange,himage,hshape,hlen,hpos,hsmall⟩

end D5.S1.Digit.Infinite.WindowCylinderPartition
