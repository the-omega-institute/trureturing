/- GID: D5/S3/Arith/Divisors/ErdosNicolas/BoxChecker
   generality: I
   mirror-B: none(waiver:proof-helper-in-main-import-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; instance=D5/S3/Arith/Divisors/ErdosNicolas/Data/Main00.chunk_checked
   digest: Exact exponent-box coverage and upper-corner numerical certificates. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Classification
import D5.S3.Arith.Divisors.ErdosNicolas.FiniteChecker
import D5.S3.Arith.Divisors.ErdosNicolas.GapChecker
import D5.S3.Arith.Divisors.ErdosNicolas.RankMajorant
import D5.S3.Arith.Divisors.ErdosNicolas.RankIndexed
import Mathlib.Algebra.BigOperators.Fin

/-! Binary splits preserve every exponent vector; leaves certify complete divisor tables. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas

open Finset

/-- Natural number associated to a prime-base exponent vector. -/
def exponentValue {k : ℕ} (p v : Fin k → ℕ) : ℕ := ∏ i, p i ^ v i

/-- Factor data for the same exponent vector, in coordinate order. -/
def exponentFactors {k : ℕ} (p v : Fin k → ℕ) : List (ℕ × ℕ) :=
  List.ofFn fun i => (p i, v i)

/-- Every coordinate is in its closed lower/upper interval. -/
def InExponentBox {k : ℕ} (lo hi v : Fin k → ℕ) : Prop :=
  ∀ i, lo i ≤ v i ∧ v i ≤ hi i

private theorem factorValue_eq_prod (fs : List (ℕ × ℕ)) :
    factorValue fs = (fs.map fun f => f.1 ^ f.2).prod := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [factorValue, ih]

/-- The explicit factor certificate denotes the product used by the exponent box. -/
private theorem factorValue_exponentFactors {k : ℕ} (p v : Fin k → ℕ) :
    factorValue (exponentFactors p v) = exponentValue p v := by
  rw [factorValue_eq_prod]
  simp only [exponentFactors, List.map_ofFn, Fin.prod_ofFn, exponentValue, Function.comp_apply]

/-- Coordinatewise exponent increase implies divisibility, with no primality assumption. -/
private theorem exponentValue_dvd {k : ℕ} (p v w : Fin k → ℕ) (h : ∀ i, v i ≤ w i) :
    exponentValue p v ∣ exponentValue p w := by
  unfold exponentValue
  exact prod_dvd_prod_of_dvd _ _ fun i _ => pow_dvd_pow (p i) (h i)

private theorem good_of_strict_bound (hbase : BaseOK) {n : ℕ}
    (hn : hHat n < (n.divisors.card : ℚ)) : Good n := by
  unfold Good
  split_ifs with he
  · have hsubset : exceptions ⊆ Icc 1 5040 := by
      intro e he
      simp only [exceptions, mem_insert, mem_singleton] at he
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    have hb := hbase n (hsubset he)
    have hlo : (n.divisors.card : ℚ) < hHat n := by
      have hh : (n.divisors.card : ℚ) < hHat n ∧ 7 * hHat n < 8 * (n.divisors.card : ℚ) := by
        simpa only [Good, he, ↓reduceIte] using hb
      exact hh.1
    exact False.elim (not_lt_of_ge hn.le hlo)
  · exact hn

/-- A numerical leaf uses one of the three complete upper-bound methods. -/
inductive ExponentBoxLeaf where
  | gap (divisors prefixes weights : List ℕ)
  | rank (R : ℕ) (divisors : List ℕ)
  | rankIndexed (R count : ℕ) (readout : ℕ → ℕ)
  | full (divisors : List ℕ)

/-- Check one leaf against the exact lower and upper products of its exponent box. -/
def checkExponentBoxLeaf {k : ℕ} (Q : ℕ) (p lo hi : Fin k → ℕ) :
    ExponentBoxLeaf → Bool
  | .gap ds ps ws =>
    decide (0 < Q) && checkFactors (exponentFactors p lo) &&
      checkDivisors (exponentValue p hi) (exponentFactors p hi) ds &&
      checkGapWeights Q ds.length ps ws &&
      decide (gapUpper ws ds < Q * factorTau (exponentFactors p lo))
  | .rank R ds =>
    decide (0 < Q) && checkFactors (exponentFactors p lo) &&
      checkDivisors (exponentValue p hi) (exponentFactors p hi) ds &&
      decide (rankUpper Q R ds < Q * factorTau (exponentFactors p lo))
  | .rankIndexed R count d =>
    let ds := (List.range count).map d
    decide (0 < Q) && checkFactors (exponentFactors p lo) &&
      checkDivisors (exponentValue p hi) (exponentFactors p hi) ds &&
      decide (rankIndexUpper Q R count d < Q * factorTau (exponentFactors p lo))
  | .full ds =>
    decide (lo = hi) &&
      checkGood Q ⟨exponentValue p hi, exponentFactors p hi, ds⟩

private theorem corner_transfer {k Q : ℕ} (p lo hi v : Fin k → ℕ)
    (hv : InExponentBox lo hi v) (hQ : 0 < Q)
    (hf : checkFactors (exponentFactors p lo) = true)
    {ds : List ℕ}
    (hds : checkDivisors (exponentValue p hi) (exponentFactors p hi) ds = true)
    {U : ℕ} (hU : (Q : ℚ) * hHat (exponentValue p hi) ≤ U)
    (hstrict : U < Q * factorTau (exponentFactors p lo)) :
    hHat (exponentValue p v) < ((exponentValue p v).divisors.card : ℚ) := by
  have hh := hds
  simp only [checkDivisors, Bool.and_eq_true, decide_eq_true_eq] at hh
  have hhi := (checkFactors_sound hh.1.1.1.1).1
  rw [factorValue_exponentFactors] at hhi
  have hlow := (checkFactors_sound hf).2
  rw [factorValue_exponentFactors] at hlow
  have hdlo := exponentValue_dvd p lo v (fun i => (hv i).1)
  have hdhi := exponentValue_dvd p v hi (fun i => (hv i).2)
  have hpos := Nat.pos_of_dvd_of_pos hdhi hhi
  have hcard : (exponentValue p lo).divisors.card ≤ (exponentValue p v).divisors.card :=
    card_le_card (Nat.divisors_subset_of_dvd hpos.ne' hdlo)
  rw [hlow] at hcard
  exact hHat_lt_of_upper_corner hQ hhi hdhi hU hcard hstrict

/-- A certified leaf proves the strengthened target at every point of its whole box. -/
private theorem checkExponentBoxLeaf_sound {k Q : ℕ} (p lo hi : Fin k → ℕ)
    (leaf : ExponentBoxLeaf) (hbase : BaseOK)
    (h : checkExponentBoxLeaf Q p lo hi leaf = true)
    (v : Fin k → ℕ) (hv : InExponentBox lo hi v) : Good (exponentValue p v) := by
  cases leaf with
  | gap ds ps ws =>
    simp only [checkExponentBoxLeaf, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hQ, hf⟩, hds⟩, hw⟩, hu⟩ := h
    obtain ⟨hs, he, _⟩ := checkDivisors_sound hds
    exact good_of_strict_bound hbase
      (corner_transfer p lo hi v hv hQ hf hds (gapUpper_sound hw hs he) hu)
  | rank R ds =>
    simp only [checkExponentBoxLeaf, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hQ, hf⟩, hds⟩, hu⟩ := h
    obtain ⟨hs, he, _⟩ := checkDivisors_sound hds
    have hb := rankUpper_sound Q R ds hs
    rw [pairRat_eq_pairSum ds hs.nodup, he] at hb
    exact good_of_strict_bound hbase (corner_transfer p lo hi v hv hQ hf hds hb hu)
  | rankIndexed R count d =>
    simp only [checkExponentBoxLeaf, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hQ, hf⟩, hds⟩, hu⟩ := h
    let ds := (List.range count).map d
    obtain ⟨hs, he, _⟩ := checkDivisors_sound hds
    have hd : ∀ i j, i < j → j < count → d i < d j := by
      intro i j hij hj
      have hi : i < count := lt_trans hij hj
      have hh := hs.rel_getElem_of_lt (by simpa only [List.length_map,
        List.length_range] using hi) (by simpa only [List.length_map,
        List.length_range] using hj) hij
      simpa only [List.getElem_map, List.getElem_range] using hh
    have himage : (range count).image d = ds.toFinset := by
      ext x
      simp only [ds, mem_image, mem_range, List.mem_toFinset, List.mem_map, List.mem_range]
    have hb := rankIndexUpper_sound Q R count d hd
    rw [← pairSum_image_eq_indexPairSum count d hd, himage, he] at hb
    exact good_of_strict_bound hbase (corner_transfer p lo hi v hv hQ hf hds hb hu)
  | full ds =>
    simp only [checkExponentBoxLeaf, Bool.and_eq_true, decide_eq_true_eq] at h
    have heq : v = hi := by
      funext i
      have hh := hv i
      rw [h.1] at hh
      omega
    rw [heq]
    exact checkGood_sound h.2

/-- Binary exponent-box subdivision; each leaf carries its actual numerical certificate. -/
inductive ExponentBoxTree (k : ℕ) where
  | leaf (certificate : ExponentBoxLeaf)
  | split (axis : Fin k) (mid : ℕ) (left right : ExponentBoxTree k)

/-- Check all leaves and require each split to be strictly inside its closed interval. -/
def checkExponentBoxTree {k : ℕ} (Q : ℕ) (p lo hi : Fin k → ℕ) :
    ExponentBoxTree k → Bool
  | .leaf c => checkExponentBoxLeaf Q p lo hi c
  | .split axis mid left right =>
    decide (lo axis ≤ mid ∧ mid < hi axis) &&
      checkExponentBoxTree Q p lo (Function.update hi axis mid) left &&
      checkExponentBoxTree Q p (Function.update lo axis (mid + 1)) hi right

/-- Compose checked subtrees without recomputing their numerical leaves. -/
private theorem checkExponentBoxTree_split {k Q : ℕ} (p lo hi : Fin k → ℕ)
    (axis : Fin k) (mid : ℕ) (left right : ExponentBoxTree k)
    (hmid : lo axis ≤ mid ∧ mid < hi axis)
    (hl : checkExponentBoxTree Q p lo (Function.update hi axis mid) left = true)
    (hr : checkExponentBoxTree Q p (Function.update lo axis (mid + 1)) hi right = true) :
    checkExponentBoxTree Q p lo hi (.split axis mid left right) = true := by
  simp only [checkExponentBoxTree, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hmid, hl⟩, hr⟩

/-- Transport a checked subtree across endpoint equalities, without comparing its checks. -/
theorem checkExponentBoxTree_bounds_congr {k Q : ℕ} {p lo hi lo' hi' : Fin k → ℕ}
    {tree : ExponentBoxTree k} (h : checkExponentBoxTree Q p lo hi tree = true)
    (hlo : lo = lo') (hhi : hi = hi') :
    checkExponentBoxTree Q p lo' hi' tree = true := by
  rw [← hlo, ← hhi]
  exact h

/-- Join opaque subtree proofs; the remaining decision is only finite endpoint arithmetic. -/
theorem checkExponentBoxTree_join {k Q : ℕ}
    {p lo hi loL hiL loR hiR : Fin k → ℕ} {axis : Fin k} {mid : ℕ}
    {left right : ExponentBoxTree k}
    (hl : checkExponentBoxTree Q p loL hiL left = true)
    (hr : checkExponentBoxTree Q p loR hiR right = true)
    (hb : lo axis ≤ mid ∧ mid < hi axis ∧ loL = lo ∧
      hiL = Function.update hi axis mid ∧ loR = Function.update lo axis (mid + 1) ∧ hiR = hi) :
    checkExponentBoxTree Q p lo hi (.split axis mid left right) = true := by
  obtain ⟨hmlo, hmhi, hloL, hhiL, hloR, hhiR⟩ := hb
  exact checkExponentBoxTree_split p lo hi axis mid left right ⟨hmlo, hmhi⟩
    (checkExponentBoxTree_bounds_congr hl hloL hhiL)
    (checkExponentBoxTree_bounds_congr hr hloR hhiR)

/-- Every point is retained by one child of every checked split. -/
theorem checkExponentBoxTree_sound {k Q : ℕ} (p lo hi : Fin k → ℕ)
    (tree : ExponentBoxTree k) (hbase : BaseOK)
    (h : checkExponentBoxTree Q p lo hi tree = true) :
    ∀ v, InExponentBox lo hi v → Good (exponentValue p v) := by
  induction tree generalizing lo hi with
  | leaf c => exact checkExponentBoxLeaf_sound p lo hi c hbase h
  | split axis mid left right ihl ihr =>
    simp only [checkExponentBoxTree, Bool.and_eq_true, decide_eq_true_eq] at h
    intro v hv
    by_cases hm : v axis ≤ mid
    · apply ihl lo (Function.update hi axis mid) h.1.2 v
      intro i
      by_cases he : i = axis
      · subst i
        simpa only [Function.update_self] using And.intro (hv axis).1 hm
      · simpa only [Function.update_of_ne he] using hv i
    · apply ihr (Function.update lo axis (mid + 1)) hi h.2 v
      intro i
      by_cases he : i = axis
      · subst i
        have hl : mid + 1 ≤ v axis := by omega
        simpa only [Function.update_self] using And.intro hl (hv axis).2
      · simpa only [Function.update_of_ne he] using hv i

/-- Checking the main root box discharges exactly the finite domain of `MainBoxOK`. -/
theorem mainBoxOK_of_checked_tree {Q : ℕ} (tree : ExponentBoxTree 7)
    (hbase : BaseOK)
    (h : checkExponentBoxTree Q boxPrimes (fun _ => 0) mainCaps tree = true) : MainBoxOK := by
  intro v hv
  have hbox : InExponentBox (fun _ => 0) mainCaps v := by
    intro i
    have hi := Fintype.mem_piFinset.mp hv i
    have hvlt := mem_range.mp hi
    exact ⟨Nat.zero_le _, by omega⟩
  have hg := checkExponentBoxTree_sound boxPrimes (fun _ => 0) mainCaps tree hbase h v hbox
  exact hg

/-- Assemble a checked indexed leaf from opaque inputs and an already proved integer bound. -/
theorem check_rankIndexed_of_checks {k Q R count : ℕ} (p lo hi : Fin k → ℕ)
    (d : ℕ → ℕ) (hQ : 0 < Q)
    (hf : checkFactors (exponentFactors p lo) = true)
    (hds : checkDivisors (exponentValue p hi) (exponentFactors p hi)
      ((List.range count).map d) = true)
    (hU : rankIndexUpper Q R count d < Q * factorTau (exponentFactors p lo)) :
    checkExponentBoxTree Q p lo hi (.leaf (.rankIndexed R count d)) = true := by
  simp only [checkExponentBoxTree, checkExponentBoxLeaf, Bool.and_eq_true,
    decide_eq_true_eq]
  exact ⟨⟨⟨hQ, hf⟩, hds⟩, hU⟩

#print axioms checkExponentBoxLeaf_sound
#print axioms checkExponentBoxTree_sound

#print axioms check_rankIndexed_of_checks

end D5.S3.Arith.ErdosNicolas
