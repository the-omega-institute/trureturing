/- GID: D5/S1/Digit/Infinite/ClosedObservationGraphRealization
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/ClosedObservationGraphRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete closed endpoint graphs and actual legal common tails. -/

import D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
import D5.S1.Digit.Infinite.WindowCylinderPartition
import D5.S1.Scale.Embedding
import D5.S0.Carrier.Units
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.ClosedObservationGraphRealization

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.SignedSeriesRange (alpha signedValue signed_series_range)
open D5.S0.Carrier (GoldenInt conj conjEquiv phiUnit)
open D5.S1.Scale (embedding embedding_injective)
open private prependBlock from D5.S1.Digit.Infinite.SignedSeriesFibres
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open scoped Topology


theorem bitShift_bitShift (x : LegalDigits) (m n : ℕ) :
    bitShift (bitShift x m) n = bitShift x (m + n) := by
  apply Subtype.ext
  funext j
  simp [bitShift, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

set_option maxHeartbeats 1600000 in
/-- The complete finite endpoint graph jointly realizes every finite path from any
specified actual legal terminal address, retaining its guard and exact deletion clock. -/
theorem closed_observation_graph_realization :
    (∀ x : LegalDigits, kappa x = -signedValue x / t ^ 2) ∧
    (∀ s : Bool, kappa '' {x | stateAddress s x} = stateInterval s) ∧
    (∀ x : LegalDigits, kappa x = branch (window x 0) (kappa (originalT x)) ∧
      stateAddress (outgoing (window x 0)) (originalT x) ∧
      ∀ j, (originalT x).val j = x.val (j + 3)) ∧
    (∀ s l s' z, lawful s l s' → stateAddress s' z →
      ∃! x : LegalDigits, stateAddress s x ∧ window x 0 = l ∧ originalT x = z) ∧
    (∀ b0 : ℝ, inCoefficientField b0 → b0 ∈ Set.Icc 0 lambda →
      ∃ q : ℕ, ∃ R : ℝ, endpointParameters b0 q R) ∧
    (∀ b0 q R, endpointParameters b0 q R →
      (endpoints q R).Finite ∧
      (∀ l x, x ∈ endpoints q R → inverseBranch l x ∈ stateInterval false →
        inverseBranch l x ∈ endpoints q R) ∧
      (Set.univ : Set (Vertex q R)).Finite ∧
      (∀ s x, x ∈ stateInterval s → ∃ v : Vertex q R,
        v.val.1 = s ∧ x ∈ piece v ∧
        (x ∈ endpoints q R → v.val.2.1 = x ∧ v.val.2.2 = x) ∧
        ∀ a b, a ∈ endpoints q R → b ∈ endpoints q R →
          a ∈ stateInterval s → b ∈ stateInterval s → x ∈ Set.Icc a b →
          piece v ⊆ Set.Icc a b) ∧
      (∀ v : Vertex q R, ∃ l u, edge v l u) ∧
      (∀ (v : Vertex q R) l s', lawful v.val.1 l s' → piece v ⊆ branch l '' stateInterval s' →
        ∀ y, y ∈ inverseBranch l '' piece v ↔
          ∃ u : Vertex q R, u.val.1 = s' ∧ y ∈ piece u ∧
            piece u ⊆ inverseBranch l '' piece v)) ∧
    (∀ {q : ℕ} {R : ℝ} (b0 : ℝ) (r : List (Fin 6))
      (vs : List (Vertex q R)) (w : List Label), ClosedPath b0 r vs w →
      ∀ v : Vertex q R, vs.getLast? = some v → ∀ z : LegalDigits,
        stateAddress v.val.1 z → kappa z ∈ piece v →
        ∃ x : LegalDigits, addressChain x vs w ∧ bitShift x (3 * w.length) = z) ∧
    (∀ x : LegalDigits, finiteTail x → ∃ z : GoldenInt, kappa x = embedding z) ∧
    (∀ l : Label, branch l '' stateInterval (outgoing l) =
      Set.Icc (if l.val 1 then -1 else if l.val 0 then
        (if l.val 2 then 2 * t else t) else (if l.val 2 then g else t - 1))
        (if l.val 1 then t - 1 else if l.val 0 then
        (if l.val 2 then 1 + t else 2 * t) else (if l.val 2 then t else g))) := by
  classical
  have ht : 0 < t := inv_pos.mpr Real.goldenRatio_pos
  have ht1 : t < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have ht2 : t ^ 2 + t = 1 := by
    dsimp [t, alpha]
    rw [Real.inv_goldenRatio]
    nlinarith [Real.goldenConj_sq]
  have htphi : t = Real.goldenRatio - 1 := by
    dsimp [t, alpha]
    rw [Real.inv_goldenRatio, Real.goldenConj]
    dsimp [Real.goldenRatio]
    ring
  have hphi : Real.goldenRatio = 1 + t := by linarith [htphi]
  have ht3 : t ^ 3 + t ^ 2 = t := by
    nlinarith [congrArg (fun z : ℝ => t * z) ht2]
  have ht4 : t ^ 4 + t ^ 3 = t ^ 2 := by
    nlinarith [congrArg (fun z : ℝ => t ^ 2 * z) ht2]
  let digitTerm (x : LegalDigits) (j : ℕ) : ℝ :=
    (-1 : ℝ) ^ (j + 1) * t ^ (j + 2) * (if x.val j then 1 else 0)
  have hsummable (x : LegalDigits) : Summable (digitTerm x) := by
    apply ((summable_geometric_of_lt_one ht.le ht1).mul_right (t ^ 2)).of_norm_bounded
    intro j
    dsimp [digitTerm]
    rw [abs_mul, abs_mul, abs_pow, abs_pow]
    simp only [abs_neg, abs_one, one_pow, one_mul, abs_of_pos ht]
    cases x.val j <;> simp [pow_add, mul_nonneg (pow_nonneg ht.le j) (sq_nonneg t)]
  have hgroup (x : LegalDigits) : kappa x = -signedValue x / t ^ 2 := by
    let e := (Nat.divModEquiv 3).symm
    have hp : Summable (fun p : ℕ × Fin 3 => digitTerm x (p.1 * 3 + p.2)) := by
      change Summable (digitTerm x ∘ e)
      exact e.summable_iff.mpr (hsummable x)
    have he : signedValue x =
        ∑' n : ℕ, ∑ i : Fin 3, digitTerm x (n * 3 + i) := by
      change (∑' j, digitTerm x j) = _
      rw [← e.tsum_eq (digitTerm x)]
      change (∑' p : ℕ × Fin 3, digitTerm x (p.1 * 3 + p.2)) = _
      rw [hp.tsum_prod]
      simp only [tsum_fintype]
    have hblock (n : ℕ) : (∑ i : Fin 3, digitTerm x (n * 3 + i)) =
        -(t ^ 2) * ((-g) ^ n * offset (window x n)) := by
      rw [Fin.sum_univ_three]
      simp only [digitTerm, window, D5.S1.Digit.Infinite.WindowSuccessorGraph.P,
        bitShift, offset, Fin.val_zero, Fin.val_one, Fin.reduceFinMk]
      have hpow : (-g) ^ n = (-1 : ℝ) ^ n * t ^ (3 * n) := by
        rw [neg_pow, g, ← pow_mul]
      have hsign : (-1 : ℝ) ^ (n * 3) = (-1 : ℝ) ^ n := by
        rw [Nat.mul_comm n 3, pow_mul]
        norm_num
      have hsign' : (-1 : ℝ) ^ (3 * n) = (-1 : ℝ) ^ n := by
        simpa only [Nat.mul_comm] using hsign
      simp [pow_add, hpow, hsign, hsign', Nat.add_comm, Nat.mul_comm]
      split_ifs <;> ring
    rw [he]
    simp_rw [hblock]
    rw [tsum_mul_left]
    dsimp [kappa]
    field_simp [ht.ne']
  have htail (x : LegalDigits) (n : ℕ) : signedValue x =
      (∑ j ∈ Finset.range n, digitTerm x j) + (-t) ^ n * signedValue (bitShift x n) := by
    have hterm (j : ℕ) : digitTerm x (j + n) =
        (-t) ^ n * digitTerm (bitShift x n) j := by
      simp [digitTerm, bitShift, pow_add]
      ring
    change (∑' j, digitTerm x j) = _
    rw [← (hsummable x).sum_add_tsum_nat_add n]
    simp_rw [hterm]
    rw [tsum_mul_left]
    rfl
  have hrec (x : LegalDigits) : kappa x = branch (window x 0) (kappa (originalT x)) := by
    rw [hgroup, htail x 3]
    rw [branch, hgroup]
    simp [Finset.sum_range_succ, digitTerm, window,
      D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift, originalT, offset, g]
    field_simp [ht.ne']
    split_ifs <;> ring
  have hrange0 : kappa '' {x | stateAddress false x} = stateInterval false := by
    ext y
    constructor
    · rintro ⟨x, _, rfl⟩
      have hx : signedValue x ∈ Set.Icc (-t) (t ^ 2) := by
        have hx : signedValue x ∈ Set.range signedValue := ⟨x, rfl⟩
        rw [signed_series_range.1] at hx
        exact hx
      rw [hgroup]
      simp only [stateInterval, Bool.false_eq_true, ↓reduceIte, Set.mem_Icc]
      constructor
      · apply (le_div_iff₀ (sq_pos_of_pos ht)).2
        nlinarith [hx.2, sq_pos_of_pos ht]
      · apply (div_le_iff₀ (sq_pos_of_pos ht)).2
        nlinarith [hx.1, sq_pos_of_pos ht]
    · intro hy
      have hsy : -(t ^ 2) * y ∈ Set.Icc (-t) (t ^ 2) := by
        simp only [stateInterval, Bool.false_eq_true, ↓reduceIte, Set.mem_Icc] at hy
        constructor <;> nlinarith [sq_pos_of_pos ht]
      obtain ⟨x, hx⟩ := signed_series_range.1.symm ▸
        (show -(t ^ 2) * y ∈ Set.Icc
          D5.S1.Digit.Infinite.SignedSeriesRange.a
          D5.S1.Digit.Infinite.SignedSeriesRange.b from hsy)
      refine ⟨x, by simp [stateAddress], ?_⟩
      rw [hgroup, hx]
      field_simp [ht.ne']
  have hrange1 : kappa '' {x | stateAddress true x} = stateInterval true := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx0 : x.val 0 = false := hx rfl
      have hb : signedValue (bitShift x 1) ∈ Set.Icc (-t) (t ^ 2) := by
        have hh : signedValue (bitShift x 1) ∈ Set.range signedValue := ⟨_, rfl⟩
        rwa [signed_series_range.1] at hh
      have hv : kappa x = signedValue (bitShift x 1) / t := by
        rw [hgroup, htail x 1]
        simp [digitTerm, hx0, pow_two]
        field_simp [ht.ne']
      rw [hv]
      simp only [stateInterval, ↓reduceIte, Set.mem_Icc]
      constructor
      · exact (le_div_iff₀ ht).2 (by nlinarith [hb.1])
      · exact (div_le_iff₀ ht).2 (by nlinarith [hb.2])
    · intro hy
      have hyb : t * y ∈ Set.Icc (-t) (t ^ 2) := by
        simp only [stateInterval, ↓reduceIte, Set.mem_Icc] at hy
        constructor <;> nlinarith [hy.1, hy.2]
      obtain ⟨z, hz⟩ := signed_series_range.1.symm ▸
        (show t * y ∈ Set.Icc D5.S1.Digit.Infinite.SignedSeriesRange.a
          D5.S1.Digit.Infinite.SignedSeriesRange.b from hyb)
      refine ⟨prependBlock .zero z, by simp [stateAddress, prependBlock], ?_⟩
      rw [hgroup, htail _ 1]
      change -((∑ j ∈ Finset.range 1, digitTerm (prependBlock .zero z) j) +
        (-t) ^ 1 * signedValue z) / t ^ 2 = y
      simp [digitTerm, prependBlock, hz]
      field_simp [ht.ne']
  have hrange (s : Bool) : kappa '' {x | stateAddress s x} = stateInterval s := by
    cases s
    · exact hrange0
    · exact hrange1
  have hprepend (s : Bool) (l : Label) (s' : Bool) (z : LegalDigits)
      (hl : lawful s l s') (hz : stateAddress s' z) :
      ∃! x : LegalDigits, stateAddress s x ∧ window x 0 = l ∧ originalT x = z := by
    let raw (j : ℕ) : Bool := if h : j < 3 then l.val ⟨j, h⟩ else z.val (j - 3)
    have hraw (j : ℕ) : ¬ (raw j = true ∧ raw (j + 1) = true) := by
      intro hj
      by_cases hj3 : j < 3
      · by_cases hj13 : j + 1 < 3
        · apply l.property j hj13
          simpa [raw, hj3, hj13] using hj
        · have hj2 : j = 2 := by omega
          have hl2 : l.val 2 = true := by simpa [raw, hj2] using hj.1
          have hz0 : z.val 0 = false := hz (by simpa [lawful, outgoing, hl2] using hl.2)
          simpa [raw, hj2, hz0] using hj.2
      · have hj13 : ¬ j + 1 < 3 := by omega
        apply z.property (j - 3)
        simpa [raw, hj3, hj13, show j + 1 - 3 = (j - 3) + 1 by omega] using hj
    let x : LegalDigits := ⟨raw, hraw⟩
    have hxw : window x 0 = l := by
      apply Subtype.ext
      funext i
      simp [window, D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift, x, raw, i.isLt]
    have hxt : originalT x = z := by
      apply Subtype.ext
      funext j
      simp [originalT, bitShift, x, raw, show ¬j + 3 < 3 by omega]
    refine ⟨x, ⟨?_, hxw, hxt⟩, ?_⟩
    · intro hs
      simpa [x, raw] using hl.1 hs
    · rintro y ⟨_, hyw, hyt⟩
      apply Subtype.ext
      funext j
      by_cases hj : j < 3
      · have hh := congrArg (fun p : Label => p.val ⟨j, hj⟩) hyw
        simpa [window, D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift, x, raw, hj] using hh
      · have hh := congrArg (fun p : LegalDigits => p.val (j - 3)) hyt
        simpa [originalT, bitShift, x, raw, hj, Nat.sub_add_cancel (by omega : 3 ≤ j)] using hh
  have hchainHead {q : ℕ} {R : ℝ} (x : LegalDigits) (v : Vertex q R)
      (vs : List (Vertex q R)) (w : List Label) (h : addressChain x (v :: vs) w) :
      stateAddress v.val.1 x ∧ kappa x ∈ piece v := by
    cases vs with
    | nil =>
      cases w with
      | nil => exact h
      | cons l w => exact False.elim h
    | cons u vs =>
      cases w with
      | nil => exact False.elim h
      | cons l w => exact ⟨h.1, h.2.1⟩
  have hlift {q : ℕ} {R : ℝ} (b0 : ℝ) (r : List (Fin 6))
      (vs : List (Vertex q R)) (w : List Label) (hp : ClosedPath b0 r vs w)
      (v : Vertex q R) (hvs : vs.getLast? = some v) (z : LegalDigits)
      (hz : stateAddress v.val.1 z) (hzp : kappa z ∈ piece v) :
      ∃ x : LegalDigits, addressChain x vs w ∧ bitShift x (3 * w.length) = z := by
    induction hp generalizing v z with
    | point i u hu =>
      have hv : u = v := by simpa using hvs
      subst v
      exact ⟨z, ⟨hz, hzp⟩, by apply Subtype.ext; funext j; simp [bitShift]⟩
    | step i r u u' vs l w hu he hp ih =>
      have hlast : (u' :: vs).getLast? = some v := by simpa using hvs
      obtain ⟨y, hy, hyt⟩ := ih v hlast z hz hzp
      have hyhead := hchainHead y u' vs w hy
      obtain ⟨x, hx, _⟩ := hprepend u.val.1 l u'.val.1 y he.1 hyhead.1
      obtain ⟨a, ha, hay⟩ := he.2.2 hyhead.2
      have hba : branch l (kappa y) = a := by
        have hg : g ≠ 0 := (pow_pos ht 3).ne'
        have hh := (div_eq_iff hg).mp hay
        dsimp [branch]
        linarith
      have hxp : kappa x ∈ piece u := by
        rw [hrec x, hx.2.1, hx.2.2, hba]
        exact ha
      refine ⟨x, ⟨hx.1, hxp, hx.2.1, ?_⟩, ?_⟩
      · simpa [hx.2.2] using hy
      · rw [List.length_cons, show 3 * (w.length + 1) = 3 + 3 * w.length by omega,
          ← bitShift_bitShift, ← originalT, hx.2.2, hyt]
  have hactual (x : LegalDigits) :
      stateAddress (outgoing (window x 0)) (originalT x) := by
    intro h
    have hx2 : x.val 2 = true := by
      simpa [outgoing, window, D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift] using h
    have hx3 : x.val 3 = false := by
      cases hh : x.val 3
      · rfl
      · exact False.elim (x.property 2 ⟨hx2, hh⟩)
    exact hx3
  have hdelta (l : Label) : embedding (offsetInteger l) = offset l := by
    cases h0 : l.val 0 <;> cases h1 : l.val 1 <;> cases h2 : l.val 2 <;>
      simp [offsetInteger, embedding, offset, h0, h1, h2] <;> nlinarith
  let zGamma : GoldenInt := ⟨3, -2⟩
  have hgamma : embedding zGamma = -g := by
    simp [zGamma, embedding, g]
    nlinarith
  have hfiniteIntegral (x : LegalDigits) (hx : finiteTail x) :
      ∃ z : GoldenInt, kappa x = embedding z := by
    obtain ⟨N, hN⟩ := hx
    have hw (j : ℕ) (hj : N ≤ j) : window x j = nullLabel := by
      apply Subtype.ext
      funext i
      change x.val (i.val + 3 * j) = false
      exact hN _ (by omega)
    have hv : kappa x = ∑ j ∈ Finset.range N, (-g) ^ j * offset (window x j) := by
      apply tsum_eq_sum
      intro j hj
      rw [hw j (by simpa using hj)]
      simp [offset, nullLabel]
    refine ⟨∑ j ∈ Finset.range N, zGamma ^ j * offsetInteger (window x j), ?_⟩
    rw [hv, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, map_pow, hgamma, hdelta]
  have hgpos : 0 < g := pow_pos ht 3
  have hglt : g < 1 := pow_lt_one₀ ht.le ht1 (by decide)
  let zInverse : GoldenInt := ⟨1, 2⟩
  have hinverseUnit : embedding zInverse * g = 1 := by
    norm_num [zInverse, D5.S1.Scale.embedding_apply]
    rw [hphi]
    dsimp [g]
    nlinarith [ht2, ht3, ht4]
  have hconjugateUnit : embedding (conj zInverse) = -g := by
    change embedding zGamma = -g
    exact hgamma
  have hinverseClosed (b0 : ℝ) (q : ℕ) (R : ℝ)
      (hp : endpointParameters b0 q R) (l : Label) (x : ℝ)
      (hx : x ∈ endpoints q R) (hy : inverseBranch l x ∈ stateInterval false) :
      inverseBranch l x ∈ endpoints q R := by
    have hq : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hp.1; omega)
    obtain ⟨_, z, rfl, hz⟩ := hx
    let u := ((q : GoldenInt) * offsetInteger l - z) * zInverse
    have hu : embedding u / q = inverseBranch l (embedding z / q) := by
      simp only [u, map_mul, map_sub, map_natCast, hdelta, inverseBranch]
      apply (eq_div_iff hgpos.ne').2
      calc
        (↑q * offset l - embedding z) * embedding zInverse / ↑q * g =
            (↑q * offset l - embedding z) / ↑q * (embedding zInverse * g) := by ring
        _ = offset l - embedding z / ↑q := by rw [hinverseUnit]; field_simp [hq]
    have huc : embedding (conj u) / q =
        g * (embedding (conj z) / q - embedding (conj (offsetInteger l))) := by
      change embedding (conjEquiv
        (((q : GoldenInt) * offsetInteger l - z) * zInverse)) / q = _
      simp only [map_mul, map_sub, map_natCast]
      change ((q : ℝ) * embedding (conj (offsetInteger l)) - embedding (conj z)) *
        embedding (conj zInverse) / q = _
      rw [hconjugateUnit]
      field_simp [hq]
      ring
    refine ⟨hy, u, hu.symm, ?_⟩
    rw [huc, abs_mul, abs_of_pos hgpos]
    calc
      g * |embedding (conj z) / q - embedding (conj (offsetInteger l))| ≤
          g * (|embedding (conj z) / q| + |embedding (conj (offsetInteger l))|) :=
        mul_le_mul_of_nonneg_left (by
          simpa only [sub_zero, zero_sub, abs_neg] using
            abs_sub_le (embedding (conj z) / q) 0 (embedding (conj (offsetInteger l))))
          (show 0 ≤ g from hgpos.le)
      _ ≤ g * (R + |embedding (conj (offsetInteger l))|) :=
        mul_le_mul_of_nonneg_left (add_le_add hz le_rfl) (show 0 ≤ g from hgpos.le)
      _ ≤ R := by have h := hp.2.2.2 l; nlinarith
  have hfiniteEndpoints (q : ℕ) (R : ℝ) (hq : 1 ≤ q) (hR : 0 ≤ R) :
      (endpoints q R).Finite := by
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    let K : ℝ := (q : ℝ) * (2 + t + R)
    have hK : 0 ≤ K := mul_nonneg hqpos.le (by linarith)
    obtain ⟨N : ℤ, hN⟩ := exists_int_gt (K * (2 + t))
    let Z : Set GoldenInt := {z | embedding z / q ∈ stateInterval false ∧
      |embedding (conj z) / q| ≤ R}
    have hbound (z : GoldenInt) (hz : z ∈ Z) :
        z.a ∈ Set.Icc (-N) N ∧ z.b ∈ Set.Icc (-N) N := by
      obtain ⟨hzr, hzc⟩ := hz
      have hr := hzr
      have hc := abs_le.mp hzc
      simp only [stateInterval, Bool.false_eq_true, ↓reduceIte, Set.mem_Icc] at hr
      have hrl := (le_div_iff₀ hqpos).mp hr.1
      have hru := (div_le_iff₀ hqpos).mp hr.2
      have hcl := (le_div_iff₀ hqpos).mp hc.1
      have hcu := (div_le_iff₀ hqpos).mp hc.2
      simp only [D5.S1.Scale.embedding_apply, conj, Int.cast_add, Int.cast_neg] at hrl hru hcl hcu
      rw [hphi] at hrl hru hcl hcu
      have hb : -(K : ℝ) ≤ z.b ∧ (z.b : ℝ) ≤ K := by
        dsimp [K]
        constructor <;> nlinarith [ht, hqpos]
      have ha : -(K * (2 + t)) ≤ z.a ∧ (z.a : ℝ) ≤ K * (2 + t) := by
        constructor <;> nlinarith [hb.1, hb.2, hK, ht]
      have hbN : -(N : ℝ) ≤ z.b ∧ (z.b : ℝ) ≤ N := by
        constructor <;> nlinarith [hb.1, hb.2, hK, ht]
      have haN : -(N : ℝ) ≤ z.a ∧ (z.a : ℝ) ≤ N := by
        constructor <;> linarith [ha.1, ha.2]
      exact ⟨by exact_mod_cast haN, by exact_mod_cast hbN⟩
    have hfZ : Z.Finite := Set.Finite.of_injOn
      (f := fun z : GoldenInt => (z.a, z.b))
      (fun z hz => hbound z hz)
      (fun x _ y _ h => GoldenInt.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
      ((Set.finite_Icc (-N) N).prod (Set.finite_Icc (-N) N))
    apply (hfZ.image (fun z => embedding z / q)).subset
    rintro x ⟨hx, z, rfl, hz⟩
    exact ⟨z, ⟨hx, hz⟩, rfl⟩
  have hcommonDenominator (C : Set ℝ) (hC : C.Finite)
      (hF : ∀ x ∈ C, inCoefficientField x) :
      ∃ q : ℕ, 1 ≤ q ∧ ∀ x ∈ C, ∃ z : GoldenInt, x = embedding z / q := by
    letI : Finite C := hC.to_subtype
    let a (x : C) : ℚ := Classical.choose (hF x x.property)
    let b (x : C) : ℚ := Classical.choose (Classical.choose_spec (hF x x.property))
    have hx (x : C) : (x : ℝ) = (a x : ℝ) + (b x : ℝ) * t :=
      Classical.choose_spec (Classical.choose_spec (hF x x.property))
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
      (Submonoid.pos ℤ) (fun p : C × Bool => if p.2 then b p.1 else a p.1)
    have hdpos : 0 < (d : ℤ) := d.property
    let q : ℕ := (d : ℤ).toNat
    have hqd : (q : ℤ) = d := Int.toNat_of_nonneg hdpos.le
    have hq : 1 ≤ q := by omega
    have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hdQ : ((d : ℤ) : ℚ) = (q : ℚ) := by exact_mod_cast hqd.symm
    refine ⟨q, hq, ?_⟩
    intro x hxc
    let c : C := ⟨x, hxc⟩
    obtain ⟨m, hm⟩ := hd (c, false)
    obtain ⟨n, hn⟩ := hd (c, true)
    have hmQ : (m : ℚ) = (q : ℚ) * a c := by
      simpa [Algebra.smul_def, hdQ] using hm
    have hnQ : (n : ℚ) = (q : ℚ) * b c := by
      simpa [Algebra.smul_def, hdQ] using hn
    have hmR : (m : ℝ) = (q : ℝ) * (a c : ℝ) := by exact_mod_cast hmQ
    have hnR : (n : ℝ) = (q : ℝ) * (b c : ℝ) := by exact_mod_cast hnQ
    refine ⟨⟨m - n, n⟩, ?_⟩
    change (c : ℝ) = _
    rw [hx c]
    simp only [D5.S1.Scale.embedding_apply, Int.cast_sub, hphi]
    apply (eq_div_iff hqR.ne').2
    rw [hmR, hnR]
    ring
  have hfieldLinear (a b : ℚ) : inCoefficientField ((a : ℝ) + b * t) := ⟨a, b, rfl⟩
  have hfieldAdd (x y : ℝ) (hx : inCoefficientField x) (hy : inCoefficientField y) :
      inCoefficientField (x + y) ∧ inCoefficientField (x - y) := by
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    constructor
    · refine ⟨a + c, b + d, ?_⟩; push_cast; ring
    · refine ⟨a - c, b - d, ?_⟩; push_cast; ring
  have hcellField (i : Fin 6) :
      inCoefficientField (cellLower i) ∧ inCoefficientField (cellUpper i) := by
    have h1 : inCoefficientField (-1 : ℝ) := by simpa using hfieldLinear (-1) 0
    have h2 : inCoefficientField (1 + t) := by simpa using hfieldLinear 1 1
    have ha : inCoefficientField (cuts 0) := by
      convert hfieldLinear (-11 / 10) (11 / 10) using 1
      norm_num [cuts, lambda]; nlinarith only [ht2]
    have hb : inCoefficientField (cuts 1) := by
      convert hfieldLinear (-13 / 10) (23 / 10) using 1
      norm_num [cuts, lambda, g]; nlinarith only [ht2, ht3]
    have hc : inCoefficientField (cuts 2) := by
      convert hfieldLinear (-1 / 2) (3 / 2) using 1
      norm_num [cuts, lambda]; nlinarith only [ht2]
    have hd : inCoefficientField (cuts 3) := by
      convert hfieldLinear (-7 / 10) (27 / 10) using 1
      norm_num [cuts, lambda]; nlinarith only [ht2]
    have he : inCoefficientField (cuts 4) := by
      convert hfieldLinear (1 / 10) (19 / 10) using 1
      norm_num [cuts, lambda]; nlinarith only [ht2]
    fin_cases i <;> norm_num [cellLower, cellUpper] <;> constructor <;> assumption
  have hparameters (b0 : ℝ) (hbF : inCoefficientField b0)
      (hb : b0 ∈ Set.Icc 0 lambda) : ∃ q : ℕ, ∃ R : ℝ, endpointParameters b0 q R := by
    have hseedFinite : (seeds b0).Finite := by
      apply Set.Finite.union
      · apply Set.Finite.union
        · simp only [Set.finite_insert, Set.finite_singleton]
        · exact Set.finite_range _
      · exact Set.finite_range _
    have hrootField : ∀ x ∈ ({-1, 1 + t, t, -t ^ 2, g, 2 * t} : Set ℝ),
        inCoefficientField x := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · simpa using hfieldLinear (-1) 0
      · simpa using hfieldLinear 1 1
      · simpa using hfieldLinear 0 1
      · convert hfieldLinear (-1) 1 using 1; norm_num; nlinarith only [ht2]
      · convert hfieldLinear (-1) 2 using 1; norm_num [g]; nlinarith only [ht2, ht3]
      · simpa using hfieldLinear 0 2
    have hseedField : ∀ x ∈ seeds b0, inCoefficientField x := by
      intro x hx
      rcases hx with (hx | ⟨i, rfl⟩) | ⟨i, rfl⟩
      · exact hrootField x hx
      · dsimp only
        rcases le_total (-1 : ℝ) (cellLower i - b0) with h | h
        · rw [max_eq_right h]; exact (hfieldAdd _ _ (hcellField i).1 hbF).2
        · rw [max_eq_left h]; simpa using hfieldLinear (-1) 0
      · dsimp only
        rcases le_total (1 + t) (cellUpper i + b0) with h | h
        · rw [min_eq_left h]; simpa using hfieldLinear 1 1
        · rw [min_eq_right h]; exact (hfieldAdd _ _ (hcellField i).2 hbF).1
    obtain ⟨q, hq, hqC⟩ := hcommonDenominator _ hseedFinite hseedField
    let z (x : ℝ) : GoldenInt := if hx : x ∈ seeds b0 then Classical.choose (hqC x hx) else 0
    obtain ⟨r0, hR0⟩ := Set.exists_upper_bound_image (seeds b0)
      (fun x => |embedding (conj (z x)) / q|) hseedFinite
    let R0 : ℝ := |embedding (conj (z r0)) / q|
    letI : Fintype Label := by
      unfold Label D5.S1.Digit.Infinite.WindowSuccessorGraph.X
      infer_instance
    letI : Nonempty Label := ⟨nullLabel⟩
    obtain ⟨l0, hA⟩ := Set.exists_upper_bound_image (Set.univ : Set Label)
      (fun l => |embedding (conj (offsetInteger l))|) Set.finite_univ
    let A : ℝ := |embedding (conj (offsetInteger l0))|
    let R := max 0 (max R0 (g * A / (1 - g)))
    refine ⟨q, R, hq, le_max_left _ _, ?_, ?_⟩
    · intro x hx
      refine ⟨?_, z x, ?_, (hR0 x hx).trans ((le_max_left _ _).trans (le_max_right _ _))⟩
      · change -1 ≤ x ∧ x ≤ 1 + t
        rcases hx with (hx | ⟨i, rfl⟩) | ⟨i, rfl⟩
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
            norm_num [stateInterval, g, lambda] <;> (try rw [abs_of_pos ht]) <;>
              (try constructor) <;> nlinarith only [ht, ht1, ht2, ht3]
        · constructor
          · exact le_max_left _ _
          · apply max_le (by linarith) ?_
            have hc := (hcellField i).1
            fin_cases i <;> norm_num [cellLower, cuts, g, lambda] <;>
              nlinarith only [hb.1, hb.2, ht, ht1, ht2, ht3]
        · constructor
          · apply le_min (by linarith) ?_
            fin_cases i <;> norm_num [cellUpper, cuts, g, lambda] <;>
              nlinarith only [hb.1, hb.2, ht, ht1, ht2, ht3]
          · exact min_le_left _ _
      · simpa only [z, dif_pos hx] using Classical.choose_spec (hqC x hx)
    · intro l
      have hR : g * A / (1 - g) ≤ R :=
        (le_max_right _ _).trans (le_max_right _ _)
      have hRg := (div_le_iff₀ (sub_pos.mpr hglt)).mp hR
      have hAl := mul_le_mul_of_nonneg_right (hA l (Set.mem_univ l)) hgpos.le
      linarith
  have hcanonical (b0 : ℝ) (q : ℕ) (R : ℝ) (hp : endpointParameters b0 q R)
      (s : Bool) (x : ℝ) (hx : x ∈ stateInterval s) : ∃ v : Vertex q R,
      v.val.1 = s ∧ x ∈ piece v ∧
      (x ∈ endpoints q R → v.val.2.1 = x ∧ v.val.2.2 = x) ∧
      ∀ a b, a ∈ endpoints q R → b ∈ endpoints q R →
        a ∈ stateInterval s → b ∈ stateInterval s → x ∈ Set.Icc a b →
        piece v ⊆ Set.Icc a b := by
    by_cases hxB : x ∈ endpoints q R
    · let v : Vertex q R := ⟨(s, x, x), hxB, hxB, hx, hx, le_rfl, Or.inl rfl⟩
      refine ⟨v, rfl, ⟨le_rfl, le_rfl⟩, fun _ => ⟨rfl, rfl⟩, ?_⟩
      intro a b _ _ _ _ hab y hy
      have hyx : y = x := le_antisymm hy.2 hy.1
      simpa [hyx] using hab
    · let L : Set ℝ := {z | z ∈ endpoints q R ∧ z ∈ stateInterval s ∧ z ≤ x}
      let U : Set ℝ := {z | z ∈ endpoints q R ∧ z ∈ stateInterval s ∧ x ≤ z}
      have hB := hfiniteEndpoints q R hp.1 hp.2.1
      have hlo : (-1 : ℝ) ∈ endpoints q R := hp.2.2.1 (by simp [seeds])
      have hhi : (if s then t else 1 + t) ∈ endpoints q R := by
        cases s <;> apply hp.2.2.1 <;> simp [seeds]
      have hLs : L.Nonempty := ⟨-1, hlo, ⟨le_rfl, hx.1.trans hx.2⟩, hx.1⟩
      have hUs : U.Nonempty :=
        ⟨_, hhi, ⟨hx.1.trans hx.2, le_rfl⟩, hx.2⟩
      obtain ⟨a, ha, hmax⟩ := Set.exists_max_image L id
        (hB.subset (fun _ hz => hz.1)) hLs
      obtain ⟨b, hb, hmin⟩ := Set.exists_min_image U id
        (hB.subset (fun _ hz => hz.1)) hUs
      have hab : a ≤ b := ha.2.2.trans hb.2.2
      have hadj : ∀ c ∈ endpoints q R, a < c → c < b → False := by
        intro c hc hac hcb
        have hcs : c ∈ stateInterval s :=
          ⟨ha.2.1.1.trans hac.le, hcb.le.trans hb.2.1.2⟩
        by_cases hcx : c ≤ x
        · exact (not_lt_of_ge (hmax c ⟨hc, hcs, hcx⟩)) hac
        · exact (not_lt_of_ge (hmin c ⟨hc, hcs, le_of_not_ge hcx⟩)) hcb
      let v : Vertex q R :=
        ⟨(s, a, b), ha.1, hb.1, ha.2.1, hb.2.1, hab, Or.inr hadj⟩
      refine ⟨v, rfl, ⟨ha.2.2, hb.2.2⟩, fun h => False.elim (hxB h), ?_⟩
      intro c d hc hd hcs hds hxcd y hy
      exact ⟨(hmax c ⟨hc, hcs, hxcd.1⟩).trans hy.1,
        hy.2.trans (hmin d ⟨hd, hds, hxcd.2⟩)⟩
  have hinverseInterval (l : Label) (a b : ℝ) :
      inverseBranch l '' Set.Icc a b = Set.Icc (inverseBranch l b) (inverseBranch l a) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      constructor <;> apply (div_le_div_iff_of_pos_right hgpos).mpr <;>
        linarith [hx.1, hx.2]
    · intro hy
      dsimp only [inverseBranch] at hy
      have hlo := (div_le_iff₀ hgpos).mp hy.1
      have hhi := (le_div_iff₀ hgpos).mp hy.2
      refine ⟨branch l y, ⟨?_, ?_⟩, ?_⟩
      · dsimp [branch]; linarith
      · dsimp [branch]; linarith
      · dsimp [inverseBranch, branch]; field_simp [hgpos.ne']; ring
  have hfullImage (b0 : ℝ) (q : ℕ) (R : ℝ) (hp : endpointParameters b0 q R)
      (v : Vertex q R) (l : Label) (s' : Bool) (_hl : lawful v.val.1 l s')
      (hd : piece v ⊆ branch l '' stateInterval s') (y : ℝ) :
      y ∈ inverseBranch l '' piece v ↔ ∃ u : Vertex q R,
        u.val.1 = s' ∧ y ∈ piece u ∧ piece u ⊆ inverseBranch l '' piece v := by
    have htailValue (x : ℝ) (hx : x ∈ piece v) :
        inverseBranch l x ∈ stateInterval s' := by
      obtain ⟨z, hz, hzx⟩ := hd hx
      have he : inverseBranch l x = z := by
        rw [← hzx]; dsimp [inverseBranch, branch]; field_simp [hgpos.ne']; ring
      rwa [he]
    have ha : inverseBranch l v.val.2.1 ∈ stateInterval s' :=
      htailValue _ ⟨le_rfl, v.property.2.2.2.2.1⟩
    have hb : inverseBranch l v.val.2.2 ∈ stateInterval s' :=
      htailValue _ ⟨v.property.2.2.2.2.1, le_rfl⟩
    have hsX : stateInterval s' ⊆ stateInterval false := by
      intro z hz
      cases s' with
      | false => exact hz
      | true => exact ⟨hz.1, hz.2.trans (by change t ≤ 1 + t; linarith)⟩
    have haB := hinverseClosed b0 q R hp l _ v.property.1 (hsX ha)
    have hbB := hinverseClosed b0 q R hp l _ v.property.2.1 (hsX hb)
    have he : inverseBranch l '' piece v =
        Set.Icc (inverseBranch l v.val.2.2) (inverseBranch l v.val.2.1) :=
      hinverseInterval l _ _
    constructor
    · intro hy
      have hys : y ∈ stateInterval s' := by
        rw [he] at hy
        exact ⟨hb.1.trans hy.1, hy.2.trans ha.2⟩
      obtain ⟨u, hus, hyu, _, huc⟩ := hcanonical b0 q R hp s' y hys
      refine ⟨u, hus, hyu, ?_⟩
      rw [he] at hy ⊢
      exact huc _ _ hbB haB hb ha hy
    · rintro ⟨u, _, hy, hu⟩; exact hu hy
  have hlabels (l : Label) : l = nullLabel ∨ l = threeLabel ∨ l = twoLabel ∨
      l = fiveLabel ∨ l = twoFiveLabel := by
    have hn0 := l.property 0 (by decide)
    have hn1 := l.property 1 (by decide)
    cases h0 : l.val 0 <;> cases h1 : l.val 1 <;> cases h2 : l.val 2
    · left
      apply Subtype.ext; funext i; fin_cases i <;> simp [nullLabel, h0, h1, h2]
    · right; right; right; left
      apply Subtype.ext; funext i; fin_cases i <;> simp [fiveLabel, h0, h1, h2]
    · right; left
      apply Subtype.ext; funext i; fin_cases i <;> simp [threeLabel, h0, h1, h2]
    · exact False.elim (hn1 ⟨h1, h2⟩)
    · right; right; left
      apply Subtype.ext; funext i; fin_cases i <;> simp [twoLabel, h0, h1, h2]
    · right; right; right; right
      apply Subtype.ext; funext i; fin_cases i <;> simp [twoFiveLabel, h0, h1, h2]
    · exact False.elim (hn0 ⟨h0, h1⟩)
    · exact False.elim (hn0 ⟨h0, h1⟩)
  have hsq : t ^ 2 = 1 - t := by linarith [ht2]
  have hhalf : (1 : ℝ) / 2 < t := by nlinarith [ht2]
  have hcube : t ^ 3 = 2 * t - 1 := by linarith [ht2, ht3]
  have hgcube : g = 2 * t - 1 := hcube
  have hgp : g * (1 + t) = 1 - t := by
    dsimp [g]
    nlinarith [ht2, ht3, ht4]
  have hgt : g * t = 2 - 3 * t := by
    dsimp [g]
    nlinarith [ht2, ht3, ht4]
  let rootLower (l : Label) : ℝ :=
    if l.val 1 then -1 else if l.val 0 then
      (if l.val 2 then 2 * t else t) else (if l.val 2 then g else t - 1)
  let rootUpper (l : Label) : ℝ :=
    if l.val 1 then t - 1 else if l.val 0 then
      (if l.val 2 then 1 + t else 2 * t) else (if l.val 2 then t else g)
  have hroot (l : Label) (y : ℝ) (hy : y ∈ stateInterval (outgoing l)) :
      rootLower l ≤ branch l y ∧ branch l y ≤ rootUpper l := by
    have hg : 0 ≤ g := (pow_pos ht 3).le
    have hlo := mul_le_mul_of_nonneg_left hy.1 hg
    have hhi := mul_le_mul_of_nonneg_left hy.2 hg
    rcases hlabels l with rfl | rfl | rfl | rfl | rfl
    all_goals
      dsimp only [stateInterval, outgoing, nullLabel, threeLabel, twoLabel,
        fiveLabel, twoFiveLabel, branch, offset, rootLower, rootUpper] at hlo hhi ⊢
      norm_num [stateInterval, outgoing, nullLabel, threeLabel, twoLabel,
        fiveLabel, twoFiveLabel] at hlo hhi
      norm_num [rootLower, rootUpper, branch, offset, nullLabel, threeLabel,
        twoLabel, fiveLabel, twoFiveLabel]
      first | rw [hgp] at hhi | rw [hgt] at hhi
      constructor <;> linarith only [hlo, hhi, hsq, hgcube]
  have hbranchInterval (l : Label) (a b : ℝ) :
      branch l '' Set.Icc a b = Set.Icc (branch l b) (branch l a) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      dsimp [branch]; constructor <;> nlinarith [hx.1, hx.2]
    · intro hy
      refine ⟨inverseBranch l y, ⟨?_, ?_⟩, ?_⟩
      · apply (le_div_iff₀ hgpos).mpr; dsimp [branch] at hy; linarith [hy.2]
      · apply (div_le_iff₀ hgpos).mpr; dsimp [branch] at hy; linarith [hy.1]
      · dsimp [branch, inverseBranch]; field_simp [hgpos.ne']; ring
  have hrootImage (l : Label) : branch l '' stateInterval (outgoing l) =
      Set.Icc (rootLower l) (rootUpper l) := by
    rw [stateInterval, hbranchInterval]
    rcases hlabels l with rfl | rfl | rfl | rfl | rfl
    all_goals
      congr 1 <;> dsimp only [branch, offset, outgoing, rootLower, rootUpper,
        nullLabel, threeLabel, twoLabel, fiveLabel, twoFiveLabel] <;> norm_num <;>
        nlinarith only [hsq, hgcube, hgp, hgt]
  have hnoDead (b0 : ℝ) (q : ℕ) (R : ℝ) (hp : endpointParameters b0 q R)
      (v : Vertex q R) : ∃ l u, edge v l u := by
    let x := (v.val.2.1 + v.val.2.2) / 2
    have hxp : x ∈ piece v := by
      constructor <;> dsimp [x] <;> linarith [v.property.2.2.2.2.1]
    have hx : x ∈ stateInterval v.val.1 :=
      ⟨v.property.2.2.1.1.trans hxp.1, hxp.2.trans v.property.2.2.2.1.2⟩
    obtain ⟨omega, hs, ho⟩ := hrange v.val.1 ▸ hx
    let l := window omega 0
    have hl : lawful v.val.1 l (outgoing l) := by
      refine ⟨?_, rfl⟩
      intro h
      simpa [l, window, D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift] using hs h
    have htail : kappa (originalT omega) ∈ stateInterval (outgoing l) := by
      rw [← hrange]; exact ⟨_, hactual omega, rfl⟩
    have hxroot : x ∈ Set.Icc (rootLower l) (rootUpper l) := by
      have h := hroot l _ htail
      rwa [← hrec omega, ho] at h
    have hrootB (m : Label) :
        rootLower m ∈ endpoints q R ∧ rootUpper m ∈ endpoints q R := by
      have he : t - 1 = -t ^ 2 := by linarith [hsq]
      rcases hlabels m with rfl | rfl | rfl | rfl | rfl
      all_goals dsimp only [rootLower, rootUpper, nullLabel, threeLabel,
        twoLabel, fiveLabel, twoFiveLabel]
      all_goals norm_num [he]
      all_goals constructor <;> apply hp.2.2.1 <;> simp [seeds]
    have hd : piece v ⊆ branch l '' stateInterval (outgoing l) := by
      rw [hrootImage]
      intro y hy
      by_cases he : v.val.2.1 = v.val.2.2
      · have hxy : y = x := by dsimp [x]; linarith [hy.1, hy.2]
        simpa [hxy] using hxroot
      · have hab := lt_of_le_of_ne v.property.2.2.2.2.1 he
        have hn := v.property.2.2.2.2.2.resolve_left he
        constructor
        · by_contra h
          exact hn _ (hrootB l).1 (by linarith [hy.1])
            (by dsimp [x] at hxroot; linarith only [hxroot.1, hab])
        · by_contra h
          exact hn _ (hrootB l).2
            (by dsimp [x] at hxroot; linarith only [hxroot.2, hab]) (by linarith [hy.2])
    obtain ⟨u, hus, _, hu⟩ := (hfullImage b0 q R hp v l (outgoing l) hl hd
      (inverseBranch l x)).mp ⟨x, hxp, rfl⟩
    refine ⟨l, u, ?_, ?_, hu⟩
    · simpa [hus] using hl
    · simpa [hus] using hd
  refine ⟨hgroup, hrange, ?_, hprepend, hparameters, ?_, hlift, hfiniteIntegral, hrootImage⟩
  · intro x
    exact ⟨hrec x, hactual x, fun _ => rfl⟩
  · intro b0 q R hp
    refine ⟨hfiniteEndpoints q R hp.1 hp.2.1, hinverseClosed b0 q R hp,
      ?_, hcanonical b0 q R hp, hnoDead b0 q R hp, hfullImage b0 q R hp⟩
    · apply Set.Finite.of_injOn (f := fun v : Vertex q R => v.val)
        (t := Set.univ ×ˢ (endpoints q R ×ˢ endpoints q R))
      · intro v _; exact ⟨Set.mem_univ _, v.property.1, v.property.2.1⟩
      · exact fun _ _ _ _ h => Subtype.ext h
      · exact Set.finite_univ.prod
          ((hfiniteEndpoints q R hp.1 hp.2.1).prod (hfiniteEndpoints q R hp.1 hp.2.1))

end D5.S1.Digit.Infinite.ClosedObservationGraphRealization
