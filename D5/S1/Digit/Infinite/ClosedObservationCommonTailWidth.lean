/- GID: D5/S1/Digit/Infinite/ClosedObservationCommonTailWidth
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/ClosedObservationCommonTailWidth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete closed endpoint graphs and actual legal common tails. -/

import D5.S1.Digit.Infinite.ClosedObservationGraphRealization
import D5.S1.Digit.Infinite.WindowCylinderPartition
import D5.S1.Scale.Embedding
import D5.S0.Carrier.Units
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Int.Interval

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.ClosedObservationCommonTailWidth

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.SignedSeriesRange (alpha signedValue signed_series_range)
open D5.S0.Carrier (GoldenInt conj conjEquiv phiUnit)
open D5.S1.Scale (embedding embedding_injective)
open private prependBlock from D5.S1.Digit.Infinite.SignedSeriesFibres
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization (hshift)
open scoped Topology


theorem hpath_read {q : ℕ} {R : ℝ} (b0 : ℝ) (r : List (Fin 6))
    (vs : List (Vertex q R)) (w : List Label) (hp : ClosedPath b0 r vs w) :
    w.length + 1 = r.length ∧ ∀ x : LegalDigits, addressChain x vs w →
      w = (List.range w.length).map (window x) ∧
      ∀ j : Fin r.length, kappa (bitShift x (3 * j)) ∈ observation b0 (r.get j) := by
  induction hp with
  | point i v hi =>
    refine ⟨rfl, ?_⟩
    intro x hx
    refine ⟨rfl, ?_⟩
    intro j
    have hj : j.val = 0 := by have h := j.isLt; change j.val < 1 at h; omega
    simpa [hj, bitShift] using hi hx.2
  | step i r v u vs l w hi he hp ih =>
    refine ⟨by simp; omega, ?_⟩
    intro x hx
    change stateAddress v.val.1 x ∧ kappa x ∈ piece v ∧ window x 0 = l ∧
      addressChain (originalT x) (u :: vs) w at hx
    obtain ⟨hw, ho⟩ := ih.2 (originalT x) hx.2.2.2
    constructor
    · rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
        ← hx.2.2.1, hw, List.length_map, List.length_range]
      congr 1
    · intro j
      by_cases hj : j.val = 0
      · simpa [hj, bitShift] using hi hx.2.1
      · have hk : j.val - 1 < r.length := by have := j.isLt; simp at this; omega
        have hh := ho ⟨j.val - 1, hk⟩
        have heq : 3 + 3 * (j.val - 1) = 3 * j.val := by omega
        have hjp : j.val = (j.val - 1) + 1 := by omega
        change kappa (bitShift (originalT x) (3 * (j.val - 1))) ∈
          observation b0 r[j.val - 1] at hh
        have hecolor : (i :: r).get j = r[j.val - 1] := by
          rw [List.get_eq_getElem]
          simpa only [← hjp] using
            (show (i :: r)[(j.val - 1) + 1] = r[j.val - 1] from by simp)
        rw [hecolor]
        simpa only [originalT, hshift, heq] using hh

theorem window_shift (x : LegalDigits) (j : ℕ) : window (bitShift x (3 * j)) 0 = window x j := by
  apply Subtype.ext; funext i; simp [window, bitShift]

theorem original_t_shift (x : LegalDigits) (j : ℕ) : originalT (bitShift x (3 * j)) = bitShift x (3 * (j + 1)) := by
  rw [originalT, hshift]; congr 1 <;> omega

set_option maxHeartbeats 1600000 in
/-- The complete graph and actual common-tail relation have a strict width bound
and a critical singleton exception. -/
theorem complete_closed_graph_common_tail_width :
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
    (∀ b0 q R, endpointParameters b0 q R → ∀ s x, stateAddress s x →
      ∃ v : ℕ → Vertex q R,
        (∀ j, (v j).val.1 = actualGuard s x j ∧
          kappa (bitShift x (3 * j)) ∈ piece (v j) ∧
          ∀ i, kappa (bitShift x (3 * j)) ∈ observation b0 i → permits b0 (v j) i) ∧
        ∀ j, edge (v j) (window x j) (v (j + 1))) ∧
    (∀ {q : ℕ} {R : ℝ} (v : ℕ → Vertex q R) (l : ℕ → Label),
      (∀ j, edge (v j) (l j) (v (j + 1))) → ∃ x : LegalDigits,
        stateAddress (v 0).val.1 x ∧ ∀ j, window x j = l j ∧
          actualGuard (v 0).val.1 x j = (v j).val.1 ∧
          kappa (bitShift x (3 * j)) ∈ piece (v j)) ∧
    (∀ Q, instrument Q → ∀ b0, 0 ≤ b0 → ∀ i,
      exactObservation Q b0 i ⊆ observation b0 i) ∧
    (∀ b0 : ℝ, 0 ≤ b0 → b0 < lambda →
      ∀ M (x y : LegalDigits) (r : Fin (M + 1) → Fin 6),
        bitShift x (3 * M) = bitShift y (3 * M) →
        (∀ j : Fin (M + 1),
          kappa (bitShift x (3 * j)) ∈ observation b0 (r j) ∧
          kappa (bitShift y (3 * j)) ∈ observation b0 (r j)) → x = y) ∧
    (∀ b0 q R, 0 ≤ b0 → b0 < lambda → endpointParameters b0 q R →
      (∀ r (v : Vertex q R) u w,
        (v, u) ∈ histories b0 r → (v, w) ∈ histories b0 r → u = w) ∧
      ∀ r : List (Fin 6),
        (histories (q := q) (R := R) b0 r).Finite ∧
        (histories (q := q) (R := R) b0 r).ncard ≤
          (Set.univ : Set (Vertex q R)).ncard ∧
        (residuals (q := q) (R := R) b0 r).ncard ≤
          (Set.univ : Set (Vertex q R)).ncard ∧
        (∀ vw ∈ histories (q := q) (R := R) b0 r,
          (r = [] → vw.2 = []) ∧ (r ≠ [] → vw.2.length + 1 = r.length) ∧
          globalLCP (histories (q := q) (R := R) b0 r) <+: vw.2) ∧
        ((histories (q := q) (R := R) b0 r).Nonempty → ∀ p : List Label,
          (∀ vw ∈ histories (q := q) (R := R) b0 r, p <+: vw.2) →
          p.length ≤ (globalLCP (histories (q := q) (R := R) b0 r)).length) ∧
        (histories (q := q) (R := R) b0 r = ∅ →
          globalLCP (histories (q := q) (R := R) b0 r) = [])) ∧
    (∀ x : LegalDigits, finiteTail x → ∃ z : GoldenInt, kappa x = embedding z) ∧
    (∀ M (x y : LegalDigits) (r : Fin (M + 1) → Fin 6),
      bitShift x (3 * M) = bitShift y (3 * M) → finiteTail (bitShift x (3 * M)) →
      (∀ j : Fin (M + 1), kappa (bitShift x (3 * j)) ∈ observation lambda (r j) ∧
        kappa (bitShift y (3 * j)) ∈ observation lambda (r j)) → x = y) ∧
    (∀ q R, endpointParameters lambda q R →
      (∀ v : Vertex q R, (∃ z : LegalDigits, stateAddress v.val.1 z ∧
        finiteTail z ∧ kappa z ∈ piece v) → ∀ r u w,
        (v, u) ∈ histories lambda r → (v, w) ∈ histories lambda r → u = w) ∧
      (∀ v : Vertex q R, v.val.2.1 < v.val.2.2 →
        ∃ z : LegalDigits, stateAddress v.val.1 z ∧ finiteTail z ∧ kappa z ∈ piece v)) ∧
    (∃ tau u v : LegalDigits,
      stateAddress false tau ∧ kappa tau = (-4 + t) / 5 ∧
      (¬ ∃ z : GoldenInt, kappa tau = embedding z) ∧
      window u 0 = threeLabel ∧ window v 0 = nullLabel ∧
      originalT u = tau ∧ originalT v = tau ∧ ¬ finiteTail u ∧ ¬ finiteTail v ∧
      kappa u = cuts 0 - lambda ∧ kappa v = cuts 1 + lambda) ∧
    (∃ Q : ℝ → Fin 6, instrument Q ∧ Q (cuts 0) = 1 ∧ Q (cuts 1) = 1) ∧
    (∀ q R, endpointParameters lambda q R → ∀ Q : ℝ → Fin 6,
      instrument Q → Q (cuts 0) = 1 → Q (cuts 1) = 1 →
      ∃ tau u v : LegalDigits, ∃ z : Vertex q R,
        stateAddress false tau ∧ kappa tau = (-4 + t) / 5 ∧
        window u 0 = threeLabel ∧ window v 0 = nullLabel ∧ u ≠ v ∧
        originalT u = tau ∧ originalT v = tau ∧ ¬ finiteTail u ∧ ¬ finiteTail v ∧
        kappa u + lambda = cuts 0 ∧ kappa v - lambda = cuts 1 ∧
        Q (kappa u + lambda) = 1 ∧ Q (kappa v - lambda) = 1 ∧ Q (kappa tau) = 0 ∧
        z.val = (false, (-4 + t) / 5, (-4 + t) / 5) ∧
        (z, [threeLabel]) ∈ histories lambda [1, 0] ∧
        (z, [nullLabel]) ∈ histories lambda [1, 0] ∧
        originalT (originalT u) = originalT tau ∧
        originalT (originalT v) = originalT tau) := by
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
  obtain ⟨hgroup, hrange, hrecActual, hprepend, hparameters, hgraph, hlift,
    hfiniteIntegral, hrootImageExact⟩ :=
    D5.S1.Digit.Infinite.ClosedObservationGraphRealization.closed_observation_graph_realization
  have hrec (x : LegalDigits) := (hrecActual x).1
  have hactual (x : LegalDigits) := (hrecActual x).2.1
  have hshift (x : LegalDigits) (m n : ℕ) :
      bitShift (bitShift x m) n = bitShift x (m + n) := by
    apply Subtype.ext
    funext j
    simp [bitShift, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hfiniteShift (x : LegalDigits) (M : ℕ) (hx : finiteTail x) :
      finiteTail (bitShift x M) := by
    obtain ⟨N, hN⟩ := hx
    exact ⟨N, fun j hj => hN (j + M) (by omega)⟩
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
  let leftLabel (i : Fin 6) : Label :=
    if i.val ≤ 1 then threeLabel else if i.val = 2 then nullLabel else
      if i.val = 3 then fiveLabel else twoLabel
  let rightLabel (i : Fin 6) : Label :=
    if i.val ≤ 1 then nullLabel else if i.val = 2 then fiveLabel else
      if i.val = 3 then twoLabel else twoFiveLabel
  have hsq : t ^ 2 = 1 - t := by linarith [ht2]
  have hhalf : (1 : ℝ) / 2 < t := by nlinarith [ht2]
  have hcube : t ^ 3 = 2 * t - 1 := by linarith [ht2, ht3]
  have hgcube : g = 2 * t - 1 := hcube
  have hgp : g * (1 + t) = 1 - t := by
    dsimp [g]
    nlinarith [ht2, ht3, ht4]
  let rootLower (l : Label) : ℝ :=
    if l.val 1 then -1 else if l.val 0 then
      (if l.val 2 then 2 * t else t) else (if l.val 2 then g else t - 1)
  let rootUpper (l : Label) : ℝ :=
    if l.val 1 then t - 1 else if l.val 0 then
      (if l.val 2 then 1 + t else 2 * t) else (if l.val 2 then t else g)
  have hgpos : 0 < g := pow_pos ht 3
  have hglt : g < 1 := pow_lt_one₀ ht.le ht1 (by decide)
  have hroot (l : Label) (y : ℝ) (hy : y ∈ stateInterval (outgoing l)) :
      rootLower l ≤ branch l y ∧ branch l y ≤ rootUpper l := by
    have hh : branch l y ∈ branch l '' stateInterval (outgoing l) := ⟨y, hy, rfl⟩
    rw [hrootImageExact] at hh
    exact hh
  have hallow (b0 y : ℝ) (hb0 : 0 ≤ b0) (hb : b0 ≤ lambda) (i : Fin 6)
      (l : Label) (hy : y ∈ stateInterval (outgoing l))
      (hl : branch l y ∈ observation b0 i) :
      l = leftLabel i ∨ l = rightLabel i := by
    have hz := hroot l y hy
    generalize branch l y = z at hz hl
    have h1 := (le_max_right (-1 : ℝ) (cellLower i - b0)).trans hl.1
    have h3 := hl.2.trans (min_le_right (1 + t) (cellUpper i + b0))
    rcases hlabels l with rfl | rfl | rfl | rfl | rfl <;> fin_cases i
    all_goals try (first | exact Or.inl rfl | exact Or.inr rfl)
    all_goals
      exfalso
      dsimp only [rootLower, rootUpper, nullLabel, threeLabel, twoLabel,
        fiveLabel, twoFiveLabel] at hz
      norm_num [rootLower, rootUpper, nullLabel, threeLabel, twoLabel,
        fiveLabel, twoFiveLabel] at hz
      norm_num [cellLower, cellUpper, cuts, lambda] at h1 h3 hb
      simp only [hsq, g, hcube] at hz h1 h3 hb
      linarith only [hhalf, ht1, hb0, hb, h1, h3, hz.1, hz.2]
  have hsingle (b0 y : ℝ) (hb0 : 0 ≤ b0) (hb : b0 < lambda) (i : Fin 6)
      (l m : Label) (hyl : y ∈ stateInterval (outgoing l))
      (hym : y ∈ stateInterval (outgoing m))
      (hl : branch l y ∈ observation b0 i) (hm : branch m y ∈ observation b0 i) :
      l = m := by
    have hL := hallow b0 y hb0 hb.le i l hyl hl
    have hM := hallow b0 y hb0 hb.le i m hym hm
    have hl0 := (le_max_left (-1 : ℝ) (cellLower i - b0)).trans hl.1
    have hl1 := (le_max_right (-1 : ℝ) (cellLower i - b0)).trans hl.1
    have hl2 := hl.2.trans (min_le_left (1 + t) (cellUpper i + b0))
    have hl3 := hl.2.trans (min_le_right (1 + t) (cellUpper i + b0))
    have hm0 := (le_max_left (-1 : ℝ) (cellLower i - b0)).trans hm.1
    have hm1 := (le_max_right (-1 : ℝ) (cellLower i - b0)).trans hm.1
    have hm2 := hm.2.trans (min_le_left (1 + t) (cellUpper i + b0))
    have hm3 := hm.2.trans (min_le_right (1 + t) (cellUpper i + b0))
    fin_cases i <;> dsimp [leftLabel, rightLabel] at hL hM
    all_goals rcases hL with rfl | rfl <;> rcases hM with rfl | rfl
    all_goals try rfl
    all_goals
      exfalso
      dsimp only [branch, offset, nullLabel, threeLabel, twoLabel, fiveLabel,
        twoFiveLabel] at hl0 hl1 hl2 hl3 hm0 hm1 hm2 hm3
      norm_num [branch, offset, outgoing, nullLabel, threeLabel, twoLabel, fiveLabel,
        twoFiveLabel, cellLower, cellUpper, cuts, lambda]
        at hl0 hl1 hl2 hl3 hm0 hm1 hm2 hm3 hb
      simp [hsq, g, hcube] at hl0 hl1 hl2 hl3 hm0 hm1 hm2 hm3 hb
      linarith only [ht, ht1, hb0, hb,
        hl0, hl1, hl2, hl3, hm0, hm1, hm2, hm3]
  have hcanonicalPaths (b0 : ℝ) (q : ℕ) (R : ℝ) (hp : endpointParameters b0 q R)
      (s : Bool) (x : LegalDigits) (hs : stateAddress s x) :
      ∃ v : ℕ → Vertex q R,
        (∀ j, (v j).val.1 = actualGuard s x j ∧
          kappa (bitShift x (3 * j)) ∈ piece (v j) ∧
          ∀ i, kappa (bitShift x (3 * j)) ∈ observation b0 i → permits b0 (v j) i) ∧
        ∀ j, edge (v j) (window x j) (v (j + 1)) := by
    have hstate (j : ℕ) : stateAddress (actualGuard s x j) (bitShift x (3 * j)) := by
      intro h
      by_cases hj : j = 0
      · subst j; simpa [actualGuard, bitShift] using hs (by simpa [actualGuard] using h)
      · have hh : x.val (3 * j - 1) = true := by simpa [actualGuard, hj] using h
        have hn := x.property (3 * j - 1)
        have he : 3 * j - 1 + 1 = 3 * j := by omega
        cases hb : x.val (3 * j)
        · simpa [bitShift] using hb
        · exact False.elim (hn ⟨hh, by simpa [he] using hb⟩)
    have hmem (j : ℕ) : kappa (bitShift x (3 * j)) ∈ stateInterval (actualGuard s x j) :=
      hrange _ ▸ ⟨_, hstate j, rfl⟩
    choose v hv using fun j => (hgraph b0 q R hp).2.2.2.1
      (actualGuard s x j) _ (hmem j)
    have hconstraint (j : ℕ) (a b : ℝ) (ha : a ∈ endpoints q R)
        (hb : b ∈ endpoints q R) (hz : kappa (bitShift x (3 * j)) ∈ Set.Icc a b) :
        piece (v j) ⊆ Set.Icc a b := by
      let u := if actualGuard s x j then t else 1 + t
      have hloB : (-1 : ℝ) ∈ endpoints q R := hp.2.2.1 (by simp [seeds])
      have hhiB : u ∈ endpoints q R := by
        dsimp [u]; split <;> apply hp.2.2.1 <;> simp [seeds]
      have hmaxB : max (-1) a ∈ endpoints q R := by
        rcases le_total (-1 : ℝ) a with h | h
        · simpa [max_eq_right h] using ha
        · simpa [max_eq_left h] using hloB
      have hminB : min u b ∈ endpoints q R := by
        rcases le_total u b with h | h
        · simpa [min_eq_left h] using hhiB
        · simpa [min_eq_right h] using hb
      have hzi : kappa (bitShift x (3 * j)) ∈ Set.Icc (max (-1) a) (min u b) :=
        ⟨max_le (hmem j).1 hz.1, le_min (hmem j).2 hz.2⟩
      have hclip := (hv j).2.2.2 _ _ hmaxB hminB
        ⟨le_max_left _ _, hzi.1.trans (hmem j).2⟩
        ⟨(hmem j).1.trans hzi.2, min_le_left _ _⟩ hzi
      exact fun y hy => ⟨(le_max_right _ _).trans (hclip hy).1,
        (hclip hy).2.trans (min_le_right _ _)⟩
    have hguard (j : ℕ) : actualGuard s x (j + 1) = outgoing (window x j) := by
      have he : 3 * (j + 1) - 1 = 2 + 3 * j := by omega
      simp [actualGuard, outgoing, window,
        D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift, he]
    have hrootB (l : Label) : rootLower l ∈ endpoints q R ∧ rootUpper l ∈ endpoints q R := by
      rcases hlabels l with rfl | rfl | rfl | rfl | rfl
      all_goals norm_num [rootLower, rootUpper, nullLabel, threeLabel, twoLabel,
        fiveLabel, twoFiveLabel, show t - 1 = -t ^ 2 by linarith [hsq]]
      all_goals constructor <;> apply hp.2.2.1 <;> simp [seeds]
    refine ⟨v, ?_, ?_⟩
    · intro j
      refine ⟨(hv j).1, (hv j).2.1, ?_⟩
      intro i hi
      exact hconstraint j _ _ (hp.2.2.1 (Or.inl (Or.inr ⟨i, rfl⟩)))
        (hp.2.2.1 (Or.inr ⟨i, rfl⟩)) hi
    · intro j
      have hl : lawful (v j).val.1 (window x j) (v (j + 1)).val.1 := by
        rw [(hv j).1, (hv (j + 1)).1, hguard]
        exact ⟨fun h => by simpa [← window_shift x j, window,
          D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift] using hstate j h, rfl⟩
      have hd : piece (v j) ⊆ branch (window x j) '' stateInterval (v (j + 1)).val.1 := by
        rw [(hv (j + 1)).1, hguard, hrootImageExact]
        apply hconstraint j _ _ (hrootB _).1 (hrootB _).2
        have hh := hroot (window x j) _ (by simpa [hguard] using hmem (j + 1))
        rwa [← window_shift x j, ← original_t_shift x j, ← hrec] at hh
      have hinv (a : ℝ) (ha : a ∈ piece (v j)) :
          inverseBranch (window x j) a ∈ stateInterval (v (j + 1)).val.1 := by
        obtain ⟨y, hy, rfl⟩ := hd ha
        have he : inverseBranch (window x j) (branch (window x j) y) = y := by
          dsimp [inverseBranch, branch]; field_simp [hgpos.ne']; ring
        rwa [he]
      have ha := hinv _ ⟨le_rfl, (v j).property.2.2.2.2.1⟩
      have hb := hinv _ ⟨(v j).property.2.2.2.2.1, le_rfl⟩
      have hsX : stateInterval (v (j + 1)).val.1 ⊆ stateInterval false := by
        intro y hy; cases h : (v (j + 1)).val.1 <;> simp [h, stateInterval] at hy ⊢
        · exact hy
        · exact ⟨hy.1, by linarith [hy.2]⟩
      have haB := (hgraph b0 q R hp).2.1 _ _ (v j).property.1 (hsX ha)
      have hbB := (hgraph b0 q R hp).2.1 _ _ (v j).property.2.1 (hsX hb)
      have he : inverseBranch (window x j) '' piece (v j) =
          Set.Icc (inverseBranch (window x j) (v j).val.2.2)
            (inverseBranch (window x j) (v j).val.2.1) := by
        ext y
        constructor
        · rintro ⟨a, ha, rfl⟩; dsimp [inverseBranch]
          constructor <;> apply (div_le_div_iff_of_pos_right hgpos).mpr <;>
            linarith [ha.1, ha.2]
        · intro hy
          dsimp [inverseBranch] at hy
          have hlo := (div_le_iff₀ hgpos).mp hy.1
          have hhi := (le_div_iff₀ hgpos).mp hy.2
          refine ⟨branch (window x j) y, ?_, ?_⟩
          · dsimp [piece, branch]; constructor <;> linarith
          · dsimp [inverseBranch, branch]; field_simp [hgpos.ne']; ring
      refine ⟨hl, hd, ?_⟩
      rw [he]
      apply hconstraint (j + 1) _ _ hbB haB
      rw [← he]
      refine ⟨kappa (bitShift x (3 * j)), (hv j).2.1, ?_⟩
      have hh := hrec (bitShift x (3 * j))
      rw [window_shift x, original_t_shift x] at hh
      dsimp [branch] at hh
      dsimp [inverseBranch]
      apply (div_eq_iff hgpos.ne').2
      linarith
  have hinfinite {q : ℕ} {R : ℝ} (v : ℕ → Vertex q R) (l : ℕ → Label)
      (he : ∀ j, edge (v j) (l j) (v (j + 1))) : ∃ x : LegalDigits,
      stateAddress (v 0).val.1 x ∧ ∀ j, window x j = l j ∧
        actualGuard (v 0).val.1 x j = (v j).val.1 ∧
        kappa (bitShift x (3 * j)) ∈ piece (v j) := by
    let raw (i : ℕ) := (l (i / 3)).val ⟨i % 3, Nat.mod_lt _ (by decide)⟩
    have hraw (i : ℕ) : ¬ (raw i = true ∧ raw (i + 1) = true) := by
      intro hh
      by_cases hi : i % 3 < 2
      · have hd : (i + 1) / 3 = i / 3 := by omega
        have hm : (i + 1) % 3 = i % 3 + 1 := by omega
        apply (l (i / 3)).property (i % 3) (by omega)
        simpa [raw, hd, hm] using hh
      · have hm : i % 3 = 2 := by omega
        have hd : (i + 1) / 3 = i / 3 + 1 := by omega
        have hm' : (i + 1) % 3 = 0 := by omega
        have hout : outgoing (l (i / 3)) = true := by simpa [raw, hm, outgoing] using hh.1
        have hs : (v (i / 3 + 1)).val.1 = true := (he (i / 3)).1.2.trans hout
        have hz := (he (i / 3 + 1)).1.1 hs
        simpa [raw, hd, hm', hz] using hh.2
    let x : LegalDigits := ⟨raw, hraw⟩
    have hw (j : ℕ) : window x j = l j := by
      apply Subtype.ext; funext i
      have hd : (i.val + 3 * j) / 3 = j := by have := i.isLt; omega
      have hm : (i.val + 3 * j) % 3 = i.val := by have := i.isLt; omega
      simp [window, D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift, x, raw,
        hd, hm, Nat.mod_eq_of_lt i.isLt]
    have hs : stateAddress (v 0).val.1 x := by
      intro h; simpa [x, raw] using (he 0).1.1 h
    have hguard (j : ℕ) : actualGuard (v 0).val.1 x j = (v j).val.1 := by
      cases j with
      | zero => simp [actualGuard]
      | succ j =>
        have hd : (3 * (j + 1) - 1) / 3 = j := by omega
        have hm : (3 * (j + 1) - 1) % 3 = 2 := by omega
        simpa [actualGuard, x, raw, hd, hm, outgoing] using (he j).1.2.symm
    have htshift (j : ℕ) : originalT (bitShift x (3 * j)) = bitShift x (3 * (j + 1)) := by
      rw [originalT, hshift]; congr 1 <;> omega
    have hwshift (j : ℕ) : window (bitShift x (3 * j)) 0 = l j := by
      have hh : window (bitShift x (3 * j)) 0 = window x j := by
        apply Subtype.ext; funext i; simp [window, bitShift]
      exact hh.trans (hw j)
    let z : ℕ → ℕ → ℝ := Nat.rec (fun j => (v j).val.2.1)
      (fun _ f j => branch (l j) (f (j + 1)))
    have hz (N j : ℕ) : z N j ∈ piece (v j) := by
      induction N generalizing j with
      | zero => exact ⟨le_rfl, (v j).property.2.2.2.2.1⟩
      | succ N ih =>
        obtain ⟨a, ha, hae⟩ := (he j).2.2 (ih (j + 1))
        have hba : branch (l j) (z N (j + 1)) = a := by
          have hh := (div_eq_iff hgpos.ne').mp hae
          dsimp [branch]; linarith
        change branch (l j) (z N (j + 1)) ∈ piece (v j)
        rwa [hba]
    have hdifference (N j : ℕ) : kappa (bitShift x (3 * j)) - z N j =
        (-g) ^ N * (kappa (bitShift x (3 * (j + N))) - (v (j + N)).val.2.1) := by
      induction N generalizing j with
      | zero => simp [z]
      | succ N ih =>
        have hh := hrec (bitShift x (3 * j))
        rw [hwshift, htshift] at hh
        change kappa (bitShift x (3 * j)) - branch (l j) (z N (j + 1)) = _
        rw [hh]
        have halg : branch (l j) (kappa (bitShift x (3 * (j + 1)))) -
            branch (l j) (z N (j + 1)) =
            -g * (kappa (bitShift x (3 * (j + 1))) - z N (j + 1)) := by
          dsimp [branch]; ring
        rw [halg, ih]
        simp [pow_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]; ring
    have hbound (j : ℕ) : |kappa (bitShift x (3 * j)) - (v j).val.2.1| ≤ 4 := by
      have hx : kappa (bitShift x (3 * j)) ∈ stateInterval false :=
        hrange false ▸ ⟨_, by simp [stateAddress], rfl⟩
      have hv := (v j).property.2.2.1
      change -1 ≤ kappa (bitShift x (3 * j)) ∧ kappa (bitShift x (3 * j)) ≤ 1 + t at hx
      change -1 ≤ (v j).val.2.1 ∧ (v j).val.2.1 ≤ _ at hv
      have hhi : (if (v j).val.1 then t else 1 + t) ≤ 1 + t := by
        split <;> linarith
      exact abs_le.mpr ⟨by linarith [hx.1, hx.2, hv.1, hv.2],
        by linarith [hx.1, hx.2, hv.1, hv.2]⟩
    refine ⟨x, hs, fun j => ⟨hw j, hguard j, ?_⟩⟩
    have hzero : Filter.Tendsto (fun N => kappa (bitShift x (3 * j)) - z N j)
        Filter.atTop (𝓝 0) := by
      apply squeeze_zero_norm (fun N => ?_)
        (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hgpos.le hglt).mul_const 4)
      rw [hdifference, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_pos hgpos]
      exact mul_le_mul_of_nonneg_left (hbound (j + N)) (pow_nonneg hgpos.le N)
    have hzlim : Filter.Tendsto (fun N => z N j) Filter.atTop
        (𝓝 (kappa (bitShift x (3 * j)))) := by
      have hh := (tendsto_const_nhds (x := kappa (bitShift x (3 * j)))).sub hzero
      simpa only [sub_sub_cancel, sub_zero] using hh
    exact isClosed_Icc.mem_of_tendsto hzlim (Filter.Eventually.of_forall (fun N => hz N j))
  have hexact (Q : ℝ → Fin 6) (hQ : instrument Q) (b0 : ℝ)
      (_hb0 : 0 ≤ b0) (i : Fin 6) : exactObservation Q b0 i ⊆ observation b0 i := by
    rintro x ⟨hx, y, hy, hQi, hdist⟩
    have hc := hQ y hy
    rw [hQi] at hc
    obtain ⟨hlo, hhi⟩ := abs_le.mp hdist
    exact ⟨max_le hx.1 (by linarith [hc.1]),
      le_min hx.2 (by linarith [hc.2])⟩
  have hcommonTail (b0 : ℝ) (hb0 : 0 ≤ b0) (hb : b0 < lambda)
      (M : ℕ) (x y : LegalDigits) (r : Fin (M + 1) → Fin 6)
      (htail : bitShift x (3 * M) = bitShift y (3 * M))
      (hobs : ∀ j : Fin (M + 1),
        kappa (bitShift x (3 * j)) ∈ observation b0 (r j) ∧
        kappa (bitShift y (3 * j)) ∈ observation b0 (r j)) : x = y := by
    induction M generalizing x y with
    | zero => simpa [bitShift] using htail
    | succ M ih =>
      let r' : Fin (M + 1) → Fin 6 := fun j => r ⟨j.val + 1, by omega⟩
      have ht' : bitShift (originalT x) (3 * M) =
          bitShift (originalT y) (3 * M) := by
        simpa [originalT, hshift, Nat.mul_add, Nat.add_comm] using htail
      have ho' (j : Fin (M + 1)) :
          kappa (bitShift (originalT x) (3 * j)) ∈ observation b0 (r' j) ∧
          kappa (bitShift (originalT y) (3 * j)) ∈ observation b0 (r' j) := by
        simpa [r', originalT, hshift, Nat.mul_add, Nat.add_comm] using
          hobs ⟨j.val + 1, by omega⟩
      have hxy := ih (originalT x) (originalT y) r' ht' ho'
      have hxr : kappa (originalT x) ∈ stateInterval (outgoing (window x 0)) := by
        rw [← hrange]
        exact ⟨_, hactual x, rfl⟩
      have hyr : kappa (originalT x) ∈ stateInterval (outgoing (window y 0)) := by
        rw [hxy, ← hrange]
        exact ⟨_, hactual y, rfl⟩
      have h0 := hobs 0
      simp only [Fin.val_zero, Nat.mul_zero] at h0
      have hs0 (z : LegalDigits) : bitShift z 0 = z := by
        apply Subtype.ext; funext j; simp [bitShift]
      rw [hs0 x, hs0 y, hrec x, hrec y, ← hxy] at h0
      have hw := hsingle b0 (kappa (originalT x)) hb0 hb (r 0)
        (window x 0) (window y 0) hxr hyr h0.1 h0.2
      apply Subtype.ext
      funext j
      by_cases hj : j < 3
      · have hh := congrArg (fun l : Label => l.val ⟨j, hj⟩) hw
        simpa [window, D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift] using hh
      · have hh := congrArg (fun z : LegalDigits => z.val (j - 3)) hxy
        simpa [originalT, bitShift, Nat.sub_add_cancel (by omega : 3 ≤ j)] using hh
  have hpairUnique {q : ℕ} {R : ℝ} (b0 : ℝ) (r : List (Fin 6))
      (v : Vertex q R) (z : LegalDigits) (hz : stateAddress v.val.1 z)
      (hzp : kappa z ∈ piece v)
      (huq : ∀ M (x y : LegalDigits) (c : Fin (M + 1) → Fin 6),
        bitShift x (3 * M) = z → bitShift y (3 * M) = z →
        (∀ j : Fin (M + 1), kappa (bitShift x (3 * j)) ∈ observation b0 (c j) ∧
          kappa (bitShift y (3 * j)) ∈ observation b0 (c j)) → x = y)
      (u w : List Label) (hu : (v, u) ∈ histories b0 r)
      (hw : (v, w) ∈ histories b0 r) : u = w := by
    by_cases hr : r = []
    · simp [histories, hr] at hu hw; exact hu.2.trans hw.2.symm
    · obtain ⟨a, as, _, halast, ha⟩ := (show ∃ a as, a.val.1 = false ∧
          (a :: as).getLast? = some v ∧ ClosedPath b0 r (a :: as) u from
          by simpa [histories, hr] using hu)
      obtain ⟨b, bs, _, hblast, hb⟩ := (show ∃ b bs, b.val.1 = false ∧
          (b :: bs).getLast? = some v ∧ ClosedPath b0 r (b :: bs) w from
          by simpa [histories, hr] using hw)
      obtain ⟨x, hx, hxt⟩ := hlift b0 r _ u ha v halast z hz hzp
      obtain ⟨y, hy, hyt⟩ := hlift b0 r _ w hb v hblast z hz hzp
      have hxread := hpath_read b0 r _ u ha
      have hyread := hpath_read b0 r _ w hb
      have hlen : w.length = u.length := by omega
      let c : Fin (u.length + 1) → Fin 6 :=
        fun j => r.get ⟨j.val, by rw [← hxread.1]; exact j.isLt⟩
      have he := huq u.length x y c hxt (by simpa [hlen] using hyt) (fun j =>
        ⟨(hxread.2 x hx).2 ⟨j.val, by omega⟩, (hyread.2 y hy).2 ⟨j.val, by omega⟩⟩)
      rw [(hxread.2 x hx).1, (hyread.2 y hy).1, hlen, he]
  have hhistoryUnique (b0 : ℝ) (q : ℕ) (R : ℝ) (hb0 : 0 ≤ b0) (hb : b0 < lambda)
      (r : List (Fin 6)) (v : Vertex q R) (u w : List Label)
      (hu : (v, u) ∈ histories b0 r) (hw : (v, w) ∈ histories b0 r) : u = w := by
    have hv : v.val.2.1 ∈ stateInterval v.val.1 := v.property.2.2.1
    obtain ⟨z, hz, he⟩ := hrange _ ▸ hv
    apply hpairUnique b0 r v z hz (by rw [he]; exact ⟨le_rfl, v.property.2.2.2.2.1⟩)
      (fun M x y c hx hy ho => hcommonTail b0 hb0 hb M x y c (hx.trans hy.symm) ho) u w hu hw
  have hlcp {q : ℕ} {R : ℝ} (H : Set (Vertex q R × List Label)) :
      (∀ vw ∈ H, globalLCP H <+: vw.2) ∧
      (H.Nonempty → ∀ p : List Label, (∀ vw ∈ H, p <+: vw.2) →
        p.length ≤ (globalLCP H).length) ∧ (H = ∅ → globalLCP H = []) := by
    by_cases hh : H.Nonempty
    · let w := (Classical.choose hh).2
      have hw : (Classical.choose hh) ∈ H := Classical.choose_spec hh
      have hzero : ∀ vw ∈ H, w.take 0 <+: vw.2 := by simp
      have hg := Nat.findGreatest_spec (P := fun n => ∀ vw ∈ H, w.take n <+: vw.2)
        (Nat.zero_le w.length) hzero
      have hgl := Nat.findGreatest_le (P := fun n => ∀ vw ∈ H, w.take n <+: vw.2) w.length
      have he : globalLCP H = w.take
          (Nat.findGreatest (fun n => ∀ vw ∈ H, w.take n <+: vw.2) w.length) := by
        simp [globalLCP, hh, w]
      refine ⟨by simpa [he] using hg, ?_, ?_⟩
      · intro _ p hp
        have hpw := hp _ hw
        have htake : w.take p.length = p := by
          obtain ⟨d, hd⟩ := hpw
          change p ++ d = w at hd
          rw [← hd]; simp
        have hle := Nat.le_findGreatest (P := fun n => ∀ vw ∈ H, w.take n <+: vw.2)
          hpw.length_le (by simpa only [htake] using hp)
        rw [he, List.length_take, min_eq_left hgl]; exact hle
      · intro hempty; exact False.elim (by simpa [hempty] using hh)
    · have he : globalLCP H = [] := by simp [globalLCP, hh]
      exact ⟨by simp [he], fun h => False.elim (hh h), fun _ => he⟩
  have hhistoryBounds (b0 : ℝ) (q : ℕ) (R : ℝ) (hb0 : 0 ≤ b0) (hb : b0 < lambda)
      (hp : endpointParameters b0 q R) (r : List (Fin 6)) :
      (histories (q := q) (R := R) b0 r).Finite ∧
      (histories (q := q) (R := R) b0 r).ncard ≤ (Set.univ : Set (Vertex q R)).ncard ∧
      (residuals (q := q) (R := R) b0 r).ncard ≤ (Set.univ : Set (Vertex q R)).ncard ∧
      (∀ vw ∈ histories (q := q) (R := R) b0 r,
        (r = [] → vw.2 = []) ∧ (r ≠ [] → vw.2.length + 1 = r.length) ∧
        globalLCP (histories (q := q) (R := R) b0 r) <+: vw.2) ∧
      ((histories (q := q) (R := R) b0 r).Nonempty → ∀ p : List Label,
        (∀ vw ∈ histories (q := q) (R := R) b0 r, p <+: vw.2) →
        p.length ≤ (globalLCP (histories (q := q) (R := R) b0 r)).length) ∧
      (histories (q := q) (R := R) b0 r = ∅ →
        globalLCP (histories (q := q) (R := R) b0 r) = []) := by
    let H := histories (q := q) (R := R) b0 r
    have hinj : Set.InjOn Prod.fst H := by
      intro a ha b hbmem hab
      apply Prod.ext hab
      rcases a with ⟨v,u⟩; rcases b with ⟨v',w⟩; dsimp at hab; subst v'
      exact hhistoryUnique b0 q R hb0 hb r v u w ha hbmem
    have hV := (hgraph b0 q R hp).2.2.1
    have hf : H.Finite := Set.Finite.of_injOn (fun _ _ => Set.mem_univ _) hinj hV
    have hcard := Set.ncard_le_ncard_of_injOn Prod.fst (fun _ _ => Set.mem_univ _) hinj hV
    have hpref := hlcp H
    refine ⟨hf, hcard, (Set.ncard_image_le hf).trans hcard, ?_, hpref.2.1, hpref.2.2⟩
    intro vw hvw
    refine ⟨?_, ?_, hpref.1 vw hvw⟩
    · intro hr; exact (show (vw.1.val.1 = false ∧ vw.2 = []) from
        by simpa [histories, hr] using hvw).2
    · intro hr
      obtain ⟨v,vs,_,_,hp⟩ := (show ∃ v vs, v.val.1 = false ∧
        (v :: vs).getLast? = some vw.1 ∧ ClosedPath b0 r (v :: vs) vw.2 from
        by simpa [histories, hr] using hvw)
      exact (hpath_read b0 r _ vw.2 hp).1
  have hfiniteUnshift (x : LegalDigits) (n : ℕ) (hx : finiteTail (bitShift x n)) :
      finiteTail x := by
    obtain ⟨N, hN⟩ := hx
    refine ⟨N + n, ?_⟩
    intro j hj
    have hh := hN (j - n) (by omega)
    simpa [bitShift, Nat.sub_add_cancel (by omega : n ≤ j)] using hh
  have hfiniteExtremes (x : LegalDigits) (hx : finiteTail x) :
      kappa x ≠ -1 ∧ kappa x ≠ 1 + t := by
    obtain ⟨N, hN⟩ := hx
    constructor
    · intro he
      have hv : signedValue x = t ^ 2 := by
        have hh := hgroup x; rw [he] at hh
        field_simp [ht.ne'] at hh; linarith
      have hxv := (signed_series_range.2.2 x).mp hv
      have hh := hN (2 * N + 1) (by omega)
      rw [hxv] at hh
      simp [D5.S1.Digit.Infinite.SignedSeriesRange.v] at hh
    · intro he
      have hv : signedValue x = -t := by
        have hh := hgroup x; rw [he] at hh
        field_simp [ht.ne'] at hh
        nlinarith [ht2, ht3]
      have hxu := (signed_series_range.2.1 x).mp hv
      have hh := hN (2 * N) (by omega)
      rw [hxu] at hh
      simp [D5.S1.Digit.Infinite.SignedSeriesRange.u] at hh
  have hfiniteCritical (x : LegalDigits) (hx : finiteTail x) (k : ℕ)
      (hk : 1 ≤ k) (hk4 : k ≤ 4) : kappa x ≠ (-5 + k + k * t) / 5 := by
    obtain ⟨z, hz⟩ := hfiniteIntegral x hx
    intro he
    have hez : embedding ((5 : GoldenInt) * z) =
        embedding (⟨-5, k⟩ : GoldenInt) := by
      rw [map_mul, map_ofNat, ← hz, he]
      simp [D5.S1.Scale.embedding_apply, hphi]; ring
    have hb := congrArg GoldenInt.b (embedding_injective hez)
    have h5 : (5 : GoldenInt) = ⟨5, 0⟩ := by decide
    rw [h5, D5.S0.Carrier.b_mul] at hb
    norm_num at hb
    omega
  have hsingleCritical (x : LegalDigits) (hx : finiteTail x) (i : Fin 6)
      (l m : Label) (hyl : kappa x ∈ stateInterval (outgoing l))
      (hym : kappa x ∈ stateInterval (outgoing m))
      (hl : branch l (kappa x) ∈ observation lambda i)
      (hm : branch m (kappa x) ∈ observation lambda i) : l = m := by
    have hL := hallow lambda _ (by dsimp [lambda]; positivity) le_rfl i l hyl hl
    have hM := hallow lambda _ (by dsimp [lambda]; positivity) le_rfl i m hym hm
    have hl0 := (le_max_left (-1 : ℝ) (cellLower i - lambda)).trans hl.1
    have hl1 := (le_max_right (-1 : ℝ) (cellLower i - lambda)).trans hl.1
    have hl2 := hl.2.trans (min_le_left (1 + t) (cellUpper i + lambda))
    have hl3 := hl.2.trans (min_le_right (1 + t) (cellUpper i + lambda))
    have hm0 := (le_max_left (-1 : ℝ) (cellLower i - lambda)).trans hm.1
    have hm1 := (le_max_right (-1 : ℝ) (cellLower i - lambda)).trans hm.1
    have hm2 := hm.2.trans (min_le_left (1 + t) (cellUpper i + lambda))
    have hm3 := hm.2.trans (min_le_right (1 + t) (cellUpper i + lambda))
    have hylX : -1 ≤ kappa x ∧ kappa x ≤ 1 + t := by
      cases hs : outgoing l <;> simp [hs, stateInterval] at hyl ⊢
      · exact hyl
      · exact ⟨hyl.1, by linarith [hyl.2]⟩
    have hlow := mul_le_mul_of_nonneg_left hylX.1 hgpos.le
    have hhigh := mul_le_mul_of_nonneg_left hylX.2 hgpos.le
    rw [hgp] at hhigh
    simp only [hgcube] at hlow hhigh
    let contact (i : Fin 6) : ℝ := match i.val with
      | 0 => 1 + t
      | 1 => (-4 + t) / 5
      | 2 => (-3 + 2 * t) / 5
      | 3 => (-2 + 3 * t) / 5
      | 4 => (-1 + 4 * t) / 5
      | _ => -1
    have hnot : kappa x ≠ contact i := by
      have hE := hfiniteExtremes x hx
      have hC1 := hfiniteCritical x hx 1 (by decide) (by decide)
      have hC2 := hfiniteCritical x hx 2 (by decide) (by decide)
      have hC3 := hfiniteCritical x hx 3 (by decide) (by decide)
      have hC4 := hfiniteCritical x hx 4 (by decide) (by decide)
      norm_num at hC1 hC2 hC3 hC4
      fin_cases i <;> norm_num [contact] <;>
        first | exact hE.1 | exact hE.2 | simpa using hC1 | simpa using hC2 |
          simpa using hC3 | simpa using hC4
    fin_cases i <;> dsimp [leftLabel, rightLabel] at hL hM
    all_goals rcases hL with rfl | rfl <;> rcases hM with rfl | rfl
    all_goals try rfl
    all_goals
      exfalso
      apply hnot
      norm_num [contact]
      apply (mul_left_cancel₀ hgpos.ne')
      simp only [hgcube]
      simp [branch, offset, nullLabel, threeLabel, twoLabel, fiveLabel,
        twoFiveLabel, cellLower, cellUpper, cuts, lambda, hsq, hgcube]
        at hl0 hl1 hl2 hl3 hm0 hm1 hm2 hm3
      nlinarith only [hl0, hl1, hl2, hl3, hm0, hm1, hm2, hm3, hlow, hhigh, ht2]
  have hcriticalCommon (M : ℕ) (x y : LegalDigits) (r : Fin (M + 1) → Fin 6)
      (htail : bitShift x (3 * M) = bitShift y (3 * M))
      (hf : finiteTail (bitShift x (3 * M)))
      (hobs : ∀ j : Fin (M + 1),
        kappa (bitShift x (3 * j)) ∈ observation lambda (r j) ∧
        kappa (bitShift y (3 * j)) ∈ observation lambda (r j)) : x = y := by
    induction M generalizing x y with
    | zero => simpa [bitShift] using htail
    | succ M ih =>
      let r' : Fin (M + 1) → Fin 6 := fun j => r ⟨j.val + 1, by omega⟩
      have ht' : bitShift (originalT x) (3 * M) =
          bitShift (originalT y) (3 * M) := by
        simpa [originalT, hshift, Nat.mul_add, Nat.add_comm] using htail
      have hf' : finiteTail (bitShift (originalT x) (3 * M)) := by
        simpa [originalT, hshift, Nat.mul_add, Nat.add_comm] using hf
      have ho' (j : Fin (M + 1)) := hobs ⟨j.val + 1, by omega⟩
      have hxy := ih (originalT x) (originalT y) r' ht' hf'
        (fun j => by simpa [r', originalT, hshift, Nat.mul_add, Nat.add_comm] using ho' j)
      have hxr : kappa (originalT x) ∈ stateInterval (outgoing (window x 0)) :=
        hrange _ ▸ ⟨_, hactual x, rfl⟩
      have hyr : kappa (originalT x) ∈ stateInterval (outgoing (window y 0)) := by
        rw [hxy, ← hrange]; exact ⟨_, hactual y, rfl⟩
      have h0 := hobs 0
      have hs0 (z : LegalDigits) : bitShift z 0 = z := by
        apply Subtype.ext; funext j; simp [bitShift]
      simp only [Fin.val_zero, Nat.mul_zero] at h0
      rw [hs0 x, hs0 y, hrec x, hrec y, ← hxy] at h0
      have hw := hsingleCritical (originalT x) (hfiniteUnshift _ _ hf') (r 0)
        (window x 0) (window y 0) hxr hyr h0.1 h0.2
      apply Subtype.ext; funext j
      by_cases hj : j < 3
      · have hh := congrArg (fun l : Label => l.val ⟨j, hj⟩) hw
        simpa [window, D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift] using hh
      · have hh := congrArg (fun z : LegalDigits => z.val (j - 3)) hxy
        simpa [originalT, bitShift, Nat.sub_add_cancel (by omega : 3 ≤ j)] using hh
  have hdensity {q : ℕ} {R : ℝ} (v : Vertex q R) (hv : v.val.2.1 < v.val.2.2) :
      ∃ z : LegalDigits, stateAddress v.val.1 z ∧ finiteTail z ∧ kappa z ∈ piece v := by
    let m := (v.val.2.1 + v.val.2.2) / 2
    have hm : m ∈ stateInterval v.val.1 := by
      constructor <;> dsimp [m] <;> linarith [v.property.2.2.1.1, v.property.2.2.2.1.2]
    obtain ⟨x, hs, hx⟩ := hrange _ ▸ hm
    let z (N : ℕ) : LegalDigits := ⟨fun j => if j < 3 * N then x.val j else false, by
      intro j hj
      by_cases h : j + 1 < 3 * N
      · apply x.property j; simpa [h, show j < 3 * N by omega] using hj
      · simpa [h] using hj.2⟩
    have hzs (N : ℕ) : stateAddress v.val.1 (z N) := by
      intro h; simp [z, hs h]
    have hzf (N : ℕ) : finiteTail (z N) := ⟨3 * N, fun j hj => by simp [z, not_lt.mpr hj]⟩
    have hzw (N j : ℕ) : window (z N) j = if j < N then window x j else nullLabel := by
      apply Subtype.ext; funext i
      by_cases h : j < N
      · simp [h, window, D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift, z,
          show i.val + 3 * j < 3 * N by have := i.isLt; omega]
      · simp [h, window, D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift, z,
          nullLabel, show ¬ i.val + 3 * j < 3 * N by omega]
    have hsum (N : ℕ) : kappa (z N) =
        ∑ j ∈ Finset.range N, (-g) ^ j * offset (window x j) := by
      have hh : kappa (z N) = ∑ j ∈ Finset.range N, (-g) ^ j * offset (window (z N) j) := by
        apply tsum_eq_sum
        intro j hj; rw [hzw]; simp [show ¬j < N by simpa using hj, offset, nullLabel]
      rw [hh]
      apply Finset.sum_congr rfl
      intro j hj; rw [hzw]; simp [Finset.mem_range.mp hj]
    have hseries : Summable (fun j => (-g) ^ j * offset (window x j)) := by
      apply ((summable_geometric_of_lt_one hgpos.le hglt).mul_right 3).of_norm_bounded
      intro j
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_pos hgpos]
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hgpos.le j)
      rcases hlabels (window x j) with h | h | h | h | h
      all_goals rw [h]; apply abs_le.mpr
      all_goals simp [offset, nullLabel, threeLabel, twoLabel, fiveLabel, twoFiveLabel]
      all_goals (try constructor) <;> nlinarith only [ht, ht1, ht2]
    have hlim : Filter.Tendsto (fun N => kappa (z N)) Filter.atTop (𝓝 m) := by
      simp_rw [hsum]
      rw [← hx]
      exact hseries.hasSum.tendsto_sum_nat
    have hmid : m ∈ Set.Ioo v.val.2.1 v.val.2.2 := by
      constructor <;> dsimp [m] <;> linarith
    obtain ⟨N, hN⟩ := (hlim.eventually (isOpen_Ioo.mem_nhds hmid)).exists
    exact ⟨z N, hzs N, hzf N, hN.1.le, hN.2.le⟩
  have hcriticalVertices (q : ℕ) (R : ℝ) (_hp : endpointParameters lambda q R) :
      (∀ v : Vertex q R, (∃ z : LegalDigits, stateAddress v.val.1 z ∧
        finiteTail z ∧ kappa z ∈ piece v) → ∀ r u w,
        (v, u) ∈ histories lambda r → (v, w) ∈ histories lambda r → u = w) ∧
      (∀ v : Vertex q R, v.val.2.1 < v.val.2.2 →
        ∃ z : LegalDigits, stateAddress v.val.1 z ∧ finiteTail z ∧ kappa z ∈ piece v) := by
    refine ⟨?_, hdensity⟩
    rintro v ⟨z, hz, hf, hp⟩ r u w hu hw
    exact hpairUnique lambda r v z hz hp
      (fun M x y c hx hy ho => hcriticalCommon M x y c (hx.trans hy.symm)
        (hx.symm ▸ hf) ho) u w hu hw
  have hcriticalScalar : ∃ tau u v : LegalDigits,
      stateAddress false tau ∧ kappa tau = (-4 + t) / 5 ∧
      (¬ ∃ z : GoldenInt, kappa tau = embedding z) ∧
      window u 0 = threeLabel ∧ window v 0 = nullLabel ∧
      originalT u = tau ∧ originalT v = tau ∧
      ¬ finiteTail u ∧ ¬ finiteTail v ∧
      kappa u = cuts 0 - lambda ∧ kappa v = cuts 1 + lambda := by
    have hy : (-4 + t) / 5 ∈ stateInterval false := by
      simp only [stateInterval, Bool.false_eq_true, ↓reduceIte, Set.mem_Icc]
      constructor <;> linarith
    obtain ⟨tau, htau, hvtau⟩ := hrange false ▸ hy
    have hnot : ¬ ∃ z : GoldenInt, kappa tau = embedding z := by
      rintro ⟨z, hz⟩
      have he : embedding ((5 : GoldenInt) * z) = embedding (⟨-5, 1⟩ : GoldenInt) := by
        rw [map_mul, map_ofNat, ← hz, hvtau]
        simp only [D5.S1.Scale.embedding_apply]
        norm_num
        linarith
      have hez := embedding_injective he
      have hb := congrArg GoldenInt.b hez
      have h5 : (5 : GoldenInt) = ⟨5, 0⟩ := by decide
      rw [h5, D5.S0.Carrier.b_mul] at hb
      norm_num at hb
      omega
    obtain ⟨u, hu, _⟩ := hprepend false threeLabel false tau
      (by simp [lawful, outgoing, threeLabel]) htau
    obtain ⟨v, hv, _⟩ := hprepend false nullLabel false tau
      (by simp [lawful, outgoing, nullLabel]) htau
    have hnu : ¬ finiteTail u := by
      intro h
      have hh := hfiniteIntegral (originalT u) (hfiniteShift u 3 h)
      rw [hu.2.2] at hh
      exact hnot hh
    have hnv : ¬ finiteTail v := by
      intro h
      have hh := hfiniteIntegral (originalT v) (hfiniteShift v 3 h)
      rw [hv.2.2] at hh
      exact hnot hh
    refine ⟨tau, u, v, htau, hvtau, hnot, hu.2.1, hv.2.1, hu.2.2, hv.2.2,
      hnu, hnv, ?_, ?_⟩
    · rw [hrec, hu.2.1, hu.2.2, hvtau]
      simp [branch, offset, threeLabel, cuts, lambda, g]
      nlinarith [congrArg (fun z : ℝ => t ^ 2 * z) ht2]
    · rw [hrec, hv.2.1, hv.2.2, hvtau]
      simp [branch, offset, nullLabel, cuts, lambda, g]
      nlinarith [congrArg (fun z : ℝ => t ^ 2 * z) ht2]
  have hInstrument : ∃ Q : ℝ → Fin 6,
      instrument Q ∧ Q (cuts 0) = 1 ∧ Q (cuts 1) = 1 := by
    have hab : cuts 0 ≤ cuts 1 := by
      norm_num [cuts, lambda, g]
      nlinarith only [ht2, ht3, ht, ht1]
    let Q (x : ℝ) : Fin 6 :=
      if x ≤ cuts 1 then (if x < cuts 0 then 0 else 1) else
      if x ≤ cuts 2 then 2 else if x ≤ cuts 3 then 3 else
      if x ≤ cuts 4 then 4 else 5
    refine ⟨Q, ?_, ?_, ?_⟩
    · intro x hx
      change -1 ≤ x ∧ x ≤ 1 + t at hx
      simp only [Q]
      split_ifs <;> norm_num [cellLower, cellUpper] <;>
        constructor <;> linarith
    · simp only [Q, hab, if_true, lt_self_iff_false, if_false]
    · simp only [Q, le_refl, if_true, not_lt.mpr hab, if_false]
  have hsingleton (q : ℕ) (R : ℝ) (hp : endpointParameters lambda q R)
      (Q : ℝ → Fin 6) (hQ : instrument Q) (hQa : Q (cuts 0) = 1) (hQb : Q (cuts 1) = 1) :
      ∃ tau u v : LegalDigits, ∃ z : Vertex q R,
        stateAddress false tau ∧ kappa tau = (-4 + t) / 5 ∧
        window u 0 = threeLabel ∧ window v 0 = nullLabel ∧ u ≠ v ∧
        originalT u = tau ∧ originalT v = tau ∧ ¬ finiteTail u ∧ ¬ finiteTail v ∧
        kappa u + lambda = cuts 0 ∧ kappa v - lambda = cuts 1 ∧
        Q (kappa u + lambda) = 1 ∧ Q (kappa v - lambda) = 1 ∧ Q (kappa tau) = 0 ∧
        z.val = (false, (-4 + t) / 5, (-4 + t) / 5) ∧
        (z, [threeLabel]) ∈ histories lambda [1, 0] ∧
        (z, [nullLabel]) ∈ histories lambda [1, 0] ∧
        originalT (originalT u) = originalT tau ∧ originalT (originalT v) = originalT tau := by
    obtain ⟨tau,u,v,hs,htau,_,huw,hvw,hut,hvt,hnu,hnv,hu,hv⟩ := hcriticalScalar
    have htauX : kappa tau ∈ stateInterval false := hrange false ▸ ⟨tau,hs,rfl⟩
    have hlo : max (-1 : ℝ) (cellLower 1 - lambda) = kappa u := by
      rw [hu]; change max (-1) (cuts 0 - lambda) = cuts 0 - lambda
      apply max_eq_right
      norm_num [cuts, lambda]; nlinarith [ht, ht1, ht2]
    have hhi : min (1 + t) (cellUpper 1 + lambda) = kappa v := by
      rw [hv]; change min (1 + t) (cuts 1 + lambda) = cuts 1 + lambda
      apply min_eq_right
      norm_num [cuts, lambda, g]; nlinarith [ht, ht1, ht2, ht3]
    have huB : kappa u ∈ endpoints q R :=
      hlo ▸ hp.2.2.1 (Or.inl (Or.inr ⟨1, rfl⟩))
    have hvB : kappa v ∈ endpoints q R := hhi ▸ hp.2.2.1 (Or.inr ⟨1,rfl⟩)
    have hinv : inverseBranch threeLabel (kappa u) = kappa tau := by
      have hh := hrec u; rw [huw,hut] at hh
      dsimp [inverseBranch,branch] at hh ⊢
      apply (div_eq_iff hgpos.ne').2; linarith
    have htauB := (hgraph lambda q R hp).2.1 threeLabel _ huB (by rwa [hinv])
    rw [hinv] at htauB
    let singleton (a : ℝ) (ha : a ∈ endpoints q R) : Vertex q R :=
      ⟨(false,a,a),ha,ha,ha.1,ha.1,le_rfl,Or.inl rfl⟩
    let z := singleton (kappa tau) htauB
    let a := singleton (kappa u) huB
    let b := singleton (kappa v) hvB
    have hpz : permits lambda z 0 := by
      intro y hy
      have hyt : y = kappa tau := le_antisymm hy.2 hy.1
      rw [hyt,htau]
      change max (-1) (-1 - lambda) ≤ (-4+t)/5 ∧
        (-4+t)/5 ≤ min (1+t) (cuts 0 + lambda)
      constructor
      · apply max_le <;> (try dsimp [lambda]) <;> nlinarith only [ht,ht1,ht2]
      · apply le_min <;> norm_num [cuts,lambda] <;> nlinarith only [ht,ht1,ht2]
    have hpa : permits lambda a 1 := by
      intro y hy
      have he : y = kappa u := le_antisymm hy.2 hy.1
      rw [he]; change max (-1) (cellLower 1 - lambda) ≤ kappa u ∧
        kappa u ≤ min (1+t) (cellUpper 1 + lambda)
      rw [hlo,hhi,hu,hv]; constructor <;> norm_num [cuts,lambda,g] <;>
        nlinarith [ht,ht1,ht2,ht3]
    have hpb : permits lambda b 1 := by
      intro y hy
      have he : y = kappa v := le_antisymm hy.2 hy.1
      rw [he]; change max (-1) (cellLower 1 - lambda) ≤ kappa v ∧
        kappa v ≤ min (1+t) (cellUpper 1 + lambda)
      rw [hlo,hhi,hu,hv]; constructor <;> norm_num [cuts,lambda,g] <;>
        nlinarith [ht,ht1,ht2,ht3]
    have hedge (c : LegalDigits) (hcB : kappa c ∈ endpoints q R) (l : Label)
        (hl : lawful false l false) (hcw : window c 0 = l) (hct : originalT c = tau) :
        edge (singleton (kappa c) hcB) l z := by
      refine ⟨hl, ?_, ?_⟩
      · intro y hy
        have he : y = kappa c := le_antisymm hy.2 hy.1
        refine ⟨kappa tau,htauX,?_⟩
        rw [he,← hct,← hcw,← hrec]
      · intro y hy
        have he : y = kappa tau := le_antisymm hy.2 hy.1
        refine ⟨kappa c,⟨le_rfl,le_rfl⟩,?_⟩
        rw [he]; have hh := hrec c; rw [hcw,hct] at hh
        dsimp [inverseBranch,branch] at hh ⊢
        apply (div_eq_iff hgpos.ne').2; linarith
    have hQ0 : Q (kappa tau) = 0 := by
      have hc := hQ _ htauX
      generalize he : Q (kappa tau) = i at hc ⊢
      fin_cases i
      · rfl
      all_goals exfalso; rw [htau] at hc
      all_goals norm_num [cellLower,cellUpper,cuts,lambda,g] at hc
      all_goals nlinarith [ht,ht1,ht2,ht3]
    have hne : u ≠ v := by
      intro he; have hh := huw.symm.trans ((congrArg (fun x => window x 0) he).trans hvw)
      have hh1 := congrArg (fun l : Label => l.val 1) hh
      norm_num [threeLabel,nullLabel] at hh1
    refine ⟨tau,u,v,z,hs,htau,huw,hvw,hne,hut,hvt,hnu,hnv,
      by linarith [hu],by linarith [hv],?_,?_,hQ0,?_,?_,?_,by rw [hut],by rw [hvt]⟩
    · simpa [hu] using hQa
    · simpa [hv] using hQb
    · change (false,kappa tau,kappa tau) = _; rw [htau]
    · change ∃ p ps, p.val.1 = false ∧ (p::ps).getLast? = some z ∧
        ClosedPath lambda [1,0] (p::ps) [threeLabel]
      exact ⟨a,[z],rfl,rfl,ClosedPath.step 1 [0] a z [] threeLabel [] hpa
        (hedge u huB threeLabel (by simp [lawful,outgoing,threeLabel]) huw hut)
        (ClosedPath.point 0 z hpz)⟩
    · change ∃ p ps, p.val.1 = false ∧ (p::ps).getLast? = some z ∧
        ClosedPath lambda [1,0] (p::ps) [nullLabel]
      exact ⟨b,[z],rfl,rfl,ClosedPath.step 1 [0] b z [] nullLabel [] hpb
        (hedge v hvB nullLabel (by simp [lawful,outgoing,nullLabel]) hvw hvt)
        (ClosedPath.point 0 z hpz)⟩
  refine ⟨hgroup, hrange, hrecActual, hprepend, hparameters, ?_, hlift,
    hcanonicalPaths, hinfinite, hexact,
    hcommonTail, (fun b0 q R hb0 hb hp =>
      ⟨hhistoryUnique b0 q R hb0 hb, hhistoryBounds b0 q R hb0 hb hp⟩),
    hfiniteIntegral, hcriticalCommon, hcriticalVertices, hcriticalScalar, hInstrument, hsingleton⟩
  · intro b0 q R hp
    exact ⟨(hgraph b0 q R hp).1, (hgraph b0 q R hp).2.1,
      (hgraph b0 q R hp).2.2.1, (hgraph b0 q R hp).2.2.2.1,
      (hgraph b0 q R hp).2.2.2.2.1, (hgraph b0 q R hp).2.2.2.2.2⟩

end D5.S1.Digit.Infinite.ClosedObservationCommonTailWidth
