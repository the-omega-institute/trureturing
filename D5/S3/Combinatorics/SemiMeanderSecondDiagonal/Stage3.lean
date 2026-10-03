/- GID: D5/S3/Combinatorics/SemiMeanderSecondDiagonal/Stage3
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SemiMeanderSecondDiagonal/Stage3
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Source-prefix equivalence and connectedness obstructions. -/

import D5.S3.Combinatorics.SemiMeanderSecondDiagonal.Stage2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SemiMeanderSecondDiagonal

open Classical

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def fromPrefixes {n : ℕ} (p q : TwoDownPrefix n) :
    UpperMatching n :=
  {
    mate := (joinedMate p) q
    mate_mate := (joinedMate_involutive p) q
    mate_ne := (joinedMate_ne p) q
    noncrossing := (joinedMate_noncrossing p) q
  }

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem fromPrefixes_leftCut {n : ℕ} (p q : TwoDownPrefix n)
    (x : Fin n) : (leftCut (fromPrefixes p q)) x = (halfCut p) x := by
  have joinedMate_left (i : Fin n) : (joinedMate p) q (leftPoint n i) =
      if hi : i ∈ (unmatchedPositions p) then
        rightPoint n (((rankJoin p) q ⟨i, hi⟩).1)
      else leftPoint n ((halfMateFin p) i) := by
    simp [joinedMate, rainbowLabel, leftPoint]
  by_cases hx : x ∈ (unmatchedPositions p)
  · have hnone : (halfCut p) x = none :=
      (Finset.mem_filter.mp hx).2
    have hright : n ≤ (rightPoint n (((rankJoin p) q ⟨x, hx⟩).1)).val := by
      have hy := (((rankJoin p) q ⟨x, hx⟩).1).isLt
      have hv : (rightPoint n (((rankJoin p) q ⟨x, hx⟩).1)).val =
          2 * n - ((((rankJoin p) q ⟨x, hx⟩).1).val + 1) := by
        simp [rightPoint, leftPoint]
      omega
    rw [hnone]
    have hcross : n ≤ ((fromPrefixes p q).mate (leftPoint n x)).val := by
      change n ≤ ((joinedMate p) q (leftPoint n x)).val
      rw [joinedMate_left, dif_pos hx]
      exact hright
    simpa [leftCut] using hcross
  · have hne : (halfMate p) x.val ≠ x.val := by
      intro hfix
      apply hx
      exact ((halfMateFin_fixed_iff p) x).mp (Fin.ext hfix)
    have hmate : (fromPrefixes p q).mate (leftPoint n x) =
        leftPoint n ((halfMateFin p) x) := by
      exact (joinedMate_left x).trans (dif_neg hx)
    have hcut := (leftCut_eq_some_iff (fromPrefixes p q)
      x ((halfMateFin p) x)).2 hmate
    simpa [halfCut, hne, halfMateFin] using hcut

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem fromPrefixes_rightCut {n : ℕ} (p q : TwoDownPrefix n)
    (x : Fin n) : (rightCut (fromPrefixes p q)) x = (halfCut q) x := by
  have joinedMate_right (j : Fin n) : (joinedMate p) q (rightPoint n j) =
      if hj : j ∈ (unmatchedPositions q) then
        leftPoint n (((rankJoin p) q).symm ⟨j, hj⟩).1
      else rightPoint n ((halfMateFin q) j) := by
    have hright : ¬ (rightPoint n j).val < n := by
      have hj := j.isLt
      have hv : (rightPoint n j).val = 2 * n - (j.val + 1) := by
        simp [rightPoint, leftPoint]
      omega
    have hlabel : rainbowLabel n (rightPoint n j) = j := by
      unfold rightPoint; rw [rainbowLabel_rev]
      simp [rainbowLabel, leftPoint]
    simp [joinedMate, hright, hlabel]
  by_cases hx : x ∈ (unmatchedPositions q)
  · have hnone : (halfCut q) x = none :=
      (Finset.mem_filter.mp hx).2
    have hleft : n ≤ (leftPoint n (((rankJoin p) q).symm ⟨x, hx⟩).1).rev.val := by
      have hy := ((((rankJoin p) q).symm ⟨x, hx⟩).1).isLt
      have hv : (leftPoint n ((((rankJoin p) q).symm ⟨x, hx⟩).1)).rev.val =
          2 * n - (((((rankJoin p) q).symm ⟨x, hx⟩).1).val + 1) := by
        simp [leftPoint]
      omega
    rw [hnone]
    have hcross : n ≤ ((fromPrefixes p q).mate (rightPoint n x)).rev.val := by
      change n ≤ ((joinedMate p) q (rightPoint n x)).rev.val
      rw [joinedMate_right, dif_pos hx]
      exact hleft
    simpa [rightCut] using hcross
  · have hne : (halfMate q) x.val ≠ x.val := by
      intro hfix
      apply hx
      exact ((halfMateFin_fixed_iff q) x).mp (Fin.ext hfix)
    have hmate : (fromPrefixes p q).mate (rightPoint n x) =
        rightPoint n ((halfMateFin q) x) := by
      exact (joinedMate_right x).trans (dif_neg hx)
    have hcut := (rightCut_eq_some_iff (fromPrefixes p q)
      x ((halfMateFin q) x)).2 hmate
    simpa [halfCut, hne, halfMateFin] using hcut

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem fromPrefixes_eq_of_cuts {n : ℕ} (M : UpperMatching n)
    (p q : TwoDownPrefix n)
    (hp : ∀ x, (leftCut M) x = (halfCut p) x)
    (hq : ∀ x, (rightCut M) x = (halfCut q) x) :
    fromPrefixes p q = M := by
  have hpoint (z : Fin (2 * n)) :
      z = leftPoint n (rainbowLabel n z) ∨
        z = rightPoint n (rainbowLabel n z) := by
    unfold rainbowLabel
    split_ifs
    · left; apply Fin.ext; rfl
    · right
      apply Fin.ext
      have := z.isLt
      simp [rightPoint, leftPoint]; omega
  have joinedMate_left (i : Fin n) : (joinedMate p) q (leftPoint n i) =
      if hi : i ∈ (unmatchedPositions p) then
        rightPoint n (((rankJoin p) q ⟨i, hi⟩).1)
      else leftPoint n ((halfMateFin p) i) := by
    simp [joinedMate, rainbowLabel, leftPoint]
  have joinedMate_right (j : Fin n) : (joinedMate p) q (rightPoint n j) =
      if hj : j ∈ (unmatchedPositions q) then
        leftPoint n (((rankJoin p) q).symm ⟨j, hj⟩).1
      else rightPoint n ((halfMateFin q) j) := by
    have hright : ¬ (rightPoint n j).val < n := by
      have hj := j.isLt
      have hv : (rightPoint n j).val = 2 * n - (j.val + 1) := by
        simp [rightPoint, leftPoint]
      omega
    have hlabel : rainbowLabel n (rightPoint n j) = j := by
      unfold rightPoint; rw [rainbowLabel_rev]
      simp [rainbowLabel, leftPoint]
    simp [joinedMate, hright, hlabel]
  have hmate (x : Fin (2 * n)) :
      (fromPrefixes p q).mate x = M.mate x := by
    rcases hpoint x with hx | hx
    · rw [hx]
      let i := rainbowLabel n x
      change (joinedMate p) q (leftPoint n i) = M.mate (leftPoint n i)
      by_cases hi : i ∈ (unmatchedPositions p)
      · have hnone : (leftCut M) i = none := by
          rw [hp i]
          exact (Finset.mem_filter.mp hi).2
        rw [joinedMate_left, dif_pos hi]
        exact crossing_eq_rankJoin M p q hp hq i hnone
      · have hne : (halfMate p) i.val ≠ i.val := by
          intro hfix
          apply hi
          exact ((halfMateFin_fixed_iff p) i).mp (Fin.ext hfix)
        have hcut : (halfCut p) i = some ((halfMateFin p) i) := by
          simp [halfCut, hne, halfMateFin]
        have hsource : M.mate (leftPoint n i) =
            leftPoint n ((halfMateFin p) i) := by
          exact (leftCut_eq_some_iff M i ((halfMateFin p) i)).1
            ((hp i).trans hcut)
        rw [joinedMate_left, dif_neg hi]
        exact hsource.symm
    · rw [hx]
      let j := rainbowLabel n x
      change (joinedMate p) q (rightPoint n j) = M.mate (rightPoint n j)
      by_cases hj : j ∈ (unmatchedPositions q)
      · let i : Fin n := (((rankJoin p) q).symm ⟨j, hj⟩).1
        have hi : i ∈ (unmatchedPositions p) :=
          (((rankJoin p) q).symm ⟨j, hj⟩).2
        have hnone : (leftCut M) i = none := by
          rw [hp i]
          exact (Finset.mem_filter.mp hi).2
        have hcross := crossing_eq_rankJoin M p q hp hq i hnone
        have hrank : ((rankJoin p) q ⟨i, hi⟩).1 = j := by
          exact congrArg Subtype.val
            (((rankJoin p) q).apply_symm_apply ⟨j, hj⟩)
        rw [hrank] at hcross
        have hback := congrArg M.mate hcross
        rw [M.mate_mate] at hback
        rw [joinedMate_right, dif_pos hj]
        exact hback.symm
      · have hne : (halfMate q) j.val ≠ j.val := by
          intro hfix
          apply hj
          exact ((halfMateFin_fixed_iff q) j).mp (Fin.ext hfix)
        have hcut : (halfCut q) j = some ((halfMateFin q) j) := by
          simp [halfCut, hne, halfMateFin]
        have hsource : M.mate (rightPoint n j) =
            rightPoint n ((halfMateFin q) j) := by
          exact (rightCut_eq_some_iff M j ((halfMateFin q) j)).1
            ((hq j).trans hcut)
        rw [joinedMate_right, dif_neg hj]
        exact hsource.symm
  cases M with
  | mk mate mate_mate mate_ne noncrossing =>
    cases h : fromPrefixes p q with
    | mk mate' mate_mate' mate_ne' noncrossing' =>
      have heq : mate' = mate := by
        funext x
        simpa only [h] using hmate x
      cases heq
      rfl

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def prefixPairWitness {n : ℕ}
    (M : UpperMatching n) (hn : 4 ≤ n) (hw : M.winding = n - 4) :
    {pq : TwoDownPrefix n × TwoDownPrefix n //
      (∀ x, (leftCut M) x = (halfCut pq.1) x) ∧
      (∀ x, (rightCut M) x = (halfCut pq.2) x)} := by
  classical
  let hleft : ∃ p : TwoDownPrefix n, ∀ x, (leftCut M) x = (halfCut p) x :=
    four_endpoint_twoDownPrefix
    (leftCut_paired_card_four M hn hw)
    (leftCut_symmetric M)
    (four_endpoint_adjacent_or_nested (leftCut_paired_card_four M hn hw)
      (leftCut_between_paired M) (leftCut_arch_span_le_three M hn hw)
      (leftCut_four_endpoint_pairing_shape M hn hw))
  let hright : ∃ q : TwoDownPrefix n, ∀ x, (rightCut M) x = (halfCut q) x :=
    four_endpoint_twoDownPrefix
    (rightCut_paired_card_four M hn hw)
    (rightCut_symmetric M)
    (four_endpoint_adjacent_or_nested (rightCut_paired_card_four M hn hw)
      (rightCut_between_paired M) (rightCut_arch_span_le_three M hn hw)
      (leftCut_four_endpoint_pairing_shape (reflected M) hn
        (by
          have hreflect : (reflected M).winding = M.winding := by
            calc
              (reflected M).winding =
                  (Finset.univ.filter fun x : Fin n =>
                    (leftCut (reflected M)) x = none).card :=
                winding_eq_leftCut_none_card (reflected M)
              _ = (Finset.univ.filter fun x : Fin n =>
                    (rightCut M) x = none).card := by rfl
              _ = M.winding := (winding_eq_rightCut_none_card M).symm
          rw [hreflect, hw])))
  exact ⟨(Classical.choose hleft, Classical.choose hright),
    Classical.choose_spec hleft, Classical.choose_spec hright⟩

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def sourcePrefixEquiv (n : ℕ) (hn : 4 ≤ n) :
    {M : UpperMatching n // M.winding = n - 4} ≃
      TwoDownPrefix n × TwoDownPrefix n :=
  {
    toFun M := ((prefixPairWitness M.1) hn M.2).1
    invFun pq := ⟨fromPrefixes pq.1 pq.2, by
      have hleft : (fromPrefixes pq.1 pq.2).winding =
          (Finset.univ.filter fun x : Fin n =>
            (leftCut (fromPrefixes pq.1 pq.2)) x = none).card := by
        exact winding_eq_leftCut_none_card (fromPrefixes pq.1 pq.2)
      rw [hleft]
      simpa [unmatchedPositions, fromPrefixes_leftCut] using
        (unmatchedPositions_card pq.1)⟩
    left_inv M := by
      exact Subtype.ext (fromPrefixes_eq_of_cuts M.1
        ((prefixPairWitness M.1) hn M.2).1.1
        ((prefixPairWitness M.1) hn M.2).1.2
        ((prefixPairWitness M.1) hn M.2).2.1
        ((prefixPairWitness M.1) hn M.2).2.2)
    right_inv pq := by
      have hw : (fromPrefixes pq.1 pq.2).winding = n - 4 := by
        have hleft : (fromPrefixes pq.1 pq.2).winding =
            (Finset.univ.filter fun x : Fin n =>
              (leftCut (fromPrefixes pq.1 pq.2)) x = none).card := by
          exact winding_eq_leftCut_none_card (fromPrefixes pq.1 pq.2)
        rw [hleft]
        simpa [unmatchedPositions, fromPrefixes_leftCut] using
          (unmatchedPositions_card pq.1)
      let w := (prefixPairWitness (fromPrefixes pq.1 pq.2))
        hn hw
      change w.1 = pq
      apply Prod.ext
      · exact halfCut_injective w.1.1 pq.1
          (fun x => (w.2.1 x).symm.trans (fromPrefixes_leftCut pq.1 pq.2 x))
      · exact halfCut_injective w.1.2 pq.2
          (fun x => (w.2.2 x).symm.trans (fromPrefixes_rightCut pq.1 pq.2 x))
  }

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def connectedSourcePrefixEquiv (n : ℕ) (hn : 4 ≤ n) :
    {M : {M : UpperMatching n // M.winding = n - 4} // M.1.oneLoop} ≃
      {pq : TwoDownPrefix n × TwoDownPrefix n //
        ∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge pq.1) pq.2) i j} :=
  (sourcePrefixEquiv n hn).subtypeEquiv (by
    intro M
    let w := (prefixPairWitness M.1) hn M.2
    let pq := w.1
    have hp : ∀ x, (leftCut M.1) x = (halfCut pq.1) x := w.2.1
    have hq : ∀ x, (rightCut M.1) x = (halfCut pq.2) x := w.2.2
    change M.1.oneLoop ↔ ∀ i j : Fin n,
      Relation.ReflTransGen ((joinedEdge pq.1) pq.2) i j
    rw [oneLoop_iff_contracted_connected]
    constructor
    · intro h i j
      exact (Relation.ReflTransGen.mono
        (fun a b hab =>
          (contractedEdge_iff_joinedEdge M.1 pq.1 pq.2 hp hq a b).1 hab)) i j
        (h i j)
    · intro h i j
      exact (Relation.ReflTransGen.mono
        (fun a b hab =>
          (contractedEdge_iff_joinedEdge M.1 pq.1 pq.2 hp hq a b).2 hab)) i j
        (h i j))

-- Extreme obstructions lead to the exhaustive A/B/C connectivity split.
set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem joinedEdge_fixed_isolated {n : ℕ}
    (p q : TwoDownPrefix n) (x : Fin n)
    (hp : x ∈ (unmatchedPositions p)) (hq : x ∈ (unmatchedPositions q))
    (hfix : ((rankJoin p) q ⟨x, hp⟩).1 = x)
    {y : Fin n} (hxy : (joinedEdge p) q x y) : y = x := by
  have hpnone : (halfCut p) x = none :=
    (Finset.mem_filter.mp hp).2
  have hqnone : (halfCut q) x = none :=
    (Finset.mem_filter.mp hq).2
  rcases hxy with hxy | hxy | ⟨_, hxy⟩ | ⟨hy, hxy⟩
  · rw [hpnone] at hxy
    cases hxy
  · rw [hqnone] at hxy
    cases hxy
  · exact hxy.symm.trans hfix
  · have heq : (⟨y, hy⟩ : (unmatchedPositions p)) = ⟨x, hp⟩ := by
      apply ((rankJoin p) q).injective
      apply Subtype.ext
      exact hxy.trans hfix.symm
    exact congrArg Subtype.val heq

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem not_connected_of_fixed_rankJoin {n : ℕ}
    (p q : TwoDownPrefix n) (x y : Fin n) (hxy : x ≠ y)
    (hp : x ∈ (unmatchedPositions p)) (hq : x ∈ (unmatchedPositions q))
    (hfix : ((rankJoin p) q ⟨x, hp⟩).1 = x) :
    ¬ (∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge p) q) i j) := by
  intro hconn
  have hstay : ∀ z : Fin n,
      Relation.ReflTransGen ((joinedEdge p) q) x z → z = x := by
    intro z hpath
    have preserved : x = x → z = x :=
      Relation.ReflTransGen.head_induction_on
        (motive := fun a _ => a = x → z = x) hpath
        (fun ha => ha)
        (fun hab _ ih ha => by
          cases ha
          exact ih ((joinedEdge_fixed_isolated p) q x hp hq hfix hab))
    exact preserved rfl
  exact hxy (hstay y (hconn x y)).symm

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem rankJoin_least_fixed {n : ℕ}
    (p q : TwoDownPrefix n) (x : Fin n)
    (hp : x ∈ (unmatchedPositions p)) (hq : x ∈ (unmatchedPositions q))
    (hpmin : ∀ y : (unmatchedPositions p), x ≤ y.1)
    (hqmin : ∀ y : (unmatchedPositions q), x ≤ y.1) :
    ((rankJoin p) q ⟨x, hp⟩).1 = x := by
  let xp : (unmatchedPositions p) := ⟨x, hp⟩
  let xq : (unmatchedPositions q) := ⟨x, hq⟩
  obtain ⟨z, hz⟩ := ((rankJoin p) q).surjective xq
  have hle : ((rankJoin p) q) xp ≤ xq := by
    rw [← hz]
    exact ((rankJoin p) q).monotone (hpmin z)
  have hge : xq ≤ ((rankJoin p) q) xp := hqmin _
  exact congrArg Subtype.val (le_antisymm hle hge)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem rankJoin_greatest_fixed {n : ℕ}
    (p q : TwoDownPrefix n) (x : Fin n)
    (hp : x ∈ (unmatchedPositions p)) (hq : x ∈ (unmatchedPositions q))
    (hpmax : ∀ y : (unmatchedPositions p), y.1 ≤ x)
    (hqmax : ∀ y : (unmatchedPositions q), y.1 ≤ x) :
    ((rankJoin p) q ⟨x, hp⟩).1 = x := by
  let xp : (unmatchedPositions p) := ⟨x, hp⟩
  let xq : (unmatchedPositions q) := ⟨x, hq⟩
  obtain ⟨z, hz⟩ := ((rankJoin p) q).surjective xq
  have hle : ((rankJoin p) q) xp ≤ xq := hqmax _
  have hge : xq ≤ ((rankJoin p) q) xp := by
    rw [← hz]
    exact ((rankJoin p) q).monotone (hpmax z)
  exact congrArg Subtype.val (le_antisymm hle hge)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem connected_extremes_paired {n : ℕ}
    (p q : TwoDownPrefix n) (hn : 4 ≤ n)
    (hconn : ∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge p) q) i j) :
    ¬ (⟨0, by omega⟩ ∈ (unmatchedPositions p) ∧
       ⟨0, by omega⟩ ∈ (unmatchedPositions q)) ∧
    ¬ (⟨n - 1, by omega⟩ ∈ (unmatchedPositions p) ∧
       ⟨n - 1, by omega⟩ ∈ (unmatchedPositions q)) := by
  constructor
  · rintro ⟨hp, hq⟩
    let x : Fin n := ⟨0, by omega⟩
    let y : Fin n := ⟨1, by omega⟩
    have hfix : ((rankJoin p) q ⟨x, hp⟩).1 = x :=
      (rankJoin_least_fixed p) q x hp hq
        (fun z => by change 0 ≤ z.1.val; omega)
        (fun z => by change 0 ≤ z.1.val; omega)
    exact ((not_connected_of_fixed_rankJoin p) q x y
      (by intro h; have := congrArg Fin.val h; dsimp [x, y] at this; omega)
      hp hq hfix) hconn
  · rintro ⟨hp, hq⟩
    let x : Fin n := ⟨n - 1, by omega⟩
    let y : Fin n := ⟨0, by omega⟩
    have hfix : ((rankJoin p) q ⟨x, hp⟩).1 = x :=
      (rankJoin_greatest_fixed p) q x hp hq
        (fun z => by change z.1.val ≤ n - 1; have := z.1.isLt; omega)
        (fun z => by change z.1.val ≤ n - 1; have := z.1.isLt; omega)
    exact ((not_connected_of_fixed_rankJoin p) q x y
      (by intro h; have := congrArg Fin.val h; dsimp [x, y] at this; omega)
      hp hq hfix) hconn

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem connected_endpoint_cases {n : ℕ}
    (p q : TwoDownPrefix n) (hn : 4 ≤ n)
    (hconn : ∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge p) q) i j) :
    (p.val.1 = 1 ∨ (p.val.1 = 2 ∧ p.val.2 = 3) ∨
      q.val.1 = 1 ∨ (q.val.1 = 2 ∧ q.val.2 = 3)) ∧
    (p.val.2 = n - 1 ∨ q.val.2 = n - 1) := by
  obtain ⟨hzero, hlast⟩ := (connected_extremes_paired p) q hn hconn
  have hzero_iff (r : TwoDownPrefix n) :
      (⟨0, by have := r.property.2.2.2; omega⟩ : Fin n) ∈ (unmatchedPositions r) ↔
        r.val.1 ≠ 1 ∧ ¬ (r.val.1 = 2 ∧ r.val.2 = 3) := by
    simp only [unmatchedPositions, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [(halfCut_eq_none_iff r)]
    dsimp
    unfold secondOpen
    split_ifs with h
    · have := r.property.1
      have := r.property.2.1
      omega
    · have := r.property.1
      have := r.property.2.1
      have := r.property.2.2.1
      omega
  have hlast_iff (r : TwoDownPrefix n) :
      (⟨n - 1, by have := r.property.2.2.2; omega⟩ : Fin n) ∈
        (unmatchedPositions r) ↔ r.val.2 ≠ n - 1 := by
    simp only [unmatchedPositions, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [(halfCut_eq_none_iff r)]
    dsimp
    unfold secondOpen
    split_ifs with h <;>
      have := r.property.1 <;>
      have := r.property.2.2.1 <;>
      have := r.property.2.2.2 <;>
      omega
  constructor
  · by_contra h
    have hpq : (p.val.1 ≠ 1 ∧ ¬ (p.val.1 = 2 ∧ p.val.2 = 3)) ∧
        (q.val.1 ≠ 1 ∧ ¬ (q.val.1 = 2 ∧ q.val.2 = 3)) := by tauto
    exact hzero ⟨(hzero_iff p).2 hpq.1,
      (hzero_iff q).2 hpq.2⟩
  · by_contra h
    have hpq : p.val.2 ≠ n - 1 ∧ q.val.2 ≠ n - 1 := by tauto
    exact hlast ⟨(hlast_iff p).2 hpq.1,
      (hlast_iff q).2 hpq.2⟩

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem rankJoin_B_closed_bound {n : ℕ} (p q : TwoDownPrefix n)
    (hp1 : p.val.1 = 1)
    (hsep : q.val.1 + 2 ≤ q.val.2)
    (i : Fin n) (hi : i.val ≤ q.val.1)
    (hpi : i ∈ (unmatchedPositions p)) :
    ((rankJoin p) q ⟨i, hpi⟩).1.val ≤ q.val.1 := by
  have hqfirst : 1 ≤ q.val.1 := q.property.1
  have hqsecond : q.val.2 < n := q.property.2.2.2
  have hpi_none : (halfCut p) i = none := (Finset.mem_filter.mp hpi).2
  have hpnone := ((halfCut_eq_none_iff p) i).1 hpi_none
  have hi2 : 2 ≤ i.val := by
    rw [hp1] at hpnone
    omega
  by_contra hgt'
  have hgt : q.val.1 < ((rankJoin p) q ⟨i, hpi⟩).1.val := by omega
  have hc2 : 2 ≤ q.val.1 := by omega
  let c : ℕ := q.val.1
  let y : (unmatchedPositions q) := (rankJoin p) q ⟨i, hpi⟩
  let f : Fin (c - 1) → Fin (c - 2) := fun k => by
    let qk : (unmatchedPositions q) := ⟨⟨k.val, by have := k.isLt; omega⟩, by
      simp only [unmatchedPositions, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [(halfCut_eq_none_iff q)]
      unfold secondOpen
      split_ifs <;> have hk := k.isLt <;> dsimp [c] at hk ⊢ <;> omega⟩
    let z : (unmatchedPositions p) := ((rankJoin p) q).symm qk
    have hzlt : z.1.val < i.val := by
      have hzorder : z < (⟨i, hpi⟩ : (unmatchedPositions p)) := by
        apply ((rankJoin p) q).lt_iff_lt.mp
        have hqk : qk.1.val < y.1.val := by
          dsimp [qk, y, c]
          have hk := k.isLt
          omega
        have hmap : ((rankJoin p) q) z <
            ((rankJoin p) q) (⟨i, hpi⟩ : (unmatchedPositions p)) := by
          simpa [z, y] using hqk
        exact hmap
      change z.1.val < i.val at hzorder
      exact hzorder
    have hz2 : 2 ≤ z.1.val := by
      have hznone : (halfCut p) z.1 = none := (Finset.mem_filter.mp z.2).2
      have hzp := ((halfCut_eq_none_iff p) z.1).1 hznone
      rw [hp1] at hzp
      omega
    exact ⟨z.1.val - 2, by dsimp [c]; omega⟩
  have hf : Function.Injective f := by
    intro k₁ k₂ heq
    dsimp [f] at heq
    let q₁ : (unmatchedPositions q) := ⟨⟨k₁.val, by have := k₁.isLt; omega⟩, by
      simp only [unmatchedPositions, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [(halfCut_eq_none_iff q)]
      unfold secondOpen
      split_ifs <;> have hk := k₁.isLt <;> dsimp [c] at hk ⊢ <;> omega⟩
    let q₂ : (unmatchedPositions q) := ⟨⟨k₂.val, by have := k₂.isLt; omega⟩, by
      simp only [unmatchedPositions, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [(halfCut_eq_none_iff q)]
      unfold secondOpen
      split_ifs <;> have hk := k₂.isLt <;> dsimp [c] at hk ⊢ <;> omega⟩
    let z₁ : (unmatchedPositions p) := ((rankJoin p) q).symm q₁
    let z₂ : (unmatchedPositions p) := ((rankJoin p) q).symm q₂
    have hz₁2 : 2 ≤ z₁.1.val := by
      have hznone := ((halfCut_eq_none_iff p) z₁.1).1 (Finset.mem_filter.mp z₁.2).2
      rw [hp1] at hznone
      omega
    have hz₂2 : 2 ≤ z₂.1.val := by
      have hznone := ((halfCut_eq_none_iff p) z₂.1).1 (Finset.mem_filter.mp z₂.2).2
      rw [hp1] at hznone
      omega
    have hz₁eq₂ : z₁.1.val = z₂.1.val := by
      have hv := congrArg Fin.val heq
      dsimp [z₁, z₂, q₁, q₂] at hv
      have hv' : z₁.1.val - 2 = z₂.1.val - 2 := by
        simpa [z₁, z₂, q₁, q₂] using hv
      omega
    have hq₁eq₂ : q₁ = q₂ := by
      have hz : z₁ = z₂ := by
        apply Subtype.ext
        exact Fin.ext hz₁eq₂
      apply ((rankJoin p) q).symm.injective
      simpa [z₁, z₂] using hz
    have hk : k₁.val = k₂.val := by
      have hv : q₁.1 = q₂.1 := congrArg Subtype.val hq₁eq₂
      have hv' := congrArg Fin.val hv
      dsimp [q₁, q₂] at hv'
      exact hv'
    exact Fin.ext hk
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hcard
  omega

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem p_edge_B_closed {n : ℕ} (p q : TwoDownPrefix n)
    (hp1 : p.val.1 = 1) (hp2 : p.val.2 = n - 1)
    (hsep : q.val.1 + 2 ≤ q.val.2)
    (i : Fin n) (hi : i.val ≤ q.val.1) {j : Fin n}
    (hcut : (halfCut p) i = some j) : j.val ≤ q.val.1 := by
  have hqfirst : 1 ≤ q.val.1 := q.property.1
  have hqbound : q.val.1 + 2 ≤ n - 1 := by
    have hqd := q.property.2.2.2
    omega
  unfold halfCut at hcut
  by_cases hfix : (halfMate p) i.val = i.val
  · simp [hfix] at hcut
  · have hcut' : some (⟨(halfMate p) i.val, (halfMate_lt p) i⟩ : Fin n) = some j := by
      simpa [hfix] using hcut
    have hv : (halfMate p) i.val = j.val := by
      have := Option.some.inj hcut'
      exact congrArg Fin.val this
    unfold halfMate secondOpen at hv
    split_ifs at hv <;> omega

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem q_edge_B_closed {n : ℕ} (q : TwoDownPrefix n)
    (hsep : q.val.1 + 2 ≤ q.val.2)
    (i : Fin n) (hi : i.val ≤ q.val.1) {j : Fin n}
    (hcut : (halfCut q) i = some j) : j.val ≤ q.val.1 := by
  unfold halfCut at hcut
  by_cases hfix : (halfMate q) i.val = i.val
  · simp [hfix] at hcut
  · have hcut' : some (⟨(halfMate q) i.val, (halfMate_lt q) i⟩ : Fin n) = some j := by
      simpa [hfix] using hcut
    have hv : (halfMate q) i.val = j.val := by
      have := Option.some.inj hcut'
      exact congrArg Fin.val this
    unfold halfMate secondOpen at hv
    split_ifs at hv <;> omega

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem rankJoin_B_preimage_closed {n : ℕ}
    (p q : TwoDownPrefix n) (hn : 5 ≤ n)
    (hp1 : p.val.1 = 1) (hp2 : p.val.2 = n - 1)
    (hsep : q.val.1 + 2 ≤ q.val.2)
    (i : Fin n) (hi : i.val ≤ q.val.1)
    (hqi : i ∈ (unmatchedPositions q))
    (j : Fin n) (hpj : j ∈ (unmatchedPositions p))
    (hr : ((rankJoin p) q ⟨j, hpj⟩).1 = i) :
    j.val ≤ q.val.1 := by
  have hqnone : (halfCut q) i = none := (Finset.mem_filter.mp hqi).2
  have hqparams := ((halfCut_eq_none_iff q) i).1 hqnone
  have hqfirst : 1 ≤ q.val.1 := q.property.1
  have hqsub : q.val.1 - 1 + 1 = q.val.1 := Nat.sub_add_cancel hqfirst
  have hi2 : i.val ≤ q.val.1 - 2 := by
    have hqfirst' : 2 ≤ q.val.1 := by
      by_contra hc
      have : q.val.1 = 1 := by omega
      omega
    have hqfirst2sub : q.val.1 - 2 + 2 = q.val.1 := Nat.sub_add_cancel hqfirst'
    have hne1 := hqparams.1
    have hne2 := hqparams.2
    omega
  by_contra hgt'
  have hgt : q.val.1 < j.val := by omega
  have hc2 : 2 ≤ q.val.1 := by omega
  have hqbound : q.val.1 + 2 ≤ n - 1 := by
    have hqd := q.property.2.2.2
    omega
  let c : ℕ := q.val.1
  let g : Fin (c - 1) → Fin (c - 2) := fun k => by
    let x : Fin n := ⟨k.val + 2, by have := k.isLt; dsimp [c]; omega⟩
    have hxnone : (halfCut p) x = none := by
      rw [(halfCut_eq_none_iff p)]
      unfold secondOpen
      split_ifs <;>
        have hk := k.isLt <;> dsimp [x, c] at hk ⊢ <;> omega
    have hxi : x ∈ (unmatchedPositions p) := by
      simp only [unmatchedPositions, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hxnone
    have hxlt : ((rankJoin p) q ⟨x, hxi⟩).1.val < i.val := by
      have horder : ((rankJoin p) q ⟨x, hxi⟩) <
          ((rankJoin p) q ⟨j, hpj⟩) := by
        apply ((rankJoin p) q).strictMono
        change x.val < j.val
        dsimp [x, c]
        have hk := k.isLt
        omega
      change ((rankJoin p) q ⟨x, hxi⟩).1.val <
        ((rankJoin p) q ⟨j, hpj⟩).1.val at horder
      rw [hr] at horder
      exact horder
    exact ⟨((rankJoin p) q ⟨x, hxi⟩).1.val, by
      dsimp [c]
      omega⟩
  have hg : Function.Injective g := by
    intro k₁ k₂ heq
    dsimp [g] at heq
    let x₁ : Fin n := ⟨k₁.val + 2, by have := k₁.isLt; dsimp [c]; omega⟩
    let x₂ : Fin n := ⟨k₂.val + 2, by have := k₂.isLt; dsimp [c]; omega⟩
    have hx₁none : (halfCut p) x₁ = none := by
      rw [(halfCut_eq_none_iff p)]
      unfold secondOpen
      split_ifs <;>
        have hk := k₁.isLt <;> dsimp [x₁, c] at hk ⊢ <;> omega
    have hx₂none : (halfCut p) x₂ = none := by
      rw [(halfCut_eq_none_iff p)]
      unfold secondOpen
      split_ifs <;>
        have hk := k₂.isLt <;> dsimp [x₂, c] at hk ⊢ <;> omega
    have hxi₁ : x₁ ∈ (unmatchedPositions p) := by
      simp only [unmatchedPositions, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hx₁none
    have hxi₂ : x₂ ∈ (unmatchedPositions p) := by
      simp only [unmatchedPositions, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hx₂none
    have hR : ((rankJoin p) q ⟨x₁, hxi₁⟩).1 =
        ((rankJoin p) q ⟨x₂, hxi₂⟩).1 := by
      apply Fin.ext
      simpa [x₁, x₂] using congrArg Fin.val heq
    have hx : x₁ = x₂ := by
      have hz : (⟨x₁, hxi₁⟩ : (unmatchedPositions p)) =
          ⟨x₂, hxi₂⟩ := ((rankJoin p) q).injective (by simpa using hR)
      have hz' := congrArg Subtype.val hz
      exact hz'
    apply Fin.ext
    have hxv := congrArg Fin.val hx
    dsimp [x₁, x₂] at hxv
    omega
  have hcard := Fintype.card_le_of_injective g hg
  simp only [Fintype.card_fin] at hcard
  omega

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem not_connected_of_B_separated {n : ℕ}
    (p q : TwoDownPrefix n) (hn : 5 ≤ n)
    (hp1 : p.val.1 = 1) (hp2 : p.val.2 = n - 1)
    (hsep : q.val.1 + 2 ≤ q.val.2) :
    ¬ (∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge p) q) i j) := by
  have hqbound : q.val.1 + 2 ≤ n - 1 := by
    have hqd := q.property.2.2.2
    omega
  let xout : Fin n := ⟨q.val.1 + 1, by omega⟩
  have hclosed : ∀ (i j : Fin n), i.val ≤ q.val.1 →
      (joinedEdge p) q i j → j.val ≤ q.val.1 := by
    intro i j hi hxy
    rcases hxy with hxy | hxy | ⟨hiP, hxy⟩ | ⟨hjP, hxy⟩
    · exact (p_edge_B_closed p) q hp1 hp2 hsep i hi hxy
    · exact (q_edge_B_closed q) hsep i hi hxy
    · rw [← hxy]
      exact (rankJoin_B_closed_bound p) q hp1 hsep i hi hiP
    · have hiQ : i ∈ (unmatchedPositions q) := by
        rw [← hxy]
        exact ((rankJoin p) q ⟨j, hjP⟩).2
      exact (rankJoin_B_preimage_closed p) q hn hp1 hp2 hsep i hi hiQ j hjP hxy
  intro hconn
  have hpath := hconn (⟨0, by omega⟩ : Fin n) xout
  have hstay : ∀ z : Fin n,
      Relation.ReflTransGen ((joinedEdge p) q) (⟨0, by omega⟩ : Fin n) z →
        z.val ≤ q.val.1 := by
    intro z hpath'
    have hbound : (⟨0, by omega⟩ : Fin n).val ≤ q.val.1 → z.val ≤ q.val.1 :=
      Relation.ReflTransGen.head_induction_on
        (motive := fun a _ => a.val ≤ q.val.1 → z.val ≤ q.val.1) hpath'
        (fun ha => ha)
        (fun hab _ ih ha => ih (hclosed _ _ ha hab))
    have hzero : (⟨0, by omega⟩ : Fin n).val ≤ q.val.1 := by
      change 0 ≤ q.val.1
      omega
    exact hbound hzero
  have hout := hstay xout hpath
  dsimp [xout] at hout
  omega

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem rankJoin_B_consecutive {n : ℕ}
    (p q : TwoDownPrefix n) (hp1 : p.val.1 = 1) (hp2 : p.val.2 = n - 1)
    (hc : 2 ≤ q.val.1) (hq : q.val.2 = q.val.1 + 1)
    (x : (unmatchedPositions p)) :
    ((rankJoin p) q x).1.val =
      if x.1.val < q.val.1 then x.1.val - 2 else x.1.val + 2 := by
  have hpu (i : Fin n) :
      i ∈ (unmatchedPositions p) ↔ 2 ≤ i.val ∧ i.val ≤ n - 3 := by
    simp only [unmatchedPositions, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [(halfCut_eq_none_iff p)]
    unfold secondOpen
    split_ifs <;>
      have := i.isLt <;> have := p.property.2.1 <;> omega
  have hqu (i : Fin n) : i ∈ (unmatchedPositions q) ↔
      i.val < q.val.1 - 2 ∨ q.val.1 + 1 < i.val := by
    simp only [unmatchedPositions, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [(halfCut_eq_none_iff q)]
    simp only [secondOpen, hq, ↓reduceIte]
    omega
  let f : (unmatchedPositions p) → (unmatchedPositions q) := fun x =>
    ⟨⟨if x.1.val < q.val.1 then x.1.val - 2 else x.1.val + 2, by
      have hx := (hpu x.1).1 x.2
      have hqbound := q.property.2.2.2
      split_ifs <;> omega⟩, by
      rw [hqu]
      have hx := (hpu x.1).1 x.2
      change (if x.1.val < q.val.1 then x.1.val - 2 else x.1.val + 2) <
        q.val.1 - 2 ∨ q.val.1 + 1 <
          (if x.1.val < q.val.1 then x.1.val - 2 else x.1.val + 2)
      split_ifs <;> omega⟩
  have hf : StrictMono f := by
    intro x y hxy
    change x.1.val < y.1.val at hxy
    change (if x.1.val < q.val.1 then x.1.val - 2 else x.1.val + 2) <
      (if y.1.val < q.val.1 then y.1.val - 2 else y.1.val + 2)
    have hx := (hpu x.1).1 x.2
    have hy := (hpu y.1).1 y.2
    split_ifs <;> omega
  have hs : Function.Surjective f := by
    intro y
    have hy := (hqu y.1).1 y.2
    by_cases hfront : y.1.val < q.val.1 - 2
    · let x : Fin n := ⟨y.1.val + 2, by
        have := q.property.2.2.2
        omega⟩
      have hx : x ∈ (unmatchedPositions p) :=
        (hpu x).2 (by
          dsimp [x]
          have := q.property.2.2.2
          omega)
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      apply Fin.ext
      change (if x.val < q.val.1 then x.val - 2 else x.val + 2) = y.1.val
      dsimp [x]
      split_ifs <;> omega
    · have hback : q.val.1 + 1 < y.1.val := hy.resolve_left hfront
      let x : Fin n := ⟨y.1.val - 2, by have := y.1.isLt; omega⟩
      have hx : x ∈ (unmatchedPositions p) :=
        (hpu x).2 (by
          dsimp [x]
          have := y.1.isLt
          have := q.property.2.2.2
          omega)
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      apply Fin.ext
      change (if x.val < q.val.1 then x.val - 2 else x.val + 2) = y.1.val
      dsimp [x]
      split_ifs <;> omega
  let e : (unmatchedPositions p) ≃o (unmatchedPositions q) :=
    hf.orderIsoOfSurjective f hs
  have he : e = (rankJoin p) q := by
    have hid := StrictMono.eq_id (e.trans ((rankJoin p) q).symm).strictMono
    apply OrderIso.ext
    apply funext
    intro z
    have hz := congrArg ((rankJoin p) q) (congrFun hid z)
    simpa [OrderIso.trans_apply] using hz
  have hfx : (e x).1.val =
      if x.1.val < q.val.1 then x.1.val - 2 else x.1.val + 2 := by
    change (f x).1.val = _
    rfl
  rwa [he] at hfx

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem halfCut_symmetric {n : ℕ}
    (p : TwoDownPrefix n) (i j : Fin n)
    (hij : (halfCut p) i = some j) : (halfCut p) j = some i := by
  unfold halfCut at hij ⊢
  by_cases hi : (halfMate p) i.val = i.val
  · simp [hi] at hij
  · have hjval : j.val = (halfMate p) i.val := by
      have h : (⟨(halfMate p) i.val, (halfMate_lt p) i⟩ : Fin n) = j := by
        simpa [hi] using hij
      exact congrArg Fin.val h |>.symm
    have hj : (halfMate p) j.val ≠ j.val := by
      rw [hjval, (halfMate_involutive p)]
      exact Ne.symm hi
    simp only [if_neg hj]
    congr 1
    apply Fin.ext
    change (halfMate p) j.val = i.val
    rw [hjval, (halfMate_involutive p)]


end D5.S3.Combinatorics.SemiMeanderSecondDiagonal
