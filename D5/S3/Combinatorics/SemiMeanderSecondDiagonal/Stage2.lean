/- GID: D5/S3/Combinatorics/SemiMeanderSecondDiagonal/Stage2
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SemiMeanderSecondDiagonal/Stage2
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Two-down-prefix pairings and the rank-joined involution. -/

import D5.S3.Combinatorics.SemiMeanderSecondDiagonal.Stage1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SemiMeanderSecondDiagonal

open Classical

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem halfMate_lt {n : ℕ} (p : TwoDownPrefix n)
    (x : Fin n) : (halfMate p) x.val < n := by
  have hf : p.val.1 < n := lt_trans p.property.2.2.1 p.property.2.2.2
  have hp : p.val.1 - 1 < n := lt_of_le_of_lt (Nat.sub_le _ _) hf
  have hs : (secondOpen p) < n := by
    unfold secondOpen
    split_ifs
    · exact lt_of_le_of_lt (Nat.sub_le _ _) hf
    · exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) p.property.2.2.2
  have hsecond := p.property.2.2.2
  unfold halfMate
  split_ifs <;> have := x.isLt <;> omega

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def halfCut {n : ℕ} (p : TwoDownPrefix n)
    (x : Fin n) : Option (Fin n) :=
  if (halfMate p) x.val = x.val then none
  else some ⟨(halfMate p) x.val, (halfMate_lt p) x⟩

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem halfCut_eq_none_iff {n : ℕ} (p : TwoDownPrefix n)
    (x : Fin n) : (halfCut p) x = none ↔
      x.val ≠ p.val.1 - 1 ∧ x.val ≠ p.val.1 ∧
      x.val ≠ (secondOpen p) ∧ x.val ≠ p.val.2 := by
  unfold halfCut
  split_ifs with h
  · exact ⟨fun _ => ((halfMate_fixed_iff p) x.val).mp h, fun _ => rfl⟩
  · simp only [false_iff]
    exact fun hx => h (((halfMate_fixed_iff p) x.val).mpr hx)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem halfCut_first_pair {n : ℕ} (p : TwoDownPrefix n) :
    (halfCut p) ⟨p.val.1 - 1, by
      exact lt_of_le_of_lt (Nat.sub_le _ _)
        (lt_trans p.property.2.2.1 p.property.2.2.2)⟩ =
      some ⟨p.val.1, by have := p.property.2.2.1; have := p.property.2.2.2; omega⟩ := by
  have hd := twoDown_endpoints_distinct p
  simp [halfCut, halfMate, hd.1.symm]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem halfCut_second_pair {n : ℕ} (p : TwoDownPrefix n) :
    (halfCut p) ⟨(secondOpen p), by
      unfold secondOpen
      split_ifs
      · exact lt_of_le_of_lt (Nat.sub_le _ _)
          (lt_trans p.property.2.2.1 p.property.2.2.2)
      · exact lt_of_le_of_lt (Nat.sub_le _ _) p.property.2.2.2⟩ =
      some ⟨p.val.2, p.property.2.2.2⟩ := by
  have hd := twoDown_endpoints_distinct p
  simp [halfCut, halfMate,
    hd.2.1.symm, hd.2.2.2.1.symm, hd.2.2.2.2.2.symm]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem halfCut_first_reverse {n : ℕ} (p : TwoDownPrefix n) :
    (halfCut p) ⟨p.val.1, lt_trans p.property.2.2.1 p.property.2.2.2⟩ =
      some ⟨p.val.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _)
        (lt_trans p.property.2.2.1 p.property.2.2.2)⟩ := by
  have hd := twoDown_endpoints_distinct p
  simp [halfCut, halfMate,
    hd.1, hd.1.symm]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem halfCut_second_reverse {n : ℕ} (p : TwoDownPrefix n) :
    (halfCut p) ⟨p.val.2, p.property.2.2.2⟩ =
      some ⟨(secondOpen p), by
        unfold secondOpen
        split_ifs
        · exact lt_of_le_of_lt (Nat.sub_le _ _)
            (lt_trans p.property.2.2.1 p.property.2.2.2)
        · exact lt_of_le_of_lt (Nat.sub_le _ _) p.property.2.2.2⟩ := by
  have hd := twoDown_endpoints_distinct p
  simp [halfCut, halfMate,
    hd.2.2.1.symm, hd.2.2.2.2.1.symm,
    hd.2.2.2.2.2, hd.2.2.2.2.2.symm]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem four_endpoint_cut_eq_halfCut
    {n : ℕ} {cut : Fin n → Option (Fin n)}
    (hcard : (Finset.univ.filter (fun x => cut x ≠ none)).card = 4)
    (p : TwoDownPrefix n)
    (hpositions : let S := Finset.univ.filter (fun x => cut x ≠ none)
      let e : Fin 4 → Fin n := S.orderEmbOfFin hcard
      ∀ x : Fin n, (halfCut p) x ≠ none → ∃ i : Fin 4, e i = x)
    (hpoints : let S := Finset.univ.filter (fun x => cut x ≠ none)
      let e : Fin 4 → Fin n := S.orderEmbOfFin hcard
      ∀ i : Fin 4, cut (e i) = (halfCut p) (e i)) :
    ∀ x, cut x = (halfCut p) x := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun x => cut x ≠ none)
  let e : Fin 4 → Fin n := S.orderEmbOfFin hcard
  change ∀ x, (halfCut p) x ≠ none → ∃ i : Fin 4, e i = x at hpositions
  change ∀ i : Fin 4, cut (e i) = (halfCut p) (e i) at hpoints
  have himage : Finset.image e Finset.univ = S := by
    dsimp [e]
    exact Finset.image_orderEmbOfFin_univ S hcard
  intro x
  by_cases hx : ∃ i : Fin 4, e i = x
  · obtain ⟨i, rfl⟩ := hx
    exact hpoints i
  · have hcut : cut x = none := by
      by_contra hn
      have hmem : x ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
      rw [← himage] at hmem
      rcases Finset.mem_image.mp hmem with ⟨i, -, hi⟩
      exact hx ⟨i, hi⟩
    have hp : (halfCut p) x = none := by
      by_contra hn
      exact hx (hpositions x hn)
    rw [hcut, hp]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem four_endpoint_twoDownPrefix
    {n : ℕ} {cut : Fin n → Option (Fin n)}
    (hcard : (Finset.univ.filter (fun x => cut x ≠ none)).card = 4)
    (hsym : ∀ x y, cut x = some y → cut y = some x)
    (hadj : let S := Finset.univ.filter (fun x => cut x ≠ none)
      let e : Fin 4 → Fin n := S.orderEmbOfFin hcard
      ((cut (e 0) = some (e 1) ∧ cut (e 2) = some (e 3)) ∧
        (e 1).val = (e 0).val + 1 ∧ (e 3).val = (e 2).val + 1) ∨
      ((cut (e 0) = some (e 3) ∧ cut (e 1) = some (e 2)) ∧
        (e 1).val = (e 0).val + 1 ∧ (e 2).val = (e 0).val + 2 ∧
        (e 3).val = (e 0).val + 3)) :
    ∃ p : TwoDownPrefix n, ∀ x, cut x = (halfCut p) x := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun x => cut x ≠ none)
  let e : Fin 4 → Fin n := S.orderEmbOfFin hcard
  change ((cut (e 0) = some (e 1) ∧ cut (e 2) = some (e 3)) ∧
      (e 1).val = (e 0).val + 1 ∧ (e 3).val = (e 2).val + 1) ∨
    ((cut (e 0) = some (e 3) ∧ cut (e 1) = some (e 2)) ∧
      (e 1).val = (e 0).val + 1 ∧ (e 2).val = (e 0).val + 2 ∧
      (e 3).val = (e 0).val + 3) at hadj
  have he_lt {i j : Fin 4} (hij : i < j) : (e i).val < (e j).val := by
    have h := (S.orderIsoOfFin hcard).strictMono hij
    simpa [e] using h
  have h01 : (e 0).val < (e 1).val := he_lt (by omega)
  have h12 : (e 1).val < (e 2).val := he_lt (by omega)
  have h23 : (e 2).val < (e 3).val := he_lt (by omega)
  rcases hadj with ⟨⟨hc01, hc23⟩, ha01, ha23⟩ |
      ⟨⟨hc03, hc12⟩, ha01, ha02, ha03⟩
  · let p : TwoDownPrefix n :=
      ⟨((e 1).val, (e 3).val), ⟨by omega, by omega, by omega, (e 3).isLt⟩⟩
    have hso : (secondOpen p) = (e 2).val := by
      dsimp [p, secondOpen]
      split_ifs <;> omega
    have hv0 : (e 0).val = p.val.1 - 1 := by dsimp [p]; omega
    have hv1 : (e 1).val = p.val.1 := rfl
    have hv2 : (e 2).val = (secondOpen p) := hso.symm
    have hv3 : (e 3).val = p.val.2 := rfl
    have hp01 : (halfCut p) (e 0) = some (e 1) := by
      have he0 : e 0 = (⟨p.val.1 - 1, by
          exact lt_of_le_of_lt (Nat.sub_le _ _)
            (lt_trans p.property.2.2.1 p.property.2.2.2)⟩ : Fin n) := Fin.ext hv0
      have he1 : e 1 = (⟨p.val.1, lt_trans p.property.2.2.1 p.property.2.2.2⟩ : Fin n) :=
        Fin.ext hv1
      rw [he0, he1]
      exact (halfCut_first_pair p)
    have hp10 : (halfCut p) (e 1) = some (e 0) := by
      have he0 : e 0 = (⟨p.val.1 - 1, by
          exact lt_of_le_of_lt (Nat.sub_le _ _)
            (lt_trans p.property.2.2.1 p.property.2.2.2)⟩ : Fin n) := Fin.ext hv0
      have he1 : e 1 = (⟨p.val.1, lt_trans p.property.2.2.1 p.property.2.2.2⟩ : Fin n) :=
        Fin.ext hv1
      rw [he0, he1]
      exact (halfCut_first_reverse p)
    have hp23 : (halfCut p) (e 2) = some (e 3) := by
      have he2 : e 2 = (⟨(secondOpen p), by rw [hso]; exact (e 2).isLt⟩ : Fin n) :=
        Fin.ext hv2
      have he3 : e 3 = (⟨p.val.2, p.property.2.2.2⟩ : Fin n) := Fin.ext hv3
      rw [he2, he3]
      exact (halfCut_second_pair p)
    have hp32 : (halfCut p) (e 3) = some (e 2) := by
      have he2 : e 2 = (⟨(secondOpen p), by rw [hso]; exact (e 2).isLt⟩ : Fin n) :=
        Fin.ext hv2
      have he3 : e 3 = (⟨p.val.2, p.property.2.2.2⟩ : Fin n) := Fin.ext hv3
      rw [he2, he3]
      exact (halfCut_second_reverse p)
    refine ⟨p, four_endpoint_cut_eq_halfCut hcard p ?_ ?_⟩
    · change ∀ x : Fin n, (halfCut p) x ≠ none → ∃ i : Fin 4, e i = x
      intro x hx
      have hv : x.val = p.val.1 - 1 ∨ x.val = p.val.1 ∨
          x.val = (secondOpen p) ∨ x.val = p.val.2 := by
        by_contra hn
        have hfix : x.val ≠ p.val.1 - 1 ∧ x.val ≠ p.val.1 ∧
            x.val ≠ (secondOpen p) ∧ x.val ≠ p.val.2 := by tauto
        exact hx (((halfCut_eq_none_iff p) x).2 hfix)
      rcases hv with h | h | h | h
      · exact ⟨0, Fin.ext (by omega)⟩
      · exact ⟨1, Fin.ext (by omega)⟩
      · exact ⟨2, Fin.ext (by omega)⟩
      · exact ⟨3, Fin.ext (by omega)⟩
    · change ∀ i : Fin 4, cut (e i) = (halfCut p) (e i)
      intro i
      fin_cases i
      · exact hc01.trans hp01.symm
      · exact (hsym _ _ hc01).trans hp10.symm
      · exact hc23.trans hp23.symm
      · exact (hsym _ _ hc23).trans hp32.symm
  · let p : TwoDownPrefix n :=
      ⟨((e 2).val, (e 3).val), ⟨by omega, by omega, h23, (e 3).isLt⟩⟩
    have hso : (secondOpen p) = (e 0).val := by
      dsimp [p, secondOpen]
      split_ifs <;> omega
    have hv0 : (e 0).val = (secondOpen p) := hso.symm
    have hv1 : (e 1).val = p.val.1 - 1 := by dsimp [p]; omega
    have hv2 : (e 2).val = p.val.1 := rfl
    have hv3 : (e 3).val = p.val.2 := rfl
    have hp12 : (halfCut p) (e 1) = some (e 2) := by
      have he1 : e 1 = (⟨p.val.1 - 1, by
          exact lt_of_le_of_lt (Nat.sub_le _ _)
            (lt_trans p.property.2.2.1 p.property.2.2.2)⟩ : Fin n) := Fin.ext hv1
      have he2 : e 2 = (⟨p.val.1, lt_trans p.property.2.2.1 p.property.2.2.2⟩ : Fin n) :=
        Fin.ext hv2
      rw [he1, he2]
      exact (halfCut_first_pair p)
    have hp21 : (halfCut p) (e 2) = some (e 1) := by
      have he1 : e 1 = (⟨p.val.1 - 1, by
          exact lt_of_le_of_lt (Nat.sub_le _ _)
            (lt_trans p.property.2.2.1 p.property.2.2.2)⟩ : Fin n) := Fin.ext hv1
      have he2 : e 2 = (⟨p.val.1, lt_trans p.property.2.2.1 p.property.2.2.2⟩ : Fin n) :=
        Fin.ext hv2
      rw [he1, he2]
      exact (halfCut_first_reverse p)
    have hp03 : (halfCut p) (e 0) = some (e 3) := by
      have he0 : e 0 = (⟨(secondOpen p), by rw [hso]; exact (e 0).isLt⟩ : Fin n) :=
        Fin.ext hv0
      have he3 : e 3 = (⟨p.val.2, p.property.2.2.2⟩ : Fin n) := Fin.ext hv3
      rw [he0, he3]
      exact (halfCut_second_pair p)
    have hp30 : (halfCut p) (e 3) = some (e 0) := by
      have he0 : e 0 = (⟨(secondOpen p), by rw [hso]; exact (e 0).isLt⟩ : Fin n) :=
        Fin.ext hv0
      have he3 : e 3 = (⟨p.val.2, p.property.2.2.2⟩ : Fin n) := Fin.ext hv3
      rw [he0, he3]
      exact (halfCut_second_reverse p)
    refine ⟨p, four_endpoint_cut_eq_halfCut hcard p ?_ ?_⟩
    · change ∀ x : Fin n, (halfCut p) x ≠ none → ∃ i : Fin 4, e i = x
      intro x hx
      have hv : x.val = p.val.1 - 1 ∨ x.val = p.val.1 ∨
          x.val = (secondOpen p) ∨ x.val = p.val.2 := by
        by_contra hn
        have hfix : x.val ≠ p.val.1 - 1 ∧ x.val ≠ p.val.1 ∧
            x.val ≠ (secondOpen p) ∧ x.val ≠ p.val.2 := by tauto
        exact hx (((halfCut_eq_none_iff p) x).2 hfix)
      rcases hv with h | h | h | h
      · exact ⟨1, Fin.ext (by omega)⟩
      · exact ⟨2, Fin.ext (by omega)⟩
      · exact ⟨0, Fin.ext (by omega)⟩
      · exact ⟨3, Fin.ext (by omega)⟩
    · change ∀ i : Fin 4, cut (e i) = (halfCut p) (e i)
      intro i
      fin_cases i
      · exact hc03.trans hp03.symm
      · exact hc12.trans hp12.symm
      · exact (hsym _ _ hc12).trans hp21.symm
      · exact (hsym _ _ hc03).trans hp30.symm

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem halfMate_lt_self_iff {n : ℕ} (p : TwoDownPrefix n)
    (x : Fin n) : (halfMate p) x.val < x.val ↔
      x.val = p.val.1 ∨ x.val = p.val.2 := by
  have hso : (secondOpen p) < p.val.2 := by
    unfold secondOpen
    split_ifs
    · exact lt_of_le_of_lt (Nat.sub_le _ _) p.property.2.2.1
    · have := p.property.2.1
      omega
  have hd := twoDown_endpoints_distinct p
  unfold halfMate
  split_ifs <;> have := p.property.1 <;> omega

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem halfCut_injective {n : ℕ} (p q : TwoDownPrefix n)
    (h : ∀ x, (halfCut p) x = (halfCut q) x) : p = q := by
  have hdown (r : TwoDownPrefix n) (x : Fin n) :
      (∃ y : Fin n, (halfCut r) x = some y ∧ y.val < x.val) ↔
        x.val = r.val.1 ∨ x.val = r.val.2 := by
    rw [← (halfMate_lt_self_iff r) x]
    constructor
    · rintro ⟨y, hy, hlt⟩
      by_cases hr : (halfMate r) x.val = x.val
      · simp [halfCut, hr] at hy
      · have heq : (⟨(halfMate r) x.val, (halfMate_lt r) x⟩ : Fin n) = y := by
          simpa [halfCut, hr] using hy
        rw [← heq] at hlt
        exact hlt
    · intro hlt
      have hne : (halfMate r) x.val ≠ x.val := by omega
      refine ⟨⟨(halfMate r) x.val, (halfMate_lt r) x⟩, ?_, hlt⟩
      simp [halfCut, hne]
  have hfirst : p.val.1 = q.val.1 ∨ p.val.1 = q.val.2 := by
    let x : Fin n := ⟨p.val.1, lt_trans p.property.2.2.1 p.property.2.2.2⟩
    have hp := (hdown p x).2 (Or.inl rfl)
    rw [h x] at hp
    exact (hdown q x).1 hp
  have hsecond : p.val.2 = q.val.1 ∨ p.val.2 = q.val.2 := by
    let x : Fin n := ⟨p.val.2, p.property.2.2.2⟩
    have hp := (hdown p x).2 (Or.inr rfl)
    rw [h x] at hp
    exact (hdown q x).1 hp
  have hvalues : p.val.1 = q.val.1 ∧ p.val.2 = q.val.2 := by
    rcases hfirst with hfirst | hfirst <;>
      rcases hsecond with hsecond | hsecond <;>
      have := p.property.2.2.1 <;> have := q.property.2.2.1 <;> omega
  exact Subtype.ext (Prod.ext hvalues.1 hvalues.2)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def pairedPositions {n : ℕ} (p : TwoDownPrefix n) :
    Finset (Fin n) :=
  {⟨p.val.1 - 1, by have := p.property.2.2.1; have := p.property.2.2.2; omega⟩,
    ⟨p.val.1, lt_trans p.property.2.2.1 p.property.2.2.2⟩,
    ⟨(secondOpen p), by
      unfold secondOpen
      split_ifs
      · have := p.property.2.2.1; have := p.property.2.2.2; omega
      · have := p.property.2.2.2; omega⟩,
    ⟨p.val.2, p.property.2.2.2⟩}

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def unmatchedPositions {n : ℕ} (p : TwoDownPrefix n) :
    Finset (Fin n) :=
  Finset.univ.filter fun x => (halfCut p) x = none

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem unmatchedPositions_card {n : ℕ} (p : TwoDownPrefix n) :
    (unmatchedPositions p).card = n - 4 := by
  have hc : (unmatchedPositions p) = (pairedPositions p)ᶜ := by
    ext x
    simp only [unmatchedPositions, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_compl]
    rw [(halfCut_eq_none_iff p)]
    simp only [pairedPositions, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff]
    tauto
  have hpaired : (pairedPositions p).card = 4 := by
    have hd := twoDown_endpoints_distinct p
    simp [pairedPositions, Fin.ext_iff, hd.1, hd.2.1,
      hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2]
  rw [hc, Finset.card_compl, hpaired]
  simp

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def crossingUnmatchedEquiv {n : ℕ} (M : UpperMatching n) :
    {x : Fin n // (leftCut M) x = none} ≃
      {y : Fin n // (rightCut M) y = none} :=
  {
    toFun x := ⟨crossingRight M x.1 x.2, crossingRight_none M x.1 x.2⟩
    invFun y := ⟨crossingLeft M y.1 y.2, crossingLeft_none M y.1 y.2⟩
    left_inv x := by
      apply Subtype.ext
      have h : leftPoint n (crossingLeft M (crossingRight M x.1 x.2)
          (crossingRight_none M x.1 x.2)) =
          M.mate (rightPoint n (crossingRight M x.1 x.2)) := by
        apply Fin.ext
        rfl
      have hpoint : rightPoint n (crossingRight M x.1 x.2) =
          M.mate (leftPoint n x.1) := by
        have hv : leftPoint n (crossingRight M x.1 x.2) =
            (M.mate (leftPoint n x.1)).rev := by
          apply Fin.ext
          rfl
        simpa [rightPoint] using congrArg Fin.rev hv
      rw [hpoint, M.mate_mate] at h
      exact Fin.ext (by simpa [leftPoint] using congrArg Fin.val h)
    right_inv y := by
      apply Subtype.ext
      have h : rightPoint n (crossingRight M (crossingLeft M y.1 y.2)
          (crossingLeft_none M y.1 y.2)) =
          M.mate (leftPoint n (crossingLeft M y.1 y.2)) := by
        have hv : leftPoint n (crossingRight M (crossingLeft M y.1 y.2)
            (crossingLeft_none M y.1 y.2)) =
            (M.mate (leftPoint n (crossingLeft M y.1 y.2))).rev := by
          apply Fin.ext
          rfl
        simpa [rightPoint] using congrArg Fin.rev hv
      have hpoint : leftPoint n (crossingLeft M y.1 y.2) =
          M.mate (rightPoint n y.1) := by
        apply Fin.ext
        rfl
      rw [hpoint, M.mate_mate] at h
      apply Fin.ext
      simpa [rightPoint, leftPoint] using congrArg Fin.val (congrArg Fin.rev h)
  }

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def crossingUnmatchedOrderIso {n : ℕ} (M : UpperMatching n) :
    {x : Fin n // (leftCut M) x = none} ≃o
      {y : Fin n // (rightCut M) y = none} :=
  {
    toEquiv := crossingUnmatchedEquiv M
    map_rel_iff' := by
      have horder (x y : Fin n) (hx : (leftCut M) x = none)
          (hy : (leftCut M) y = none) (hxy : x < y) :
          crossingRight M x hx < crossingRight M y hy := by
        have hmate := crossing_rank_order M (leftPoint n x) (leftPoint n y)
          (by simp [leftPoint, x.isLt])
          (by simp [leftPoint, y.isLt])
          (by simpa [leftPoint] using hxy)
          (by simpa [leftCut] using hx)
          (by simpa [leftCut] using hy)
        have hrx : (crossingRight M x hx).val =
            2 * n - ((M.mate (leftPoint n x)).val + 1) := by
          simp [crossingRight]
        have hry : (crossingRight M y hy).val =
            2 * n - ((M.mate (leftPoint n y)).val + 1) := by
          simp [crossingRight]
        change (crossingRight M x hx).val < (crossingRight M y hy).val
        omega
      intro x y
      constructor
      · intro hxy
        by_contra hnot
        have hyx : y < x := lt_of_not_ge hnot
        have hrev := horder y.1 x.1 y.2 x.2 hyx
        exact (not_lt_of_ge hxy) hrev
      · intro hxy
        rcases eq_or_lt_of_le hxy with heq | hlt
        · subst y
          exact le_refl _
        · exact le_of_lt (horder x.1 y.1 x.2 y.2 hlt)
  }

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def rankJoin {n : ℕ} (p q : TwoDownPrefix n) :
    (unmatchedPositions p) ≃o (unmatchedPositions q) :=
  ((unmatchedPositions p).orderIsoOfFin (unmatchedPositions_card p)).symm.trans
    ((unmatchedPositions q).orderIsoOfFin (unmatchedPositions_card q))

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def unmatchedCutIso {n : ℕ} (p : TwoDownPrefix n) :
    (unmatchedPositions p) ≃o {x : Fin n // (halfCut p) x = none} :=
  OrderIso.setCongr ((unmatchedPositions p) : Set (Fin n))
    {x : Fin n | (halfCut p) x = none} (by
      ext x
      simp [unmatchedPositions])

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem crossing_eq_rankJoin {n : ℕ} (M : UpperMatching n)
    (p q : TwoDownPrefix n)
    (hp : ∀ x, (leftCut M) x = (halfCut p) x)
    (hq : ∀ x, (rightCut M) x = (halfCut q) x)
    (x : Fin n) (hx : (leftCut M) x = none) :
    rightPoint n (((rankJoin p) q ⟨x, by
      simp [unmatchedPositions, ← hp x, hx]⟩).1) =
      M.mate (leftPoint n x) := by
  let left : (unmatchedPositions p) ≃o {x : Fin n // (leftCut M) x = none} :=
    (unmatchedCutIso p) |>.trans
      (OrderIso.setCongr {x : Fin n | (halfCut p) x = none}
        {x : Fin n | (leftCut M) x = none} (by
          ext y
          simp [hp y]))
  let right : {x : Fin n // (rightCut M) x = none} ≃o (unmatchedPositions q) :=
    (OrderIso.setCongr {x : Fin n | (rightCut M) x = none}
      {x : Fin n | (halfCut q) x = none} (by
        ext y
        simp [hq y])).trans (unmatchedCutIso q).symm
  let sourceIso : (unmatchedPositions p) ≃o (unmatchedPositions q) :=
    (left.trans (crossingUnmatchedOrderIso M)).trans right
  have hcanonical : sourceIso = (rankJoin p) q := by
    have hself := StrictMono.eq_id (((rankJoin p) q).trans sourceIso.symm).strictMono
    apply OrderIso.ext
    apply funext
    intro y
    have hy := congrFun hself y
    have hy' := congrArg sourceIso hy
    simpa using hy'.symm
  let xp : (unmatchedPositions p) := ⟨x, by
    simp [unmatchedPositions, ← hp x, hx]⟩
  have hsource : (sourceIso xp).1 = crossingRight M x hx := by
    rfl
  rw [← hcanonical]
  have hpoint : rightPoint n (crossingRight M x hx) =
      M.mate (leftPoint n x) := by
    have hv : leftPoint n (crossingRight M x hx) =
        (M.mate (leftPoint n x)).rev := by
      apply Fin.ext
      rfl
    simpa [rightPoint] using congrArg Fin.rev hv
  exact (congrArg (rightPoint n) hsource).trans hpoint

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def joinedEdge {n : ℕ} (p q : TwoDownPrefix n)
    (i j : Fin n) : Prop :=
  (halfCut p) i = some j ∨ (halfCut q) i = some j ∨
    (∃ hi : i ∈ (unmatchedPositions p),
      ((rankJoin p) q ⟨i, hi⟩).1 = j) ∨
    (∃ hj : j ∈ (unmatchedPositions p),
      ((rankJoin p) q ⟨j, hj⟩).1 = i)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem contractedEdge_iff_joinedEdge {n : ℕ} (M : UpperMatching n)
    (p q : TwoDownPrefix n)
    (hp : ∀ x, (leftCut M) x = (halfCut p) x)
    (hq : ∀ x, (rightCut M) x = (halfCut q) x)
    (i j : Fin n) : (contractedEdge M) i j ↔ (joinedEdge p) q i j := by
  have hcross (a b : Fin n) :
      M.mate (leftPoint n a) = rightPoint n b ↔
        ∃ ha : a ∈ (unmatchedPositions p),
          ((rankJoin p) q ⟨a, ha⟩).1 = b := by
    constructor
    · intro hab
      have hright : n ≤ (rightPoint n b).val := by
        have hb := b.isLt
        have hv : (rightPoint n b).val = 2 * n - (b.val + 1) := by
          simp [rightPoint, leftPoint]
        omega
      have haNone : (leftCut M) a = none :=
        (by simpa [leftCut] using (show
          n ≤ (M.mate (leftPoint n a)).val by rw [hab]; exact hright))
      have ha : a ∈ (unmatchedPositions p) := by
        simp [unmatchedPositions, ← hp a, haNone]
      refine ⟨ha, ?_⟩
      have hjoin := crossing_eq_rankJoin M p q hp hq a haNone
      rw [hab] at hjoin
      apply Fin.ext
      simpa [rightPoint, leftPoint] using congrArg Fin.val (congrArg Fin.rev hjoin)
    · rintro ⟨ha, hab⟩
      have haNone : (leftCut M) a = none := by
        have hpa : (halfCut p) a = none :=
          (Finset.mem_filter.mp ha).2
        exact (hp a).trans hpa
      have hjoin := crossing_eq_rankJoin M p q hp hq a haNone
      exact hjoin.symm.trans (congrArg (rightPoint n) hab)
  rw [contractedEdge_iff_cut_or_cross]
  change ((leftCut M) i = some j ∨ (rightCut M) i = some j ∨
    M.mate (leftPoint n i) = rightPoint n j ∨
    M.mate (leftPoint n j) = rightPoint n i) ↔
    ((halfCut p) i = some j ∨ (halfCut q) i = some j ∨
      (∃ hi : i ∈ (unmatchedPositions p),
        ((rankJoin p) q ⟨i, hi⟩).1 = j) ∨
      (∃ hj : j ∈ (unmatchedPositions p),
        ((rankJoin p) q ⟨j, hj⟩).1 = i))
  rw [hp i, hq i, hcross i j, hcross j i]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def halfMateFin {n : ℕ} (p : TwoDownPrefix n)
    (x : Fin n) : Fin n :=
  ⟨(halfMate p) x.val, (halfMate_lt p) x⟩

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem halfMateFin_fixed_iff {n : ℕ}
    (p : TwoDownPrefix n) (x : Fin n) :
    (halfMateFin p) x = x ↔ x ∈ (unmatchedPositions p) := by
  simp only [unmatchedPositions, Finset.mem_filter,
    Finset.mem_univ, true_and, (halfCut_eq_none_iff p),
    ← (halfMate_fixed_iff p)]
  simp [halfMateFin, Fin.ext_iff]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem halfMate_interval {n : ℕ}
    (p : TwoDownPrefix n) (a b : Fin n)
    (hab : a.val < b.val) (hbetween : b.val < (halfMate p) a.val) :
    (halfMate p) b.val ≠ b.val ∧
      (halfMate p) b.val < (halfMate p) a.val := by
  have hfirst := p.property.1
  have hsecond := p.property.2.1
  have hordered := p.property.2.2.1
  have hd := twoDown_endpoints_distinct p
  unfold halfMate secondOpen at hbetween hd ⊢
  split_ifs at hbetween hd ⊢ <;> omega

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def joinedMate {n : ℕ} (p q : TwoDownPrefix n)
    (x : Fin (2 * n)) : Fin (2 * n) :=
  if x.val < n then
    let i := rainbowLabel n x
    if hi : i ∈ (unmatchedPositions p) then
      rightPoint n (((rankJoin p) q ⟨i, hi⟩).1)
    else leftPoint n ((halfMateFin p) i)
  else
    let j := rainbowLabel n x
    if hj : j ∈ (unmatchedPositions q) then
      leftPoint n (((rankJoin p) q).symm ⟨j, hj⟩).1
    else rightPoint n ((halfMateFin q) j)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem joinedMate_involutive {n : ℕ}
    (p q : TwoDownPrefix n) (x : Fin (2 * n)) :
    (joinedMate p) q ((joinedMate p) q x) = x := by
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
  have hinv (r : TwoDownPrefix n) (i : Fin n) :
      (halfMateFin r) ((halfMateFin r) i) = i := by
    apply Fin.ext
    exact (halfMate_involutive r) i.val
  have hnonfixed (r : TwoDownPrefix n) (i : Fin n)
      (hi : i ∉ (unmatchedPositions r)) :
      (halfMateFin r) i ∉ (unmatchedPositions r) := by
    intro hmate
    have hfix := ((halfMateFin_fixed_iff r) ((halfMateFin r) i)).2 hmate
    have hback := hinv r i
    have heq : (halfMateFin r) i = i := (hback.symm.trans hfix).symm
    exact hi (((halfMateFin_fixed_iff r) i).1 heq)
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
  rcases hpoint x with hleft | hright
  · rw [hleft]
    let i := rainbowLabel n x
    change (joinedMate p) q ((joinedMate p) q (leftPoint n i)) = leftPoint n i
    by_cases hi : i ∈ (unmatchedPositions p)
    · have hj : ((rankJoin p) q ⟨i, hi⟩).1 ∈ (unmatchedPositions q) :=
        ((rankJoin p) q ⟨i, hi⟩).2
      rw [joinedMate_left, dif_pos hi, joinedMate_right, dif_pos hj]
      simp
    · have hm := hnonfixed p i hi
      rw [joinedMate_left, dif_neg hi, joinedMate_left, dif_neg hm,
        hinv p i]
  · rw [hright]
    let j := rainbowLabel n x
    change (joinedMate p) q ((joinedMate p) q (rightPoint n j)) = rightPoint n j
    by_cases hj : j ∈ (unmatchedPositions q)
    · have hi : (((rankJoin p) q).symm ⟨j, hj⟩).1 ∈ (unmatchedPositions p) :=
        (((rankJoin p) q).symm ⟨j, hj⟩).2
      rw [joinedMate_right, dif_pos hj, joinedMate_left, dif_pos hi]
      simp
    · have hm := hnonfixed q j hj
      rw [joinedMate_right, dif_neg hj, joinedMate_right, dif_neg hm,
        hinv q j]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem joinedMate_ne {n : ℕ}
    (p q : TwoDownPrefix n) (x : Fin (2 * n)) :
    (joinedMate p) q x ≠ x := by
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
  have right_ge (j : Fin n) : n ≤ (rightPoint n j).val := by
    have hj := j.isLt
    have hv : (rightPoint n j).val = 2 * n - (j.val + 1) := by
      simp [rightPoint, leftPoint]
    omega
  rcases hpoint x with hleft | hright
  · rw [hleft]
    let i := rainbowLabel n x
    change (joinedMate p) q (leftPoint n i) ≠ leftPoint n i
    by_cases hi : i ∈ (unmatchedPositions p)
    · rw [joinedMate_left, dif_pos hi]
      intro heq
      have hl : (rightPoint n (((rankJoin p) q ⟨i, hi⟩).1)).val < n := by
        rw [heq]
        exact i.isLt
      exact (not_lt_of_ge (right_ge _)) hl
    · rw [joinedMate_left, dif_neg hi]
      intro heq
      have hv := congrArg (rainbowLabel n) heq
      have hfix : (halfMateFin p) i = i := by
        simpa [rainbowLabel, leftPoint] using hv
      exact hi (((halfMateFin_fixed_iff p) i).1 hfix)
  · rw [hright]
    let j := rainbowLabel n x
    change (joinedMate p) q (rightPoint n j) ≠ rightPoint n j
    by_cases hj : j ∈ (unmatchedPositions q)
    · rw [joinedMate_right, dif_pos hj]
      intro heq
      have hv : (leftPoint n (((rankJoin p) q).symm ⟨j, hj⟩).1).val < n :=
        (((rankJoin p) q).symm ⟨j, hj⟩).1.isLt
      rw [heq] at hv
      exact (not_lt_of_ge (right_ge j)) hv
    · rw [joinedMate_right, dif_neg hj]
      intro heq
      have hv := congrArg (rainbowLabel n) heq
      have hlabel (k : Fin n) : rainbowLabel n (rightPoint n k) = k := by
        unfold rightPoint; rw [rainbowLabel_rev]
        simp [rainbowLabel, leftPoint]
      simp only [hlabel] at hv
      exact hj (((halfMateFin_fixed_iff q) j).1 hv)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem joinedMate_noncrossing {n : ℕ}
    (p q : TwoDownPrefix n) (a b : Fin (2 * n))
    (hab : a.val < b.val)
    (hbetween : b.val < ((joinedMate p) q a).val)
    (hends : ((joinedMate p) q a).val < ((joinedMate p) q b).val) : False := by
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
  have right_val (i : Fin n) :
      (rightPoint n i).val = 2 * n - (i.val + 1) := by
    simp [rightPoint, leftPoint]
  have right_ge (i : Fin n) : n ≤ (rightPoint n i).val := by
    have := i.isLt
    rw [right_val]
    omega
  rcases hpoint a with ha | ha <;>
    rcases hpoint b with hb | hb
  · let i := rainbowLabel n a
    let j := rainbowLabel n b
    rw [ha, hb] at hab hbetween hends
    change (leftPoint n i).val < (leftPoint n j).val at hab
    change (leftPoint n j).val < ((joinedMate p) q (leftPoint n i)).val at hbetween
    change ((joinedMate p) q (leftPoint n i)).val <
      ((joinedMate p) q (leftPoint n j)).val at hends
    have hij : i.val < j.val := by simpa [leftPoint] using hab
    by_cases hi : i ∈ (unmatchedPositions p)
    · rw [joinedMate_left, dif_pos hi] at hbetween hends
      by_cases hj : j ∈ (unmatchedPositions p)
      · rw [joinedMate_left, dif_pos hj] at hends
        have horder : ((rankJoin p) q ⟨i, hi⟩).1.val <
            ((rankJoin p) q ⟨j, hj⟩).1.val := by
          exact ((rankJoin p) q).strictMono hij
        simp only [right_val] at hends
        have hk := ((rankJoin p) q ⟨i, hi⟩).1.isLt
        have hl := ((rankJoin p) q ⟨j, hj⟩).1.isLt
        omega
      · rw [joinedMate_left, dif_neg hj] at hends
        have hl : (leftPoint n ((halfMateFin p) j)).val < n :=
          ((halfMateFin p) j).isLt
        exact (not_lt_of_ge (right_ge _)) (lt_trans hends hl)
    · rw [joinedMate_left, dif_neg hi] at hbetween hends
      have hinside : j.val < (halfMate p) i.val := by
        simpa [leftPoint, halfMateFin] using hbetween
      have hinterval := (halfMate_interval p) i j hij hinside
      have hj : j ∉ (unmatchedPositions p) := by
        intro hj
        have hfix := ((halfMateFin_fixed_iff p) j).2 hj
        exact hinterval.1 (congrArg Fin.val hfix)
      rw [joinedMate_left, dif_neg hj] at hends
      have hreverse : (halfMate p) i.val < (halfMate p) j.val := by
        simpa [leftPoint, halfMateFin] using hends
      omega
  · let i := rainbowLabel n a
    let j := rainbowLabel n b
    rw [ha, hb] at hab hbetween hends
    change (leftPoint n i).val < (rightPoint n j).val at hab
    change (rightPoint n j).val < ((joinedMate p) q (leftPoint n i)).val at hbetween
    change ((joinedMate p) q (leftPoint n i)).val <
      ((joinedMate p) q (rightPoint n j)).val at hends
    by_cases hi : i ∈ (unmatchedPositions p)
    · rw [joinedMate_left, dif_pos hi] at hbetween hends
      by_cases hj : j ∈ (unmatchedPositions q)
      · rw [joinedMate_right, dif_pos hj] at hends
        have hl : (leftPoint n (((rankJoin p) q).symm ⟨j, hj⟩).1).val < n :=
          (((rankJoin p) q).symm ⟨j, hj⟩).1.isLt
        exact (not_lt_of_ge (right_ge _)) (lt_trans hends hl)
      · rw [joinedMate_right, dif_neg hj] at hends
        let k : Fin n := ((rankJoin p) q ⟨i, hi⟩).1
        have hk : k ∈ (unmatchedPositions q) :=
          ((rankJoin p) q ⟨i, hi⟩).2
        have hkj : k.val < j.val := by
          simp only [right_val] at hbetween
          have hklt := k.isLt
          have hjlt := j.isLt
          omega
        have hmj : ((halfMateFin q) j).val < k.val := by
          simp only [right_val] at hends
          have hklt := k.isLt
          have hmlt := ((halfMateFin q) j).isLt
          omega
        let u := (halfMateFin q) j
        have hinterval : k.val < (halfMate q) u.val := by
          simpa [u, halfMateFin, (halfMate_involutive q)] using hkj
        have hfixed := ((halfMateFin_fixed_iff q) k).2 hk
        exact ((halfMate_interval q) u k hmj hinterval).1
          (congrArg Fin.val hfixed)
    · rw [joinedMate_left, dif_neg hi] at hbetween
      have hl : (leftPoint n ((halfMateFin p) i)).val < n :=
        ((halfMateFin p) i).isLt
      exact (not_lt_of_ge (right_ge j)) (lt_trans hbetween hl)
  · let i := rainbowLabel n a
    let j := rainbowLabel n b
    rw [ha, hb] at hab
    have hl : (leftPoint n j).val < n := j.isLt
    exact (not_lt_of_ge (right_ge i)) (lt_trans hab hl)
  · let i := rainbowLabel n a
    let j := rainbowLabel n b
    rw [ha, hb] at hab hbetween hends
    change (rightPoint n i).val < (rightPoint n j).val at hab
    change (rightPoint n j).val < ((joinedMate p) q (rightPoint n i)).val at hbetween
    change ((joinedMate p) q (rightPoint n i)).val <
      ((joinedMate p) q (rightPoint n j)).val at hends
    have hji : j.val < i.val := by
      simp only [right_val] at hab
      have hi := i.isLt
      have hj := j.isLt
      omega
    by_cases hi : i ∈ (unmatchedPositions q)
    · rw [joinedMate_right, dif_pos hi] at hbetween
      have hl : (leftPoint n (((rankJoin p) q).symm ⟨i, hi⟩).1).val < n :=
        (((rankJoin p) q).symm ⟨i, hi⟩).1.isLt
      exact (not_lt_of_ge (right_ge j)) (lt_trans hbetween hl)
    · rw [joinedMate_right, dif_neg hi] at hbetween hends
      by_cases hj : j ∈ (unmatchedPositions q)
      · rw [joinedMate_right, dif_pos hj] at hends
        have hl : (leftPoint n (((rankJoin p) q).symm ⟨j, hj⟩).1).val < n :=
          (((rankJoin p) q).symm ⟨j, hj⟩).1.isLt
        exact (not_lt_of_ge (right_ge _)) (lt_trans hends hl)
      · rw [joinedMate_right, dif_neg hj] at hends
        have huj : ((halfMateFin q) i).val < j.val := by
          simp only [right_val] at hbetween
          have hu := ((halfMateFin q) i).isLt
          have hjlt := j.isLt
          omega
        have hvu : ((halfMateFin q) j).val < ((halfMateFin q) i).val := by
          simp only [right_val] at hends
          have hu := ((halfMateFin q) i).isLt
          have hv := ((halfMateFin q) j).isLt
          omega
        let v := (halfMateFin q) j
        let u := (halfMateFin q) i
        have hbackj : (halfMate q) v.val = j.val := by
          simp [v, halfMateFin, (halfMate_involutive q)]
        have hinterval : u.val < (halfMate q) v.val := by
          rw [hbackj]
          exact huj
        have hnest := ((halfMate_interval q) v u hvu hinterval).2
        have hbacki : (halfMate q) u.val = i.val := by
          simp [u, halfMateFin, (halfMate_involutive q)]
        omega

-- Join unmatched positions by rank to reconstruct the source involution.

end D5.S3.Combinatorics.SemiMeanderSecondDiagonal
