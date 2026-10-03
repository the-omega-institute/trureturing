/- GID: D5/S3/Combinatorics/SemiMeanderSecondDiagonal/Stage5
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SemiMeanderSecondDiagonal/Stage5
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Canonical connected pairs and their exact count. -/

import D5.S3.Combinatorics.SemiMeanderSecondDiagonal.Stage4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SemiMeanderSecondDiagonal

open Classical

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem not_connected_B_four
    (p q : TwoDownPrefix 4) (hp1 : p.val.1 = 1) (hp2 : p.val.2 = 3)
    (hq1 : q.val.1 = 1) (hq2 : q.val.2 = 3) :
    ¬ (∀ i j : Fin 4, Relation.ReflTransGen ((joinedEdge p) q) i j) := by
  let t : TwoDownPrefix 4 := ⟨(1, 3), ⟨ by decide, by decide, by decide, by decide⟩⟩
  have hpt : p = t := by
    rcases p with ⟨⟨a, b⟩, _⟩
    change a = 1 at hp1
    change b = 3 at hp2
    subst a
    subst b
    rfl
  have hqt : q = t := by
    rcases q with ⟨⟨a, b⟩, _⟩
    change a = 1 at hq1
    change b = 3 at hq2
    subst a
    subst b
    rfl
  subst p
  subst q
  have hempty : (unmatchedPositions t) = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa using (unmatchedPositions_card t)
  have hedge (i j : Fin 4) (h : (joinedEdge t) t i j) :
      (i.val < 2 ↔ j.val < 2) := by
    have hcut : ∀ a b : Fin 4, (halfCut t) a = some b →
        (a.val < 2 ↔ b.val < 2) := by
      intro a b hab
      fin_cases a <;> fin_cases b <;>
        simp [halfCut, halfMate, secondOpen, t] at hab ⊢
    rcases h with h | h | ⟨hi, _⟩ | ⟨hj, _⟩
    · exact hcut i j h
    · exact hcut i j h
    · simp [hempty] at hi
    · simp [hempty] at hj
  intro hconn
  have hpath := hconn (0 : Fin 4) (2 : Fin 4)
  have hinv : ∀ j : Fin 4,
      Relation.ReflTransGen ((joinedEdge t) t) (0 : Fin 4) j → j.val < 2 := by
    intro j h
    induction h with
    | refl => decide
    | @tail b c _ hbc ih => exact (hedge b c hbc).mp ih
  exact (by decide : ¬ (2 : Fin 4).val < 2) (hinv 2 hpath)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def canonicalA {n : ℕ} (p q : TwoDownPrefix n) : Prop :=
  p.val.1 = 1 ∧ p.val.2 ≤ n - 2 ∧ q.val.2 = n - 1 ∧
    p.val.2 - 1 ≤ q.val.1 ∧ q.val.1 % 2 ≠ p.val.2 % 2

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def canonicalB {n : ℕ} (p q : TwoDownPrefix n) : Prop :=
  p.val.1 = 1 ∧ p.val.2 = n - 1 ∧ 2 ≤ q.val.1 ∧
    q.val.2 = q.val.1 + 1

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def canonicalC {n : ℕ} (p q : TwoDownPrefix n) : Prop :=
  p.val.1 = 2 ∧ p.val.2 = 3 ∧ q.val.2 = n - 1 ∧
    3 ≤ q.val.1 ∧ q.val.1 % 2 = 1

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def canonical {n : ℕ} (p q : TwoDownPrefix n) : Prop :=
  canonicalA p q ∨ canonicalB p q ∨ canonicalC p q

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem connected_canonical_of_endpoint {n : ℕ}
    (p q : TwoDownPrefix n) (hn : 4 ≤ n)
    (hconn : ∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge p) q) i j)
    (hp : p.val.1 = 1 ∨ (p.val.1 = 2 ∧ p.val.2 = 3))
    (hq : q.val.2 = n - 1) : canonical p q ∨ canonical q p := by
  rcases hp with hp1 | ⟨hp1, hp2⟩
  · by_cases hplast : p.val.2 = n - 1
    · by_cases hq1 : q.val.1 = 1
      · have hnp : n = 4 := by
          by_contra hne
          have hn5 : 5 ≤ n := by omega
          exact ((not_connected_of_B_separated p) q hn5 hp1 hplast
            (by have := q.property.2.1; omega)) hconn
        subst n
        exact False.elim (((not_connected_B_four p) q hp1 (by omega) hq1 (by omega)) hconn)
      · have hqfirst : 2 ≤ q.val.1 := by have := q.property.1; omega
        have hconsec : q.val.2 = q.val.1 + 1 := by
          by_contra hne
          have hn5 : 5 ≤ n := by
            have := q.property.2.1
            have := q.property.2.2.1
            omega
          exact ((not_connected_of_B_separated p) q hn5 hp1 hplast
            (by have := q.property.2.2.1; omega)) hconn
        exact Or.inl (Or.inr (Or.inl ⟨hp1, hplast, hqfirst, hconsec⟩))
    · have hpbound : p.val.2 ≤ n - 2 := by
        have := p.property.2.2.2
        omega
      have hA := ((connected_iff_A p) q hp1 hpbound hq).mp hconn
      exact Or.inl (Or.inl ⟨hp1, hpbound, hq, hA.1, hA.2⟩)
  · have hC := ((connected_iff_C p) q hp1 hp2 hq).mp hconn
    by_cases hq1 : q.val.1 = 1
    · have hqB : q.val.2 = n - 1 := hq
      have hpB : p.val.2 = p.val.1 + 1 := by omega
      exact Or.inr (Or.inr (Or.inl ⟨hq1, hqB, by omega, hpB⟩))
    · exact Or.inl (Or.inr (Or.inr ⟨hp1, hp2, hq, by
        have := q.property.1
        omega, hC⟩))

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem connected_canonical_of_terminal_B {n : ℕ}
    (p q : TwoDownPrefix n) (hn : 4 ≤ n)
    (hconn : ∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge p) q) i j)
    (hp1 : p.val.1 = 1) (hp2 : p.val.2 = n - 1) :
    canonical p q := by
  by_cases hq1 : q.val.1 = 1
  · by_cases hn4 : n = 4
    · subst n
      exact False.elim (((not_connected_B_four p) q hp1 (by omega) hq1 (by
        have := q.property.2.2.2
        have := q.property.2.1
        omega)) hconn)
    · have hn5 : 5 ≤ n := by omega
      exact False.elim (((not_connected_of_B_separated p) q hn5 hp1 hp2
        (by have := q.property.2.1; omega)) hconn)
  · have hqfirst : 2 ≤ q.val.1 := by have := q.property.1; omega
    have hconsec : q.val.2 = q.val.1 + 1 := by
      by_contra hne
      have hn5 : 5 ≤ n := by
        have := q.property.2.2.2
        have := q.property.2.2.1
        omega
      exact ((not_connected_of_B_separated p) q hn5 hp1 hp2
        (by have := q.property.2.2.1; omega)) hconn
    exact Or.inr (Or.inl ⟨hp1, hp2, hqfirst, hconsec⟩)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem connected_iff_canonical_or_swap {n : ℕ} (p q : TwoDownPrefix n)
    (hn : 4 ≤ n) :
    (∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge p) q) i j) ↔
      canonical p q ∨ canonical q p := by
  have connected_swap :
      (∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge p) q) i j) ↔
      (∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge q) p) i j) := by
    constructor <;> intro h i j
    · exact Relation.ReflTransGen.mono ((joinedEdge_swap q) p) i j (h i j)
    · exact Relation.ReflTransGen.mono ((joinedEdge_swap p) q) i j (h i j)
  constructor
  · intro hconn
    obtain ⟨hfirst, hlast⟩ := (connected_endpoint_cases p) q hn hconn
    rcases hfirst with hp1 | hpC | hq1 | hqC
    · rcases hlast with hp2 | hq2
      · exact Or.inl (connected_canonical_of_terminal_B p q hn hconn hp1 hp2)
      · exact connected_canonical_of_endpoint p q hn hconn (Or.inl hp1) hq2
    · rcases hlast with hpLast | hqLast
      · have hn4 : n = 4 := by
          have := p.property.2.2.2
          omega
        have hqLast : q.val.2 = n - 1 := by
          have := q.property.2.2.2
          have := q.property.2.1
          omega
        exact connected_canonical_of_endpoint p q hn hconn (Or.inr hpC) hqLast
      · exact connected_canonical_of_endpoint p q hn hconn (Or.inr hpC) hqLast
    · rcases hlast with hpLast | hqLast
      · have hs := connected_canonical_of_endpoint q p hn
          (connected_swap.mp hconn) (Or.inl hq1) hpLast
        exact hs.symm
      · have hs := connected_canonical_of_terminal_B q p hn
          (connected_swap.mp hconn) hq1 hqLast
        exact Or.inr hs
    · rcases hlast with hpLast | hqLast
      · have hs := connected_canonical_of_endpoint q p hn
          (connected_swap.mp hconn) (Or.inr hqC) hpLast
        exact hs.symm
      · have hn4 : n = 4 := by
          have := q.property.2.2.2
          omega
        have hpLast : p.val.2 = n - 1 := by
          have := p.property.2.2.2
          have := p.property.2.1
          omega
        have hs := connected_canonical_of_endpoint q p hn
          (connected_swap.mp hconn) (Or.inr hqC) hpLast
        exact hs.symm
  · rintro (h | h)
    · rcases h with hA | hB | hC
      · exact ((connected_iff_A p) q hA.1 hA.2.1 hA.2.2.1).2
          ⟨hA.2.2.2.1, hA.2.2.2.2⟩
      · exact (connected_of_B_consecutive p) q hB.1 hB.2.1 hB.2.2.1 hB.2.2.2
      · exact ((connected_iff_C p) q hC.1 hC.2.1 hC.2.2.1).2 hC.2.2.2.2
    · apply connected_swap.mpr
      rcases h with hA | hB | hC
      · exact ((connected_iff_A q) p hA.1 hA.2.1 hA.2.2.1).2
          ⟨hA.2.2.2.1, hA.2.2.2.2⟩
      · exact (connected_of_B_consecutive q) p hB.1 hB.2.1 hB.2.2.1 hB.2.2.2
      · exact ((connected_iff_C q) p hC.1 hC.2.1 hC.2.2.1).2 hC.2.2.2.2

-- Count the disjoint canonical families and their exchanged copies.
set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable instance prefixFinite (n : ℕ) : Finite (TwoDownPrefix n) := by
  let f : TwoDownPrefix n → Fin n × Fin n := fun p =>
    (⟨p.val.1, lt_trans p.property.2.2.1 p.property.2.2.2⟩, ⟨p.val.2, p.property.2.2.2⟩)
  apply Finite.of_injective f
  intro p q h
  have hfirst : p.val.1 = q.val.1 := congrArg (fun x : Fin n × Fin n => x.1.val) h
  have hsecond : p.val.2 = q.val.2 := congrArg (fun x : Fin n × Fin n => x.2.val) h
  rcases p with ⟨⟨a, b⟩, _⟩
  rcases q with ⟨⟨c, d⟩, _⟩
  change a = c at hfirst
  change b = d at hsecond
  subst c
  subst d
  rfl

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable instance prefixFintype (n : ℕ) : Fintype (TwoDownPrefix n) :=
  Fintype.ofFinite _

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def sourceCount (n : ℕ) (hn : 4 ≤ n) : ℕ :=
  letI : Finite {M : {M : UpperMatching n // M.winding = n - 4} // M.1.oneLoop} :=
    Finite.of_injective (connectedSourcePrefixEquiv n hn)
      (connectedSourcePrefixEquiv n hn).injective
  Nat.card {M : {M : UpperMatching n // M.winding = n - 4} // M.1.oneLoop}

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem connected_pair_card_double (n : ℕ) (hn : 4 ≤ n) :
    Nat.card {pq : TwoDownPrefix n × TwoDownPrefix n //
      ∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge pq.1) pq.2) i j} =
      2 * Nat.card {pq : TwoDownPrefix n × TwoDownPrefix n //
        canonical pq.1 pq.2} := by
  classical
  let A : Finset (TwoDownPrefix n × TwoDownPrefix n) :=
    Finset.univ.filter (fun pq => canonical pq.1 pq.2)
  let B : Finset (TwoDownPrefix n × TwoDownPrefix n) :=
    Finset.univ.filter (fun pq => canonical pq.2 pq.1)
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro pq ha hb
    have h := (Finset.mem_filter.mp ha).2
    have hs := (Finset.mem_filter.mp hb).2
    rcases h with h | h | h <;>
      rcases hs with hs | hs | hs <;>
      simp only [canonicalA, canonicalB, canonicalC] at h hs <;>
      have hpge := pq.1.property.2.1 <;>
      have hqge := pq.2.property.2.1 <;>
      have hpord := pq.1.property.2.2.1 <;>
      have hqord := pq.2.property.2.2.1 <;>
      omega
  have hconn : (Finset.univ.filter (fun pq : TwoDownPrefix n × TwoDownPrefix n =>
      ∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge pq.1) pq.2) i j)) = A ∪ B := by
    ext pq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, A, B]
    exact connected_iff_canonical_or_swap pq.1 pq.2 hn
  have hswap : A.card = B.card := by
    apply Finset.card_bij (fun pq _ => (pq.2, pq.1))
    · intro pq hpq
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (Finset.mem_filter.mp hpq).2
    · intro a _ b _ hab
      exact Prod.ext (congrArg Prod.snd hab) (congrArg Prod.fst hab)
    · intro pq hpq
      refine ⟨(pq.2, pq.1), ?_, rfl⟩
      simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using
        (Finset.mem_filter.mp hpq).2
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Fintype.card_subtype]
  change (Finset.univ.filter (fun pq : TwoDownPrefix n × TwoDownPrefix n =>
    ∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge pq.1) pq.2) i j)).card =
    2 * A.card
  rw [hconn, Finset.card_union_of_disjoint hdis, ← hswap]
  omega

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def canonicalBEquiv (n : ℕ) (hn : 4 ≤ n) :
    {pq : TwoDownPrefix n × TwoDownPrefix n // canonicalB pq.1 pq.2} ≃
      {c : ℕ // c ∈ Finset.Icc 2 (n - 2)} :=
  {
    toFun pq := ⟨pq.1.2.val.1, by
      rcases pq.2 with ⟨_, _, hc, hd⟩
      exact Finset.mem_Icc.mpr ⟨hc, by
        have := pq.1.2.property.2.2.2
        omega⟩⟩
    invFun c := ⟨
      (⟨(1, n - 1), ⟨ by omega, by omega, by omega, by omega⟩⟩,
       ⟨(c.1, c.1 + 1), ⟨ by
         have := (Finset.mem_Icc.mp c.2).1
         omega, by
         have := (Finset.mem_Icc.mp c.2).1
         omega, by omega, by
         have := (Finset.mem_Icc.mp c.2).2
         omega⟩⟩),
      by exact ⟨rfl, rfl, (Finset.mem_Icc.mp c.2).1, rfl⟩⟩
    left_inv pq := by
      have ext_positions (p q : TwoDownPrefix n)
          (hfirst : p.val.1 = q.val.1) (hsecond : p.val.2 = q.val.2) : p = q := by
        rcases p with ⟨⟨a, b⟩, _⟩
        rcases q with ⟨⟨c, d⟩, _⟩
        change a = c at hfirst
        change b = d at hsecond
        subst c
        subst d
        rfl
      apply Subtype.ext
      apply Prod.ext
      · apply ext_positions
        · exact pq.2.1.symm
        · exact pq.2.2.1.symm
      · apply ext_positions
        · rfl
        · exact pq.2.2.2.2.symm
    right_inv c := Subtype.ext rfl
  }

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def canonicalCEquiv (n : ℕ) (hn : 4 ≤ n) :
    {pq : TwoDownPrefix n × TwoDownPrefix n // canonicalC pq.1 pq.2} ≃
      {k : ℕ // k ∈ Finset.Icc 1 ((n - 3) / 2)} :=
  {
    toFun pq := ⟨pq.1.2.val.1 / 2, by
      rcases pq.2 with ⟨_, _, _, hc, hd⟩
      have hlt := pq.1.2.property.2.2.2
      have hord := pq.1.2.property.2.2.1
      have hlast := pq.2.2.2.1
      have hmod := hd
      exact Finset.mem_Icc.mpr (by
        constructor <;> omega)⟩
    invFun k := ⟨
      (⟨(2, 3), ⟨ by omega, by omega, by omega, by omega⟩⟩,
       ⟨(2 * k.1 + 1, n - 1), ⟨ by
         have := (Finset.mem_Icc.mp k.2).1
         omega, by
         have := (Finset.mem_Icc.mp k.2).1
         omega, by
         have := (Finset.mem_Icc.mp k.2).2
         omega, by
         have := (Finset.mem_Icc.mp k.2).2
         omega⟩⟩),
      by
        refine ⟨rfl, rfl, rfl, ?_, ?_⟩
        · have := (Finset.mem_Icc.mp k.2).1
          change 3 ≤ 2 * k.1 + 1
          omega
        · change (2 * k.1 + 1) % 2 = 1
          omega⟩
    left_inv pq := by
      have ext_positions (p q : TwoDownPrefix n)
          (hfirst : p.val.1 = q.val.1) (hsecond : p.val.2 = q.val.2) : p = q := by
        rcases p with ⟨⟨a, b⟩, _⟩
        rcases q with ⟨⟨c, d⟩, _⟩
        change a = c at hfirst
        change b = d at hsecond
        subst c
        subst d
        rfl
      apply Subtype.ext
      apply Prod.ext
      · apply ext_positions
        · exact pq.2.1.symm
        · exact pq.2.2.1.symm
      · apply ext_positions
        · have hmod := pq.2.2.2.2
          change 2 * (pq.1.2.val.1 / 2) + 1 = pq.1.2.val.1
          omega
        · exact pq.2.2.2.1.symm
    right_inv k := by
      apply Subtype.ext
      dsimp
      omega
  }

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def canonicalAEquiv (n : ℕ) (hn : 4 ≤ n) :
    {pq : TwoDownPrefix n × TwoDownPrefix n // canonicalA pq.1 pq.2} ≃
      Σ r : {r : ℕ // r ∈ Finset.Icc 1 (n - 4)},
        {k : ℕ // k ∈ Finset.Icc 0 (r.1 / 2)} :=
  {
    toFun pq := ⟨
      ⟨n - 1 - pq.1.1.val.2, by
        have hpbound := pq.2.2.1
        have hpge := pq.1.1.property.2.1
        have hplt := pq.1.1.property.2.2.2
        exact Finset.mem_Icc.mpr (by constructor <;> omega)⟩,
      ⟨(pq.1.2.val.1 - (pq.1.1.val.2 - 1)) / 2, by
        rcases pq.2 with ⟨hp1, hpbound, hq2, hlate, hpar⟩
        have hpge := pq.1.1.property.2.1
        have hqord := pq.1.2.property.2.2.1
        have hqlt := pq.1.2.property.2.2.2
        apply Finset.mem_Icc.mpr
        constructor
        · omega
        · change (pq.1.2.val.1 - (pq.1.1.val.2 - 1)) / 2 ≤
            (n - 1 - pq.1.1.val.2) / 2
          omega⟩⟩
    invFun rk := ⟨
      (⟨(1, n - 1 - rk.1.1), ⟨
        by omega, by
          have hr := (Finset.mem_Icc.mp rk.1.2).2
          omega, by
          have hr := (Finset.mem_Icc.mp rk.1.2).2
          omega, by
          have hr := (Finset.mem_Icc.mp rk.1.2).1
          omega⟩⟩,
       ⟨((n - 1 - rk.1.1) - 1 + 2 * rk.2.1, n - 1), ⟨
         by
           have hr := (Finset.mem_Icc.mp rk.1.2).2
           omega, by
           have hr := (Finset.mem_Icc.mp rk.1.2).2
           omega, by
           have hr := (Finset.mem_Icc.mp rk.1.2).2
           have hk := (Finset.mem_Icc.mp rk.2.2).2
           omega, by omega⟩⟩),
      by
        change 1 = 1 ∧ n - 1 - rk.1.1 ≤ n - 2 ∧ n - 1 = n - 1 ∧
          (n - 1 - rk.1.1) - 1 ≤ (n - 1 - rk.1.1) - 1 + 2 * rk.2.1 ∧
          ((n - 1 - rk.1.1) - 1 + 2 * rk.2.1) % 2 ≠
            (n - 1 - rk.1.1) % 2
        have hr := (Finset.mem_Icc.mp rk.1.2).1
        have hr' := (Finset.mem_Icc.mp rk.1.2).2
        omega⟩
    left_inv pq := by
      have ext_positions (p q : TwoDownPrefix n)
          (hfirst : p.val.1 = q.val.1) (hsecond : p.val.2 = q.val.2) : p = q := by
        rcases p with ⟨⟨a, b⟩, _⟩
        rcases q with ⟨⟨c, d⟩, _⟩
        change a = c at hfirst
        change b = d at hsecond
        subst c
        subst d
        rfl
      apply Subtype.ext
      apply Prod.ext
      · apply ext_positions
        · exact pq.2.1.symm
        · have hpge := pq.1.1.property.2.1
          have hpbound := pq.2.2.1
          change n - 1 - (n - 1 - pq.1.1.val.2) = pq.1.1.val.2
          omega
      · apply ext_positions
        · rcases pq.2 with ⟨_, hpbound, _, hlate, hpar⟩
          have hpge := pq.1.1.property.2.1
          have hqord := pq.1.2.property.2.2.1
          change (n - 1 - (n - 1 - pq.1.1.val.2)) - 1 +
            2 * ((pq.1.2.val.1 - (pq.1.1.val.2 - 1)) / 2) = pq.1.2.val.1
          omega
        · exact pq.2.2.2.1.symm
    right_inv rk := by
      have hrval : n - 1 - (n - 1 - rk.1.1) = rk.1.1 := by
        have hr := (Finset.mem_Icc.mp rk.1.2).2
        omega
      have hr : (⟨n - 1 - (n - 1 - rk.1.1), by
        simpa only [hrval] using rk.1.2⟩ :
        {r : ℕ // r ∈ Finset.Icc 1 (n - 4)}) = rk.1 := Subtype.ext hrval
      apply Sigma.ext hr
      apply (Subtype.heq_iff_coe_eq (by
        intro x
        simp only [Finset.mem_Icc, hrval])).2
      change ((n - 1 - rk.1.1) - 1 + 2 * rk.2.1 -
        ((n - 1 - rk.1.1) - 1)) / 2 = rk.2.1
      have hr' := (Finset.mem_Icc.mp rk.1.2).2
      omega
  }

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem sum_A_fibers (m : ℕ) :
    (∑ r ∈ Finset.Icc 1 m, (1 + r / 2)) = m + (m * m) / 4 := by
  induction m using Nat.twoStepInduction with
  | zero => simp
  | one => norm_num
  | more m ih _ =>
    rw [show m + 2 = (m + 1) + 1 by omega,
      Finset.sum_Icc_succ_top (by omega),
      Finset.sum_Icc_succ_top (by omega), ih]
    have hs : (m + 1) / 2 + (m + 2) / 2 = m + 1 := by omega
    have hsq : (m + 2) * (m + 2) = m * m + 4 * (m + 1) := by ring
    rw [hsq]
    omega

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem canonicalA_card (n : ℕ) (hn : 4 ≤ n) :
    Nat.card {pq : TwoDownPrefix n × TwoDownPrefix n // canonicalA pq.1 pq.2} =
      (n - 4) + ((n - 4) * (n - 4)) / 4 := by
  have hfiber (r : {r : ℕ // r ∈ Finset.Icc 1 (n - 4)}) :
      Nat.card {k : ℕ // k ∈ Finset.Icc 0 (r.1 / 2)} = 1 + r.1 / 2 := by
    change Nat.card (Finset.Icc 0 (r.1 / 2) : Set ℕ) = 1 + r.1 / 2
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, Nat.card_Icc]
    omega
  calc
    Nat.card {pq : TwoDownPrefix n × TwoDownPrefix n // canonicalA pq.1 pq.2} =
        Nat.card (Σ r : {r : ℕ // r ∈ Finset.Icc 1 (n - 4)},
          {k : ℕ // k ∈ Finset.Icc 0 (r.1 / 2)}) :=
      Nat.card_congr (canonicalAEquiv n hn)
    _ = ∑ r : {r : ℕ // r ∈ Finset.Icc 1 (n - 4)}, (1 + r.1 / 2) := by
      rw [Nat.card_sigma]
      apply Finset.sum_congr rfl
      intro r _
      exact hfiber r
    _ = ∑ r ∈ Finset.Icc 1 (n - 4), (1 + r / 2) := by
      exact Finset.sum_coe_sort (Finset.Icc 1 (n - 4)) (fun r => 1 + r / 2)
    _ = (n - 4) + ((n - 4) * (n - 4)) / 4 := sum_A_fibers (n - 4)

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem canonical_card (n : ℕ) (hn : 4 ≤ n) :
    Nat.card {pq : TwoDownPrefix n × TwoDownPrefix n // canonical pq.1 pq.2} =
      (n - 4) + ((n - 4) * (n - 4)) / 4 +
        ((n - 4) + 1) + (((n - 4) + 1) / 2) := by
  have hBresult : Nat.card
      {pq : TwoDownPrefix n × TwoDownPrefix n // canonicalB pq.1 pq.2} =
      (n - 4) + 1 := by
    rw [Nat.card_congr (canonicalBEquiv n hn)]
    change Nat.card (Finset.Icc 2 (n - 2) : Set ℕ) = (n - 4) + 1
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, Nat.card_Icc]
    omega
  have hCresult : Nat.card
      {pq : TwoDownPrefix n × TwoDownPrefix n // canonicalC pq.1 pq.2} =
      ((n - 4) + 1) / 2 := by
    rw [Nat.card_congr (canonicalCEquiv n hn)]
    change Nat.card (Finset.Icc 1 ((n - 3) / 2) : Set ℕ) = ((n - 4) + 1) / 2
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, Nat.card_Icc]
    omega
  classical
  let A : Finset (TwoDownPrefix n × TwoDownPrefix n) :=
    Finset.univ.filter (fun pq => canonicalA pq.1 pq.2)
  let B : Finset (TwoDownPrefix n × TwoDownPrefix n) :=
    Finset.univ.filter (fun pq => canonicalB pq.1 pq.2)
  let C : Finset (TwoDownPrefix n × TwoDownPrefix n) :=
    Finset.univ.filter (fun pq => canonicalC pq.1 pq.2)
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro pq hpA hpB
    have hA := (Finset.mem_filter.mp hpA).2
    have hB := (Finset.mem_filter.mp hpB).2
    simp only [canonicalA, canonicalB] at hA hB
    have hpge := pq.1.property.2.1
    omega
  have hAC : Disjoint A C := by
    apply Finset.disjoint_left.mpr
    intro pq hpA hpC
    have hA := (Finset.mem_filter.mp hpA).2
    have hC := (Finset.mem_filter.mp hpC).2
    simp only [canonicalA, canonicalC] at hA hC
    have hpge := pq.1.property.2.1
    omega
  have hBC : Disjoint B C := by
    apply Finset.disjoint_left.mpr
    intro pq hpB hpC
    have hB := (Finset.mem_filter.mp hpB).2
    have hC := (Finset.mem_filter.mp hpC).2
    simp only [canonicalB, canonicalC] at hB hC
    have hpge := pq.1.property.2.1
    omega
  have hABC : Disjoint (A ∪ B) C := by
    apply Finset.disjoint_left.mpr
    intro pq hpAB hpC
    rcases Finset.mem_union.mp hpAB with hpA | hpB
    · exact (Finset.disjoint_left.mp hAC) hpA hpC
    · exact (Finset.disjoint_left.mp hBC) hpB hpC
  have hcanon : (Finset.univ.filter (fun pq : TwoDownPrefix n × TwoDownPrefix n =>
      canonical pq.1 pq.2)) = (A ∪ B) ∪ C := by
    ext pq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    simp only [A, B, C, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [canonical, or_assoc]
  have hAcard : A.card =
      Nat.card {pq : TwoDownPrefix n × TwoDownPrefix n // canonicalA pq.1 pq.2} := by
    simp only [A, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hBcard : B.card =
      Nat.card {pq : TwoDownPrefix n × TwoDownPrefix n // canonicalB pq.1 pq.2} := by
    simp only [B, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hCcard : C.card =
      Nat.card {pq : TwoDownPrefix n × TwoDownPrefix n // canonicalC pq.1 pq.2} := by
    simp only [C, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hcanon,
    Finset.card_union_of_disjoint hABC, Finset.card_union_of_disjoint hAB,
    hAcard, hBcard, hCcard, canonicalA_card n hn, hBresult,
    hCresult]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem canonical_count_arithmetic (m : ℕ) :
    4 * (m + (m * m) / 4 + (m + 1) + (m + 1) / 2) + 20 =
      (m + 4) * (m + 4) + 2 * (m + 4) + (m + 4) % 2 := by
  have hsq : (m * m) % 4 = m % 2 := by
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · have hm : m = 2 * (m / 2) := by omega
      rw [hm]
      ring_nf
      omega
    · have hm : m = 2 * (m / 2) + 1 := by omega
      rw [hm]
      ring_nf
      omega
  have hdiv := Nat.div_add_mod (m * m) 4
  have hhalf : 2 * ((m + 1) / 2) = m + m % 2 := by omega
  have hmod : (m + 4) % 2 = m % 2 := by omega
  rw [hmod]
  nlinarith


end D5.S3.Combinatorics.SemiMeanderSecondDiagonal
