/- GID: D5/S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Ring.Finset, mathlib/module/Mathlib.Data.Fintype.BigOperators]
   utility: none
   digest: Literal labeled-graph avoidance and its allowed-vertex state yield Barker's recurrence. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Crossing- and nesting-free labeled graphs

This module proves Colin Barker's 2019 OEIS A326244 conjecture.  Vertices are
linearly ordered by `Fin n`; an edge is represented by its increasing ordered
pair.  The counted object is therefore the literal labeled simple graph from
the OEIS entry, rather than a surrogate encoding.

The proof removes the largest vertex and records the old vertices `c` for
which every edge ending to the right of `c` is incident with `c`.  Any subset
of these allowed vertices can be joined to the new maximum.  The next allowed
set has size `r + 1`, `2`, or `1` according as that subset is empty, a
singleton, or larger.  Three weighted counts then give the claimed recurrence.
-/

namespace D5.S1.Words.Patterns.NoncrossingNonnestingGraphRecurrence

open scoped Classical

/-- The two endpoint orders called crossing in OEIS A326244. -/
def Crossing {n : ℕ} (e f : Fin n × Fin n) : Prop :=
  (e.1 < f.1 ∧ f.1 < e.2 ∧ e.2 < f.2) ∨
    (f.1 < e.1 ∧ e.1 < f.2 ∧ f.2 < e.2)

/-- The two endpoint orders called nesting in OEIS A326244. -/
def Nesting {n : ℕ} (e f : Fin n × Fin n) : Prop :=
  (e.1 < f.1 ∧ f.1 < f.2 ∧ f.2 < e.2) ∨
    (f.1 < e.1 ∧ e.1 < e.2 ∧ e.2 < f.2)

/-- A literal simple graph whose increasing edges neither cross nor nest. -/
def IsAvoiding {n : ℕ} (E : Finset (Fin n × Fin n)) : Prop :=
  (∀ e ∈ E, e.1 < e.2) ∧
    ∀ e ∈ E, ∀ f ∈ E, ¬ Crossing e f ∧ ¬ Nesting e f

/-- Number of labeled `n`-vertex simple graphs with neither pattern. -/
noncomputable def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun E : Finset (Fin n × Fin n) => IsAvoiding E)).card

private abbrev Edge (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}

private def GoodEdges {n : ℕ} (E : Finset (Edge n)) : Prop :=
  ∀ e ∈ E, ∀ f ∈ E, ¬ Crossing e.1 f.1 ∧ ¬ Nesting e.1 f.1

private abbrev GoodGraph (n : ℕ) := {E : Finset (Edge n) // GoodEdges E}

private def allowedEdges {n : ℕ} (E : Finset (Edge n)) : Finset (Fin n) :=
  Finset.univ.filter fun c =>
    ∀ e ∈ E, c < e.1.2 → e.1.1 = c ∨ e.1.2 = c

private def Allowed {n : ℕ} (G : GoodGraph n) : Finset (Fin n) :=
  allowedEdges G.1

private def edgeSuccEquiv (n : ℕ) : Edge (n + 1) ≃ Edge n ⊕ Fin n where
  toFun e :=
    if hright : e.1.2 = Fin.last n then
      Sum.inr (Fin.castPred e.1.1 (by
        exact (Fin.lt_last_iff_ne_last.mp (hright ▸ e.2))))
    else
      Sum.inl ⟨(Fin.castPred e.1.1 (by
        exact (Fin.lt_last_iff_ne_last.mp
          (e.2.trans (Fin.lt_last_iff_ne_last.mpr hright)))),
        Fin.castPred e.1.2 hright), e.2⟩
  invFun
    | Sum.inl e => ⟨(e.1.1.castSucc, e.1.2.castSucc), e.2⟩
    | Sum.inr c => ⟨(c.castSucc, Fin.last n), Fin.castSucc_lt_last c⟩
  left_inv e := by
    by_cases hright : e.1.2 = Fin.last n
    · simp [hright]
      apply Subtype.ext
      apply Prod.ext
      · simp
      · exact hright.symm
    · simp [hright]
  right_inv e := by
    rcases e with e | c
    · simp
    · simp

private def splitEdges (n : ℕ) :
    Finset (Edge (n + 1)) ≃ Finset (Edge n) × Finset (Fin n) :=
  (Equiv.finsetCongr (edgeSuccEquiv n)).trans Finset.sumEquiv.toEquiv

private def extendEdges (E : Finset (Edge n)) (S : Finset (Fin n)) :
    Finset (Edge (n + 1)) :=
  (splitEdges n).symm (E, S)

private theorem goodEdges_extend_iff (E : Finset (Edge n)) (S : Finset (Fin n)) :
    GoodEdges (extendEdges E S) ↔ GoodEdges E ∧ S ⊆ allowedEdges E := by
  constructor
  · intro hgood
    constructor
    · intro e he f hf
      have hpair := hgood
        ((edgeSuccEquiv n).symm (Sum.inl e)) (by
          simpa [extendEdges, splitEdges] using he)
        ((edgeSuccEquiv n).symm (Sum.inl f)) (by
          simpa [extendEdges, splitEdges] using hf)
      simpa [Crossing, Nesting, edgeSuccEquiv] using hpair
    · intro c hc
      simp only [allowedEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      intro e he hce
      by_cases hac : e.1.1 = c
      · exact Or.inl hac
      by_cases hbc : e.1.2 = c
      · exact Or.inr hbc
      exfalso
      have hpair := hgood
        ((edgeSuccEquiv n).symm (Sum.inl e)) (by
          simpa [extendEdges, splitEdges] using he)
        ((edgeSuccEquiv n).symm (Sum.inr c)) (by
          simpa [extendEdges, splitEdges] using hc)
      simp [Crossing, Nesting, edgeSuccEquiv] at hpair
      omega
  · rintro ⟨hgood, hallowed⟩ x hx y hy
    cases hxcase : edgeSuccEquiv n x with
    | inl e =>
        have hxform : x = (edgeSuccEquiv n).symm (Sum.inl e) := by
          apply (edgeSuccEquiv n).injective
          simpa using hxcase
        subst x
        have he : e ∈ E := by
          simpa [extendEdges, splitEdges] using hx
        cases hycase : edgeSuccEquiv n y with
        | inl f =>
            have hyform : y = (edgeSuccEquiv n).symm (Sum.inl f) := by
              apply (edgeSuccEquiv n).injective
              simpa using hycase
            subst y
            have hf : f ∈ E := by
              simpa [extendEdges, splitEdges] using hy
            simpa [Crossing, Nesting, edgeSuccEquiv] using hgood e he f hf
        | inr c =>
            have hyform : y = (edgeSuccEquiv n).symm (Sum.inr c) := by
              apply (edgeSuccEquiv n).injective
              simpa using hycase
            subst y
            have hc : c ∈ S := by
              simpa [extendEdges, splitEdges] using hy
            have hcAllowed := hallowed hc
            simp only [allowedEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hcAllowed
            have hincident := hcAllowed e he
            simp [Crossing, Nesting, edgeSuccEquiv]
            constructor
            · constructor
              · intro hac
                by_contra hbc
                have := hincident (by omega)
                omega
              · intro _
                exact Fin.le_last _
            · constructor
              · intro _
                exact Fin.le_last _
              · by_contra hac
                have := hincident (by omega)
                omega
    | inr c =>
        have hxform : x = (edgeSuccEquiv n).symm (Sum.inr c) := by
          apply (edgeSuccEquiv n).injective
          simpa using hxcase
        subst x
        have hc : c ∈ S := by
          simpa [extendEdges, splitEdges] using hx
        cases hycase : edgeSuccEquiv n y with
        | inl f =>
            have hyform : y = (edgeSuccEquiv n).symm (Sum.inl f) := by
              apply (edgeSuccEquiv n).injective
              simpa using hycase
            subst y
            have hf : f ∈ E := by
              simpa [extendEdges, splitEdges] using hy
            have hcAllowed := hallowed hc
            simp only [allowedEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hcAllowed
            have hincident := hcAllowed f hf
            simp [Crossing, Nesting, edgeSuccEquiv]
            constructor
            · constructor
              · intro _
                exact Fin.le_last _
              · intro hac
                by_contra hbc
                have := hincident (by omega)
                omega
            · constructor
              · by_contra hac
                have := hincident (by omega)
                omega
              · intro _
                exact Fin.le_last _
        | inr d =>
            have hyform : y = (edgeSuccEquiv n).symm (Sum.inr d) := by
              apply (edgeSuccEquiv n).injective
              simpa using hycase
            subst y
            simp [Crossing, Nesting, edgeSuccEquiv]

private theorem castSucc_mem_allowedEdges_extend_iff
    (E : Finset (Edge n)) (S : Finset (Fin n)) (d : Fin n) :
    d.castSucc ∈ allowedEdges (extendEdges E S) ↔
      d ∈ allowedEdges E ∧ S ⊆ {d} := by
  constructor
  · intro hd
    simp only [allowedEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
    constructor
    · intro e he hde
      have hincident := hd ((edgeSuccEquiv n).symm (Sum.inl e)) (by
        simpa [extendEdges, splitEdges] using he) (by
        simpa [edgeSuccEquiv] using hde)
      simpa [edgeSuccEquiv] using hincident
    · intro c hc
      have hincident := hd ((edgeSuccEquiv n).symm (Sum.inr c)) (by
        simpa [extendEdges, splitEdges] using hc) (Fin.castSucc_lt_last d)
      have hcd : c = d := by
        simpa [edgeSuccEquiv] using hincident.resolve_right
          (fun h => Fin.castSucc_ne_last d h.symm)
      simpa using hcd
  · rintro ⟨hd, hsingle⟩
    simp only [allowedEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
    intro x hx hdx
    cases hxcase : edgeSuccEquiv n x with
    | inl e =>
        have hxform : x = (edgeSuccEquiv n).symm (Sum.inl e) := by
          apply (edgeSuccEquiv n).injective
          simpa using hxcase
        subst x
        have he : e ∈ E := by
          simpa [extendEdges, splitEdges] using hx
        have hincident := hd e he (by simpa [edgeSuccEquiv] using hdx)
        simpa [edgeSuccEquiv] using hincident
    | inr c =>
        have hxform : x = (edgeSuccEquiv n).symm (Sum.inr c) := by
          apply (edgeSuccEquiv n).injective
          simpa using hxcase
        subst x
        have hc : c ∈ S := by
          simpa [extendEdges, splitEdges] using hx
        have hcd : c = d := by simpa using hsingle hc
        exact Or.inl (by simp [edgeSuccEquiv, hcd])

private theorem last_mem_allowedEdges_extend (E : Finset (Edge n)) (S : Finset (Fin n)) :
    Fin.last n ∈ allowedEdges (extendEdges E S) := by
  simp only [allowedEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  intro e _ hlast
  exact (not_lt_of_ge (Fin.le_last e.1.2) hlast).elim

private theorem card_allowedEdges_extend (E : Finset (Edge n)) (S : Finset (Fin n))
    (hallowed : S ⊆ allowedEdges E) :
    (allowedEdges (extendEdges E S)).card =
      if S = ∅ then (allowedEdges E).card + 1 else if S.card = 1 then 2 else 1 := by
  by_cases hempty : S = ∅
  · have hset : allowedEdges (extendEdges E S) =
        insert (Fin.last n) ((allowedEdges E).map Fin.castSuccEmb) := by
      ext x
      cases x using Fin.lastCases with
      | last => simp [last_mem_allowedEdges_extend]
      | cast d =>
          rw [castSucc_mem_allowedEdges_extend_iff]
          simp [hempty]
    rw [hset, if_pos hempty, Finset.card_insert_of_notMem]
    · simp
    · simp
  · by_cases hone : S.card = 1
    · obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp hone
      have hcAllowed : c ∈ allowedEdges E := hallowed (by simp)
      have hset : allowedEdges (extendEdges E {c}) =
          {c.castSucc, Fin.last n} := by
        ext x
        cases x using Fin.lastCases with
        | last => simp [last_mem_allowedEdges_extend]
        | cast d =>
            rw [castSucc_mem_allowedEdges_extend_iff]
            simp only [Finset.singleton_subset_iff, Finset.mem_singleton,
              Finset.mem_insert, Fin.castSucc_inj, Fin.castSucc_ne_last, or_false]
            constructor
            · rintro ⟨_, hcd⟩
              exact hcd.symm
            · intro hdc
              subst d
              exact ⟨hcAllowed, by simp⟩
      rw [hset]
      simp
    · have hset : allowedEdges (extendEdges E S) = {Fin.last n} := by
        ext x
        cases x using Fin.lastCases with
        | last => simp [last_mem_allowedEdges_extend]
        | cast d =>
            rw [castSucc_mem_allowedEdges_extend_iff]
            simp only [Finset.mem_singleton]
            constructor
            · rintro ⟨_, hsubset⟩
              have hcard : S.card ≤ 1 := by
                simpa using Finset.card_le_card hsubset
              exact (hone (Nat.le_antisymm hcard (Nat.one_le_iff_ne_zero.mpr
                (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hempty))))).elim
            · intro h
              exact (Fin.castSucc_ne_last d h).elim
      rw [hset, if_neg hempty, if_neg hone]
      simp

private def goodGraphEquivAvoiding (n : ℕ) :
    GoodGraph n ≃ {E : Finset (Fin n × Fin n) // IsAvoiding E} :=
  (((Equiv.finsetSubtypeComm (fun e : Fin n × Fin n => e.1 < e.2)).subtypeEquiv
    (p := GoodEdges) (q := fun E => IsAvoiding E.1)
    (fun E => by
      let valEmb : Edge n ↪ Fin n × Fin n := ⟨Subtype.val, Subtype.val_injective⟩
      change GoodEdges E ↔ IsAvoiding (E.map valEmb)
      constructor
      · intro hgood
        constructor
        · intro e he
          obtain ⟨e', _, rfl⟩ := Finset.mem_map.mp he
          exact e'.2
        intro e he f hf
        obtain ⟨e', he', rfl⟩ := Finset.mem_map.mp he
        obtain ⟨f', hf', rfl⟩ := Finset.mem_map.mp hf
        exact hgood e' he' f' hf'
      · rintro ⟨_, hgood⟩ e he f hf
        exact hgood e.1 (Finset.mem_map.mpr ⟨e, he, rfl⟩)
          f.1 (Finset.mem_map.mpr ⟨f, hf, rfl⟩)))).trans
    (Equiv.subtypeSubtypeEquivSubtype (fun h => h.1))

private def goodGraphSuccEquiv (n : ℕ) :
    GoodGraph (n + 1) ≃
      Σ G : GoodGraph n, {S : Finset (Fin n) // S ⊆ Allowed G} :=
  ((splitEdges n).subtypeEquiv (p := GoodEdges)
    (q := fun p => GoodEdges p.1 ∧ p.2 ⊆ allowedEdges p.1) (fun E => by
    simpa [extendEdges] using
      (goodEdges_extend_iff (E := (splitEdges n E).1) (S := (splitEdges n E).2)))).trans
    { toFun := fun p => ⟨⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩⟩
      invFun := fun p => ⟨(p.1.1, p.2.1), ⟨p.1.2, p.2.2⟩⟩
      left_inv := by rintro ⟨⟨E, S⟩, hE, hS⟩; rfl
      right_inv := by rintro ⟨⟨E, hE⟩, ⟨S, hS⟩⟩; rfl }

private noncomputable def X (n : ℕ) : ℕ := Fintype.card (GoodGraph n)

private noncomputable def Y (n : ℕ) : ℕ :=
  ∑ G : GoodGraph n, (Allowed G).card

private noncomputable def Z (n : ℕ) : ℕ :=
  ∑ G : GoodGraph n, 2 ^ (Allowed G).card

private theorem X_succ (n : ℕ) : X (n + 1) = Z n := by
  rw [X, Fintype.card_congr (goodGraphSuccEquiv n), Fintype.card_sigma, Z]
  apply Finset.sum_congr rfl
  intro G _
  rw [Fintype.card_subtype]
  change (Finset.univ.filter (fun S : Finset (Fin n) => S ⊆ Allowed G)).card = _
  rw [Finset.filter_subset_univ, Finset.card_powerset]

private theorem Y_succ (n : ℕ) : Y (n + 1) = 2 * Y n + Z n := by
  have hcard (G : GoodGraph n) (S : {S : Finset (Fin n) // S ⊆ Allowed G}) :
      (Allowed ((goodGraphSuccEquiv n).symm ⟨G, S⟩)).card =
        if S.1 = ∅ then (Allowed G).card + 1 else if S.1.card = 1 then 2 else 1 := by
    change (allowedEdges (extendEdges G.1 S.1)).card = _
    exact card_allowedEdges_extend G.1 S.1 S.2
  have hsum (G : GoodGraph n) :
      (∑ S : {S : Finset (Fin n) // S ⊆ Allowed G},
        if S.1 = ∅ then (Allowed G).card + 1 else if S.1.card = 1 then 2 else 1) =
        2 * (Allowed G).card + 2 ^ (Allowed G).card := by
    let A := Allowed G
    let r := A.card
    let p : Finset (Fin n) → Prop := fun S => S ⊆ A
    let f : Finset (Fin n) → ℕ := fun S =>
      if S = ∅ then r + 1 else if S.card = 1 then 2 else 1
    change (∑ S : Subtype p, f S.1) = 2 * r + 2 ^ r
    calc
      (∑ S : Subtype p, f S.1) =
          ∑ S ∈ Finset.univ.filter p, f S :=
        (Finset.sum_subtype (F := inferInstance) (Finset.univ.filter p)
          (fun S => by simp [p]) f).symm
      _ = ∑ S ∈ A.powerset, f S := by rw [Finset.filter_subset_univ]
      _ = 2 * r + 2 ^ r := by
        dsimp only [f]
        have hrewrite (S : Finset (Fin n)) :
            (if S = ∅ then r + 1 else if S.card = 1 then 2 else 1) =
              1 + (if S = ∅ then r else 0) + (if S.card = 1 then 1 else 0) := by
          by_cases hS0 : S = ∅
          · subst S
            simp [Nat.add_comm]
          by_cases hS1 : S.card = 1 <;> simp [hS0, hS1]
        simp_rw [hrewrite, Finset.sum_add_distrib]
        have hsingle :
            (∑ S ∈ A.powerset, if S.card = 1 then 1 else 0) = r := by
          rw [Finset.sum_boole]
          change (A.powerset.filter (fun S => S.card = 1)).card = r
          rw [← Finset.powersetCard_eq_filter, Finset.card_powersetCard]
          simp [r]
        simp [hsingle, Finset.card_powerset, r]
        omega
  rw [Y]
  calc
    (∑ H : GoodGraph (n + 1), (Allowed H).card) =
        ∑ p : (Σ G : GoodGraph n, {S : Finset (Fin n) // S ⊆ Allowed G}),
          (Allowed ((goodGraphSuccEquiv n).symm p)).card := by
      exact ((goodGraphSuccEquiv n).symm.sum_comp
        (fun H : GoodGraph (n + 1) => (Allowed H).card)).symm
    _ = ∑ G : GoodGraph n, (2 * (Allowed G).card + 2 ^ (Allowed G).card) := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro G _
      simp_rw [hcard]
      exact hsum G
    _ = 2 * Y n + Z n := by
      rw [Y, Z]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]

private theorem Z_succ (n : ℕ) : Z (n + 1) + 2 * X n = 2 * Y n + 4 * Z n := by
  have hcard (G : GoodGraph n) (S : {S : Finset (Fin n) // S ⊆ Allowed G}) :
      (Allowed ((goodGraphSuccEquiv n).symm ⟨G, S⟩)).card =
        if S.1 = ∅ then (Allowed G).card + 1 else if S.1.card = 1 then 2 else 1 := by
    change (allowedEdges (extendEdges G.1 S.1)).card = _
    exact card_allowedEdges_extend G.1 S.1 S.2
  have hfiber (G : GoodGraph n) :
      (∑ S : {S : Finset (Fin n) // S ⊆ Allowed G},
        2 ^ (if S.1 = ∅ then (Allowed G).card + 1 else
          if S.1.card = 1 then 2 else 1)) + 2 =
        2 * (Allowed G).card + 4 * 2 ^ (Allowed G).card := by
    let A := Allowed G
    let r := A.card
    let p : Finset (Fin n) → Prop := fun S => S ⊆ A
    let f : Finset (Fin n) → ℕ := fun S =>
      if S = ∅ then r + 1 else if S.card = 1 then 2 else 1
    change (∑ S : Subtype p, 2 ^ f S.1) + 2 = 2 * r + 4 * 2 ^ r
    have hsubsum : (∑ S : Subtype p, 2 ^ f S.1) =
        ∑ S ∈ A.powerset, 2 ^ f S := by
      calc
        (∑ S : Subtype p, 2 ^ f S.1) =
            ∑ S ∈ Finset.univ.filter p, 2 ^ f S :=
          (Finset.sum_subtype (F := inferInstance) (Finset.univ.filter p)
            (fun S => by simp [p]) (fun S => 2 ^ f S)).symm
        _ = ∑ S ∈ A.powerset, 2 ^ f S := by rw [Finset.filter_subset_univ]
    have hemptyTwo : (∑ S ∈ A.powerset, if S = ∅ then 2 else 0) = 2 := by
      simp
    have hrewrite (S : Finset (Fin n)) :
        2 ^ f S + (if S = ∅ then 2 else 0) =
          2 + (if S = ∅ then 2 * 2 ^ r else 0) +
            (if S.card = 1 then 2 else 0) := by
      dsimp only [f]
      by_cases hS0 : S = ∅
      · subst S
        simp [pow_succ]
        omega
      by_cases hS1 : S.card = 1 <;> simp [hS0, hS1]
    have hsingleTwo :
        (∑ S ∈ A.powerset, if S.card = 1 then 2 else 0) = 2 * r := by
      have hpoint (S : Finset (Fin n)) :
          (if S.card = 1 then 2 else 0) = 2 * (if S.card = 1 then 1 else 0) := by
        by_cases hS : S.card = 1 <;> simp [hS]
      simp_rw [hpoint, ← Finset.mul_sum, Finset.sum_boole]
      change 2 * (A.powerset.filter (fun S => S.card = 1)).card = 2 * r
      rw [← Finset.powersetCard_eq_filter, Finset.card_powersetCard]
      simp [r]
    calc
      (∑ S : Subtype p, 2 ^ f S.1) + 2 =
          (∑ S ∈ A.powerset, 2 ^ f S) + 2 := by rw [hsubsum]
      _ = (∑ S ∈ A.powerset, 2 ^ f S) +
          ∑ S ∈ A.powerset, (if S = ∅ then 2 else 0) := by rw [hemptyTwo]
      _ = ∑ S ∈ A.powerset, (2 ^ f S + (if S = ∅ then 2 else 0)) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ S ∈ A.powerset,
          (2 + (if S = ∅ then 2 * 2 ^ r else 0) +
            (if S.card = 1 then 2 else 0)) := by
        exact Finset.sum_congr rfl fun S _ => hrewrite S
      _ = 2 * r + 4 * 2 ^ r := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp [hsingleTwo, Finset.card_powerset, r]
        omega
  calc
    Z (n + 1) + 2 * X n =
        (∑ G : GoodGraph n,
          ∑ S : {S : Finset (Fin n) // S ⊆ Allowed G},
            2 ^ (if S.1 = ∅ then (Allowed G).card + 1 else
              if S.1.card = 1 then 2 else 1)) + 2 * Fintype.card (GoodGraph n) := by
      congr 1
      rw [Z]
      calc
        (∑ H : GoodGraph (n + 1), 2 ^ (Allowed H).card) =
            ∑ p : (Σ G : GoodGraph n, {S : Finset (Fin n) // S ⊆ Allowed G}),
              2 ^ (Allowed ((goodGraphSuccEquiv n).symm p)).card := by
          exact ((goodGraphSuccEquiv n).symm.sum_comp
            (fun H : GoodGraph (n + 1) => 2 ^ (Allowed H).card)).symm
        _ = ∑ G : GoodGraph n,
            ∑ S : {S : Finset (Fin n) // S ⊆ Allowed G},
              2 ^ (if S.1 = ∅ then (Allowed G).card + 1 else
                if S.1.card = 1 then 2 else 1) := by
          rw [Fintype.sum_sigma]
          apply Finset.sum_congr rfl
          intro G _
          simp_rw [hcard]
    _ = ∑ G : GoodGraph n, (2 * (Allowed G).card + 4 * 2 ^ (Allowed G).card) := by
      have hconst : 2 * Fintype.card (GoodGraph n) = ∑ _ : GoodGraph n, 2 := by
        simp [Nat.mul_comm]
      rw [hconst, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro G _
      exact hfiber G
    _ = 2 * Y n + 4 * Z n := by
      rw [Y, Z, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]

private theorem X_recurrence (n : ℕ) :
    X (n + 3) + 8 * X (n + 1) = 6 * X (n + 2) + 4 * X n := by
  have hx0 : (X (n + 1) : ℤ) = Z n := by exact_mod_cast X_succ n
  have hx1 : (X (n + 2) : ℤ) = Z (n + 1) := by
    exact_mod_cast X_succ (n + 1)
  have hx2 : (X (n + 3) : ℤ) = Z (n + 2) := by
    exact_mod_cast X_succ (n + 2)
  have hy0 : (Y (n + 1) : ℤ) = 2 * Y n + Z n := by exact_mod_cast Y_succ n
  have hz0 : (Z (n + 1) : ℤ) + 2 * X n = 2 * Y n + 4 * Z n := by
    exact_mod_cast Z_succ n
  have hz1 : (Z (n + 2) : ℤ) + 2 * X (n + 1) =
      2 * Y (n + 1) + 4 * Z (n + 1) := by
    exact_mod_cast Z_succ (n + 1)
  have hrecZ : (X (n + 3) : ℤ) + 8 * X (n + 1) =
      6 * X (n + 2) + 4 * X n := by
    omega
  exact_mod_cast hrecZ

/-- Barker's conjectured third-order recurrence for OEIS A326244. -/
theorem barker_a326244 : ∀ n, 2 < n →
    (a n : ℤ) = 6 * a (n - 1) - 8 * a (n - 2) + 4 * a (n - 3) := by
  have ha (k : ℕ) : a k = X k := by
    calc
      a k = Fintype.card {E : Finset (Fin k × Fin k) // IsAvoiding E} := by
        rw [a, Fintype.card_subtype]
      _ = Fintype.card (GoodGraph k) :=
        (Fintype.card_congr (goodGraphEquivAvoiding k)).symm
      _ = X k := rfl
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := by
    exact ⟨n - 3, by omega⟩
  have h1 : m + 3 - 1 = m + 2 := by omega
  have h2 : m + 3 - 2 = m + 1 := by omega
  have h3 : m + 3 - 3 = m := by omega
  rw [h1, h2, h3, ha, ha, ha, ha]
  have hrec := X_recurrence m
  have hrecZ :
      (X (m + 3) : ℤ) + 8 * X (m + 1) = 6 * X (m + 2) + 4 * X m := by
    exact_mod_cast hrec
  omega

#print axioms barker_a326244

end D5.S1.Words.Patterns.NoncrossingNonnestingGraphRecurrence
