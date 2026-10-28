/- GID: D5/S3/Combinatorics/Graph/Domination/TrapezohedralApexClassification
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/TrapezohedralApexClassification
   mirror-E: none(waiver:unbounded-constructive-proof)
   anchors: []
   utility: none
   digest: Actual connected minimal dominating sets have exactly one apex and one opposite label. -/

import D5.S3.Combinatorics.Graph.Domination.TrapezohedralMinimalDomination

/-! Apex classification for the original labelled subsets. Connectivity is used
only for the selected induced subgraph; all-subset minimality remains independent. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Domination.TrapezohedralApexClassification

open D5.S3.Combinatorics.Graph.Domination.TrapezohedralMinimalDomination

open Vertex

private theorem selected_neighbor {n : ℕ} {S : Set (Vertex n)}
    (hc : ((graph n).induce S).Connected) {x y : Vertex n}
    (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y) :
    ∃ z ∈ S, (graph n).Adj x z := by
  have hne' : (⟨x, hx⟩ : S) ≠ ⟨y, hy⟩ := by
    intro h
    exact hne (congrArg Subtype.val h)
  obtain ⟨⟨z, hz⟩, hadj⟩ := (hc ⟨x, hx⟩ ⟨y, hy⟩).nonempty_neighborSet_left hne'
  exact ⟨z, hz, hadj⟩

private theorem admissible_private {n : ℕ} {S : Set (Vertex n)} (hS : Admissible S) :
    ∀ s ∈ S, ∃ w, ClosedPrivate (graph n) S s w :=
  ((minimalDominating_iff_private (graph n) S).mp
    ((minimalDominating_iff_proper (graph n) S).mpr hS.1)).2

private theorem not_both_apices {n : ℕ} {S : Set (Vertex n)} (hS : Admissible S)
    (ha : alpha ∈ S) (hb : beta ∈ S) : False := by
  have hd : (graph n).IsDominating ({alpha, beta} : Set (Vertex n)) := by
    intro v
    cases v with
    | alpha => exact Or.inl (by simp)
    | beta => exact Or.inl (by simp)
    | a i => exact Or.inr ⟨alpha, by simp, trivial⟩
    | b i => exact Or.inr ⟨beta, by simp, trivial⟩
  have hsub : S ⊆ ({alpha, beta} : Set (Vertex n)) :=
    ((minimalDominating_iff_proper (graph n) S).mpr hS.1).2 _
      (by intro x hx; rcases hx with rfl | rfl <;> assumption) hd
  obtain ⟨v, hv, hadj⟩ := selected_neighbor hS.2 ha hb (by simp)
  have hv' := hsub hv
  cases v <;> simp_all [graph, adjacent] <;> aesop

/-- The selected alpha forces a unique selected b-label. -/
theorem alpha_unique_opposite {n : ℕ} {S : Set (Vertex n)} (hS : Admissible S)
    (ha : alpha ∈ S) (hb : beta ∉ S) : ∃! j : Fin n, b j ∈ S := by
  obtain ⟨j, hj⟩ : ∃ j : Fin n, b j ∈ S := by
    rcases hS.1.1 beta with h | ⟨v, hv, hadj⟩
    · exact False.elim (hb h)
    · cases v <;> simp_all [graph, adjacent] <;> aesop
  refine ⟨j, hj, ?_⟩
  intro i hi
  obtain ⟨v, hv, hadj⟩ := selected_neighbor hS.2 hi ha (by simp)
  obtain ⟨k, hk, hki⟩ : ∃ k : Fin n, a k ∈ S ∧ (graph n).Adj (b i) (a k) := by
    cases v with
    | alpha => exact False.elim hadj
    | beta => exact False.elim (hb hv)
    | b l => exact False.elim hadj
    | a k => exact ⟨k, hv, hadj⟩
  obtain ⟨w, hw, hu⟩ := admissible_private hS (b i) hi
  cases w with
  | alpha => simp [graph, adjacent] at hw
  | beta =>
    have heq := hu (b j) hj (Or.inr trivial)
    exact (Vertex.b.inj heq).symm
  | a l =>
    have heq := hu alpha ha (Or.inr trivial)
    cases heq
  | b l =>
    have hli : l = i := by simpa [graph, adjacent] using hw
    subst l
    have heq := hu (a k) hk (Or.inr hki)
    cases heq

private theorem fin_not_covered_by_pair {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    ¬ (∀ k : Fin n, k = i ∨ k = j) := by
  classical
  intro h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {i, j} := by
    intro k _
    simpa using h k
  have hc := Finset.card_le_card hsub
  have hp : ({i, j} : Finset (Fin n)).card ≤ 2 := by
    calc
      _ ≤ ({j} : Finset (Fin n)).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  omega

private theorem no_apex_not_unique_b {n : ℕ} (hn : 3 ≤ n) {S : Set (Vertex n)}
    (hS : Admissible S) (ha : alpha ∉ S)
    (j : Fin n) (hj : b j ∈ S) : ∃ k : Fin n, b k ∈ S ∧ k ≠ j := by
  classical
  by_contra! hnone
  have huniq : ∀ k : Fin n, b k ∈ S → k = j := by
    intro k hk
    exact hnone k hk
  apply fin_not_covered_by_pair hn j (finRotate n j)
  intro i
  have hselected : a i ∈ S → i = j ∨ i = finRotate n j := by
    intro hi
    obtain ⟨v, hv, hadj⟩ := selected_neighbor hS.2 hi hj (by simp)
    cases v with
    | alpha => exact False.elim (ha hv)
    | beta => exact False.elim hadj
    | a k => exact False.elim hadj
    | b k => simpa only [graph, adjacent, huniq k hv] using hadj
  rcases hS.1.1 (a i) with hi | ⟨v, hv, hadj⟩
  · exact hselected hi
  · cases v with
    | alpha => exact False.elim (ha hv)
    | beta => exact False.elim hadj
    | a k => exact False.elim hadj
    | b k => simpa only [graph, adjacent, huniq k hv] using hadj

private theorem no_apex_not_unique_a {n : ℕ} (hn : 3 ≤ n) {S : Set (Vertex n)}
    (hS : Admissible S) (hb : beta ∉ S)
    (i : Fin n) (hi : a i ∈ S) : ∃ k : Fin n, a k ∈ S ∧ k ≠ i := by
  classical
  by_contra! hnone
  have huniq : ∀ k : Fin n, a k ∈ S → k = i := by
    intro k hk
    exact hnone k hk
  apply fin_not_covered_by_pair hn i ((finRotate n).symm i)
  intro j
  have convert : (graph n).Adj (b j) (a i) →
      j = i ∨ j = (finRotate n).symm i := by
    rintro (h | h)
    · exact Or.inl h.symm
    · right
      exact ((finRotate n).symm_apply_eq.mpr h).symm
  have hselected : b j ∈ S → j = i ∨ j = (finRotate n).symm i := by
    intro hj
    obtain ⟨v, hv, hadj⟩ := selected_neighbor hS.2 hj hi (by simp)
    cases v with
    | alpha => exact False.elim hadj
    | beta => exact False.elim (hb hv)
    | b k => exact False.elim hadj
    | a k => apply convert; simpa only [graph, adjacent, huniq k hv] using hadj
  rcases hS.1.1 (b j) with hj | ⟨v, hv, hadj⟩
  · exact hselected hj
  · cases v with
    | alpha => exact False.elim hadj
    | beta => exact False.elim (hb hv)
    | b k => exact False.elim hadj
    | a k => apply convert; simpa only [graph, adjacent, huniq k hv] using hadj

private theorem b_has_unique_selected_a {n : ℕ} {S : Set (Vertex n)}
    (hS : Admissible S) (p q : Fin n) (hp : b p ∈ S) (hq : b q ∈ S) (hpq : p ≠ q)
    (j i k : Fin n) (hj : b j ∈ S) (hi : a i ∈ S) (hk : a k ∈ S)
    (hji : (graph n).Adj (b j) (a i)) (hjk : (graph n).Adj (b j) (a k)) : i = k := by
  by_contra hik
  obtain ⟨w, hw, hu⟩ := admissible_private hS (b j) hj
  cases w with
  | alpha => simp [graph, adjacent] at hw
  | beta =>
    have heqp := Vertex.b.inj (hu (b p) hp (Or.inr trivial))
    have heqq := Vertex.b.inj (hu (b q) hq (Or.inr trivial))
    exact hpq (heqp.trans heqq.symm)
  | b l =>
    have hlj : l = j := by simpa [graph, adjacent] using hw
    subst l
    have heq := hu (a i) hi (Or.inr hji)
    cases heq
  | a l =>
    have hl : l = j ∨ l = finRotate n j := by simpa [graph, adjacent] using hw
    have hili : i = j ∨ i = finRotate n j := hji
    have hilk : k = j ∨ k = finRotate n j := hjk
    have hlik : l = i ∨ l = k := by aesop
    have hlS : a l ∈ S := hlik.elim (fun h => h ▸ hi) (fun h => h ▸ hk)
    have heq := hu (a l) hlS (Or.inl rfl)
    cases heq

private theorem no_neither_apex {n : ℕ} (hn : 3 ≤ n) {S : Set (Vertex n)}
    (hS : Admissible S) (ha : alpha ∉ S) (hb : beta ∉ S) : False := by
  obtain ⟨i, hi⟩ : ∃ i : Fin n, a i ∈ S := by
    rcases hS.1.1 alpha with h | ⟨v, hv, hadj⟩
    · exact False.elim (ha h)
    · cases v <;> simp_all [graph, adjacent] <;> aesop
  obtain ⟨j, hj⟩ : ∃ j : Fin n, b j ∈ S := by
    rcases hS.1.1 beta with h | ⟨v, hv, hadj⟩
    · exact False.elim (hb h)
    · cases v <;> simp_all [graph, adjacent] <;> aesop
  obtain ⟨k, hk, hki⟩ := no_apex_not_unique_a hn hS hb i hi
  obtain ⟨l, hl, hlj⟩ := no_apex_not_unique_b hn hS ha j hj
  let P : S → Prop := fun x => x.val = a i ∨ (graph n).Adj (a i) x.val
  have hstep : ∀ x y : S, P x → ((graph n).induce S).Adj x y → P y := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ (heq | hadj) hxy
    · exact Or.inr (heq ▸ hxy)
    · cases x with
      | alpha => exact False.elim (ha hx)
      | beta => exact False.elim (hb hx)
      | a t => exact False.elim hadj
      | b t =>
        cases y with
        | alpha => exact False.elim (ha hy)
        | beta => exact False.elim (hb hy)
        | b u => exact False.elim hxy
        | a u =>
          have hui := b_has_unique_selected_a hS j l hj hl (Ne.symm hlj)
            t u i hx hy hi hxy hadj.symm
          exact Or.inl (congrArg a hui)
  have hw : ∀ {x y : S}, ((graph n).induce S).Walk x y → P x → P y := by
    intro x y w
    induction w with
    | nil => exact id
    | @cons x y z hadj w ih => exact fun h => ih (hstep x y h hadj)
  obtain ⟨w⟩ := hS.2 ⟨a i, hi⟩ ⟨a k, hk⟩
  have hend := hw w (Or.inl rfl)
  rcases hend with heq | hadj
  · exact hki (Vertex.a.inj heq)
  · exact False.elim hadj

/-- Every actual admissible subset contains exactly one of the two apices. -/
theorem exactly_one_apex {n : ℕ} (hn : 3 ≤ n) {S : Set (Vertex n)} (hS : Admissible S) :
    (alpha ∈ S ∧ beta ∉ S) ∨ (beta ∈ S ∧ alpha ∉ S) := by
  classical
  by_cases ha : alpha ∈ S
  · exact Or.inl ⟨ha, fun hb => not_both_apices hS ha hb⟩
  · right
    exact ⟨Classical.byContradiction (fun hb => no_neither_apex hn hS ha hb), ha⟩

/-- Reading the unique opposite label and selected same-type labels reconstructs S. -/
theorem alpha_reconstruction {n : ℕ} {S : Set (Vertex n)} (hS : Admissible S)
    (ha : alpha ∈ S) (hb : beta ∉ S) :
    ∃! j : Fin n, S = alphaSet j {i | a i ∈ S} := by
  obtain ⟨j, hj, huniq⟩ := alpha_unique_opposite hS ha hb
  have heq : S = alphaSet j {i | a i ∈ S} := by
    ext v
    cases v with
    | alpha => change (alpha ∈ S ↔ True); simp [ha]
    | beta => change (beta ∈ S ↔ False); simp [hb]
    | a i => rfl
    | b i => exact ⟨huniq i, fun h => h ▸ hj⟩
  refine ⟨j, heq, ?_⟩
  intro k hk
  apply huniq k
  rw [hk]
  exact rfl

end D5.S3.Combinatorics.Graph.Domination.TrapezohedralApexClassification
