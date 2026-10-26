/- GID: D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/MutualVisibility/Connectivity
   mirror-E: none(waiver:no-computational-evidence)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: none
   digest: Finite separator connectivity is bounded by minimum degree and has the complete-graph convention. -/

import D5.S3.Combinatorics.Graph.MutualVisibility.Model

/-! Original-host mutual visibility and its finite reconfiguration geometry. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.MutualVisibility

open SimpleGraph

variable {W : Type*} [DecidableEq W]

/-- Reachability inside one actual induced graph after deleting the given cut. -/
def CutReach (G : SimpleGraph W) (C : Finset W) (s t : W) : Prop :=
  ∃ hs : s ∉ C, ∃ ht : t ∉ C,
    (G.induce {v | v ∉ C}).Reachable ⟨s, hs⟩ ⟨t, ht⟩

private theorem cutReach_refl (G : SimpleGraph W) {C : Finset W} {s : W}
    (hs : s ∉ C) : CutReach G C s s := ⟨hs, hs, Reachable.refl _⟩

theorem cutReach_trans {G : SimpleGraph W} {C : Finset W} {s t u : W}
    (hst : CutReach G C s t) (htu : CutReach G C t u) : CutReach G C s u := by
  obtain ⟨hs, ht, hst⟩ := hst
  obtain ⟨_, hu, htu⟩ := htu
  exact ⟨hs, hu, hst.trans htu⟩

theorem cutReach_step {G : SimpleGraph W} {C : Finset W} {s t u : W}
    (hst : CutReach G C s t) (htu : G.Adj t u) (hu : u ∉ C) : CutReach G C s u := by
  obtain ⟨hs, ht, hst⟩ := hst
  exact ⟨hs, hu, hst.trans (show (G.induce {v | v ∉ C}).Adj ⟨t, ht⟩ ⟨u, hu⟩ from htu).reachable⟩

theorem cutReach_two_step_payment {G : SimpleGraph W} {C : Finset W} {s t u v : W}
    (hs : CutReach G C s t) (htu : G.Adj t u) (huv : G.Adj u v)
    (hv : ¬ CutReach G C s v) : u ∈ C ∨ v ∈ C := by
  by_cases huC : u ∈ C
  · exact Or.inl huC
  · right
    by_contra hvC
    exact hv (cutReach_step (cutReach_step hs htu huC) huv hvC)

/-- A finite chain from a surviving component to its outside must meet the actual cut. -/
theorem cutReach_chain_payment {G : SimpleGraph W} {C : Finset W} {s : W}
    (f : ℕ → W) {a b : ℕ} (hab : a ≤ b)
    (hstep : ∀ k, a ≤ k → k < b → G.Adj (f k) (f (k + 1)))
    (hstart : CutReach G C s (f b) ∨ f b ∈ C)
    (hend : ¬ CutReach G C s (f a)) :
    ∃ k, a ≤ k ∧ k ≤ b ∧ f k ∈ C := by
  classical
  rcases hstart with hs | hcut
  · by_contra hn
    have hnot : ∀ k, a ≤ k → k ≤ b → f k ∉ C := by
      intro k ha hb hc
      exact hn ⟨k, ha, hb, hc⟩
    have hrec : ∀ k, a ≤ k → k ≤ b → CutReach G C (f a) (f k) := by
      intro k hak
      induction k, hak using Nat.le_induction with
      | base =>
          intro _
          exact cutReach_refl G (hnot a le_rfl hab)
      | succ k hak ih =>
          intro hkb
          exact cutReach_step (ih (by omega)) (hstep k hak (by omega))
            (hnot (k + 1) (by omega) hkb)
    obtain ⟨hfa, hfb, hr⟩ := hrec b hab le_rfl
    obtain ⟨hs, _, hsr⟩ := hs
    exact hend ⟨hs, hfa, hsr.trans hr.symm⟩
  · exact ⟨b, hab, le_rfl, hcut⟩

variable [Fintype W]

private theorem separators_nonempty (G : SimpleGraph W) :
    ({k | ∃ C : Finset W, C.card = k ∧ Separates G C} : Set ℕ).Nonempty := by
  exact ⟨_, Finset.univ, rfl, Or.inl (by simp)⟩

private theorem connectivity_attained (G : SimpleGraph W) :
    ∃ C : Finset W, C.card = vertexConnectivity G ∧ Separates G C :=
  Nat.sInf_mem (separators_nonempty G)

private theorem connectivity_le_cut (G : SimpleGraph W) {C : Finset W}
    (hC : Separates G C) : vertexConnectivity G ≤ C.card :=
  Nat.sInf_le ⟨C, rfl, hC⟩

private theorem connectivity_le_degree (G : SimpleGraph W) [DecidableRel G.Adj] (v : W) :
    vertexConnectivity G ≤ G.degree v := by
  let C := G.neighborFinset v
  have hv : v ∉ C := by simp [C]
  have hC : Separates G C := by
    by_cases hs : (Finset.univ \ C).card ≤ 1
    · exact Or.inl hs
    · right
      intro hc
      have hv' : v ∈ Finset.univ \ C := by simp [hv]
      obtain ⟨u, hu, huv⟩ := Finset.exists_mem_ne (by omega : 1 < (Finset.univ \ C).card) v
      have huC : u ∉ C := (Finset.mem_sdiff.mp hu).2
      let v' : {x : W | x ∉ C} := ⟨v, hv⟩
      let u' : {x : W | x ∉ C} := ⟨u, huC⟩
      have hne : v' ≠ u' := fun h => huv (congrArg Subtype.val h).symm
      have hr := hc v' u'
      obtain ⟨z, hz⟩ := hr.nonempty_neighborSet_left hne
      exact z.property (by simpa [C] using hz)
  simpa [C] using connectivity_le_cut G hC

theorem connectivity_le_minDegree (G : SimpleGraph W) [DecidableRel G.Adj]
    [Nonempty W] : vertexConnectivity G ≤ G.minDegree := by
  obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  rw [hv]
  exact connectivity_le_degree G v

theorem minDegree_le_connectivity (G : SimpleGraph W) [DecidableRel G.Adj]
    [Nonempty W]
    (h : ∀ C : Finset W, C.card < G.minDegree →
      (G.induce {v | v ∉ C}).Preconnected) :
    G.minDegree ≤ vertexConnectivity G := by
  obtain ⟨C, hcard, hsep⟩ := connectivity_attained G
  by_contra hlt
  have hlt' : C.card < G.minDegree := by omega
  have hleft : 1 < (Finset.univ \ C).card := by
    have htotal := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ C)
    have hb := G.minDegree_lt_card
    simp only [Finset.card_univ] at htotal
    omega
  exact hsep.elim (by omega) (fun hn => hn (h C hlt'))

private theorem connectivity_complete [Nonempty W] :
    vertexConnectivity (⊤ : SimpleGraph W) = Fintype.card W - 1 := by
  classical
  obtain ⟨v⟩ := (inferInstance : Nonempty W)
  apply le_antisymm
  · simpa using connectivity_le_degree (⊤ : SimpleGraph W) v
  · obtain ⟨C, hcard, hsep⟩ := connectivity_attained (⊤ : SimpleGraph W)
    have hp : ((⊤ : SimpleGraph W).induce {v | v ∉ C}).Preconnected := by
      intro u v
      by_cases he : u = v
      · exact he ▸ Reachable.refl u
      · exact (show ((⊤ : SimpleGraph W).induce {v | v ∉ C}).Adj u v from
          fun he' => he (Subtype.ext he')).reachable
    have hleft : (Finset.univ \ C).card ≤ 1 :=
      hsep.elim id (fun hn => (hn hp).elim)
    have htotal := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ C)
    simp only [Finset.card_univ] at htotal
    omega

/-- The unchanged whole source event; no separator reduction is assumed as a premise. -/
def FullMaximalConnectivityClaim : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V] [Nonempty V] (H : SimpleGraph V),
    H.Connected → vertexConnectivity (reconfiguration H) = (reconfiguration H).minDegree

end D5.S3.Combinatorics.Graph.MutualVisibility
