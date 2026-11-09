/- GID: D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentBase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Directed distances and the ordered-pair solid-resolving criterion. -/

/-
admission_basis: escape-witness
escape_witness: D5.S3.Combinatorics.Graph.Walks.SolidResolvingTournamentBase.directedDistance_le_walkBound
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/23622
solid_iff_ordered — proof_shape: bind-only; escape_witness: none; consumers: profile_constraints, card_bound_of_profile_model.
  Direct frozen dependencies: none.
profile_constraints — proof_shape: bind-only; escape_witness: none; consumers: card_bound_of_profile_model.
  Direct frozen dependencies: none.
directedDistance_le_walkBound — proof_shape: content; escape_witness: directedDistance_le_walkBound; consumers: nonpath_upper_4_5, nonpath_upper_5_5, nonpath_upper_4_2, nonpath_upper_5_4, representative_path_upper_5_40, nonpath_upper_3_0, representative_path_upper_5_41, nonpath_upper_4_0, representative_path_upper_5_76, nonpath_upper_5_9, representative_path_upper_5_10, representative_path_upper_4_4, nonpath_upper_5_0, nonpath_upper_5_2, representative_path_upper_5_12, representative_path_upper_3_2, nonpath_upper_5_11, representative_path_upper_5_8.
  Direct frozen dependencies: none.
dimension_lower_of_fixed_card_bound — proof_shape: bind-only; escape_witness: none; consumers: claim_of_card_bounds.
  Direct frozen dependencies: none.
-/

import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic.NormNum

namespace D5.S3.Combinatorics.Graph.Walks.SolidResolvingTournamentBase

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
universe uSolid

noncomputable def directedDistance {V : Type*} (R : V → V → Prop) (u v : V) : ℕ∞ :=
  letI : Quiver V := ⟨fun a b => PLift (R a b)⟩
  ⨅ p : Quiver.Path u v, (p.length : ℕ∞)


noncomputable def distanceToSet {V : Type*} (R : V → V → Prop)
    (u : V) (X : Set V) : ℕ∞ :=
  ⨅ v : X, directedDistance R u v


def IsSolidResolving {V : Type*} (R : V → V → Prop) (S : Set V) : Prop :=
  ∀ (v : V) (X : Set V), X.Nonempty → X ≠ {v} →
    ∃ w : V, w ∈ S ∧ directedDistance R w v ≠ distanceToSet R w X


noncomputable def solidMetricDimension {V : Type*} [Fintype V]
    (R : V → V → Prop) : ℕ :=
  sInf {k : ℕ | ∃ S : Finset V, IsSolidResolving R (S : Set V) ∧ S.card = k}


private lemma directedDistance_self (R : V → V → Prop) (v : V) : directedDistance R v v = 0 := by
  unfold directedDistance
  letI : Quiver V := ⟨fun a b => PLift (R a b)⟩
  apply le_antisymm
  · exact iInf_le_of_le (Quiver.Path.nil) (by simp)
  · exact bot_le

private lemma directedDistance_pos {V : Type*} (R : V → V → Prop) {u v : V}
    (h : u ≠ v) : 1 ≤ directedDistance R u v := by
  unfold directedDistance
  letI : Quiver V := ⟨fun a b => PLift (R a b)⟩
  refine le_iInf (fun p => ?_)
  have hz : p.length ≠ 0 := by
    intro hz
    exact h (Quiver.Path.eq_of_length_zero p hz)
  have hn : 1 ≤ p.length := Nat.one_le_iff_ne_zero.mpr hz
  exact_mod_cast hn

private lemma directedDistance_triangle {V : Type*} (R : V → V → Prop) (a b c : V) :
    directedDistance R a c ≤ directedDistance R a b + directedDistance R b c := by
  unfold directedDistance
  letI : Quiver V := ⟨fun x y => PLift (R x y)⟩
  apply ENat.le_iInf_add_iInf
  intro p q
  exact iInf_le_of_le (p.comp q) (by simp [Quiver.Path.length_comp])

private lemma distanceToSet_pos {V : Type*} (R : V → V → Prop) {u : V} {X : Set V}
    (hu : u ∉ X) : 1 ≤ distanceToSet R u X := by
  unfold distanceToSet
  refine le_iInf (fun x => directedDistance_pos R ?_)
  intro hux
  exact hu (by simpa [hux] using x.property)

private lemma solid_univ [Fintype V] (R : V → V → Prop) :
    IsSolidResolving R (Set.univ : Set V) := by
  intro v X hX hneq
  by_cases hv : v ∉ X
  · refine ⟨v, Set.mem_univ _, ?_⟩
    have hzero := directedDistance_self R v
    have hpos := distanceToSet_pos R hv
    rw [hzero]
    exact (ne_of_gt (lt_of_lt_of_le (by norm_num) hpos)).symm
  · have hvX : v ∈ X := by simpa using hv
    obtain ⟨u, huX, huv⟩ : ∃ u, u ∈ X ∧ u ≠ v := by
      by_contra h
      push_neg at h
      apply hneq
      ext x
      constructor
      · intro hx
        have : x = v := h x hx
        simpa [this] using hvX
      · intro hx
        exact (by simpa using hx) ▸ hvX
    refine ⟨u, Set.mem_univ _, ?_⟩
    have hpos := directedDistance_pos R huv
    have hset : distanceToSet R u X = 0 := by
      apply le_antisymm
      · unfold distanceToSet
        exact iInf_le_of_le ⟨u, huX⟩ (by simp [directedDistance_self])
      · exact bot_le
    rw [hset]
    exact (ne_of_gt (lt_of_lt_of_le (by norm_num) hpos))

private lemma solid_mono [Fintype V] {R : V → V → Prop} {S T : Set V}
    (hS : IsSolidResolving R S) (hST : S ⊆ T) : IsSolidResolving R T := by
  intro v X hX hneq
  obtain ⟨w, hwS, hne⟩ := hS v X hX hneq
  exact ⟨w, hST hwS, hne⟩

private lemma solidMetricDimension_mem [Fintype V] (R : V → V → Prop) :
    ∃ k : ℕ, k ∈ {k : ℕ | ∃ S : Finset V, IsSolidResolving R (S : Set V) ∧ S.card = k} := by
  refine ⟨Fintype.card V, ?_⟩
  refine ⟨Finset.univ, ?_, ?_⟩
  · simpa using solid_univ R
  · simp

private lemma distanceToSet_pair {V : Type*} (R : V → V → Prop) (w u v : V) :
    distanceToSet R w ({u, v} : Set V) = min (directedDistance R w u) (directedDistance R w v) := by
  unfold distanceToSet
  apply le_antisymm
  · apply le_min
    · exact iInf_le_of_le ⟨u, by simp⟩ le_rfl
    · exact iInf_le_of_le ⟨v, by simp⟩ le_rfl
  · refine le_iInf (fun x => ?_)
    have hor : x.val = u ∨ x.val = v := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using x.property
    rcases hor with hxu | hxv
    · simpa [hxu] using (min_le_left (directedDistance R w u) (directedDistance R w v))
    · simpa [hxv] using (min_le_right (directedDistance R w u) (directedDistance R w v))

private lemma distanceToSet_le {V : Type*} (R : V → V → Prop) {w : V} {X : Set V}
    {u : V} (hu : u ∈ X) : distanceToSet R w X ≤ directedDistance R w u := by
  unfold distanceToSet
  exact iInf_le_of_le ⟨u, hu⟩ le_rfl

lemma solid_iff_ordered {V : Type*} (R : V → V → Prop) (S : Set V) :
    IsSolidResolving R S ↔
      ∀ ⦃u v : V⦄, u ≠ v → ∃ w ∈ S, directedDistance R w u < directedDistance R w v := by
  constructor
  · intro h u v huv
    obtain ⟨w, hw, hne⟩ := h v ({u, v} : Set V) (by simp) (by
      intro heq
      have hmem : u ∈ ({v} : Set V) := (Set.ext_iff.mp heq u).mp (by simp)
      exact huv (by simpa using hmem))
    have hmin := distanceToSet_pair R w u v
    rw [hmin] at hne
    have hminlt : min (directedDistance R w u) (directedDistance R w v) <
        directedDistance R w v :=
      lt_of_le_of_ne (min_le_right _ _) hne.symm
    have hlt : directedDistance R w u < directedDistance R w v := by
      exact (min_lt_iff.mp hminlt).resolve_right (lt_irrefl _)
    exact ⟨w, hw, hlt⟩
  · intro h v X hX hneq
    obtain ⟨u, huX, huv⟩ : ∃ u, u ∈ X ∧ u ≠ v := by
      by_cases hall : ∀ x, x ∈ X → x = v
      · obtain ⟨x, hx⟩ := hX
        have hvX : v ∈ X := (hall x hx) ▸ hx
        exfalso
        apply hneq
        ext x
        constructor
        · intro hx'
          have hxv : x = v := hall x hx'
          simpa [hxv]
        · intro hx'
          have hxv : x = v := by simpa using hx'
          exact hxv ▸ hvX
      · push_neg at hall
        exact hall
    obtain ⟨w, hw, hlt⟩ := h huv
    refine ⟨w, hw, ?_⟩
    have hle := distanceToSet_le (w := w) R huX
    exact ne_of_gt (lt_of_le_of_lt hle hlt)

lemma profile_constraints {V : Type*} {k : ℕ}
    (R : V → V → Prop) (L : Fin k → V)
    (hS : IsSolidResolving R (Set.range L))
    {u : V} (hu : u ∉ Set.range L)
    (D : Fin k → Fin k → ℕ∞)
    (hD : ∀ i j, directedDistance R (L i) (L j) ≤ D i j) :
    (∀ i, 1 ≤ directedDistance R (L i) u) ∧
      (∀ j, ∃ i, directedDistance R (L i) u < D i j) ∧
      (∀ i j, directedDistance R (L i) u ≤ D i j + directedDistance R (L j) u) := by
  have horder := (solid_iff_ordered R (Set.range L)).mp hS
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply directedDistance_pos R
    intro hEq
    apply hu
    exact ⟨i, hEq⟩
  · intro j
    have huv : u ≠ L j := by
      intro hEq
      apply hu
      exact ⟨j, hEq.symm⟩
    obtain ⟨w, hw, hlt⟩ := horder huv
    rcases hw with ⟨i, rfl⟩
    exact ⟨i, lt_of_lt_of_le hlt (hD i j)⟩
  · intro i j
    exact (directedDistance_triangle R (L i) (L j) u).trans
      (by simpa [add_comm] using
        (add_le_add_right (hD i j) (directedDistance R (L j) u)))



private lemma directedDistance_le_edge {V : Type*} (R : V → V → Prop) {a b : V}
    (h : R a b) : directedDistance R a b ≤ 1 := by
  unfold directedDistance
  letI : Quiver V := ⟨fun a b => PLift (R a b)⟩
  let e : a ⟶ b := ⟨h⟩
  exact iInf_le_of_le e.toPath (by rfl)

def pairIndex (k i j : Nat) : Nat := i * (2*k-i-1) / 2 + (j-i-1)

def maskArc {k : Nat} (m : Nat) (i j : Fin k) : Bool :=
  if i.val < j.val then m.testBit (pairIndex k i.val j.val)
  else if j.val < i.val then !(m.testBit (pairIndex k j.val i.val))
  else false

def walkBound {k : Nat} (m : Nat) : Nat → Fin k → Fin k → Bool
  | 0, i, j => i == j
  | n+1, i, j => walkBound m n i j ||
      (List.finRange k).any (fun z => walkBound m n i z && maskArc m z j)

lemma directedDistance_le_walkBound {V : Type*} {k : Nat}
    (R : V → V → Prop) (L : Fin k → V) (m : Nat)
    (hE : ∀ i j, maskArc m i j = true → R (L i) (L j))
    (n : Nat) (i j : Fin k) (h : walkBound m n i j = true) :
    directedDistance R (L i) (L j) ≤ n := by
  induction n generalizing i j with
  | zero =>
    have hij : i = j := by simpa [walkBound] using h
    subst j
    simp [directedDistance_self]
  | succ n ih =>
    simp only [walkBound, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨z, _, hz, he⟩
    · exact (ih i j h).trans (by exact_mod_cast Nat.le_succ n)
    · have ht := directedDistance_triangle R (L i) (L z) (L j)
      have ha := ih i z hz
      have hb := directedDistance_le_edge R (hE z j he)
      exact ht.trans (by simpa only [Nat.cast_add, Nat.cast_one] using add_le_add ha hb)

lemma dimension_lower_of_fixed_card_bound {V : Type*} [Fintype V]
    (R : V → V → Prop) (k c : Nat) (hk : k ≤ Fintype.card V)
    (hc : c < Fintype.card V)
    (hbound : ∀ S : Finset V, S.card = k → IsSolidResolving R (S : Set V) →
      Fintype.card V ≤ c) : k+1 ≤ solidMetricDimension R := by
  classical
  unfold solidMetricDimension
  apply le_csInf (solidMetricDimension_mem R)
  intro n hn
  obtain ⟨S, hS, rfl⟩ := hn
  by_contra hn
  have hSk : S.card ≤ k := by omega
  obtain ⟨T, hST, hT⟩ := Finset.exists_superset_card_eq hSk hk
  have hsolid : IsSolidResolving R (T : Set V) := solid_mono hS (by
    intro v hv
    exact hST hv)
  have hcard := hbound T hT hsolid
  omega

end D5.S3.Combinatorics.Graph.Walks.SolidResolvingTournamentBase
