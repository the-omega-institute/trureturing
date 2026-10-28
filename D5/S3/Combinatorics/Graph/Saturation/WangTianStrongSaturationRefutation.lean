/- GID: D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Data.Finset.Max, mathlib/module/Mathlib.Data.List.Chain]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.claim; result=D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.result; claim=D5/S3/Combinatorics/Graph/Saturation/WangTianStrongSaturationRefutation.claim
   digest: Odd orders refute the unrestricted exact strong-digraph saturation formula. -/
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Saturation.WangTianStrongSaturationRefutation

/-- An ordered, unequal pair; reciprocal arcs are independent elements. -/
abbrev Arc (n : ℕ) := {p : Fin n × Fin n // p.1 ≠ p.2}

/-- A vertex subset and an arbitrary arc subset, retaining isolated vertices. -/
structure Digraph (n : ℕ) where
  vertices : Finset (Fin n)
  arcs : Finset (Arc n)
  endpoints : ∀ e ∈ arcs, e.val.1 ∈ vertices ∧ e.val.2 ∈ vertices

def Adj {n : ℕ} (H : Digraph n) (a b : Fin n) : Prop :=
  ∃ e ∈ H.arcs, e.val = (a, b)

/-- The list starts at a, ends at b, has no repeated vertices and uses directed arcs. -/
def Dipath {n : ℕ} (H : Digraph n) (a b : Fin n) : Prop :=
  ∃ l : List (Fin n), (a :: l).Nodup ∧
    (∀ v ∈ a :: l, v ∈ H.vertices) ∧ List.IsChain H.Adj (a :: l) ∧
    (a :: l).getLast (List.cons_ne_nil _ _) = b

def Strong {n : ℕ} (H : Digraph n) : Prop :=
  ∀ a ∈ H.vertices, ∀ b ∈ H.vertices, a ≠ b → H.Dipath a b

def delete {n : ℕ} (H : Digraph n) (S : Finset (Fin n)) : Digraph n where
  vertices := H.vertices \ S
  arcs := H.arcs.filter (fun e => e.val.1 ∉ S ∧ e.val.2 ∉ S)
  endpoints := by
    intro e he
    obtain ⟨he, ha, hb⟩ := Finset.mem_filter.mp he
    exact ⟨Finset.mem_sdiff.mpr ⟨(H.endpoints e he).1, ha⟩,
      Finset.mem_sdiff.mpr ⟨(H.endpoints e he).2, hb⟩⟩

/-- Trivial means exactly one vertex, even though pairwise reachability is then vacuous. -/
def Separator {n : ℕ} (H : Digraph n) (S : Finset (Fin n)) : Prop :=
  S ⊆ H.vertices ∧ (¬ (H.delete S).Strong ∨ (H.delete S).vertices.card = 1)

noncomputable def separatorCards {n : ℕ} (H : Digraph n) : Finset ℕ := by
  classical
  exact ((H.vertices.powerset).filter H.Separator).image Finset.card

private theorem erase_separator {n : ℕ} (H : Digraph n) {u : Fin n}
    (hu : u ∈ H.vertices) : H.Separator (H.vertices.erase u) := by
  refine ⟨Finset.erase_subset _ _, Or.inr ?_⟩
  simp [delete, Finset.sdiff_erase_self hu]

private theorem separatorCards_nonempty {n : ℕ} (H : Digraph n)
    (hne : H.vertices.Nonempty) : H.separatorCards.Nonempty := by
  classical
  obtain ⟨u, hu⟩ := hne
  refine ⟨(H.vertices.erase u).card, Finset.mem_image.mpr ⟨_, ?_, rfl⟩⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.erase_subset _ _),
    erase_separator H hu⟩

/-- The actual minimum separator size, with attainment and domination retained. -/
noncomputable def connectivity {n : ℕ} (H : Digraph n) (hne : H.vertices.Nonempty) :
    {m : ℕ // (∃ S, H.Separator S ∧ S.card = m) ∧
      ∀ S, H.Separator S → m ≤ S.card} := by
  classical
  let m := H.separatorCards.min' (separatorCards_nonempty H hne)
  refine ⟨m, ?_, ?_⟩
  · obtain ⟨S, hS, hm⟩ := Finset.mem_image.mp
      (Finset.min'_mem H.separatorCards (separatorCards_nonempty H hne))
    exact ⟨S, (Finset.mem_filter.mp hS).2, hm⟩
  · intro S hS
    apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨S,
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS.1, hS⟩, rfl⟩

/-- Empty digraphs are excluded; no minimum of an empty separator family is used. -/
def KStrong {n : ℕ} (k : ℕ) (H : Digraph n) : Prop :=
  ∃ hne : H.vertices.Nonempty, k ≤ (H.connectivity hne).val

private theorem kstrong_order {n k : ℕ} (H : Digraph n) (h : KStrong k H) :
    k + 1 ≤ H.vertices.card := by
  obtain ⟨hne, hk⟩ := h
  obtain ⟨u, hu⟩ := hne
  have hm := (H.connectivity hne).property.2 _ (erase_separator H hu)
  have hc := Finset.card_erase_lt_of_mem hu
  omega

/-- Subgraphs range independently over vertex subsets and arc subsets. -/
def Forbidden {n : ℕ} (k : ℕ) (A : Finset (Arc n)) : Prop :=
  ∃ H : Digraph n, H.arcs ⊆ A ∧ KStrong k H

def Free {n : ℕ} (k : ℕ) (A : Finset (Arc n)) : Prop := ¬ Forbidden k A

def Saturated {n : ℕ} (k : ℕ) (A : Finset (Arc n)) : Prop :=
  Free k A ∧ ∀ e : Arc n, e ∉ A → Forbidden k (insert e A)

private theorem free_small {n k : ℕ} (hn : n ≤ k) (A : Finset (Arc n)) :
    Free k A := by
  rintro ⟨H, _, hH⟩
  have hs := kstrong_order H hH
  have hc : H.vertices.card ≤ n := by
    simpa using Finset.card_le_univ H.vertices
  omega

private theorem empty_free {n k : ℕ} (hk : 1 ≤ k) : Free k (∅ : Finset (Arc n)) := by
  classical
  rintro ⟨H, hA, hK⟩
  have hArc : H.arcs = ∅ := Finset.subset_empty.mp hA
  obtain ⟨hne, hK⟩ := hK
  have horder := kstrong_order H ⟨hne, hK⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < H.vertices.card)
  have hsep : H.Separator ∅ := by
    refine ⟨Finset.empty_subset _, Or.inl ?_⟩
    intro hs
    obtain ⟨l, _, _, hchain, hlast⟩ := hs a (by simpa [delete] using ha)
      b (by simpa [delete] using hb) hab
    have hr := List.relationReflTransGen_of_exists_isChain_cons l hchain hlast
    have heq : b = a := Relation.reflTransGen_iff_eq (fun v hv => by
      obtain ⟨e, he, _⟩ := hv
      simpa [delete, hArc] using he) |>.mp hr
    exact hab heq.symm
  have hm := (H.connectivity hne).property.2 ∅ hsep
  simp only [Finset.card_empty] at hm
  omega

/-- A maximum-cardinality free arc set is saturated. Small complete digraphs
are handled explicitly, including the zero-vertex complete digraph. -/
private theorem saturated_exists (k n : ℕ) (hk : 1 ≤ k) :
    ∃ A : Finset (Arc n), Saturated k A := by
  classical
  by_cases hn : n ≤ k
  · refine ⟨Finset.univ, free_small hn _, ?_⟩
    intro e he
    exact False.elim (he (Finset.mem_univ e))
  let family := (Finset.univ : Finset (Arc n)).powerset.filter (Free k)
  have hne : family.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨?_, empty_free hk⟩⟩
    exact Finset.mem_powerset.mpr (Finset.empty_subset _)
  obtain ⟨A, hA, hmax⟩ := Finset.exists_max_image family Finset.card hne
  refine ⟨A, (Finset.mem_filter.mp hA).2, ?_⟩
  intro e he
  by_contra hfree
  have hmem : insert e A ∈ family :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hfree⟩
  have hle := hmax _ hmem
  rw [Finset.card_insert_of_notMem he] at hle
  omega

noncomputable def saturatedFamily (k n : ℕ) : Finset (Finset (Arc n)) := by
  classical
  exact (Finset.univ : Finset (Arc n)).powerset.filter (Saturated k)

private theorem saturatedFamily_nonempty (k n : ℕ) (hk : 1 ≤ k) :
    (saturatedFamily k n).Nonempty := by
  classical
  obtain ⟨A, hA⟩ := saturated_exists k n hk
  exact ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hA⟩⟩

/-- The attained actual maximum, rather than an arbitrary integer-valued function
or a default value for an empty family. The certificate is part of its type. -/
noncomputable def extremum (k n : ℕ) (hk : 1 ≤ k) :
    {m : ℕ // (∃ A : Finset (Arc n), Saturated k A ∧ A.card = m) ∧
      ∀ B : Finset (Arc n), Saturated k B → B.card ≤ m} := by
  classical
  let counts := (saturatedFamily k n).image Finset.card
  have hne : counts.Nonempty := (saturatedFamily_nonempty k n hk).image Finset.card
  refine ⟨counts.max' hne, ?_, ?_⟩
  · obtain ⟨A, hA, hcard⟩ := Finset.mem_image.mp (counts.max'_mem hne)
    exact ⟨A, (Finset.mem_filter.mp hA).2, hcard⟩
  · intro B hB
    apply counts.le_max'
    exact Finset.mem_image.mpr ⟨B,
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hB⟩, rfl⟩

/-- The full unrestricted eventual equality, with every division and subtraction in Q. -/
def claim : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ((extremum k n hk).val : ℚ) =
      ((3 : ℚ) / 2) * ((k : ℚ) - (4 : ℚ) / 3) * ((n : ℚ) - (k : ℚ) + 1) +
        (Nat.choose n 2 : ℚ)

/-- At k=3, the odd order 2N+5 contradicts integrality for every proposed threshold. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨N, hN⟩ := h 3 (by omega)
  have heq := hN (2 * N + 5) (by omega)
  have hdouble :
      ((2 * (extremum 3 (2 * N + 5) (by omega)).val : ℕ) : ℚ) =
      ((2 * (Nat.choose (2 * N + 5) 2 + 5 * N + 7) + 1 : ℕ) : ℚ) := by
    push_cast
    push_cast at heq
    linarith
  have hnat := Nat.cast_injective (R := ℚ) hdouble
  exact Nat.not_even_two_mul_add_one _ (hnat ▸ even_two_mul _)

end D5.S3.Combinatorics.Graph.Saturation.WangTianStrongSaturationRefutation
