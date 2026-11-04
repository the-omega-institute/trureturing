/- GID: D5/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/TrapezohedralMinimalDomination
   mirror-E: none(waiver:unbounded-constructive-proof)
   anchors: []
   utility: none
   digest: Closed-private witnesses and labelled one-apex trapezohedral configurations. -/

import D5.S3.Combinatorics.Graph.DominatingSetAverage
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Combinatorics.SimpleGraph.VertexCover

/-! Closed domination uses the existing `SimpleGraph.IsDominating`. Minimality
ranges over all subsets, without a connectivity restriction. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Domination.TrapezohedralMinimalDomination

section Minimality

variable {V : Type*} (G : SimpleGraph V)

/-- Inclusion-minimal closed domination, independently of connectivity. -/
def MinimalDominating (S : Set V) : Prop :=
  G.IsDominating S ∧ ∀ T : Set V, T ⊆ S → G.IsDominating T → S ⊆ T

/-- A closed-private witness; in particular `w = s` is permitted. -/
def ClosedPrivate (S : Set V) (s w : V) : Prop :=
  (w = s ∨ G.Adj w s) ∧ ∀ t ∈ S, (w = t ∨ G.Adj w t) → t = s

/-- The closed-private characterization retains self-private witnesses. -/
theorem minimalDominating_iff_private (S : Set V) :
    MinimalDominating G S ↔
      G.IsDominating S ∧ ∀ s ∈ S, ∃ w, ClosedPrivate G S s w := by
  classical
  constructor
  · rintro ⟨hd, hm⟩
    refine ⟨hd, fun s hs => ?_⟩
    have hn : ¬ G.IsDominating (S \ {s}) := by
      intro ht
      have hmem := hm (S \ {s}) Set.sdiff_subset ht hs
      exact hmem.2 (by simp)
    change ¬ (∀ w, w ∈ S \ {s} ∨ ∃ t ∈ S \ {s}, G.Adj w t) at hn
    obtain ⟨w, hw⟩ := not_forall.mp hn
    have only : ∀ t ∈ S, (w = t ∨ G.Adj w t) → t = s := by
      intro t ht hwt
      by_contra hts
      have hte : t ∈ S \ {s} := ⟨ht, by simpa using hts⟩
      apply hw
      rcases hwt with rfl | hadj
      · exact Or.inl hte
      · exact Or.inr ⟨t, hte, hadj⟩
    refine ⟨w, ?_, only⟩
    rcases hd w with hwS | ⟨t, ht, hadj⟩
    · exact Or.inl (only w hwS (Or.inl rfl))
    · exact Or.inr (only t ht (Or.inr hadj) ▸ hadj)
  · rintro ⟨hd, hp⟩
    refine ⟨hd, ?_⟩
    intro T hTS hT s hs
    obtain ⟨w, _, hw⟩ := hp s hs
    rcases hT w with hwT | ⟨t, ht, hadj⟩
    · exact hw w (hTS hwT) (Or.inl rfl) ▸ hwT
    · exact hw t (hTS ht) (Or.inr hadj) ▸ ht

/-- The subset formulation is exactly failure of every proper dominating subset. -/
theorem minimalDominating_iff_proper (S : Set V) :
    MinimalDominating G S ↔
      G.IsDominating S ∧ ∀ T : Set V, T ⊂ S → ¬ G.IsDominating T := by
  constructor
  · rintro ⟨hd, hm⟩
    refine ⟨hd, ?_⟩
    intro T hTS hT
    exact hTS.2 (hm T hTS.1 hT)
  · rintro ⟨hd, hm⟩
    refine ⟨hd, ?_⟩
    intro T hTS hT
    by_contra hn
    exact hm T ⟨hTS, hn⟩ hT

end Minimality

/-- All labels are distinct constructors. The cyclic order is `a i, b i, a (i+1)`. -/
inductive Vertex (n : ℕ)
  | alpha : Vertex n
  | beta : Vertex n
  | a : Fin n → Vertex n
  | b : Fin n → Vertex n
  deriving DecidableEq, Fintype

open Vertex

/-- Exactly the two rim-edge families and two apex-edge families. -/
def adjacent {n : ℕ} : Vertex n → Vertex n → Prop
  | alpha, a _ => True
  | a _, alpha => True
  | beta, b _ => True
  | b _, beta => True
  | a i, b j => i = j ∨ i = finRotate n j
  | b j, a i => i = j ∨ i = finRotate n j
  | _, _ => False

/-- The literal labelled trapezohedral graph. Only orders at least three are counted. -/
def graph (n : ℕ) : SimpleGraph (Vertex n) where
  Adj := adjacent
  symm := ⟨by intro u v; cases u <;> cases v <;> simp [adjacent]⟩
  loopless := ⟨by intro u; cases u <;> simp [adjacent]⟩

/-- Connected induced subgraph as well as minimality among all dominating subsets. -/
def Admissible {n : ℕ} (S : Set (Vertex n)) : Prop :=
  ((graph n).IsDominating S ∧
    ∀ T : Set (Vertex n), T ⊂ S → ¬ (graph n).IsDominating T) ∧
      ((graph n).induce S).Connected

/-- Count actual labelled finite subsets, with the source's zero coefficients below order three. -/
noncomputable def actualCount (n : ℕ) : ℕ :=
  if 3 ≤ n then Nat.card {S : Set (Vertex n) // Admissible S} else 0

/-- A one-apex set with opposite label `j` and selected same-type labels `C`. -/
def alphaSet {n : ℕ} (j : Fin n) (C : Set (Fin n)) : Set (Vertex n)
  | alpha => True
  | beta => False
  | a i => i ∈ C
  | b i => i = j

/-- Each edge except the tagged deleted edge is covered. -/
def CutCover {n : ℕ} (j : Fin n) (C : Set (Fin n)) : Prop :=
  ∀ i : Fin n, i ≠ j → i ∈ C ∨ finRotate n i ∈ C

/-- Minimality of the cover is against all proper subcovers. -/
def MinimalCutCover {n : ℕ} (j : Fin n) (C : Set (Fin n)) : Prop :=
  CutCover j C ∧ ∀ D : Set (Fin n), D ⊆ C → CutCover j D → C ⊆ D

private theorem dominates_alphaSet_iff {n : ℕ} (j : Fin n) (C : Set (Fin n)) :
    (graph n).IsDominating (alphaSet j C) ↔ CutCover j C := by
  constructor
  · intro hd i hij
    rcases hd (b i) with hi | ⟨v, hv, hadj⟩
    · exact False.elim (hij hi)
    · cases v with
      | alpha => exact False.elim hadj
      | beta => exact False.elim hv
      | a k =>
        rcases hadj with rfl | rfl
        · exact Or.inl hv
        · exact Or.inr hv
      | b k => exact False.elim hadj
  · intro hc v
    cases v with
    | alpha => exact Or.inl trivial
    | beta => exact Or.inr ⟨b j, rfl, trivial⟩
    | a i => exact Or.inr ⟨alpha, trivial, trivial⟩
    | b i =>
      by_cases hij : i = j
      · exact Or.inl hij
      · rcases hc i hij with hi | hi
        · exact Or.inr ⟨a i, hi, Or.inl rfl⟩
        · exact Or.inr ⟨a (finRotate n i), hi, Or.inr rfl⟩

/-- A selected cover vertex has an edge whose other endpoint is omitted. -/
def CutPrivate {n : ℕ} (j : Fin n) (C : Set (Fin n)) (i : Fin n) : Prop :=
  ∃ k : Fin n, k ≠ j ∧
    ((i = k ∧ finRotate n k ∉ C) ∨ (i = finRotate n k ∧ k ∉ C))

private theorem rotate_ne {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    finRotate n i ≠ i := by
  cases n with
  | zero => omega
  | succ m =>
    intro h
    have hv := congrArg Fin.val h
    rw [coe_finRotate] at hv
    split_ifs at hv with hi
    · have hv' : i.val = m := congrArg Fin.val hi
      omega
    · omega

private theorem minimalCutCover_iff_private {n : ℕ} (hn : 2 ≤ n)
    (j : Fin n) (C : Set (Fin n)) :
    MinimalCutCover j C ↔ CutCover j C ∧ ∀ i ∈ C, CutPrivate j C i := by
  classical
  constructor
  · rintro ⟨hc, hm⟩
    refine ⟨hc, fun i hi => ?_⟩
    have hncover : ¬ CutCover j (C \ {i}) := by
      intro hd
      have hmem := hm (C \ {i}) Set.sdiff_subset hd hi
      exact hmem.2 (by simp)
    unfold CutCover at hncover
    push Not at hncover
    obtain ⟨k, hkj, hk, hr⟩ := hncover
    rcases hc k hkj with hkC | hrC
    · have hki : k = i := by
        by_contra hne
        exact hk ⟨hkC, by simpa using hne⟩
      refine ⟨k, hkj, Or.inl ⟨hki.symm, ?_⟩⟩
      intro hrC
      exact hr ⟨hrC, by simpa [hki] using rotate_ne hn k⟩
    · have hri : finRotate n k = i := by
        by_contra hne
        exact hr ⟨hrC, by simpa using hne⟩
      refine ⟨k, hkj, Or.inr ⟨hri.symm, ?_⟩⟩
      intro hkC
      exact hk ⟨hkC, by simpa [← hri] using (rotate_ne hn k).symm⟩
  · rintro ⟨hc, hp⟩
    refine ⟨hc, ?_⟩
    intro D hDC hd i hi
    obtain ⟨k, hkj, hk⟩ := hp i hi
    rcases hk with ⟨hik, hr⟩ | ⟨hir, hk⟩
    · rw [hik]
      exact (hd k hkj).resolve_right (fun h => hr (hDC h))
    · rw [hir]
      exact (hd k hkj).resolve_left (fun h => hk (hDC h))

private theorem cover_nonempty {n : ℕ} (hn : 2 ≤ n) {j : Fin n}
    {C : Set (Fin n)} (hc : CutCover j C) : C.Nonempty := by
  rcases hc (finRotate n j) (rotate_ne hn j) with h | h
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩

private theorem private_sameType_iff {n : ℕ} (hn : 2 ≤ n)
    (j i : Fin n) (C : Set (Fin n)) :
    (∃ w, ClosedPrivate (graph n) (alphaSet j C) (a i) w) ↔ CutPrivate j C i := by
  constructor
  · rintro ⟨w, hw, hu⟩
    cases w with
    | alpha =>
      have h := hu alpha trivial (Or.inl rfl)
      cases h
    | beta => simpa [graph, adjacent] using hw
    | a k =>
      rcases hw with heq | hadj
      · cases heq
        have h := hu alpha trivial (Or.inr (by trivial))
        cases h
      · exact False.elim hadj
    | b k =>
      have hkj : k ≠ j := by
        intro h
        subst k
        have heq := hu (b j) rfl (Or.inl rfl)
        cases heq
      have hki : i = k ∨ i = finRotate n k := by
        simpa [graph, adjacent] using hw
      refine ⟨k, hkj, ?_⟩
      rcases hki with hik | hir
      · subst i
        refine Or.inl ⟨rfl, ?_⟩
        intro hr
        have heq := hu (a (finRotate n k)) hr (Or.inr (Or.inr rfl))
        exact rotate_ne hn k (Vertex.a.inj heq)
      · subst i
        refine Or.inr ⟨rfl, ?_⟩
        intro hk
        have heq := hu (a k) hk (Or.inr (Or.inl rfl))
        exact rotate_ne hn k (Vertex.a.inj heq).symm
  · rintro ⟨k, hkj, hk⟩
    refine ⟨b k, ?_, ?_⟩
    · rcases hk with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · intro t ht hwt
      cases t with
      | alpha => simpa [graph, adjacent] using hwt
      | beta => exact False.elim ht
      | a l =>
        have hl : l = k ∨ l = finRotate n k := by
          simpa [graph, adjacent] using hwt
        rcases hk with ⟨rfl, hr⟩ | ⟨rfl, hkc⟩
        · rcases hl with rfl | rfl
          · rfl
          · exact False.elim (hr ht)
        · rcases hl with rfl | rfl
          · exact False.elim (hkc ht)
          · rfl
      | b l =>
        have hl : l = j := ht
        subst l
        have heq : k = j := by simpa [graph, adjacent] using hwt
        exact False.elim (hkj heq)

private theorem private_apex_iff {n : ℕ} (j : Fin n) (C : Set (Fin n))
    (hC : C.Nonempty) :
    (∃ w, ClosedPrivate (graph n) (alphaSet j C) alpha w) ↔
      ∃ i : Fin n, i ∉ C ∧ i ≠ j ∧ i ≠ finRotate n j := by
  constructor
  · rintro ⟨w, hw, hu⟩
    cases w with
    | alpha =>
      obtain ⟨i, hi⟩ := hC
      have heq := hu (a i) hi (Or.inr (by trivial))
      cases heq
    | beta => simpa [graph, adjacent] using hw
    | b k => simpa [graph, adjacent] using hw
    | a i =>
      refine ⟨i, ?_, ?_, ?_⟩
      · intro hi
        have heq := hu (a i) hi (Or.inl rfl)
        cases heq
      · intro hij
        subst i
        have heq := hu (b j) rfl (Or.inr (Or.inl rfl))
        cases heq
      · intro hij
        subst i
        have heq := hu (b j) rfl (Or.inr (Or.inr rfl))
        cases heq
  · rintro ⟨i, hi, hij, hir⟩
    refine ⟨a i, Or.inr trivial, ?_⟩
    intro t ht hwt
    cases t with
    | alpha => rfl
    | beta => exact False.elim ht
    | a k =>
      have heq : i = k := by simpa [graph, adjacent] using hwt
      subst k
      exact False.elim (hi ht)
    | b k =>
      have hkj : k = j := ht
      subst k
      have h : i = j ∨ i = finRotate n j := by
        simpa [graph, adjacent] using hwt
      exact False.elim (h.elim hij hir)

private theorem connected_alphaSet_iff {n : ℕ} (j : Fin n) (C : Set (Fin n)) :
    ((graph n).induce (alphaSet j C)).Connected ↔ j ∈ C ∨ finRotate n j ∈ C := by
  constructor
  · intro hc
    have hr := hc ⟨b j, rfl⟩ ⟨alpha, trivial⟩
    have hne : (⟨b j, rfl⟩ : alphaSet j C) ≠ ⟨alpha, trivial⟩ := by
      intro h
      have heq := congrArg Subtype.val h
      cases heq
    obtain ⟨⟨v, hv⟩, hadj⟩ := hr.nonempty_neighborSet_left hne
    cases v with
    | alpha => exact False.elim hadj
    | beta => exact False.elim hv
    | b i => exact False.elim hadj
    | a i =>
      rcases hadj with rfl | rfl
      · exact Or.inl hv
      · exact Or.inr hv
  · intro he
    apply (((graph n).induce (alphaSet j C)).connected_iff_exists_forall_reachable).mpr
    let root : alphaSet j C := ⟨alpha, trivial⟩
    have reachA (i : Fin n) (hi : i ∈ C) :
        ((graph n).induce (alphaSet j C)).Reachable root ⟨a i, hi⟩ :=
      SimpleGraph.Adj.reachable (show adjacent alpha (a i) from trivial)
    refine ⟨root, ?_⟩
    rintro ⟨v, hv⟩
    cases v with
    | alpha => exact SimpleGraph.Reachable.refl _
    | beta => exact False.elim hv
    | a i => exact reachA i hv
    | b i =>
      change i = j at hv
      subst i
      rcases he with hj | hj
      · exact (reachA j hj).trans
          (SimpleGraph.Adj.reachable (show adjacent (a j) (b j) from Or.inl rfl))
      · exact (reachA (finRotate n j) hj).trans
          (SimpleGraph.Adj.reachable
            (show adjacent (a (finRotate n j)) (b j) from Or.inr rfl))

/-- Exact forward and reverse conditions for a fixed labelled one-apex set.
The omitted interior label supplies the apex's closed-private witness. -/
private theorem alphaSet_admissible_with_interior_iff {n : ℕ} (hn : 3 ≤ n) (j : Fin n) (C : Set (Fin n)) :
    Admissible (alphaSet j C) ↔
      MinimalCutCover j C ∧ (j ∈ C ∨ finRotate n j ∈ C) ∧
        ∃ i : Fin n, i ∉ C ∧ i ≠ j ∧ i ≠ finRotate n j := by
  have hn2 : 2 ≤ n := by omega
  constructor
  · rintro ⟨hm, hconn⟩
    obtain ⟨hd, hp⟩ := (minimalDominating_iff_private (graph n) _).mp
      ((minimalDominating_iff_proper (graph n) _).mpr hm)
    have hc := (dominates_alphaSet_iff j C).mp hd
    refine ⟨(minimalCutCover_iff_private hn2 j C).mpr ⟨hc, ?_⟩,
      (connected_alphaSet_iff j C).mp hconn, ?_⟩
    · intro i hi
      exact (private_sameType_iff hn2 j i C).mp (hp (a i) hi)
    · exact (private_apex_iff j C (cover_nonempty hn2 hc)).mp (hp alpha trivial)
  · rintro ⟨hc, hend, hinterior⟩
    refine ⟨(minimalDominating_iff_proper (graph n) _).mp
      ((minimalDominating_iff_private (graph n) _).mpr ⟨?_, ?_⟩),
      (connected_alphaSet_iff j C).mpr hend⟩
    · exact (dominates_alphaSet_iff j C).mpr hc.1
    · intro s hs
      cases s with
      | alpha => exact (private_apex_iff j C (cover_nonempty hn2 hc.1)).mpr hinterior
      | beta => exact False.elim hs
      | a i =>
        exact (private_sameType_iff hn2 j i C).mpr
          (((minimalCutCover_iff_private hn2 j C).mp hc).2 i hs)
      | b i =>
        change i = j at hs
        subst i
        refine ⟨beta, Or.inr trivial, ?_⟩
        intro t ht hwt
        cases t with
        | alpha => simp [graph, adjacent] at hwt
        | beta => exact False.elim ht
        | a k => simp [graph, adjacent] at hwt
        | b k => exact congrArg b ht

private theorem rotate_twice_ne {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    finRotate n (finRotate n i) ≠ i := by
  letI : NeZero n := ⟨by omega⟩
  intro h
  have htwo : (1 : Fin n) + 1 = 2 := by
    apply Fin.ext
    simp [Fin.val_add, Nat.mod_eq_of_lt (show 1 < n by omega),
      Nat.mod_eq_of_lt (show 2 < n by omega)]
  have he : i + (2 : Fin n) = i + 0 := by
    simpa only [finRotate_apply, add_assoc, htwo, add_zero] using h
  have hz : (2 : Fin n) = 0 := add_left_cancel he
  have hv := congrArg Fin.val hz
  norm_num [Fin.val_natCast, Nat.mod_eq_of_lt (show 2 < n by omega)] at hv

private theorem cover_omits_interior {n : ℕ} (hn : 3 ≤ n) (j : Fin n)
    (C : Set (Fin n)) (hc : MinimalCutCover j C)
    (he : j ∈ C ∨ finRotate n j ∈ C) :
    ∃ i : Fin n, i ∉ C ∧ i ≠ j ∧ i ≠ finRotate n j := by
  classical
  by_contra! hnone
  have hall : ∀ i : Fin n, i ≠ j → i ≠ finRotate n j → i ∈ C := by
    intro i hij hir
    by_contra hi
    exact hir (hnone i hi hij)
  have hp := ((minimalCutCover_iff_private (by omega) j C).mp hc).2
  rcases he with hj | hr
  · obtain ⟨k, hkj, hk⟩ := hp j hj
    rcases hk with ⟨hjk, _⟩ | ⟨hjr, hkC⟩
    · exact hkj hjk.symm
    · have hkr : k ≠ finRotate n j := by
        intro heq
        have hbad : finRotate n (finRotate n j) = j := by rw [← heq, ← hjr]
        exact rotate_twice_ne hn j hbad
      exact hkC (hall k hkj hkr)
  · obtain ⟨k, hkj, hk⟩ := hp (finRotate n j) hr
    rcases hk with ⟨hrk, hrC⟩ | ⟨hrr, _⟩
    · have hrj : finRotate n k ≠ j := by
        intro heq
        exact rotate_twice_ne hn j (by rw [hrk, heq])
      have hrr : finRotate n k ≠ finRotate n j := by
        intro heq
        exact hkj ((finRotate n).injective heq)
      exact hrC (hall (finRotate n k) hrj hrr)
    · exact hkj ((finRotate n).injective hrr).symm

/-- Complete fixed-tag inverse: no additional privacy condition is assumed. -/
theorem alphaSet_admissible_iff {n : ℕ} (hn : 3 ≤ n) (j : Fin n) (C : Set (Fin n)) :
    Admissible (alphaSet j C) ↔
      MinimalCutCover j C ∧ (j ∈ C ∨ finRotate n j ∈ C) := by
  constructor
  · intro h
    have he := (alphaSet_admissible_with_interior_iff hn j C).mp h
    exact ⟨he.1, he.2.1⟩
  · rintro ⟨hc, he⟩
    exact (alphaSet_admissible_with_interior_iff hn j C).mpr
      ⟨hc, he, cover_omits_interior hn j C hc he⟩

end D5.S3.Combinatorics.Graph.Domination.TrapezohedralMinimalDomination
