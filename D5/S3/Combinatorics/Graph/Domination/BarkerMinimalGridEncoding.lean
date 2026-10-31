/- GID: D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/BarkerMinimalGridEncoding
   mirror-E: none(waiver:internal-stage-a)
   anchors: []
   utility: none
   digest: Labelled open-grid subsets are encoded by column masks with closed private witnesses. -/

import D5.S3.Combinatorics.Graph.DominatingSetAverageBoundNonstem
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Fintype.Powerset

/-! Exact actual-subset and column-word interfaces for the open three-row grid. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridEncoding

open Finset
open D5.S3.Combinatorics.Graph.DominatingSetAverage
open D5.S3.Combinatorics.Graph.DominatingSetAverageBoundCounting
open D5.S3.Combinatorics.Graph.DominatingSetAverageBoundNonstem

/-- Closed domination and inclusion minimality under every proper subset. -/
def MinimalDominating {V : Type} (G : SimpleGraph V) (S : Finset V) : Prop :=
  G.IsDominating (S : Set V) ∧
    ∀ T : Finset V, T ⊂ S → ¬ G.IsDominating (T : Set V)

/-- A closed neighbourhood includes its centre. -/
def Closed {V : Type} (G : SimpleGraph V) (u v : V) : Prop := u = v ∨ G.Adj u v

/-- A witness is existential information, never an extra counted choice. -/
def ClosedPrivate {V : Type} (G : SimpleGraph V) (S : Finset V) (v z : V) : Prop :=
  Closed G z v ∧ ∀ w ∈ S, Closed G z w → w = v

/-- The closed-private-witness form of minimal domination. The existing critical
vertex and private-neighbour suppliers discharge its two alternatives. This is
Gangloff--Talon, arXiv:1906.10779v2, Proposition 1, in closed-neighbour notation;
the domination premise is retained. -/
theorem minimal_iff_closed_private {V : Type} [Finite V]
    (G : SimpleGraph V) (S : Finset V) :
    MinimalDominating G S ↔ G.IsDominating (S : Set V) ∧
      ∀ v ∈ S, ∃ z, ClosedPrivate G S v z := by
  classical
  let := Fintype.ofFinite V
  constructor
  · intro h
    refine ⟨h.1, fun v hv => ?_⟩
    have hc : v ∈ criticalVertices G S :=
      mem_filter.mpr ⟨hv, h.2 (S.erase v) (erase_ssubset hv)⟩
    by_cases he : v ∈ externallyCritical G S
    · obtain ⟨z, hz, hvz⟩ := (mem_filter.mp he).2
      have hp := (mem_filter.mp hz).2
      obtain ⟨a, ha⟩ := card_eq_one.mp hp.2
      have hva : v = a := by
        have : v ∈ S.filter (G.Adj z) := mem_filter.mpr ⟨hv, G.adj_symm hvz⟩
        simpa [ha] using this
      refine ⟨z, Or.inr (G.adj_symm hvz), ?_⟩
      intro w hw hwz
      rcases hwz with rfl | hwz
      · exact (hp.1 hw).elim
      · have : w ∈ S.filter (G.Adj z) := mem_filter.mpr ⟨hw, hwz⟩
        have hwa : w = a := by simpa [ha] using this
        exact hwa.trans hva.symm
    · have hs : v ∈ selfCritical G S := mem_sdiff.mpr ⟨hc, he⟩
      refine ⟨v, Or.inl rfl, ?_⟩
      intro w hw hwv
      rcases hwv with heq | hadj
      · exact heq.symm
      · exact (selfCritical_no_selected_neighbor G S v h.1 hs w hw hadj).elim
  · rintro ⟨hd, hp⟩
    refine ⟨hd, fun T hT hdom => ?_⟩
    obtain ⟨v, hv, hsub⟩ := ssubset_iff_exists_subset_erase.mp hT
    obtain ⟨z, hzv, huniq⟩ := hp v hv
    have hdel := dominating_mono hdom hsub
    rcases hdel z with hz | ⟨w, hw, hzw⟩
    · have heq := huniq z (mem_of_mem_erase hz) (Or.inl rfl)
      exact (mem_erase.mp hz).1 heq
    · have heq := huniq w (mem_of_mem_erase hw) (Or.inr hzw)
      exact (mem_erase.mp hw).1 heq

/-- Row labels and column labels; translating both by one gives the source labels. -/
abbrev Vertex (n : ℕ) := Fin 3 × Fin n

/-- Ordinary open grid, with adjacency exactly at Manhattan distance one. -/
def grid (n : ℕ) : SimpleGraph (Vertex n) where
  Adj u v := Nat.dist u.1.val v.1.val + Nat.dist u.2.val v.2.val = 1
  symm := ⟨by intro u v h; simpa only [Nat.dist_comm] using h⟩
  loopless := ⟨by intro v; simp⟩

/-- A mask has one selection bit for each of the three labelled rows. -/
abbrev Mask := Fin 3 → Bool

/-- A word contains precisely one mask for every real column. -/
abbrev Word (n : ℕ) := Fin n → Mask

/-- Read the actual subset, without choosing witnesses or identifying symmetries. -/
def encode {n : ℕ} (S : Finset (Vertex n)) : Word n :=
  fun c r => decide ((r, c) ∈ S)

/-- Recover the selected labelled vertices from their column bits. -/
def decode {n : ℕ} (w : Word n) : Finset (Vertex n) :=
  univ.filter fun v => w v.2 v.1 = true

@[simp] theorem mem_decode {n : ℕ} (w : Word n) (v : Vertex n) :
    v ∈ decode w ↔ w v.2 v.1 = true := by simp [decode]

/-- The actual-subset/word bijection, with no quotient and no multiplicity. -/
def subsetWordEquiv (n : ℕ) : Finset (Vertex n) ≃ Word n where
  toFun := encode
  invFun := decode
  left_inv S := by ext v; simp [encode]
  right_inv w := by
    funext c r
    simp [encode]

/-- Absent columns have no vertices; a present mask may still select no rows. -/
abbrev Column := Option Mask

/-- Open padding: even a real empty mask is returned as `some`, never `none`. -/
def padded {n : ℕ} (w : Word n) (c : ℤ) : Column :=
  if h : 0 ≤ c ∧ c < n then some (w ⟨c.toNat, by omega⟩) else none

/-- The exact family of actual inclusion-minimal dominating subsets. -/
noncomputable def minimalSets (n : ℕ) : Finset (Finset (Vertex n)) := by
  classical
  exact univ.filter (MinimalDominating (grid n))

/-- This is the source count, including every actual subset exactly once. -/
noncomputable def actualCount (n : ℕ) : ℕ := (minimalSets n).card

/-- Word acceptance still refers to the independently defined actual graph. -/
def ValidWord {n : ℕ} (w : Word n) : Prop :=
  (grid n).IsDominating (decode w : Set (Vertex n)) ∧
    ∀ v ∈ decode w, ∃ z, ClosedPrivate (grid n) (decode w) v z

/-- Exact acceptance, including all real columns and both open ends. -/
theorem validWord_iff {n : ℕ} (w : Word n) :
    ValidWord w ↔ MinimalDominating (grid n) (decode w) :=
  (minimal_iff_closed_private (grid n) (decode w)).symm

/-- Restricting the bijection preserves exactly the original subset predicate. -/
noncomputable def minimalWordEquiv (n : ℕ) :
    {S : Finset (Vertex n) // MinimalDominating (grid n) S} ≃
      {w : Word n // ValidWord w} :=
  (subsetWordEquiv n).subtypeEquiv fun S => by
    change MinimalDominating (grid n) S ↔ ValidWord (encode S)
    have hd : decode (encode S) = S := (subsetWordEquiv n).left_inv S
    rw [validWord_iff, hd]

/-- Every closed neighbour is at column distance at most one. -/
private theorem closed_column_dist {n : ℕ} {u v : Vertex n}
    (h : Closed (grid n) u v) : Nat.dist u.2.val v.2.val ≤ 1 := by
  rcases h with rfl | h
  · simp
  · change Nat.dist u.1.val v.1.val + Nat.dist u.2.val v.2.val = 1 at h
    omega

/-- A neighbour of a possible private witness lies in the five-column window. -/
private theorem private_window_bound {n : ℕ} {v z u : Vertex n}
    (hz : Closed (grid n) z v) (hu : Closed (grid n) z u) :
    Nat.dist u.2.val v.2.val ≤ 2 := by
  have h₁ := closed_column_dist hz
  have h₂ := closed_column_dist hu
  have ht := Nat.dist.triangle_inequality u.2.val z.2.val v.2.val
  rw [Nat.dist_comm u.2.val z.2.val] at ht
  omega

/-- The column test only inspects selected vertices within two columns of its
centre. Candidate witnesses are actual vertices, so absent columns supply none. -/
def ColumnTest {n : ℕ} (S : Finset (Vertex n)) (c : Fin n) : Prop :=
  (∀ r : Fin 3, ∃ v ∈ S, Closed (grid n) (r, c) v) ∧
    ∀ r : Fin 3, (r, c) ∈ S → ∃ z : Vertex n,
      Closed (grid n) z (r, c) ∧
        ∀ v ∈ S, Nat.dist v.2.val c.val ≤ 2 → Closed (grid n) z v → v = (r, c)

/-- The entire original proper-subset condition is equivalent to the five-column
closed-private-witness test at every real column, for every width. -/
theorem minimal_iff_column_tests {n : ℕ} (S : Finset (Vertex n)) :
    MinimalDominating (grid n) S ↔ ∀ c, ColumnTest S c := by
  rw [minimal_iff_closed_private]
  constructor
  · rintro ⟨hd, hp⟩ c
    constructor
    · intro r
      rcases hd (r, c) with h | ⟨v, hv, hadj⟩
      · exact ⟨(r, c), h, Or.inl rfl⟩
      · exact ⟨v, hv, Or.inr hadj⟩
    · intro r hr
      obtain ⟨z, hz, huniq⟩ := hp (r, c) hr
      exact ⟨z, hz, fun v hv _ h => huniq v hv h⟩
  · intro h
    constructor
    · rintro ⟨r, c⟩
      obtain ⟨u, hu, hclosed⟩ := (h c).1 r
      rcases hclosed with heq | hadj
      · exact Or.inl (heq.symm ▸ hu)
      · exact Or.inr ⟨u, hu, hadj⟩
    · intro v hv
      obtain ⟨z, hz, huniq⟩ := (h v.2).2 v.1 hv
      exact ⟨z, hz, fun u hu hzu => huniq u hu (private_window_bound hz hzu) hzu⟩


end D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridEncoding
