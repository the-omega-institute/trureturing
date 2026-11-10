/- GID: D5/S3/Geometry/FiniteMatchingCoreClosure
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteMatchingCoreClosure
   mirror-E: none(waiver:finite-critical-face-closure)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Iterated matching closure has bounded dimension and a maximal critical antichain with full proper boundaries. -/
import D5.S3.Geometry.FiniteMatchingCollapse

/-! UNCOMPILED. The closure is an actual bounded finite iteration. Each step
adds every nonempty subface of an upper whose lower is already present.
Empty subfaces occur only through AugmentedFace in the boundary theorem.
The cardinal bound D means simplicial dimension at most D-1. D=1 is allowed.
-/

noncomputable section
open Set Finset

namespace D5.S3.Geometry.FiniteMatchingCoreClosure

open FiniteAcyclicFaceMatching FiniteElementaryCollapse
open FiniteRelativeSimplicialCollapse
open FiniteComponentClosure (vertexComplex)
open FiniteVertexDominationCollapse (faceSet mem_faceSet)

variable {V : Type*} [Fintype V] [DecidableEq V]

def iterate (f : Finset (Finset V) → Finset (Finset V))
    (S : Finset (Finset V)) : Nat → Finset (Finset V)
  | 0 => S
  | n + 1 => f (iterate f S n)

/-- Inflation alone forces stabilization by the number of possible faces.
This is a bound for an arbitrary finite closure algorithm, not an enumeration
of small complexes or a hypothesis that the desired endpoint exists. -/
theorem iterate_stable (f : Finset (Finset V) → Finset (Finset V))
    (hf : ∀ S, S ⊆ f S) (S : Finset (Finset V)) :
    f (iterate f S (Fintype.card (Finset V))) =
      iterate f S (Fintype.card (Finset V)) := by
  classical
  let N := Fintype.card (Finset V)
  let A := iterate f S
  have hafter : ∀ i, f (A i) = A i → ∀ k, A (i + k) = A i := by
    intro i hi k
    induction k with
    | zero => simp
    | succ k ih =>
        change f (A (i + k)) = A i
        rw [ih, hi]
  by_contra hN
  have hn : ∀ i, i ≤ N → f (A i) ≠ A i := by
    intro i hi he
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hi
    have hsame : A N = A i := by simpa only [hk] using hafter i he k
    exact hN (by rw [hsame, he])
  have hgrow : ∀ i, i ≤ N + 1 → i ≤ (A i).card := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ i ih =>
        intro hi
        have hiN : i ≤ N := by omega
        have hlt : (A i).card < (A (i + 1)).card := by
          apply Finset.card_lt_card
          refine Finset.ssubset_iff_subset_ne.mpr ⟨hf (A i), ?_⟩
          intro he
          exact hn i hiN he.symm
        have hprev := ih (by omega)
        omega
  have hbound : (A (N + 1)).card ≤ N := by
    have h := Finset.card_le_card (Finset.subset_univ (A (N + 1)))
    simpa [N] using h
  have h := hgrow (N + 1) le_rfl
  omega

def Downward (S : Finset (Finset V)) : Prop :=
  ∀ s ∈ S, ∀ t ⊆ s, t.Nonempty → t ∈ S

namespace Pairing

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

def seed (_M : Pairing K) (Q : Finset (Finset V)) : Finset (Finset V) := by
  classical exact Finset.univ.filter fun s => s.Nonempty ∧ ∃ q ∈ Q, s ⊆ q

def expand (S : Finset (Finset V)) : Finset (Finset V) := by
  classical exact S ∪ Finset.univ.filter fun s =>
    s.Nonempty ∧ ∃ e ∈ M.pairs, e.1 ∈ S ∧ s ⊆ upper e

@[simp] theorem mem_seed (Q : Finset (Finset V)) (s : Finset V) :
    s ∈ M.seed Q ↔ s.Nonempty ∧ ∃ q ∈ Q, s ⊆ q := by
  classical simp [seed]

@[simp] theorem mem_expand (S : Finset (Finset V)) (s : Finset V) :
    s ∈ M.expand S ↔ s ∈ S ∨
      (s.Nonempty ∧ ∃ e ∈ M.pairs, e.1 ∈ S ∧ s ⊆ upper e) := by
  classical simp [expand]

theorem expand_inflationary (S : Finset (Finset V)) : S ⊆ M.expand S := by
  intro s hs
  exact (M.mem_expand S s).mpr (Or.inl hs)

theorem seed_downward (Q : Finset (Finset V)) : Downward (M.seed Q) := by
  intro s hs t hts ht
  obtain ⟨_, q, hq, hsq⟩ := (M.mem_seed Q s).mp hs
  exact (M.mem_seed Q t).mpr ⟨ht, q, hq, hts.trans hsq⟩

theorem expand_downward {S : Finset (Finset V)} (hS : Downward S) :
    Downward (M.expand S) := by
  intro s hs t hts ht
  rcases (M.mem_expand S s).mp hs with hs | ⟨_, e, he, hl, hsu⟩
  · exact (M.mem_expand S t).mpr (Or.inl (hS s hs t hts ht))
  · exact (M.mem_expand S t).mpr (Or.inr ⟨ht, e, he, hl, hts.trans hsu⟩)

def stage (Q : Finset (Finset V)) (n : Nat) : Finset (Finset V) :=
  iterate M.expand (M.seed Q) n

def closureFaces (Q : Finset (Finset V)) : Finset (Finset V) :=
  M.stage Q (Fintype.card (Finset V))

theorem closure_fixed (Q : Finset (Finset V)) :
    M.expand (M.closureFaces Q) = M.closureFaces Q :=
  iterate_stable M.expand M.expand_inflationary (M.seed Q)

theorem stage_downward (Q : Finset (Finset V)) (n : Nat) :
    Downward (M.stage Q n) := by
  induction n with
  | zero => exact M.seed_downward Q
  | succ n ih => exact M.expand_downward ih

theorem stage_nonempty (Q : Finset (Finset V)) (n : Nat) :
    ∀ s ∈ M.stage Q n, s.Nonempty := by
  induction n with
  | zero => exact fun s hs => ((M.mem_seed Q s).mp hs).1
  | succ n ih =>
      intro s hs
      rcases (M.mem_expand (M.stage Q n) s).mp hs with hs | hs
      · exact ih s hs
      · exact hs.1

theorem stage_le_ambient (Q : Finset (Finset V)) (hQ : ∀ q ∈ Q, q ∈ K)
    (n : Nat) : ∀ s ∈ M.stage Q n, s ∈ K := by
  induction n with
  | zero =>
      intro s hs
      obtain ⟨hsn, q, hq, hsq⟩ := (M.mem_seed Q s).mp hs
      exact (K.isRelLowerSet_faces (hQ q hq)).2 hsq hsn
  | succ n ih =>
      intro s hs
      rcases (M.mem_expand (M.stage Q n) s).mp hs with hs | ⟨hsn, e, he, _, hsu⟩
      · exact ih s hs
      · exact (K.isRelLowerSet_faces (M.upper_mem e he)).2 hsu hsn

/-- Native nonempty complex; the missing empty face is not a point. -/
def closure (Q : Finset (Finset V)) : PreAbstractSimplicialComplex V where
  faces := {s | s ∈ M.closureFaces Q}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨M.stage_nonempty Q _ s hs, fun t hts ht =>
      M.stage_downward Q _ s hs t hts ht⟩

theorem closure_le (Q : Finset (Finset V)) (hQ : ∀ q ∈ Q, q ∈ K) :
    M.closure Q ≤ K := M.stage_le_ambient Q hQ _

theorem seed_le_stage (Q : Finset (Finset V)) (n : Nat) :
    M.seed Q ⊆ M.stage Q n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact ih.trans (M.expand_inflationary _)

theorem seed_mem_closure (Q : Finset (Finset V)) {q : Finset V}
    (hq : q ∈ Q) (hqn : q.Nonempty) : q ∈ M.closure Q :=
  M.seed_le_stage Q _ ((M.mem_seed Q q).mpr ⟨hqn, q, hq, le_rfl⟩)

theorem closure_saturated (Q : Finset (Finset V)) : M.Saturated (M.closure Q) := by
  intro e he
  constructor
  · intro hl
    have hu : upper e ∈ M.expand (M.closureFaces Q) :=
      (M.mem_expand _ _).mpr (Or.inr
        ⟨(M.lower_nonempty e he).mono (subset_insert _ _), e, he, hl, le_rfl⟩)
    simpa only [M.closure_fixed Q] using hu
  · intro hu
    exact M.stage_downward Q _ _ hu _ (subset_insert _ _) (M.lower_nonempty e he)

/-- Leastness also certifies that no gratuitous faces are introduced. -/
theorem closure_le_saturated (Q : Finset (Finset V))
    (T : PreAbstractSimplicialComplex V) (hT : M.Saturated T)
    (hQ : ∀ q ∈ Q, q ∈ T) : M.closure Q ≤ T := by
  have hi : ∀ n, ∀ s ∈ M.stage Q n, s ∈ T := by
    intro n
    induction n with
    | zero =>
        intro s hs
        obtain ⟨hsn, q, hq, hsq⟩ := (M.mem_seed Q s).mp hs
        exact (T.isRelLowerSet_faces (hQ q hq)).2 hsq hsn
    | succ n ih =>
        intro s hs
        rcases (M.mem_expand (M.stage Q n) s).mp hs with hs | ⟨hsn, e, he, hl, hsu⟩
        · exact ih s hs
        · exact (T.isRelLowerSet_faces ((hT e he).mp (ih _ hl))).2 hsu hsn
  exact hi _

/-- The second invariant is essential: a face at the top allowed dimension
can never be a matched LOWER, even if it was introduced as an upper. -/
def DimensionInvariant (D : Nat) (S : Finset (Finset V)) : Prop :=
  ∀ s ∈ S, s.card ≤ D ∧ ∀ e ∈ M.pairs, s = e.1 → s.card < D

theorem seed_dimension (Q : Finset (Finset V)) (D : Nat)
    (hcard : ∀ q ∈ Q, q.card ≤ D)
    (hcrit : ∀ q ∈ Q, M.Unmatched q) : M.DimensionInvariant D (M.seed Q) := by
  intro s hs
  obtain ⟨_, q, hq, hsq⟩ := (M.mem_seed Q s).mp hs
  have hsc : s.card ≤ D := (Finset.card_le_card hsq).trans (hcard q hq)
  refine ⟨hsc, ?_⟩
  intro e he hse
  by_contra hnot
  have hqc : q.card ≤ s.card := by have h := hcard q hq; omega
  have heq : s = q := Finset.eq_of_subset_of_card_le hsq hqc
  exact hcrit q hq e he (Or.inl (heq.symm.trans hse))

theorem expand_dimension (D : Nat) {S : Finset (Finset V)}
    (hS : M.DimensionInvariant D S) : M.DimensionInvariant D (M.expand S) := by
  intro s hs
  rcases (M.mem_expand S s).mp hs with hs | ⟨_, e, he, hl, hsu⟩
  · exact hS s hs
  · have hlc : e.1.card < D := (hS e.1 hl).2 e he rfl
    have huc : (upper e).card ≤ D := by
      have hu : (upper e).card = e.1.card + 1 :=
        Finset.card_insert_of_notMem (M.apex_notMem e he)
      omega
    have hsc : s.card ≤ D := (Finset.card_le_card hsu).trans huc
    refine ⟨hsc, ?_⟩
    intro f hf hsf
    by_contra hnot
    have heq : s = upper e := Finset.eq_of_subset_of_card_le hsu (by omega)
    have hef : e = f := M.disjoint e he f hf s (Or.inr heq) (Or.inl hsf)
    subst f
    exact M.lower_ne_upper he (hsf.symm.trans heq)

theorem closure_dimension (Q : Finset (Finset V)) (D : Nat)
    (hcard : ∀ q ∈ Q, q.card ≤ D)
    (hcrit : ∀ q ∈ Q, M.Unmatched q) :
    ∀ s ∈ M.closure Q, s.card ≤ D := by
  have hi : ∀ n, M.DimensionInvariant D (M.stage Q n) := by
    intro n
    induction n with
    | zero => exact M.seed_dimension Q D hcard hcrit
    | succ n ih => exact M.expand_dimension D ih
  exact fun s hs => (hi _ s hs).1

end Pairing

open Pairing

/-- Exact unmatched data. None of the fields asserts a collapse or topology.
The singleton point is separate from the distinct same-cardinality critical
faces. Their common cardinality D is positive, including the discrete case. -/
structure CriticalData {K : PreAbstractSimplicialComplex V} (M : Pairing K) where
  p : V
  critical : Finset (Finset V)
  D : Nat
  positive : 0 < D
  point_mem : ({p} : Finset V) ∈ K
  critical_mem : ∀ s ∈ critical, s ∈ K
  point_not_critical : ({p} : Finset V) ∉ critical
  cardinality : ∀ s ∈ critical, s.card = D
  unmatched : ∀ s ∈ K, M.Unmatched s ↔ s = {p} ∨ s ∈ critical

namespace CriticalData

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

def seeds : Finset (Finset V) := insert {A.p} A.critical

def X : PreAbstractSimplicialComplex V := M.closure A.seeds

theorem seeds_mem : ∀ s ∈ A.seeds, s ∈ K := by
  intro s hs
  rcases Finset.mem_insert.mp hs with rfl | hs
  · exact A.point_mem
  · exact A.critical_mem s hs

theorem seeds_unmatched : ∀ s ∈ A.seeds, M.Unmatched s := by
  intro s hs
  apply (A.unmatched s (A.seeds_mem s hs)).mpr
  exact Finset.mem_insert.mp hs

theorem seeds_card : ∀ s ∈ A.seeds, s.card ≤ A.D := by
  intro s hs
  rcases Finset.mem_insert.mp hs with rfl | hs
  · simpa using A.positive
  · exact (A.cardinality s hs).le

theorem X_le : A.X ≤ K := M.closure_le A.seeds A.seeds_mem

theorem X_saturated : M.Saturated A.X := M.closure_saturated A.seeds

theorem X_dimension : ∀ s ∈ A.X, s.card ≤ A.D :=
  M.closure_dimension A.seeds A.D A.seeds_card A.seeds_unmatched

theorem critical_nonempty {s : Finset V} (hs : s ∈ A.critical) : s.Nonempty :=
  (K.isRelLowerSet_faces (A.critical_mem s hs)).1

theorem critical_in_X {s : Finset V} (hs : s ∈ A.critical) : s ∈ A.X :=
  M.seed_mem_closure A.seeds (Finset.mem_insert_of_mem hs) (A.critical_nonempty hs)

theorem point_in_X : ({A.p} : Finset V) ∈ A.X :=
  M.seed_mem_closure A.seeds (Finset.mem_insert_self _ _) (Finset.singleton_nonempty _)

/-- Every critical simplex is maximal in the ACTUAL closure. -/
theorem critical_maximal {s t : Finset V} (hs : s ∈ A.critical)
    (ht : t ∈ A.X) (hst : s ⊆ t) : s = t :=
  Finset.eq_of_subset_of_card_le hst (by rw [A.cardinality s hs]; exact A.X_dimension t ht)

theorem critical_antichain {s t : Finset V} (hs : s ∈ A.critical)
    (ht : t ∈ A.critical) (hst : s ⊆ t) : s = t :=
  A.critical_maximal hs (A.critical_in_X ht) hst

/-- Delete only the maximal unmatched critical faces, not their boundaries. -/
def C : PreAbstractSimplicialComplex V where
  faces := {s | s ∈ A.X ∧ s ∉ A.critical}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨(A.X.isRelLowerSet_faces hs.1).1, ?_⟩
    intro t hts ht
    refine ⟨(A.X.isRelLowerSet_faces hs.1).2 hts ht, ?_⟩
    intro htc
    exact hs.2 (A.critical_maximal htc hs.1 hts ▸ htc)

theorem mem_C (s : Finset V) : s ∈ A.C ↔ s ∈ A.X ∧ s ∉ A.critical := Iff.rfl

theorem C_le_X : A.C ≤ A.X := fun _ hs => hs.1

theorem point_in_C : ({A.p} : Finset V) ∈ A.C :=
  ⟨A.point_in_X, A.point_not_critical⟩

theorem vertex_le_C : vertexComplex A.p ≤ A.C := by
  intro s hs
  have he : s = {A.p} := Set.mem_singleton_iff.mp hs
  simpa only [he] using A.point_in_C

/-- Includes the augmented empty subface without treating it as a point. -/
theorem proper_boundary {s t : Finset V} (hs : s ∈ A.critical) (hts : t ⊂ s) :
    AugmentedFace A.C t := by
  by_cases ht : t = ∅
  · exact Or.inl ht
  · refine Or.inr ⟨(A.X.isRelLowerSet_faces (A.critical_in_X hs)).2
      hts.subset (Finset.nonempty_iff_ne_empty.mpr ht), ?_⟩
    intro htc
    exact hts.ne (A.critical_antichain htc hs hts.subset)

theorem X_core_equation (s : Finset V) :
    s ∈ A.X ↔ s ∈ A.C ∨ s ∈ A.critical := by
  constructor
  · intro hs
    by_cases hc : s ∈ A.critical
    · exact Or.inr hc
    · exact Or.inl ⟨hs, hc⟩
  · rintro (hs | hs)
    · exact hs.1
    · exact A.critical_in_X hs

/-- Literal simplex-attachment equation on the same original ground. -/
theorem X_cell_equation (s : Finset V) :
    s ∈ A.X ↔ s ∈ A.C ∨ (s.Nonempty ∧ ∃ t ∈ A.critical, s ⊆ t) := by
  constructor
  · intro hs
    rcases (A.X_core_equation s).mp hs with hc | ht
    · exact Or.inl hc
    · exact Or.inr ⟨A.critical_nonempty ht, s, ht, le_rfl⟩
  · rintro (hs | ⟨hn, t, ht, hst⟩)
    · exact hs.1
    · exact (A.X.isRelLowerSet_faces (A.critical_in_X ht)).2 hst hn

theorem boundary_in_core_iff {s t : Finset V} (hs : s ∈ A.critical) (hts : t ⊆ s) :
    AugmentedFace A.C t ↔ t ≠ s := by
  constructor
  · intro ht heq
    subst t
    rcases ht with he | hc
    · exact (A.critical_nonempty hs).ne_empty he
    · exact hc.2 hs
  · intro hne
    exact A.proper_boundary hs (Finset.ssubset_iff_subset_ne.mpr ⟨hts, hne⟩)

theorem critical_unmatched {s : Finset V} (hs : s ∈ A.critical) : M.Unmatched s :=
  (A.unmatched s (A.critical_mem s hs)).mpr (Or.inr hs)

theorem point_unmatched : M.Unmatched {A.p} :=
  (A.unmatched _ A.point_mem).mpr (Or.inl rfl)

theorem C_saturated : M.Saturated A.C := by
  intro e he
  have hlc : e.1 ∉ A.critical := fun hc =>
    A.critical_unmatched hc e he (Or.inl rfl)
  have huc : upper e ∉ A.critical := fun hc =>
    A.critical_unmatched hc e he (Or.inr rfl)
  exact ⟨fun h => ⟨(A.X_saturated e he).mp h.1, huc⟩,
    fun h => ⟨(A.X_saturated e he).mpr h.1, hlc⟩⟩

theorem vertex_saturated : M.Saturated (vertexComplex A.p) := by
  intro e he
  have hl : e.1 ∉ vertexComplex A.p := by
    intro h
    exact A.point_unmatched e he (Or.inl (Set.mem_singleton_iff.mp h).symm)
  have hu : upper e ∉ vertexComplex A.p := by
    intro h
    exact A.point_unmatched e he (Or.inr (Set.mem_singleton_iff.mp h).symm)
  exact ⟨fun h => (hl h).elim, fun h => (hu h).elim⟩

theorem core_unmatched {s : Finset V} (hs : s ∈ A.C) :
    M.Unmatched s ↔ s = {A.p} := by
  constructor
  · intro hu
    exact ((A.unmatched s (A.X_le hs.1)).mp hu).resolve_right hs.2
  · intro he
    simpa only [he] using A.point_unmatched

/-- In dimension zero the closure is literally discrete; no empty lower pair
is used. This is a conclusion of the cardinal invariant, not a special axiom. -/
theorem discrete_when_D_one (hD : A.D = 1) {s : Finset V} (hs : s ∈ A.X) :
    ∃ v, s = {v} := by
  have hle := A.X_dimension s hs
  have hpos := Finset.card_pos.mpr ((A.X.isRelLowerSet_faces hs).1)
  have hc : s.card = 1 := by omega
  exact Finset.card_eq_one.mp hc

end CriticalData
end D5.S3.Geometry.FiniteMatchingCoreClosure
