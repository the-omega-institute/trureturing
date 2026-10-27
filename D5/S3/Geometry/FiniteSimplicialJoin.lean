/- GID: D5/S3/Geometry/FiniteSimplicialJoin
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteSimplicialJoin
   mirror-E: none(waiver:finite-simplicial-join)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic, mathlib/module/Mathlib.Topology.Homeomorph.Lemmas]
   utility: none
   digest: The barycentric map identifies the ordinary quotient join with the actual finite simplicial join realization. -/
import D5.S3.Geometry.FiniteConeCollapse
import Mathlib.Analysis.Convex.Topology
import Mathlib.Data.Finset.Sum
import Mathlib.Topology.Homeomorph.Lemmas

/-!
The ordinary join forgets the right factor at zero and the left factor at one.
The simplicial join has nonempty faces, allowing either tagged block to be empty.
Both factor realizations must be nonempty for the barycentric identification.
This is the classical finite realization theorem, not a solution of Question 22.
-/

noncomputable section
open Set Finset Topology
open scoped BigOperators unitInterval

namespace D5.S3.Geometry.FiniteSimplicialJoin

/-- Endpoint identifications on the actual product with the closed unit interval. -/
def ordinaryJoinSetoid (X Y : Type*) : Setoid (X × Y × I) where
  r p q := p.2.2 = q.2.2 ∧ (p.2.2 = 1 ∨ p.1 = q.1) ∧
    (p.2.2 = 0 ∨ p.2.1 = q.2.1)
  iseqv := {
    refl := fun _ => ⟨rfl, Or.inr rfl, Or.inr rfl⟩
    symm := by
      rintro p q ⟨ht, hx, hy⟩
      exact ⟨ht.symm, hx.elim (fun h => Or.inl (ht ▸ h)) (fun h => Or.inr h.symm),
        hy.elim (fun h => Or.inl (ht ▸ h)) (fun h => Or.inr h.symm)⟩
    trans := by
      rintro p q r ⟨ht, hx, hy⟩ ⟨hu, hxx, hyy⟩
      refine ⟨ht.trans hu, ?_, ?_⟩
      · rcases hx with h | h
        · exact Or.inl h
        · rcases hxx with h' | h'
          · exact Or.inl (ht.trans h')
          · exact Or.inr (h.trans h')
      · rcases hy with h | h
        · exact Or.inl h
        · rcases hyy with h' | h'
          · exact Or.inl (ht.trans h')
          · exact Or.inr (h.trans h') }

/-- Ordinary join, equipped with Lean's native quotient topology. -/
abbrev OrdinaryJoin (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :=
  Quotient (ordinaryJoinSetoid X Y)

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- Nonempty tagged faces whose nonempty blocks are faces of the factors. -/
def simplicialJoin (M : PreAbstractSimplicialComplex V)
    (N : PreAbstractSimplicialComplex W) : PreAbstractSimplicialComplex (V ⊕ W) where
  faces := {s | s.Nonempty ∧ (s.toLeft = ∅ ∨ s.toLeft ∈ M) ∧
    (s.toRight = ∅ ∨ s.toRight ∈ N)}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hl, hr⟩
    refine ⟨hs, ?_⟩
    intro r hrs hn
    refine ⟨hn, ?_, ?_⟩
    · by_cases he : r.toLeft = ∅
      · exact Or.inl he
      · right
        rcases hl with h | h
        · exact (he (Finset.eq_empty_iff_forall_notMem.mpr (by
            intro v hv
            have := Finset.toLeft_subset_toLeft hrs hv
            simpa [h] using this))).elim
        · exact (M.isRelLowerSet_faces h).2 (Finset.toLeft_subset_toLeft hrs)
            (Finset.nonempty_iff_ne_empty.mpr he)
    · by_cases he : r.toRight = ∅
      · exact Or.inl he
      · right
        rcases hr with h | h
        · exact (he (Finset.eq_empty_iff_forall_notMem.mpr (by
            intro v hv
            have := Finset.toRight_subset_toRight hrs hv
            simpa [h] using this))).elim
        · exact (N.isRelLowerSet_faces h).2 (Finset.toRight_subset_toRight hrs)
            (Finset.nonempty_iff_ne_empty.mpr he)

open FiniteConeCollapse

variable [Fintype V] [Fintype W]
variable (M : PreAbstractSimplicialComplex V) (N : PreAbstractSimplicialComplex W)

/-- The previously defined actual coordinate realization, as a topological space. -/
abbrev Space (M : PreAbstractSimplicialComplex V) := ↥(realization M)

private theorem point_data (x : Space M) :
    (∀ v, 0 ≤ x.val v) ∧ (∑ v, x.val v) = 1 := by
  obtain ⟨s, hs, hx⟩ := x.property
  rw [← faceSimplex_eq_convexHull] at hx
  exact ⟨hx.1, hx.2.1⟩

private theorem compact_realization : IsCompact (realization M) := by
  have he : realization M = ⋃ s ∈ M.faces,
      convexHull ℝ ((fun v : V => Pi.single v (1 : ℝ)) '' (s : Set V)) := by
    ext x
    constructor
    · rintro ⟨s, hs, hx⟩
      exact Set.mem_iUnion₂.mpr ⟨s, hs, hx⟩
    · intro hx
      obtain ⟨s, hs, hx⟩ := Set.mem_iUnion₂.mp hx
      exact ⟨s, hs, hx⟩
  rw [he]
  exact (Set.toFinite M.faces).isCompact_biUnion fun s _ =>
    (s.finite_toSet.image _).isCompact_convexHull ℝ

/-- The barycentric formula on representatives in the actual factor realizations. -/
def representative (p : Space M × Space N × I) : (V ⊕ W) → ℝ :=
  Sum.elim (fun v => (1 - (p.2.2 : ℝ)) * p.1.val v)
    (fun w => (p.2.2 : ℝ) * p.2.1.val w)

private theorem representative_mem (p : Space M × Space N × I) :
    representative M N p ∈ realization (simplicialJoin M N) := by
  obtain ⟨s, hs, hx⟩ := p.1.property
  obtain ⟨r, hr, hy⟩ := p.2.1.property
  rw [← faceSimplex_eq_convexHull] at hx hy
  refine ⟨s.disjSum r, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · obtain ⟨v, hv⟩ := (M.isRelLowerSet_faces hs).1
      exact ⟨Sum.inl v, by simpa using hv⟩
    · exact Or.inr (by simpa using hs)
    · exact Or.inr (by simpa using hr)
  · rw [← faceSimplex_eq_convexHull]
    refine ⟨?_, ?_, ?_⟩
    · intro v
      cases v with
      | inl v => exact mul_nonneg (sub_nonneg.mpr p.2.2.property.2) (hx.1 v)
      | inr w => exact mul_nonneg p.2.2.property.1 (hy.1 w)
    · simp only [representative, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        ← Finset.mul_sum, hx.2.1, hy.2.1, mul_one]
      ring
    · intro v hv
      cases v with
      | inl v => simp only [inl_mem_disjSum] at hv; simp [representative, hx.2.2 v hv]
      | inr w => simp only [inr_mem_disjSum] at hv; simp [representative, hy.2.2 w hv]

private theorem continuous_representative : Continuous (representative M N) := by
  apply continuous_pi
  intro v
  cases v with
  | inl v =>
    exact (continuous_const.sub (continuous_subtype_val.comp
      (continuous_snd.comp continuous_snd))).mul
      ((continuous_apply v).comp (continuous_subtype_val.comp continuous_fst))
  | inr w =>
    exact (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)).mul
      ((continuous_apply w).comp (continuous_subtype_val.comp
        (continuous_fst.comp continuous_snd)))

private theorem right_mass (p : Space M × Space N × I) :
    (∑ w, representative M N p (.inr w)) = (p.2.2 : ℝ) := by
  simp [representative, ← Finset.mul_sum, (point_data N p.2.1).2]

/-- The barycentric map has exactly the ordinary join's endpoint fibers. -/
theorem representative_eq_iff (p q : Space M × Space N × I) :
    representative M N p = representative M N q ↔
      (ordinaryJoinSetoid (Space M) (Space N)).r p q := by
  constructor
  · intro h
    have ht : p.2.2 = q.2.2 := Subtype.ext (by
      rw [← right_mass M N p, ← right_mass M N q, h])
    refine ⟨ht, ?_, ?_⟩
    · by_cases he : p.2.2 = 1
      · exact Or.inl he
      · right
        apply Subtype.ext
        funext v
        have hc := congrFun h (Sum.inl v)
        change (1 - (p.2.2 : ℝ)) * p.1.val v =
          (1 - (q.2.2 : ℝ)) * q.1.val v at hc
        rw [← ht] at hc
        exact mul_left_cancel₀ (sub_ne_zero.mpr (fun hh => he (Subtype.ext hh.symm))) hc
    · by_cases he : p.2.2 = 0
      · exact Or.inl he
      · right
        apply Subtype.ext
        funext w
        have hc := congrFun h (Sum.inr w)
        change (p.2.2 : ℝ) * p.2.1.val w = (q.2.2 : ℝ) * q.2.1.val w at hc
        rw [← ht] at hc
        exact mul_left_cancel₀ (fun hh => he (Subtype.ext hh)) hc
  · rintro ⟨ht, hx, hy⟩
    funext v
    cases v with
    | inl v =>
      rcases hx with hx | hx
      · simp [representative, ← ht, hx]
      · simp [representative, ← ht, hx]
    | inr w =>
      rcases hy with hy | hy
      · simp [representative, ← ht, hy]
      · simp [representative, ← ht, hy]

/-- A normalized block in an actual factor; a zero block uses a chosen actual point. -/
private theorem factor_of_mass (x₀ : Space M) (s : Finset V)
    (hs : s = ∅ ∨ s ∈ M) (f : V → ℝ) (hf : ∀ v, 0 ≤ f v)
    (hz : ∀ v ∉ s, f v = 0) (m : ℝ) (hm : 0 ≤ m) (hmass : ∑ v, f v = m) :
    ∃ x : Space M, ∀ v, m * x.val v = f v := by
  by_cases he : m = 0
  · refine ⟨x₀, ?_⟩
    intro v
    have hv := Finset.single_le_sum (fun w _ => hf w) (Finset.mem_univ v)
    rw [hmass, he] at hv
    simp [he, le_antisymm hv (hf v)]
  · have hpos : 0 < m := lt_of_le_of_ne hm (Ne.symm he)
    have hs' : s ∈ M := by
      rcases hs with hs | hs
      · have hfzero : ∀ v, f v = 0 := fun v => hz v (by simp [hs])
        have : m = 0 := by rw [← hmass]; simp [hfzero]
        exact (he this).elim
      · exact hs
    have hx : (fun v => f v / m) ∈ faceSimplex s := by
      refine ⟨fun v => div_nonneg (hf v) hm, ?_, ?_⟩
      · simp [← Finset.sum_div, hmass, he]
      · intro v hv
        simp [hz v hv]
    refine ⟨⟨(fun v => f v / m), s, hs', ?_⟩, ?_⟩
    · rwa [faceSimplex_eq_convexHull] at hx
    · intro v
      exact mul_div_cancel₀ (f v) he

private theorem representative_surjective (hM : Nonempty (Space M)) (hN : Nonempty (Space N)) :
    ∀ z : Space (simplicialJoin M N), ∃ p : Space M × Space N × I,
      representative M N p = z.val := by
  intro z
  obtain ⟨s, hs, hz⟩ := z.property
  rw [← faceSimplex_eq_convexHull] at hz
  have hs' : s.Nonempty ∧ (s.toLeft = ∅ ∨ s.toLeft ∈ M) ∧
      (s.toRight = ∅ ∨ s.toRight ∈ N) := hs
  let t : ℝ := ∑ w, z.val (Sum.inr w)
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun w _ => hz.1 _
  have hl0 : 0 ≤ ∑ v, z.val (Sum.inl v) := Finset.sum_nonneg fun v _ => hz.1 _
  have htot : (∑ v, z.val (Sum.inl v)) + t = 1 := by
    simpa only [Fintype.sum_sum_type] using hz.2.1
  have ht1 : t ≤ 1 := by linarith
  obtain ⟨x, hx⟩ := factor_of_mass M (Classical.choice hM) s.toLeft hs'.2.1
    (fun v => z.val (Sum.inl v)) (fun v => hz.1 _) (fun v hv => hz.2.2 _ (by simpa using hv))
    (1-t) (by linarith) (by linarith)
  obtain ⟨y, hy⟩ := factor_of_mass N (Classical.choice hN) s.toRight hs'.2.2
    (fun w => z.val (Sum.inr w)) (fun w => hz.1 _) (fun w hw => hz.2.2 _ (by simpa using hw))
    t ht0 rfl
  refine ⟨(x, y, ⟨t, ht0, ht1⟩), ?_⟩
  funext v
  cases v with
  | inl v => exact hx v
  | inr w => exact hy w

/-- The continuous map out of the ordinary join, given by the barycentric formula. -/
def realizationMap : OrdinaryJoin (Space M) (Space N) → Space (simplicialJoin M N) :=
  Quotient.lift (fun p => ⟨representative M N p, representative_mem M N p⟩)
    (fun p q h => Subtype.ext ((representative_eq_iff M N p q).2 h))

private theorem continuous_realizationMap : Continuous (realizationMap M N) :=
  (continuous_representative M N).subtype_mk _ |>.quotient_lift _

private theorem realizationMap_bijective (hM : Nonempty (Space M)) (hN : Nonempty (Space N)) :
    Function.Bijective (realizationMap M N) := by
  constructor
  · intro p q
    refine Quotient.inductionOn₂ p q ?_
    intro a b h
    exact Quotient.sound ((representative_eq_iff M N a b).1 (congrArg Subtype.val h))
  · intro z
    obtain ⟨p, hp⟩ := representative_surjective M N hM hN z
    exact ⟨Quotient.mk _ p, Subtype.ext hp⟩

/-- The ordinary topological join of the actual nonempty realizations is homeomorphic
    to the actual realization of the nonempty-face simplicial join. -/
def joinHomeomorph (hM : Nonempty (Space M)) (hN : Nonempty (Space N)) :
    OrdinaryJoin (Space M) (Space N) ≃ₜ Space (simplicialJoin M N) := by
  letI : CompactSpace (Space M) := isCompact_iff_compactSpace.mp (compact_realization M)
  letI : CompactSpace (Space N) := isCompact_iff_compactSpace.mp (compact_realization N)
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (realizationMap M N) (realizationMap_bijective M N hM hN))
    (continuous_realizationMap M N)

#print axioms representative_eq_iff
#print axioms joinHomeomorph

end D5.S3.Geometry.FiniteSimplicialJoin
