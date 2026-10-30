/- GID: D5/S3/Quantum/Contextuality/LazyTwoCausalJOneFacet
   generality: I
   mirror-B: D5/B/S3/Quantum/Contextuality/LazyTwoCausalJOneFacet
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The lazy two-causal inequality J1 induces a facet for every party count at least two. -/

import D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The lazy binary scenario and inequality (10) of Abbott–Wechs–Costa–Branciard,
    Genuinely Multipartite Noncausality, arXiv:1708.07663v2, Definition 2.
    The affine dimension assertion resolves their all-party facet conjecture. -/

set_option autoImplicit false

noncomputable section

open Finset

namespace D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet

open D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift (labelKernel)

/-- The first nonempty proper group answers from its own inputs; all outputs are lazy. -/
def IsLazyTwoCausalStrategy {n : ℕ} (k : Finset (Fin n))
    (f : Finset (Fin n) → Finset (Fin n)) : Prop :=
  k.Nonempty ∧ k ≠ univ ∧ (∀ t, f t ⊆ t) ∧
    ∀ t u, t ∩ k = u ∩ k → f t ∩ k = f u ∩ k

/-- The convex hull of deterministic two-causal correlations in the lazy binary scenario. -/
def twoCausalPolytope (n : ℕ) : Set (Finset (Fin n) → Finset (Fin n) → ℝ) :=
  convexHull ℝ {p | ∃ k f, IsLazyTwoCausalStrategy k f ∧ p = labelKernel f}

/-- Inequality (10). On a lazy table, inputs supported in `k` force all outputs outside
`k` to zero, so the marginal event that every output in `k` is one is exactly `p k k`. -/
def jOne {n : ℕ} (p : Finset (Fin n) → Finset (Fin n) → ℝ) : ℝ :=
  (∑ k with k.Nonempty ∧ k ≠ univ, p k k) - p univ univ

/-- Validity and codimension one of the zero face for every number of parties at least two. -/
def claim : Prop := ∀ n : ℕ, 2 ≤ n →
  (∀ p ∈ twoCausalPolytope n, 0 ≤ jOne p) ∧
  Module.finrank ℝ (vectorSpan ℝ (twoCausalPolytope n ∩ {p | jOne p = 0})) + 1 =
    Module.finrank ℝ (vectorSpan ℝ (twoCausalPolytope n))

private abbrev Reduced (n : ℕ) :=
  {i : Finset (Fin n) × Finset (Fin n) // i.2.Nonempty ∧ i.2 ⊆ i.1}

private abbrev FaceIndex (n : ℕ) := {i : Reduced n // i.1 ≠ (univ, univ)}

private def jLinear (n : ℕ) : (Finset (Fin n) → Finset (Fin n) → ℝ) →ₗ[ℝ] ℝ where
  toFun := jOne
  map_add' := by
    intro p q
    change (∑ k with k.Nonempty ∧ k ≠ univ, (p k k + q k k)) -
      (p univ univ + q univ univ) = _
    rw [Finset.sum_add_distrib]
    change _ = ((∑ k with k.Nonempty ∧ k ≠ univ, p k k) - p univ univ) +
      ((∑ k with k.Nonempty ∧ k ≠ univ, q k k) - q univ univ)
    ring
  map_smul' := by
    intro c p
    change (∑ k with k.Nonempty ∧ k ≠ univ, c * p k k) - c * p univ univ =
      c * ((∑ k with k.Nonempty ∧ k ≠ univ, p k k) - p univ univ)
    rw [← Finset.mul_sum, mul_sub]

private lemma admissible_group {n : ℕ} (hn : 2 ≤ n) :
    ∃ k : Finset (Fin n), k.Nonempty ∧ k ≠ univ := by
  refine ⟨{⟨0, by omega⟩}, singleton_nonempty _, ?_⟩
  intro h
  have hm : (⟨1, by omega⟩ : Fin n) ∈ ({⟨0, by omega⟩} : Finset (Fin n)) :=
    h ▸ mem_univ _
  simp only [mem_singleton, Fin.mk.injEq] at hm
  omega

private lemma vertex_valid {n : ℕ} {k : Finset (Fin n)}
    {f : Finset (Fin n) → Finset (Fin n)} (hf : IsLazyTwoCausalStrategy k f) :
    0 ≤ jOne (labelKernel f) := by
  classical
  have hforced : f univ = univ → f k = k := by
    intro hu
    have hd := hf.2.2.2 univ k (by simp)
    simpa only [hu, univ_inter, inter_eq_left.mpr (hf.2.2.1 k)] using hd.symm
  have hnonneg (t a : Finset (Fin n)) : 0 ≤ labelKernel f t a := by
    change 0 ≤ if f t = a then (1 : ℝ) else 0
    exact ite_nonneg zero_le_one le_rfl
  have hsingle : labelKernel f k k ≤
      ∑ t with t.Nonempty ∧ t ≠ univ, labelKernel f t t :=
    single_le_sum (fun t _ => hnonneg t t) (by simp [hf.1, hf.2.1])
  have hle : labelKernel f univ univ ≤ labelKernel f k k := by
    by_cases hu : f univ = univ
    · change (if f univ = univ then (1 : ℝ) else 0) ≤ if f k = k then 1 else 0
      rw [ite_eq_left hu, ite_eq_left (hforced hu)]
    · calc
        labelKernel f univ univ = 0 := ite_eq_right hu
        _ ≤ labelKernel f k k := hnonneg k k
  exact sub_nonneg.mpr (hle.trans hsingle)

private lemma validity (n : ℕ) : ∀ p ∈ twoCausalPolytope n, 0 ≤ jOne p := by
  apply convexHull_min
  · rintro p ⟨k, f, hf, rfl⟩
    exact vertex_valid hf
  · exact convex_halfSpace_ge (jLinear n).isLinear 0

private lemma polytope_laws (n : ℕ) : ∀ p ∈ twoCausalPolytope n,
    (∀ t a, ¬ a ⊆ t → p t a = 0) ∧ ∀ t, ∑ a, p t a = 1 := by
  classical
  apply convexHull_min
  · rintro p ⟨k, f, hf, rfl⟩
    constructor
    · intro t a ha
      have hne : f t ≠ a := fun h => ha (h ▸ hf.2.2.1 t)
      exact ite_eq_right hne
    · intro t
      change ∑ a, (if f t = a then (1 : ℝ) else 0) = 1
      simp
  · intro p hp q hq a b _ _ hab
    constructor
    · intro t u hu
      change a * p t u + b * q t u = 0
      rw [hp.1 t u hu, hq.1 t u hu, mul_zero, mul_zero, add_zero]
    · intro t
      change ∑ u, (a * p t u + b * q t u) = 1
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, hp.2, hq.2, mul_one, mul_one, hab]

private def homogeneousSpace (n : ℕ) :
    Submodule ℝ (Finset (Fin n) → Finset (Fin n) → ℝ) where
  carrier := {q | (∀ t a, ¬ a ⊆ t → q t a = 0) ∧ ∀ t, ∑ a, q t a = 0}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    constructor
    · intro t a ha
      change p t a + q t a = 0
      rw [hp.1 t a ha, hq.1 t a ha, add_zero]
    · intro t
      change ∑ a, (p t a + q t a) = 0
      rw [sum_add_distrib, hp.2, hq.2, add_zero]
  smul_mem' := by
    intro c p hp
    constructor
    · intro t a ha
      change c * p t a = 0
      rw [hp.1 t a ha, mul_zero]
    · intro t
      change ∑ a, c * p t a = 0
      rw [← mul_sum, hp.2, mul_zero]

private lemma polytope_span_le (n : ℕ) :
    vectorSpan ℝ (twoCausalPolytope n) ≤ homogeneousSpace n := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro _ ⟨p, hp, q, hq, rfl⟩
  have hlp := polytope_laws n p hp
  have hlq := polytope_laws n q hq
  constructor
  · intro t a ha
    change p t a - q t a = 0
    rw [hlp.1 t a ha, hlq.1 t a ha, sub_self]
  · intro t
    change ∑ a, (p t a - q t a) = 0
    rw [sum_sub_distrib, hlp.2, hlq.2, sub_self]

private def restriction (n : ℕ) : homogeneousSpace n →ₗ[ℝ] (Reduced n → ℝ) where
  toFun q i := q.1 i.1.1 i.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma restriction_injective (n : ℕ) : Function.Injective (restriction n) := by
  classical
  intro p q hpq
  apply Subtype.ext
  funext t a
  have hne (b : Finset (Fin n)) (hb : b ≠ ∅) : p.1 t b = q.1 t b := by
    by_cases hbt : b ⊆ t
    · exact congrFun hpq ⟨(t, b), nonempty_iff_ne_empty.mpr hb, hbt⟩
    · exact (p.2.1 t b hbt).trans (q.2.1 t b hbt).symm
  by_cases ha : a = ∅
  · subst a
    have hp := p.2.2 t
    have hq := q.2.2 t
    rw [← sum_erase_add _ _ (mem_univ (∅ : Finset (Fin n)))] at hp hq
    have he : ∑ b ∈ univ.erase (∅ : Finset (Fin n)), p.1 t b =
        ∑ b ∈ univ.erase (∅ : Finset (Fin n)), q.1 t b :=
      sum_congr rfl (fun b hb => hne b (mem_erase.mp hb).1)
    linarith
  · exact hne a ha

private lemma dimension_upper (n : ℕ) :
    Module.finrank ℝ (vectorSpan ℝ (twoCausalPolytope n)) ≤ Fintype.card (Reduced n) := by
  have hs := Submodule.finrank_mono (polytope_span_le n)
  have hr := LinearMap.finrank_le_finrank_of_injective (restriction_injective n)
  rw [Module.finrank_fintype_fun_eq_card] at hr
  exact hs.trans hr

private def block {n : ℕ} (k t : Finset (Fin n)) :=
  (if k ⊆ t then k else ∅) ∪ (if t = univ then univ \ k else ∅)

private lemma zero_on_face {n : ℕ} (hn : 2 ≤ n) :
    labelKernel (fun _ : Finset (Fin n) => ∅) ∈
      twoCausalPolytope n ∩ {p | jOne p = 0} := by
  classical
  obtain ⟨k, hk, hku⟩ := admissible_group hn
  have hu : (univ : Finset (Fin n)).Nonempty := hk.mono (subset_univ _)
  constructor
  · apply subset_convexHull ℝ _
    exact ⟨k, (fun _ => ∅), ⟨hk, hku, fun _ => empty_subset _, by simp⟩, rfl⟩
  · change (∑ t with t.Nonempty ∧ t ≠ univ,
      labelKernel (fun _ => ∅) t t) -
        labelKernel (fun _ => ∅) univ univ = 0
    have hz : ∀ t : Finset (Fin n), t.Nonempty →
        labelKernel (fun _ => ∅) t t = 0 := by
      intro t ht
      exact ite_eq_right (Ne.symm ht.ne_empty)
    rw [hz univ hu, sub_zero]
    exact sum_eq_zero (fun t ht => hz t (mem_filter.mp ht).2.1)

private lemma spike_on_face {n : ℕ} {t a : Finset (Fin n)}
    (ha : a.Nonempty) (hat : a ⊂ t) :
    labelKernel (Function.update (fun _ => (∅ : Finset (Fin n))) t a) ∈
      twoCausalPolytope n ∩ {p | jOne p = 0} := by
  classical
  have hgroup : (univ \ a).Nonempty :=
    sdiff_nonempty.mpr (fun h => hat.not_ge ((subset_univ t).trans h))
  have hproper : univ \ a ≠ univ := by
    intro he
    obtain ⟨x, hx⟩ := ha
    have hm : x ∈ univ \ a := by rw [he]; exact mem_univ x
    exact (mem_sdiff.mp hm).2 hx
  have hz (u : Finset (Fin n)) :
      (Function.update (fun _ => (∅ : Finset (Fin n))) t a) u ∩ (univ \ a) = ∅ := by
    rw [Function.update_apply]
    split_ifs <;> simp only [inter_sdiff_self, empty_inter]
  constructor
  · apply subset_convexHull ℝ _
    refine ⟨univ \ a, Function.update (fun _ => (∅ : Finset (Fin n))) t a,
      ⟨hgroup, hproper, ?_, ?_⟩, rfl⟩
    · intro u
      rw [Function.update_apply]
      split_ifs with h
      · exact h ▸ hat.subset
      · exact empty_subset _
    · intro u v _
      rw [hz, hz]
  · have hdiag (u : Finset (Fin n)) (hu : u.Nonempty) :
        labelKernel (Function.update (fun _ => (∅ : Finset (Fin n))) t a) u u = 0 := by
      simp only [labelKernel, Function.update_apply]
      by_cases he : u = t
      · subst u
        simp only [ite_true, ite_eq_right (ne_of_lt hat)]
      · simp only [ite_eq_right he, ite_eq_right (Ne.symm hu.ne_empty)]
    have hu : (univ : Finset (Fin n)).Nonempty := ha.mono (subset_univ _)
    change (∑ u with u.Nonempty ∧ u ≠ univ,
      labelKernel (Function.update (fun _ => (∅ : Finset (Fin n))) t a) u u) -
        labelKernel (Function.update (fun _ => (∅ : Finset (Fin n))) t a) univ univ = 0
    rw [hdiag univ hu, sub_zero]
    exact sum_eq_zero (fun u hu => hdiag u (mem_filter.mp hu).2.1)

private lemma block_on_face {n : ℕ} {k : Finset (Fin n)}
    (hk : k.Nonempty) (hku : k ≠ univ) :
    labelKernel (block k) ∈ twoCausalPolytope n ∩ {p | jOne p = 0} := by
  classical
  have hfull : block k univ = univ := by
    change (if k ⊆ univ then k else ∅) ∪
      (if (univ : Finset (Fin n)) = univ then univ \ k else ∅) = univ
    rw [ite_eq_left (subset_univ _), ite_eq_left rfl, union_sdiff_of_subset (subset_univ _)]
  have hfirst (t : Finset (Fin n)) :
      block k t ∩ k = if k ⊆ t then k else ∅ := by
    change ((if k ⊆ t then k else ∅) ∪
      (if t = univ then univ \ k else ∅)) ∩ k = _
    rw [union_inter_distrib_right]
    split_ifs <;> simp only [inter_self, sdiff_inter_self, empty_inter, union_empty]
  constructor
  · apply subset_convexHull ℝ _
    refine ⟨k, block k, ⟨hk, hku, ?_, ?_⟩, rfl⟩
    · intro t
      change (if k ⊆ t then k else ∅) ∪ (if t = univ then univ \ k else ∅) ⊆ t
      apply union_subset
      · split_ifs with h
        · exact h
        · exact empty_subset _
      · split_ifs with h
        · subst t
          exact subset_univ _
        · exact empty_subset _
    · intro t u h
      rw [hfirst, hfirst]
      have he : (k ⊆ t) ↔ (k ⊆ u) := by
        rw [← inter_eq_right, ← inter_eq_right, h]
      simp only [he]
  · have hd (t : Finset (Fin n)) (ht : t.Nonempty) (htu : t ≠ univ) :
        labelKernel (block k) t t = if k = t then 1 else 0 := by
      change (if ((if k ⊆ t then k else ∅) ∪
        (if t = univ then univ \ k else ∅)) = t then (1 : ℝ) else 0) = _
      rw [ite_eq_right htu, union_empty]
      by_cases hkt : k ⊆ t
      · rw [ite_eq_left hkt]
      · have hne : k ≠ t := fun h => hkt (h ▸ subset_rfl)
        rw [ite_eq_right hkt, ite_eq_right (Ne.symm ht.ne_empty), ite_eq_right hne]
    change (∑ t with t.Nonempty ∧ t ≠ univ,
      labelKernel (block k) t t) - labelKernel (block k) univ univ = 0
    have he : (∑ t with t.Nonempty ∧ t ≠ univ,
        labelKernel (block k) t t) = 1 := by
      calc
        _ = ∑ t with t.Nonempty ∧ t ≠ univ, (if k = t then (1 : ℝ) else 0) :=
          sum_congr rfl (fun t ht => hd t (mem_filter.mp ht).2.1 (mem_filter.mp ht).2.2)
        _ = 1 := by simp [hk, hku]
    rw [he]
    change 1 - (if block k univ = univ then (1 : ℝ) else 0) = 0
    rw [ite_eq_left hfull, sub_self]

private def facePoint {n : ℕ} (i : FaceIndex n) :
    Finset (Fin n) → Finset (Fin n) → ℝ :=
  if i.1.1.2 = i.1.1.1 then labelKernel (block i.1.1.1)
  else labelKernel (Function.update (fun _ => (∅ : Finset (Fin n))) i.1.1.1 i.1.1.2)

private lemma facePoint_mem {n : ℕ} (i : FaceIndex n) :
    facePoint i ∈ twoCausalPolytope n ∩ {p | jOne p = 0} := by
  classical
  by_cases h : i.1.1.2 = i.1.1.1
  · change (if i.1.1.2 = i.1.1.1 then _ else _) ∈ _
    rw [ite_eq_left h]
    apply block_on_face (h ▸ i.1.2.1)
    intro hu
    apply i.2
    exact Prod.ext hu (h.trans hu)
  · change (if i.1.1.2 = i.1.1.1 then _ else _) ∈ _
    rw [ite_eq_right h]
    exact spike_on_face i.1.2.1 (Finset.ssubset_iff_subset_ne.mpr ⟨i.1.2.2, h⟩)

private lemma off_diagonal_coordinate {n : ℕ} (i j : FaceIndex n)
    (hi : i.1.1.2 ≠ i.1.1.1) :
    (facePoint i -ᵥ labelKernel (fun _ : Finset (Fin n) => ∅))
      j.1.1.1 j.1.1.2 = if i = j then 1 else 0 := by
  classical
  have hz : labelKernel (fun _ : Finset (Fin n) => ∅) j.1.1.1 j.1.1.2 = 0 :=
    ite_eq_right (Ne.symm j.1.2.1.ne_empty)
  change facePoint i j.1.1.1 j.1.1.2 -
    labelKernel (fun _ : Finset (Fin n) => ∅) j.1.1.1 j.1.1.2 = _
  rw [hz, sub_zero]
  by_cases he : i = j
  · subst j
    change (if i.1.1.2 = i.1.1.1 then labelKernel (block i.1.1.1)
      else labelKernel (Function.update (fun _ => (∅ : Finset (Fin n))) i.1.1.1 i.1.1.2))
      i.1.1.1 i.1.1.2 = _
    rw [ite_eq_right hi]
    simp only [labelKernel, Function.update_apply, ite_true]
  · have hf :
        (Function.update (fun _ => (∅ : Finset (Fin n))) i.1.1.1 i.1.1.2) j.1.1.1 ≠ j.1.1.2 := by
      rw [Function.update_apply]
      split_ifs with ht
      · intro ha
        exact he (Subtype.ext (Subtype.ext (Prod.ext ht.symm ha)))
      · exact Ne.symm j.1.2.1.ne_empty
    change (if i.1.1.2 = i.1.1.1 then labelKernel (block i.1.1.1)
      else labelKernel (Function.update (fun _ => (∅ : Finset (Fin n))) i.1.1.1 i.1.1.2))
      j.1.1.1 j.1.1.2 = _
    rw [ite_eq_right hi]
    change (if (Function.update (fun _ => (∅ : Finset (Fin n))) i.1.1.1 i.1.1.2) j.1.1.1 = j.1.1.2
      then (1 : ℝ) else 0) = _
    rw [ite_eq_right hf, ite_eq_right he]

private lemma diagonal_coordinate {n : ℕ} (i j : FaceIndex n)
    (hj : j.1.1.2 = j.1.1.1) :
    (facePoint i -ᵥ labelKernel (fun _ : Finset (Fin n) => ∅))
      j.1.1.1 j.1.1.2 = if i = j then 1 else 0 := by
  classical
  by_cases hi : i.1.1.2 = i.1.1.1
  · have hju : j.1.1.1 ≠ univ := by
      intro h
      exact j.2 (Prod.ext h (hj.trans h))
    have hz : labelKernel (fun _ : Finset (Fin n) => ∅)
        j.1.1.1 j.1.1.2 = 0 := ite_eq_right (Ne.symm j.1.2.1.ne_empty)
    change facePoint i j.1.1.1 j.1.1.2 -
      labelKernel (fun _ : Finset (Fin n) => ∅) j.1.1.1 j.1.1.2 = _
    rw [hz, sub_zero]
    by_cases he : i = j
    · subst i
      change (if j.1.1.2 = j.1.1.1 then labelKernel (block j.1.1.1)
        else labelKernel (Function.update (fun _ => (∅ : Finset (Fin n))) j.1.1.1 j.1.1.2))
        j.1.1.1 j.1.1.2 = _
      rw [ite_eq_left hj]
      change (if ((if j.1.1.1 ⊆ j.1.1.1 then j.1.1.1 else ∅) ∪
        (if j.1.1.1 = univ then univ \ j.1.1.1 else ∅)) = j.1.1.2
        then (1 : ℝ) else 0) = if j = j then 1 else 0
      simp only [hj, ite_true, ite_eq_left (subset_refl _), ite_eq_right hju, union_empty]
    · have hnt : i.1.1.1 ≠ j.1.1.1 := by
        intro h
        exact he (Subtype.ext (Subtype.ext (Prod.ext h (hi.trans (h.trans hj.symm)))))
      have hf : block i.1.1.1 j.1.1.1 ≠ j.1.1.2 := by
        change ((if i.1.1.1 ⊆ j.1.1.1 then i.1.1.1 else ∅) ∪
          (if j.1.1.1 = univ then univ \ i.1.1.1 else ∅)) ≠ j.1.1.2
        rw [ite_eq_right hju, union_empty]
        split_ifs
        · exact fun h => hnt (h.trans hj)
        · exact Ne.symm j.1.2.1.ne_empty
      change (if i.1.1.2 = i.1.1.1 then labelKernel (block i.1.1.1)
        else labelKernel (Function.update (fun _ => (∅ : Finset (Fin n))) i.1.1.1 i.1.1.2))
        j.1.1.1 j.1.1.2 = _
      rw [ite_eq_left hi]
      change (if block i.1.1.1 j.1.1.1 = j.1.1.2
        then (1 : ℝ) else 0) = _
      rw [ite_eq_right hf, ite_eq_right he]
  · exact off_diagonal_coordinate i j hi

private lemma face_independent (n : ℕ) : LinearIndependent ℝ
    (fun i : FaceIndex n => facePoint i -ᵥ
      labelKernel (fun _ : Finset (Fin n) => ∅)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hdiag (i : FaceIndex n) (hi : i.1.1.2 = i.1.1.1) : c i = 0 := by
    have he := congrArg (fun p : Finset (Fin n) → Finset (Fin n) → ℝ =>
      p i.1.1.1 i.1.1.2) hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at he
    simp only [diagonal_coordinate _ _ hi] at he
    simpa using he
  by_cases hj : j.1.1.2 = j.1.1.1
  · exact hdiag j hj
  · have he := congrArg (fun p : Finset (Fin n) → Finset (Fin n) → ℝ =>
        p j.1.1.1 j.1.1.2) hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at he
    have ht (i : FaceIndex n) :
        c i * (facePoint i -ᵥ labelKernel (fun _ : Finset (Fin n) => ∅))
          j.1.1.1 j.1.1.2 = if i = j then c j else 0 := by
      by_cases hi : i.1.1.2 = i.1.1.1
      · have hne : i ≠ j := fun h => hj (h ▸ hi)
        rw [hdiag i hi, zero_mul, ite_eq_right hne]
      · rw [off_diagonal_coordinate i j hi]
        split_ifs with h
        · rw [h, mul_one]
        · exact mul_zero _
    simp_rw [ht] at he
    simpa using he

private lemma index_count {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card (FaceIndex n) + 1 = Fintype.card (Reduced n) := by
  classical
  let u : Reduced n := ⟨(univ, univ), ⟨⟨⟨0, by omega⟩, mem_univ _⟩, subset_rfl⟩⟩
  have he : Fintype.card (FaceIndex n) = Fintype.card {i : Reduced n // i ≠ u} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun i => by
      constructor
      · intro hne he
        exact hne (congrArg Subtype.val he)
      · intro hne he
        exact hne (Subtype.ext he)))
  have hp : 0 < Fintype.card (Reduced n) := Fintype.card_pos_iff.mpr ⟨u⟩
  rw [he, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  omega

private lemma dimension_lower {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card (FaceIndex n) ≤
      Module.finrank ℝ (vectorSpan ℝ (twoCausalPolytope n ∩ {p | jOne p = 0})) := by
  let v (i : FaceIndex n) :
      vectorSpan ℝ (twoCausalPolytope n ∩ {p | jOne p = 0}) :=
    ⟨facePoint i -ᵥ labelKernel (fun _ : Finset (Fin n) => ∅),
      vsub_mem_vectorSpan ℝ (facePoint_mem i) (zero_on_face hn)⟩
  have hv : LinearIndependent ℝ v :=
    (face_independent n).of_comp (vectorSpan ℝ
      (twoCausalPolytope n ∩ {p | jOne p = 0})).subtype
  exact hv.fintype_card_le_finrank

private lemma identity_positive {n : ℕ} (hn : 2 ≤ n) :
    labelKernel (fun t : Finset (Fin n) => t) ∈ twoCausalPolytope n ∧
      0 < jOne (labelKernel (fun t : Finset (Fin n) => t)) := by
  classical
  obtain ⟨k, hk, hku⟩ := admissible_group hn
  have hcomp : (univ \ k).Nonempty := sdiff_nonempty.mpr
    (fun h => hku (subset_antisymm (subset_univ _) h))
  have hcompu : univ \ k ≠ univ := by
    intro h
    obtain ⟨x, hx⟩ := hk
    have hm : x ∈ univ \ k := by rw [h]; exact mem_univ x
    exact (mem_sdiff.mp hm).2 hx
  have hneq : k ≠ univ \ k := by
    intro h
    obtain ⟨x, hx⟩ := hk
    exact (mem_sdiff.mp (h ▸ hx)).2 hx
  have hc : 2 ≤ (univ.filter (fun t : Finset (Fin n) => t.Nonempty ∧ t ≠ univ)).card := by
    have hsub : {k, univ \ k} ⊆
        univ.filter (fun t : Finset (Fin n) => t.Nonempty ∧ t ≠ univ) := by
      intro t ht
      rcases mem_insert.mp ht with rfl | ht
      · exact mem_filter.mpr ⟨mem_univ _, hk, hku⟩
      · have he := mem_singleton.mp ht
        subst t
        exact mem_filter.mpr ⟨mem_univ _, hcomp, hcompu⟩
    simpa only [card_pair hneq] using card_le_card hsub
  constructor
  · apply subset_convexHull ℝ _
    exact ⟨k, (fun t => t), ⟨hk, hku, fun _ => subset_rfl, fun _ _ h => h⟩, rfl⟩
  · change 0 < (∑ t with t.Nonempty ∧ t ≠ univ,
      (if t = t then (1 : ℝ) else 0)) - (if (univ : Finset (Fin n)) = univ then 1 else 0)
    simp only [ite_true, sum_const, nsmul_eq_mul, mul_one]
    have hr : (2 : ℝ) ≤
        ((univ.filter (fun t : Finset (Fin n) => t.Nonempty ∧ t ≠ univ)).card : ℝ) :=
      Nat.cast_le.mpr hc
    linarith

private lemma dimension_strict {n : ℕ} (hn : 2 ≤ n) :
    Module.finrank ℝ (vectorSpan ℝ (twoCausalPolytope n ∩ {p | jOne p = 0})) + 1 ≤
      Module.finrank ℝ (vectorSpan ℝ (twoCausalPolytope n)) := by
  have hker : vectorSpan ℝ (twoCausalPolytope n ∩ {p | jOne p = 0}) ≤
      LinearMap.ker (jLinear n) := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨p, hp, q, hq, rfl⟩
    change jLinear n (p - q) = 0
    rw [map_sub]
    change jOne p - jOne q = 0
    rw [hp.2, hq.2, sub_self]
  have hle : vectorSpan ℝ (twoCausalPolytope n ∩ {p | jOne p = 0}) ≤
      vectorSpan ℝ (twoCausalPolytope n) := vectorSpan_mono ℝ Set.inter_subset_left
  have hnot : ¬ vectorSpan ℝ (twoCausalPolytope n) ≤
      vectorSpan ℝ (twoCausalPolytope n ∩ {p | jOne p = 0}) := by
    intro h
    have hz := zero_on_face hn
    have hid := identity_positive hn
    have hd := vsub_mem_vectorSpan ℝ hid.1 hz.1
    have he := hker (h hd)
    change jLinear n (labelKernel (fun t : Finset (Fin n) => t) -
      labelKernel (fun _ : Finset (Fin n) => ∅)) = 0 at he
    rw [map_sub] at he
    change jOne (labelKernel (fun t : Finset (Fin n) => t)) -
      jOne (labelKernel (fun _ : Finset (Fin n) => ∅)) = 0 at he
    rw [hz.2, sub_zero] at he
    exact (ne_of_gt hid.2) he
  exact Nat.add_one_le_iff.mpr (Submodule.finrank_lt_finrank_of_lt (lt_of_le_not_ge hle hnot))

/-- The lazy two-causal inequality is facet inducing for all `n ≥ 2`. -/
theorem result : claim := by
  intro n hn
  refine ⟨validity n, ?_⟩
  have hu := dimension_upper n
  have hl := dimension_lower hn
  have hc := index_count hn
  have hs := dimension_strict hn
  omega

end D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet
