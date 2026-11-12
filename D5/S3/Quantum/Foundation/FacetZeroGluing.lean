/- GID: D5/S3/Quantum/Foundation/FacetZeroGluing
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/FacetZeroGluing
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Original mixed-state zero gluing and native codimension-one cone faces. -/

import D5.S3.Quantum.Foundation.WeightedRelationConfirmation
import Mathlib.Geometry.Convex.Cone.Face.Lattice
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Finset.Max
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Full mixed-state zero gluing on the original cone, with native whole-base facets. -/

noncomputable section

namespace D5.S3.Quantum.Foundation.FacetZeroGluing

open CircuitBalancedConfirmation WeightedRelationConfirmation

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A]

/-- The entire original mixed-state exclusion set. -/
def exclusion (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) (p : A) : Set A :=
  {x | x ∈ base C u ∧ ∃ f, confirms C u p f ∧ f x = 0}

private theorem finite_zero_test {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    (hZ : zeroGluing C u) (p : pure C u)
    (hD : (exclusion C u p).Nonempty) (s : Finset A)
    (hs : (s : Set A) ⊆ exclusion C u p) :
    ∃ z ∈ exclusion C u p, ∀ f, confirms C u p f → f z = 0 →
      ∀ x ∈ s, f x = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨z, hz⟩ := hD
    exact ⟨z, hz, by simp⟩
  | @insert a s ha ih =>
    have haD := hs (Finset.mem_insert_self a s)
    obtain ⟨z, hz, htest⟩ := ih (fun x hx => hs (Finset.mem_insert_of_mem hx))
    let w := (1 / 2 : ℝ) • (a + z)
    have hwK : w ∈ base C u := by
      simpa [w, smul_add] using
        base_convex C u haD.1 hz.1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    refine ⟨w, ⟨hwK, hZ p a z haD.1 hz.1 haD.2 hz.2⟩, ?_⟩
    intro f hf hfw x hx
    have hfa := (hf.1 a haD.1.1).1
    have hfz := (hf.1 z hz.1.1).1
    have heq : (1 / 2 : ℝ) * (f a + f z) = 0 := by
      simpa only [w, map_smul, map_add, smul_eq_mul] using hfw
    have hfa0 : f a = 0 := by linarith
    have hfz0 : f z = 0 := by linarith
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hfa0
    · exact htest f hf hfz0 x hx

/-- A single original proper confirmer cuts out all original exclusions.
Neither a least effect nor exposedness of the exclusion set is an input. -/
theorem zero_gluing_common_effect {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    (hZ : zeroGluing C u) (p : pure C u)
    (hD : (exclusion C u p).Nonempty) :
    ∃ f, confirms C u p f ∧
      exclusion C u p = {x | x ∈ base C u ∧ f x = 0} := by
  classical
  obtain ⟨s, hs, _, hspan, _⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn ℝ (exclusion C u p)
  obtain ⟨z, hz, htest⟩ := finite_zero_test hZ p hD s hs
  obtain ⟨f, hf, hfz⟩ := hz.2
  have hker : Submodule.span ℝ (exclusion C u p) ≤ LinearMap.ker f := by
    rw [← hspan]
    exact Submodule.span_le.mpr (fun x hx => htest f hf hfz x hx)
  refine ⟨f, hf, Set.ext fun x => ?_⟩
  constructor
  · intro hx
    exact ⟨hx.1, hker (Submodule.subset_span hx)⟩
  · intro hx
    exact ⟨hx.1, f, hf, hx.2⟩

private theorem face_span_inter {C : PointedCone ℝ A} (F : PointedCone.Face C)
    {x : A} (hx : x ∈ C) (hxspan : x ∈ Submodule.span ℝ (F : Set A)) : x ∈ F := by
  obtain ⟨a, ha, b, hb, hab⟩ := F.toPointedCone.mem_span.mp hxspan
  apply F.isFaceOf.mem_of_add_mem_left hx (F.isFaceOf.le hb)
  simpa [hab] using ha

private theorem native_facet_support {C : PointedCone ℝ A}
    (hgen : Submodule.span ℝ (C : Set A) = ⊤) (F : PointedCone.Face C)
    (hdim : Module.finrank ℝ (Submodule.span ℝ (F : Set A)) + 1 =
      Module.finrank ℝ A) :
    ∃ g : A →ₗ[ℝ] ℝ, g ≠ 0 ∧ (∀ x ∈ C, 0 ≤ g x) ∧
      (∀ x ∈ C, g x = 0 ↔ x ∈ F) ∧
      LinearMap.ker g = Submodule.span ℝ (F : Set A) := by
  classical
  let S := Submodule.span ℝ (F : Set A)
  have hS : S < ⊤ := by
    apply lt_of_le_of_ne le_top
    intro he
    have hh : Module.finrank ℝ S = Module.finrank ℝ A := by rw [he, finrank_top]
    dsimp [S] at hh
    omega
  obtain ⟨g, hg, hSg⟩ := S.exists_le_ker_of_lt_top hS
  have hker : LinearMap.ker g = S := by
    apply (Submodule.eq_of_le_of_finrank_eq hSg ?_).symm
    have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hg
    dsimp [S]
    omega
  have hx : ∃ x ∈ C, g x ≠ 0 := by
    by_contra! h
    have hh : Submodule.span ℝ (C : Set A) ≤ LinearMap.ker g :=
      Submodule.span_le.mpr h
    rw [hgen] at hh
    exact hg (LinearMap.ker_eq_top.mp (top_le_iff.mp hh))
  obtain ⟨x, hx, hgx⟩ := hx
  let f := if 0 < g x then g else -g
  have hfker : LinearMap.ker f = S := by
    dsimp [f]
    split_ifs <;> simpa using hker
  have hfx : 0 < f x := by
    dsimp [f]
    split_ifs with h
    · exact h
    · simp only [LinearMap.neg_apply]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt h) hgx)
  have hnonneg : ∀ y ∈ C, 0 ≤ f y := by
    intro y hy
    by_contra! hfy
    let z := (-f y) • x + (f x) • y
    have hzC : z ∈ C := C.add_mem (C.smul_mem (neg_pos.mpr hfy).le hx)
      (C.smul_mem hfx.le hy)
    have hz0 : f z = 0 := by simp [z, map_add, map_smul]; ring
    have hzF : z ∈ F := face_span_inter F hzC (by
      change z ∈ S
      rw [← hfker]
      exact hz0)
    have hxF := F.isFaceOf.mem_of_smul_add_mem hx (C.smul_mem hfx.le hy)
      (neg_pos.mpr hfy) hzF
    have hx0 : f x = 0 := by
      apply (show S ≤ LinearMap.ker f by rw [hfker])
      exact Submodule.subset_span hxF
    linarith
  refine ⟨f, (by intro hf; simpa [hf] using hfx), hnonneg, ?_, hfker⟩
  intro y hy
  constructor
  · intro hy0
    exact face_span_inter F hy (by
      change y ∈ S
      rw [← hfker]
      exact hy0)
  · intro hyF
    exact (show S ≤ LinearMap.ker f by rw [hfker]) (Submodule.subset_span hyF)

/-- Native faces of the entire original cone with codimension-one linear span.
Their normalized slices are the whole-base facets. -/
def facets (C : PointedCone ℝ A) :=
  {F : PointedCone.Face C //
    Module.finrank ℝ (Submodule.span ℝ (F : Set A)) + 1 = Module.finrank ℝ A}

private theorem facet_effect {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    [Finite (pure C u)] (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set A) = ⊤) (F : facets C) :
    ∃ (p : pure C u) (h : A →ₗ[ℝ] ℝ), confirms C u p h ∧
      ∀ x ∈ base C u, h x = 0 ↔ x ∈ F.1 := by
  classical
  obtain ⟨g, hg, hnonneg, hzero, _⟩ := native_facet_support hgen F.1 F.2
  have hpos : ∃ q : pure C u, 0 < g q := by
    by_contra! hn
    have hz (q : pure C u) : g q = 0 :=
      le_antisymm (hn q) (hnonneg q (pure_mem q).1)
    have hker : Submodule.span ℝ (pure C u) ≤ LinearMap.ker g :=
      Submodule.span_le.mpr (fun x hx => hz ⟨x, hx⟩)
    rw [pure_span (base_compact hclosed hstrict) hstrict hgen] at hker
    exact hg (LinearMap.ker_eq_top.mp (top_le_iff.mp hker))
  obtain ⟨q, hq⟩ := hpos
  letI : Nonempty (pure C u) := ⟨q⟩
  letI := Fintype.ofFinite (pure C u)
  obtain ⟨p, _, hp⟩ := Finset.univ.exists_max_image (fun r : pure C u => g r)
    Finset.univ_nonempty
  have hgp : 0 < g p := hq.trans_le (hp q (Finset.mem_univ q))
  let h : A →ₗ[ℝ] ℝ := (g p)⁻¹ • g
  have hproper : proper C u h := cone_bound (base_compact hclosed hstrict) hstrict (by
    intro r
    change 0 ≤ (g p)⁻¹ * g r ∧ (g p)⁻¹ * g r ≤ 1
    exact ⟨mul_nonneg (inv_nonneg.mpr hgp.le) (hnonneg r (pure_mem r).1),
      by simpa [mul_comm, div_eq_mul_inv] using
        (div_le_one hgp).mpr (hp r (Finset.mem_univ r))⟩)
  refine ⟨p, h, ⟨hproper, ?_⟩, ?_⟩
  · simp [h, hgp.ne']
  · intro x hx
    simpa [h, LinearMap.smul_apply, smul_eq_mul, hgp.ne'] using hzero x hx.1

private theorem facet_exclusion {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    [Finite (pure C u)] (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set A) = ⊤)
    (hdim : 2 ≤ Module.finrank ℝ A) (hZ : zeroGluing C u) (F : facets C) :
    ∃ p : pure C u, exclusion C u p = base F.1.toPointedCone u ∧ (p : A) ∉ F.1 := by
  classical
  obtain ⟨p, h, hh, hzero⟩ := facet_effect hclosed hstrict hgen F
  have hsub : base F.1.toPointedCone u ⊆ exclusion C u p := by
    intro x hx
    have hxK : x ∈ base C u := ⟨F.1.isFaceOf.le hx.1, hx.2⟩
    exact ⟨hxK, h, hh, (hzero x hxK).mpr hx.1⟩
  have hFne : ∃ x ∈ F.1, x ≠ (0 : A) := by
    by_contra! hn
    have hspan : Submodule.span ℝ (F.1 : Set A) = ⊥ :=
      le_antisymm (Submodule.span_le.mpr (fun x hx => by simpa [hn x hx])) bot_le
    have hf := F.2
    rw [hspan, finrank_bot] at hf
    omega
  obtain ⟨x, hx, hx0⟩ := hFne
  have hux := hstrict x (F.1.isFaceOf.le hx) hx0
  have hnorm : (u x)⁻¹ • x ∈ base F.1.toPointedCone u :=
    ⟨F.1.toPointedCone.smul_mem (inv_nonneg.mpr hux.le) hx,
      by simp [map_smul, hux.ne']⟩
  obtain ⟨f, hf, hfD⟩ := zero_gluing_common_effect hZ p ⟨_, hsub hnorm⟩
  have hvanish : ∀ y ∈ F.1, f y = 0 := by
    intro y hy
    by_cases hy0 : y = 0
    · simp [hy0]
    have huy := hstrict y (F.1.isFaceOf.le hy) hy0
    have hyN : (u y)⁻¹ • y ∈ base F.1.toPointedCone u :=
      ⟨F.1.toPointedCone.smul_mem (inv_nonneg.mpr huy.le) hy,
        by simp [map_smul, huy.ne']⟩
    have hz := hsub hyN
    rw [hfD] at hz
    simpa [map_smul, huy.ne'] using hz.2
  have hfle : Submodule.span ℝ (F.1 : Set A) ≤ LinearMap.ker f :=
    Submodule.span_le.mpr hvanish
  have hfne : f ≠ 0 := by intro he; simpa [he] using hf.2
  have hfker : LinearMap.ker f = Submodule.span ℝ (F.1 : Set A) := by
    apply (Submodule.eq_of_le_of_finrank_eq hfle ?_).symm
    have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hfne
    have hd := F.2
    omega
  refine ⟨p, Set.Subset.antisymm ?_ hsub, ?_⟩
  · intro y hy
    have hz := hy
    rw [hfD] at hz
    exact ⟨face_span_inter F.1 hy.1.1 (by
      rw [← hfker]
      exact hz.2), hy.1.2⟩
  · intro hpF
    have hhp := (hzero p (pure_mem p)).mpr hpF
    linarith [hh.2]

private theorem exclusion_symmetric {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    (p q : pure C u) : (q : A) ∈ exclusion C u p ↔ (p : A) ∈ exclusion C u q := by
  suffices ∀ p q : pure C u, (q : A) ∈ exclusion C u p →
      (p : A) ∈ exclusion C u q from ⟨this p q, this q p⟩
  intro p q hq
  obtain ⟨f, hf, hfq⟩ := hq.2
  refine ⟨pure_mem p, u - f, ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    have hfx := hf.1 x hx
    simp only [LinearMap.sub_apply]
    constructor <;> linarith
  · simp [LinearMap.sub_apply, (pure_mem q).2, hfq]
  · simp [LinearMap.sub_apply, (pure_mem p).2, hf.2]

private theorem normalized_face_dimension (D : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (hstrict : ∀ x ∈ D, x ≠ 0 → 0 < u x) (hne : ∃ x ∈ D, x ≠ (0 : A)) :
    Module.finrank ℝ (affineSpan ℝ (base D u)).direction + 1 =
      Module.finrank ℝ (Submodule.span ℝ (D : Set A)) := by
  obtain ⟨x, hx, hx0⟩ := hne
  have hux := hstrict x hx hx0
  let q := (u x)⁻¹ • x
  have hq : q ∈ base D u :=
    ⟨D.smul_mem (inv_nonneg.mpr hux.le) hx, by simp [q, map_smul, hux.ne']⟩
  let T := vectorSpan ℝ (base D u)
  have hTu : T ≤ LinearMap.ker u := by
    apply Submodule.span_le.mpr
    rintro v ⟨a, ha, b, hb, rfl⟩
    change u (a - b) = 0
    simp [map_sub, ha.2, hb.2]
  have hqT : q ∉ T := by
    intro h
    have hh : u q = 0 := hTu h
    linarith [hq.2]
  have hTS : T ≤ Submodule.span ℝ (D : Set A) := by
    apply Submodule.span_le.mpr
    rintro v ⟨a, ha, b, hb, rfl⟩
    exact (Submodule.span ℝ (D : Set A)).sub_mem
      (Submodule.subset_span ha.1) (Submodule.subset_span hb.1)
  have hspan : Submodule.span ℝ (D : Set A) = T ⊔ Submodule.span ℝ {q} := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      intro y hy
      by_cases hy0 : y = 0
      · simp [hy0]
      have huy := hstrict y hy hy0
      let z := (u y)⁻¹ • y
      have hz : z ∈ base D u :=
        ⟨D.smul_mem (inv_nonneg.mpr huy.le) hy, by simp [z, map_smul, huy.ne']⟩
      have hzT : z - q ∈ T := vsub_mem_vectorSpan ℝ hz hq
      have hzS : z ∈ T ⊔ Submodule.span ℝ {q} := by
        have hh := (T ⊔ Submodule.span ℝ {q}).add_mem
          (Submodule.mem_sup_left hzT)
          (Submodule.mem_sup_right (Submodule.mem_span_singleton_self q))
        simpa using hh
      have hh := (T ⊔ Submodule.span ℝ {q}).smul_mem (u y) hzS
      simpa [z, smul_smul, huy.ne'] using hh
    · exact sup_le hTS (Submodule.span_le.mpr (by
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        exact hy ▸ Submodule.subset_span hq.1))
  rw [direction_affineSpan, hspan, Submodule.finrank_sup_span_singleton hqT]

private theorem facet_slice_dimension {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hdim : 2 ≤ Module.finrank ℝ A) (F : facets C) :
    Module.finrank ℝ (affineSpan ℝ (base F.1.toPointedCone u)).direction + 2 =
      Module.finrank ℝ A := by
  have hFne : ∃ x ∈ F.1, x ≠ (0 : A) := by
    by_contra! hn
    have hspan : Submodule.span ℝ (F.1 : Set A) = ⊥ :=
      le_antisymm (Submodule.span_le.mpr (fun x hx => by simpa [hn x hx])) bot_le
    have hf := F.2
    rw [hspan, finrank_bot] at hf
    omega
  have hh := normalized_face_dimension F.1.toPointedCone u
    (fun x hx => hstrict x (F.1.isFaceOf.le hx)) hFne
  change Module.finrank ℝ (affineSpan ℝ (base F.1.toPointedCone u)).direction + 1 =
    Module.finrank ℝ (Submodule.span ℝ (F.1 : Set A)) at hh
  have hf := F.2
  omega

private theorem base_face_lift {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x) {S : Set A}
    (hconv : Convex ℝ S) (hext : IsExtreme ℝ (base C u) S) :
    ∃ F : PointedCone.Face C, base F.toPointedCone u = S := by
  let H := ConvexCone.hull ℝ S
  let D : PointedCone ℝ A := {
    carrier := {x | x = 0 ∨ x ∈ H}
    zero_mem' := Or.inl rfl
    add_mem' := by
      intro x y hx hy
      rcases hx with rfl | hx
      · simpa using hy
      rcases hy with rfl | hy
      · simpa using (Or.inr hx : x = 0 ∨ x ∈ H)
      exact Or.inr (H.add_mem hx hy)
    smul_mem' := by
      intro a x hx
      by_cases ha : (a : ℝ) = 0
      · left
        change (a : ℝ) • x = 0
        simp [ha]
      rcases hx with rfl | hx
      · left; simp
      · exact Or.inr (H.smul_mem (lt_of_le_of_ne a.property (Ne.symm ha)) hx) }
  have hmem {x : A} : x ∈ D ↔ x = 0 ∨ ∃ r : ℝ, 0 < r ∧ ∃ y ∈ S, r • y = x := by
    change (x = 0 ∨ x ∈ H) ↔ _
    rw [ConvexCone.mem_hull_of_convex hconv]
    rfl
  have hle : D ≤ C := by
    intro x hx
    rcases hmem.mp hx with rfl | ⟨r, hr, y, hy, rfl⟩
    · exact C.zero_mem
    · exact C.smul_mem hr.le (hext.subset hy).1
  have hbase : base D u = S := by
    ext x
    constructor
    · intro hx
      rcases hmem.mp hx.1 with rfl | ⟨r, hr, y, hy, rfl⟩
      · simpa using hx.2
      have hr1 : r = 1 := by simpa [map_smul, (hext.subset hy).2] using hx.2
      simpa [hr1] using hy
    · intro hx
      exact ⟨hmem.mpr (Or.inr ⟨1, zero_lt_one, x, hx, one_smul ℝ x⟩),
        (hext.subset hx).2⟩
  have hface : D.IsFaceOf C := by
    apply PointedCone.IsFaceOf.of_mem_of_add_mem_left hle
    intro x y hx hy hxy
    by_cases hx0 : x = 0
    · subst x; exact D.zero_mem
    by_cases hy0 : y = 0
    · simpa [hy0] using hxy
    have hux := hstrict x hx hx0
    have huy := hstrict y hy hy0
    have hsum : 0 < u (x + y) := by simpa only [map_add] using add_pos hux huy
    have hnK {z : A} (hz : z ∈ C) (huz : 0 < u z) :
        (u z)⁻¹ • z ∈ base C u :=
      ⟨C.smul_mem (inv_nonneg.mpr huz.le) hz, by simp [map_smul, huz.ne']⟩
    have hnD : (u (x + y))⁻¹ • (x + y) ∈ base D u :=
      ⟨D.smul_mem (inv_nonneg.mpr hsum.le) hxy, by simp [map_smul, hsum.ne']⟩
    rw [hbase] at hnD
    have hseg : (u (x + y))⁻¹ • (x + y) ∈
        openSegment ℝ ((u x)⁻¹ • x) ((u y)⁻¹ • y) := by
      refine ⟨u x / u (x + y), u y / u (x + y),
        div_pos hux hsum, div_pos huy hsum, ?_, ?_⟩
      · rw [← add_div, ← map_add, div_self hsum.ne']
      · simp only [smul_smul, div_eq_mul_inv]
        rw [mul_right_comm (u x), mul_inv_cancel₀ hux.ne',
          mul_right_comm (u y), mul_inv_cancel₀ huy.ne', one_mul, one_mul, smul_add]
    have hnS := hext.left_mem_of_mem_openSegment (hnK hx hux) (hnK hy huy) hnD hseg
    apply hmem.mpr
    exact Or.inr ⟨u x, hux, (u x)⁻¹ • x, hnS, by simp [smul_smul, hux.ne']⟩
  exact ⟨⟨D, hface⟩, hbase⟩

/-- All actual nonempty convex faces of the entire original base of dimension
`dim(A)-2`, expressed by Mathlib's native extreme-subset predicate. -/
def baseFacets (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) :=
  {S : Set A // S.Nonempty ∧ Convex ℝ S ∧ IsExtreme ℝ (base C u) S ∧
    Module.finrank ℝ (affineSpan ℝ S).direction + 2 = Module.finrank ℝ A}

/-- Every native whole-cone facet has an original nonincident pure confirmer;
every choice is injective and obeys symmetric cross incidence. -/
theorem whole_facet_injection {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    [Finite (pure C u)] (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set A) = ⊤)
    (hdim : 2 ≤ Module.finrank ℝ A) (hZ : zeroGluing C u) :
    (Module.finrank ℝ (affineSpan ℝ (base C u)).direction + 1 = Module.finrank ℝ A) ∧
    (∀ F : PointedCone.Face C, (∃ x ∈ F, x ≠ (0 : A)) →
      ((∃ G : facets C, G.1 = F) ↔
        Module.finrank ℝ (affineSpan ℝ (base F.toPointedCone u)).direction + 2 =
          Module.finrank ℝ A)) ∧
    (∀ F : facets C,
      Convex ℝ (base F.1.toPointedCone u) ∧
      IsExtreme ℝ (base C u) (base F.1.toPointedCone u) ∧
      Module.finrank ℝ (affineSpan ℝ (base F.1.toPointedCone u)).direction + 2 =
        Module.finrank ℝ A) ∧
    (∀ F : facets C, ∃ p : pure C u,
      exclusion C u p = base F.1.toPointedCone u ∧ (p : A) ∉ F.1) ∧
    (∀ v : facets C → pure C u,
      (∀ F, exclusion C u (v F) = base F.1.toPointedCone u) →
      Function.Injective v ∧ Nat.card (facets C) ≤ Nat.card (pure C u) ∧
        ∀ F G, (v G : A) ∈ F.1 ↔ (v F : A) ∈ G.1) ∧
    (∀ S : baseFacets C u, ∃ F : facets C, base F.1.toPointedCone u = S.1) ∧
    (∀ S : baseFacets C u, ∃ p : pure C u,
      exclusion C u p = S.1 ∧ (p : A) ∉ S.1) ∧
    (∀ v : baseFacets C u → pure C u,
      (∀ S, exclusion C u (v S) = S.1) →
      Function.Injective v ∧ Nat.card (baseFacets C u) ≤ Nat.card (pure C u) ∧
        ∀ F G, (v G : A) ∈ F.1 ↔ (v F : A) ∈ G.1) := by
  classical
  have hCne : ∃ x ∈ C, x ≠ (0 : A) := by
    by_contra! hn
    have hs : Submodule.span ℝ (C : Set A) = ⊥ :=
      le_antisymm (Submodule.span_le.mpr (fun x hx => by simp [hn x hx])) bot_le
    have hf : Module.finrank ℝ (Submodule.span ℝ (C : Set A)) = 0 := by
      rw [hs, finrank_bot]
    rw [hgen, finrank_top] at hf
    omega
  have hbaseDim := normalized_face_dimension C u hstrict hCne
  rw [hgen, finrank_top] at hbaseDim
  have hlift (S : baseFacets C u) : ∃ F : facets C,
      base F.1.toPointedCone u = S.1 := by
    obtain ⟨F, hF⟩ := base_face_lift hstrict S.2.2.1 S.2.2.2.1
    obtain ⟨x, hx⟩ := S.2.1
    have hxF : x ∈ base F.toPointedCone u := hF.symm ▸ hx
    have hx0 : x ≠ 0 := by intro he; simpa [he] using hxF.2
    have hd := normalized_face_dimension F.toPointedCone u
      (fun y hy => hstrict y (F.isFaceOf.le hy)) ⟨x, hxF.1, hx0⟩
    rw [hF] at hd
    have hS := S.2.2.2.2
    exact ⟨⟨F, by omega⟩, hF⟩
  refine ⟨hbaseDim, ?_, ?_, facet_exclusion hclosed hstrict hgen hdim hZ,
    ?_, hlift, ?_, ?_⟩
  · intro F hne
    have hf := normalized_face_dimension F.toPointedCone u
      (fun x hx => hstrict x (F.isFaceOf.le hx)) hne
    change Module.finrank ℝ (affineSpan ℝ (base F.toPointedCone u)).direction + 1 =
      Module.finrank ℝ (Submodule.span ℝ (F : Set A)) at hf
    constructor
    · rintro ⟨G, rfl⟩
      exact facet_slice_dimension hstrict hdim G
    · intro hd
      exact ⟨⟨F, by omega⟩, rfl⟩
  · intro F
    refine ⟨base_convex F.1.toPointedCone u, ?_, facet_slice_dimension hstrict hdim F⟩
    refine ⟨fun x hx => ⟨F.1.isFaceOf.le hx.1, hx.2⟩, ?_⟩
    intro x hx y hy z hz hseg
    exact ⟨F.1.isFaceOf.isExtreme.left_mem_of_mem_openSegment hx.1 hy.1 hz.1 hseg, hx.2⟩
  · intro v hv
    have hinj : Function.Injective v := by
      intro F G he
      have hb : base F.1.toPointedCone u = base G.1.toPointedCone u := by
        rw [← hv F, ← hv G, he]
      apply Subtype.ext
      apply PointedCone.Face.ext
      intro x
      by_cases hx0 : x = 0
      · subst x
        exact iff_of_true F.1.toPointedCone.zero_mem G.1.toPointedCone.zero_mem
      have hinc (F G : facets C)
          (hb : base F.1.toPointedCone u = base G.1.toPointedCone u)
          (hx : x ∈ F.1) : x ∈ G.1 := by
        have hux := hstrict x (F.1.isFaceOf.le hx) hx0
        have hn : (u x)⁻¹ • x ∈ base F.1.toPointedCone u :=
          ⟨F.1.toPointedCone.smul_mem (inv_nonneg.mpr hux.le) hx,
            by simp [map_smul, hux.ne']⟩
        rw [hb] at hn
        have hm := G.1.toPointedCone.smul_mem hux.le hn.1
        simpa [smul_smul, hux.ne'] using hm
      exact ⟨hinc F G hb, hinc G F hb.symm⟩
    refine ⟨hinj, Nat.card_le_card_of_injective v hinj, ?_⟩
    intro F G
    have hF : (v G : A) ∈ F.1 ↔ (v G : A) ∈ exclusion C u (v F) := by
      rw [hv F]
      exact ⟨fun h => ⟨h, (pure_mem (v G)).2⟩, fun h => h.1⟩
    have hG : (v F : A) ∈ G.1 ↔ (v F : A) ∈ exclusion C u (v G) := by
      rw [hv G]
      exact ⟨fun h => ⟨h, (pure_mem (v F)).2⟩, fun h => h.1⟩
    exact hF.trans ((exclusion_symmetric (v F) (v G)).trans hG.symm)
  · intro S
    obtain ⟨F, hF⟩ := hlift S
    obtain ⟨p, hp, hnon⟩ := facet_exclusion hclosed hstrict hgen hdim hZ F
    refine ⟨p, hp.trans hF, ?_⟩
    intro hpin
    have hpF : (p : A) ∈ base F.1.toPointedCone u := hF.symm ▸ hpin
    exact hnon hpF.1
  · intro v hv
    have hinj : Function.Injective v := by
      intro F G h
      apply Subtype.ext
      rw [← hv F, ← hv G, h]
    refine ⟨hinj, Nat.card_le_card_of_injective v hinj, ?_⟩
    intro F G
    rw [← hv F, ← hv G]
    exact exclusion_symmetric (v F) (v G)

end D5.S3.Quantum.Foundation.FacetZeroGluing
