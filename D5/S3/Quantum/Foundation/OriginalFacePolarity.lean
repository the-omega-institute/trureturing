/- GID: D5/S3/Quantum/Foundation/OriginalFacePolarity
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalFacePolarity
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Original exclusion incidence, mixed face orthogonality and projective polarity. -/

import D5.S3.Quantum.Foundation.ExclusionBallFaces
import Mathlib.Combinatorics.Configuration

/-! The full original base and all its convex faces, without a closed-face premise. -/

noncomputable section
open Set

namespace D5.S3.Quantum.Foundation.OriginalFacePolarity

open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces WholePairBallConfirmation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- All nonpoint proper original convex faces. -/
def Line (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) :=
  {F : Set V // F.Nontrivial ∧ Convex ℝ F ∧ IsExtreme ℝ (base C u) F ∧ F ≠ base C u}

instance : Membership (pure C u) (Line C u) := ⟨fun L p => (p : V) ∈ L.val⟩

/-- Intersection inside the entire base, over every original pure point in F. -/
def zeroComplement (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (F : Set V) : Set V :=
  {x | x ∈ base C u ∧ ∀ q : pure C u, (q : V) ∈ F → x ∈ exclusion C u q}

/-- Every exclusion has a whole ball chart of dimension at least two. -/
def thickExclusionBalls (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) : Prop :=
  ∀ p : pure C u, ∃ b : ExclusionChart C u p, 2 ≤ b.dim

private theorem not_self (p : pure C u) : (p : V) ∉ exclusion C u p := by
  rintro ⟨_, f, hf, hz⟩
  linarith [hf.2]

private theorem pair_le_face
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x) {F : Set V}
    (hconv : Convex ℝ F) (hface : IsExtreme ℝ (base C u) F)
    {p q : pure C u} (hp : (p : V) ∈ F) (hq : (q : V) ∈ F) :
    pairBase C u p q ⊆ F := by
  obtain ⟨G, hG⟩ := base_face_lift hstrict hconv hface
  intro x hx
  have hpG : (p : V) ∈ G := (show (p : V) ∈ base G.toPointedCone u from hG.symm ▸ hp).1
  have hqG : (q : V) ∈ G := (show (q : V) ∈ base G.toPointedCone u from hG.symm ▸ hq).1
  rw [← hG]
  exact ⟨hx.2 G hpG hqG, hx.1.2⟩

section Geometry

variable (hclosed : IsClosed (C : Set V))
  (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
  (hgen : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
  (hPair : pairProper C u)

private def pole (p : pure C u) : Line C u := by
  have g := (exclusion_ball_faces hclosed hstrict hgen hB).1 p
  exact ⟨exclusion C u p, g.1, g.2.2.1, g.2.2.2.2.1, g.2.2.2.2.2.1⟩

private theorem line_eq_pole (L : Line C u) :
    ∃ p : pure C u, L.val = exclusion C u p := by
  rcases (exclusion_ball_faces hclosed hstrict hgen hB).2.1 L.val
    L.property.1.nonempty L.property.2.1 L.property.2.2.1 L.property.2.2.2 with
    ⟨p, hp⟩ | h
  · exact (L.property.1.ne_singleton hp).elim
  · exact h

private theorem distinct_exclusion_intersection (p q : pure C u)
    (hne : exclusion C u p ≠ exclusion C u q) :
    ∃ r : pure C u, exclusion C u p ∩ exclusion C u q = {(r : V)} := by
  have hpq : p ≠ q := fun he => hne (congrArg (fun s : pure C u => exclusion C u s) he)
  have all := exclusion_ball_faces hclosed hstrict hgen hB
  obtain ⟨r, hr⟩ := (all.2.2 hPair).1 p q hpq
  have hpH : (p : V) ∈ pairBase C u p q := ⟨pure_mem p, fun _ hp _ => hp⟩
  have hqH : (q : V) ∈ pairBase C u p q := ⟨pure_mem q, fun _ _ hq => hq⟩
  have hrp := (exclusion_symmetric r p).mp (hr ▸ hpH)
  have hrq := (exclusion_symmetric r q).mp (hr ▸ hqH)
  have hface := (all.1 p).2.2.2.2.1.inter (all.1 q).2.2.2.2.1
  have hconv := (all.1 p).2.2.1.inter (all.1 q).2.2.1
  refine ⟨r, ?_⟩
  apply Set.Subsingleton.eq_singleton_of_mem _ ⟨hrp, hrq⟩
  apply Set.not_nontrivial_iff.mp
  intro hn
  obtain ⟨bp⟩ := hB p
  obtain ⟨bq⟩ := hB q
  have he1 := chart_face_eq bp hconv
    (hface.mono (all.1 p).2.2.2.2.1.subset inter_subset_left) hn
  have he2 := chart_face_eq bq hconv
    (hface.mono (all.1 q).2.2.2.2.1.subset inter_subset_right) hn
  exact hne (he1.symm.trans he2)

private theorem exclusion_injective :
    Function.Injective (fun p : pure C u => exclusion C u p) := by
  intro p q he
  by_contra hpq
  have all := exclusion_ball_faces hclosed hstrict hgen hB
  obtain ⟨s, hs⟩ := (all.2.2 hPair).1 p q hpq
  have hpH : (p : V) ∈ pairBase C u p q := ⟨pure_mem p, fun _ hp _ => hp⟩
  have hqH : (q : V) ∈ pairBase C u p q := ⟨pure_mem q, fun _ _ hq => hq⟩
  have hne : exclusion C u s ≠ exclusion C u p := by
    intro h
    exact not_self p (h ▸ (hs ▸ hpH))
  obtain ⟨r, hr⟩ := distinct_exclusion_intersection hclosed hstrict hgen hB hPair s p hne
  have hrmem : (r : V) ∈ exclusion C u s ∩ exclusion C u p := hr.symm ▸ mem_singleton _
  have hpr : (p : V) ∈ exclusion C u r := (exclusion_symmetric p r).mp hrmem.2
  have hqr : (q : V) ∈ exclusion C u r :=
    (exclusion_symmetric q r).mp (he ▸ hrmem.2)
  have hsub : exclusion C u s ⊆ exclusion C u r := by
    rw [← hs]
    exact pair_le_face hstrict (all.1 r).2.2.1 (all.1 r).2.2.2.2.1 hpr hqr
  obtain ⟨br⟩ := hB r
  have heq := chart_face_eq br (all.1 s).2.2.1
    ((all.1 s).2.2.2.2.1.mono (all.1 r).2.2.2.2.1.subset hsub) (all.1 s).1
  exact not_self r (heq ▸ hrmem.1)

private theorem pure_pair_in_ball (p : pure C u) :
    ∃ a b : pure C u, (a : V) ∈ exclusion C u p ∧ (b : V) ∈ exclusion C u p ∧ a ≠ b := by
  classical
  have g := (exclusion_ball_faces hclosed hstrict hgen hB).1 p
  obtain ⟨x, hx⟩ := g.2.1.extremePoints_nonempty g.1.nonempty
  have hxP : x ∈ pure C u := g.2.2.2.2.1.extremePoints_subset_extremePoints hx
  by_contra! hn
  have hsingle : (exclusion C u p).extremePoints ℝ ⊆ {x} := by
    intro y hy
    have hyP : y ∈ pure C u := g.2.2.2.2.1.extremePoints_subset_extremePoints hy
    exact congrArg Subtype.val (hn ⟨y, hyP⟩ ⟨x, hxP⟩ hy.1 hx.1)
  have hsub : exclusion C u p ⊆ {x} := by
    rw [← closure_convexHull_extremePoints g.2.1 g.2.2.1]
    exact closure_minimal (convexHull_min hsingle (convex_singleton x)) isClosed_singleton
  exact g.1.not_subsingleton (subsingleton_singleton.mono hsub)

private theorem ball_complement (p : pure C u) :
    zeroComplement C u (exclusion C u p) = {(p : V)} := by
  obtain ⟨a, b, ha, hb, hab⟩ := pure_pair_in_ball hclosed hstrict hgen hB p
  have hne : exclusion C u a ≠ exclusion C u b :=
    fun h => hab (exclusion_injective hclosed hstrict hgen hB hPair h)
  obtain ⟨r, hr⟩ := distinct_exclusion_intersection hclosed hstrict hgen hB hPair a b hne
  have hp : (p : V) ∈ exclusion C u a ∩ exclusion C u b :=
    ⟨(exclusion_symmetric p a).mpr ha, (exclusion_symmetric p b).mpr hb⟩
  have hpr : (p : V) = r := hr ▸ hp
  ext x
  constructor
  · intro hx
    have hh : x ∈ exclusion C u a ∩ exclusion C u b := ⟨hx.2 a ha, hx.2 b hb⟩
    have hxr : x = r := hr ▸ hh
    exact hxr.trans hpr.symm
  · intro hx
    rcases mem_singleton_iff.mp hx with rfl
    exact ⟨pure_mem p, fun q hq => (exclusion_symmetric p q).mpr hq⟩

private theorem chart_boundary (p : pure C u) (b : ExclusionChart C u p) :
    exclusion C u p ∩ pure C u = b.param '' Metric.sphere 0 1 := by
  letI : Nonempty (Fin b.dim) := ⟨⟨0, b.dim_pos⟩⟩
  have g := (exclusion_ball_faces hclosed hstrict hgen hB).1 p
  rw [show exclusion C u p ∩ pure C u = (exclusion C u p).extremePoints ℝ from
    g.2.2.2.2.1.extremePoints_eq.symm]
  rw [← b.whole]
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, rfl⟩ := hx.1
    have he := affine_extreme_preimage b.param b.injective _ s hx
    rw [StrictConvexSpace.extremePoints_closedBall_eq_sphere] at he
    exact ⟨s, he, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    apply affine_extreme_image _ (convex_closedBall _ _) b.param b.injective.injOn
    rwa [StrictConvexSpace.extremePoints_closedBall_eq_sphere]

private theorem complement_antitone : Antitone (zeroComplement C u) := by
  intro F G hFG x hx
  exact ⟨hx.1, fun q hq => hx.2 q (hFG hq)⟩

private theorem complement_empty : zeroComplement C u ∅ = base C u := by
  ext x
  simp [zeroComplement]

private theorem complement_singleton (p : pure C u) :
    zeroComplement C u {(p : V)} = exclusion C u p := by
  ext x
  constructor
  · intro hx
    exact hx.2 p rfl
  · intro hx
    refine ⟨hx.1, fun q hq => ?_⟩
    have he : q = p := Subtype.ext (mem_singleton_iff.mp hq)
    exact he.symm ▸ hx

private theorem pure_nonempty [Nontrivial V] : Nonempty (pure C u) := by
  by_contra hn
  have he : pure C u = ∅ := Set.eq_empty_iff_forall_not_mem.mpr
    (fun x hx => hn ⟨⟨x, hx⟩⟩)
  have hs := pure_span (base_compact hclosed hstrict) hstrict hgen
  rw [he, Submodule.span_empty] at hs
  exact bot_ne_top hs

private theorem complement_base [Nontrivial V] :
    zeroComplement C u (base C u) = ∅ := by
  obtain ⟨p⟩ := pure_nonempty hclosed hstrict hgen
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro x hx
  have hsub := complement_antitone ((exclusion_ball_faces hclosed hstrict hgen hB).1 p).2.2.2.2.1.subset
  have hxsingle := ball_complement hclosed hstrict hgen hB hPair p ▸ hsub hx
  have hxp : x = p := mem_singleton_iff.mp hxsingle
  exact not_self p (hxp ▸ hx.2 p (pure_mem p))

private theorem complement_face (F : Set V) :
    Convex ℝ (zeroComplement C u F) ∧ IsExtreme ℝ (base C u) (zeroComplement C u F) := by
  have all := exclusion_ball_faces hclosed hstrict hgen hB
  constructor
  · intro x hx y hy a b ha hb hab
    exact ⟨base_convex C u hx.1 hy.1 ha hb hab,
      fun q hq => (all.1 q).2.2.1 (hx.2 q hq) (hy.2 q hq) ha hb hab⟩
  · refine ⟨fun _ hx => hx.1, ?_⟩
    intro x hx y hy z hz hseg
    exact ⟨hx, fun q hq => (all.1 q).2.2.2.2.1.left_mem_of_mem_openSegment
      hx hy (hz.2 q hq) hseg⟩

private theorem double_complement [Nontrivial V] (F : Set V)
    (hconv : Convex ℝ F) (hface : IsExtreme ℝ (base C u) F) :
    zeroComplement C u (zeroComplement C u F) = F := by
  by_cases hne : F.Nonempty
  · by_cases he : F = base C u
    · rw [he, complement_base hclosed hstrict hgen hB hPair, complement_empty]
    · rcases (exclusion_ball_faces hclosed hstrict hgen hB).2.1 F hne hconv hface he with
        ⟨p, hp⟩ | ⟨p, hp⟩
      · rw [hp, complement_singleton, ball_complement hclosed hstrict hgen hB hPair]
      · rw [hp, ball_complement hclosed hstrict hgen hB hPair, complement_singleton]
  · have he : F = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [he, complement_empty, complement_base hclosed hstrict hgen hB hPair]

private def poleEquiv : pure C u ≃ Line C u := by
  apply Equiv.ofBijective (pole hclosed hstrict hgen hB)
  constructor
  · intro p q h
    exact exclusion_injective hclosed hstrict hgen hB hPair (congrArg Subtype.val h)
  · intro L
    obtain ⟨p, hp⟩ := line_eq_pole hclosed hstrict hgen hB L
    exact ⟨p, Subtype.ext hp.symm⟩

private theorem line_intersection (L M : Line C u) (hne : L ≠ M) :
    ∃ r : pure C u, L.val ∩ M.val = {(r : V)} := by
  obtain ⟨p, hp⟩ := line_eq_pole hclosed hstrict hgen hB L
  obtain ⟨q, hq⟩ := line_eq_pole hclosed hstrict hgen hB M
  have hD : exclusion C u p ≠ exclusion C u q := by
    intro he
    exact hne (Subtype.ext (hp.trans (he.trans hq.symm)))
  simpa only [hp, hq] using
    distinct_exclusion_intersection hclosed hstrict hgen hB hPair p q hD

private theorem line_unique {a b : pure C u} (hab : a ≠ b) {L M : Line C u}
    (haL : a ∈ L) (hbL : b ∈ L) (haM : a ∈ M) (hbM : b ∈ M) : L = M := by
  by_contra hne
  obtain ⟨r, hr⟩ := line_intersection hclosed hstrict hgen hB hPair L M hne
  have ha : (a : V) = r := hr ▸ (show (a : V) ∈ L.val ∩ M.val from ⟨haL, haM⟩)
  have hb : (b : V) = r := hr ▸ (show (b : V) ∈ L.val ∩ M.val from ⟨hbL, hbM⟩)
  exact hab (Subtype.ext (ha.trans hb.symm))

private def join (a b : pure C u) (hab : a ≠ b) : Line C u :=
  pole hclosed hstrict hgen hB
    ((exclusion_ball_faces hclosed hstrict hgen hB).2.2 hPair |>.1 a b hab).choose

private theorem join_mem (a b : pure C u) (hab : a ≠ b) :
    a ∈ join hclosed hstrict hgen hB hPair a b hab ∧
    b ∈ join hclosed hstrict hgen hB hPair a b hab := by
  have h := ((exclusion_ball_faces hclosed hstrict hgen hB).2.2 hPair).1 a b hab
  change (a : V) ∈ exclusion C u h.choose ∧ (b : V) ∈ exclusion C u h.choose
  rw [← h.choose_spec]
  exact ⟨⟨pure_mem a, fun _ ha _ => ha⟩, ⟨pure_mem b, fun _ _ hb => hb⟩⟩

private theorem boundary_injective :
    Function.Injective (fun L : Line C u => L.val ∩ pure C u) := by
  intro L M he
  obtain ⟨p, hp⟩ := line_eq_pole hclosed hstrict hgen hB L
  obtain ⟨a, b, ha, hb, hab⟩ := pure_pair_in_ball hclosed hstrict hgen hB p
  have haL : a ∈ L := hp.symm ▸ ha
  have hbL : b ∈ L := hp.symm ▸ hb
  have haM : a ∈ M := (he ▸ (show (a : V) ∈ L.val ∩ pure C u from ⟨haL, a.property⟩)).1
  have hbM : b ∈ M := (he ▸ (show (b : V) ∈ L.val ∩ pure C u from ⟨hbL, b.property⟩)).1
  exact line_unique hclosed hstrict hgen hB hPair hab haL hbL haM hbM

end Geometry

end D5.S3.Quantum.Foundation.OriginalFacePolarity
