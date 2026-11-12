/- GID: D5/S3/Quantum/Foundation/LinearJoinRetraction
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/LinearJoinRetraction
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: A real linear join supplies both positive trace-subunital retractions, surjective restriction of the full proper-effect intervals, and inheritance of the original G2 midpoint law on each supported side. -/

import D5.S3.Quantum.Foundation.WeightedRelationConfirmation
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Foundation.LinearJoinRetraction

open CircuitBalancedConfirmation

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A]

/-! ### The two sides of a linear join -/

/-- The cone and unit obtained by restricting the original carrier to a subspace. -/
def sideCone (C : PointedCone ℝ A) (U : Submodule ℝ A) : PointedCone ℝ U :=
  C.comap U.subtype

def sideUnit (u : A →ₗ[ℝ] ℝ) (U : Submodule ℝ A) : U →ₗ[ℝ] ℝ :=
  u.comp U.subtype

/-- A linear join with an explicit overlap projection on each side.  The two
projections are the abstract form of the orthogonal maps π_S used in (97.7).
The overlap equations make the glued maps independent of a chosen decomposition. -/
structure JoinData where
  leftSubspace : Submodule ℝ A
  rightSubspace : Submodule ℝ A
  overlapSubspace : Submodule ℝ A
  hSU : (overlapSubspace : Submodule ℝ A) ≤ leftSubspace
  hSW : (overlapSubspace : Submodule ℝ A) ≤ rightSubspace
  hjoin : leftSubspace ⊔ rightSubspace = ⊤
  hoverlap : leftSubspace ⊓ rightSubspace = overlapSubspace
  piY : rightSubspace →ₗ[ℝ] overlapSubspace
  piZ : leftSubspace →ₗ[ℝ] overlapSubspace
  piY_fix : ∀ s : overlapSubspace, piY (overlapSubspace.inclusion hSW s) = s
  piZ_fix : ∀ s : overlapSubspace, piZ (overlapSubspace.inclusion hSU s) = s

namespace JoinData

/-- The sum map from the two subspaces onto their linear join. -/
def sumMap (J : JoinData (A := A)) : J.leftSubspace × J.rightSubspace →ₗ[ℝ] A :=
  J.leftSubspace.subtype.coprod J.rightSubspace.subtype

private theorem sumMap_surjective (J : JoinData (A := A)) :
    Function.Surjective J.sumMap := by
  intro x
  obtain ⟨u, hu, w, hw, hsum⟩ :=
    (Submodule.sup_eq_top_iff J.leftSubspace J.rightSubspace).mp J.hjoin x
  refine ⟨(⟨u, hu⟩, ⟨w, hw⟩), ?_⟩
  simpa [sumMap, LinearMap.coprod_apply] using hsum.symm

private theorem left_kernel_compatibility (J : JoinData (A := A)) :
    LinearMap.ker J.sumMap ≤
      LinearMap.ker (LinearMap.id.coprod
        ((Submodule.inclusion J.hSU).comp J.piY)) := by
  intro x hx
  rcases x with ⟨u, w⟩
  have hsum : (u : A) + (w : A) = 0 := by
    change J.sumMap (u, w) = 0 at hx
    simpa [sumMap, LinearMap.coprod_apply] using hx
  have hwU : (w : A) ∈ J.leftSubspace := by
    have huU : (u : A) ∈ J.leftSubspace := u.property
    rw [eq_neg_of_add_eq_zero_right hsum]
    exact J.leftSubspace.neg_mem huU
  have hwS : (w : A) ∈ J.overlapSubspace := by
    rw [← J.hoverlap]
    exact ⟨hwU, w.property⟩
  let s : J.overlapSubspace := ⟨(w : A), hwS⟩
  have hsW : J.overlapSubspace.inclusion J.hSW s = w := by
    apply Subtype.ext
    rfl
  have hpi : J.piY w = s := by
    rw [← hsW]
    exact J.piY_fix s
  apply Subtype.ext
  change (u : A) + ((Submodule.inclusion J.hSU) (J.piY w) : A) = 0
  rw [hpi]
  change (u : A) + (J.overlapSubspace.inclusion J.hSW s : A) = 0
  have hsW' : ((J.overlapSubspace.inclusion J.hSW s : J.rightSubspace) : A) =
      (w : A) := congrArg (fun t : J.rightSubspace => (t : A)) hsW
  change (u : A) + (w : A) = 0
  exact hsum

private theorem right_kernel_compatibility (J : JoinData (A := A)) :
    LinearMap.ker J.sumMap ≤
      LinearMap.ker (((Submodule.inclusion J.hSW).comp J.piZ).coprod LinearMap.id) := by
  intro x hx
  rcases x with ⟨u, w⟩
  have hsum : (u : A) + (w : A) = 0 := by
    change J.sumMap (u, w) = 0 at hx
    simpa [sumMap, LinearMap.coprod_apply] using hx
  have huW : (u : A) ∈ J.rightSubspace := by
    have hwW : (w : A) ∈ J.rightSubspace := w.property
    rw [eq_neg_of_add_eq_zero_left hsum]
    exact J.rightSubspace.neg_mem hwW
  have huS : (u : A) ∈ J.overlapSubspace := by
    rw [← J.hoverlap]
    exact ⟨u.property, huW⟩
  let s : J.overlapSubspace := ⟨(u : A), huS⟩
  have hsU : J.overlapSubspace.inclusion J.hSU s = u := by
    apply Subtype.ext
    rfl
  have hpi : J.piZ u = s := by
    rw [← hsU]
    exact J.piZ_fix s
  apply Subtype.ext
  change ((Submodule.inclusion J.hSW) (J.piZ u) : A) + (w : A) = 0
  rw [hpi]
  have hsU' : ((J.overlapSubspace.inclusion J.hSU s : J.leftSubspace) : A) =
      (u : A) := congrArg (fun t : J.leftSubspace => (t : A)) hsU
  change (u : A) + (w : A) = 0
  exact hsum

/-- The left retraction (R_Y), obtained by gluing the identity on (U) to
(pi_S:W	o S). -/
def leftRetraction (J : JoinData (A := A)) : A →ₗ[ℝ] J.leftSubspace :=
  J.sumMap.liftOfSurjective (sumMap_surjective J)
    ⟨LinearMap.id.coprod ((Submodule.inclusion J.hSU).comp J.piY),
      left_kernel_compatibility J⟩

/-- The right retraction (R_Z), obtained by gluing (pi_S:U	o S) to the
identity on (W). -/
def rightRetraction (J : JoinData (A := A)) : A →ₗ[ℝ] J.rightSubspace :=
  J.sumMap.liftOfSurjective (sumMap_surjective J)
    ⟨((Submodule.inclusion J.hSW).comp J.piZ).coprod LinearMap.id,
      right_kernel_compatibility J⟩

theorem leftRetraction_on_left (J : JoinData (A := A)) (x : J.leftSubspace) :
    J.leftRetraction (J.leftSubspace.subtype x) = x := by
  have h := LinearMap.equivOfSurjective_apply
    (sumMap_surjective J) (left_kernel_compatibility J)
      (m := (x, 0))
  simpa [leftRetraction, sumMap] using h

theorem leftRetraction_on_right (J : JoinData (A := A)) (x : J.rightSubspace) :
    J.leftRetraction (J.rightSubspace.subtype x) =
      Submodule.inclusion J.hSU (J.piY x) := by
  have h := LinearMap.equivOfSurjective_apply
    (sumMap_surjective J) (left_kernel_compatibility J)
      (m := (0, x))
  simpa [leftRetraction, sumMap] using h

theorem rightRetraction_on_left (J : JoinData (A := A)) (x : J.leftSubspace) :
    J.rightRetraction (J.leftSubspace.subtype x) =
      Submodule.inclusion J.hSW (J.piZ x) := by
  have h := LinearMap.equivOfSurjective_apply
    (sumMap_surjective J) (right_kernel_compatibility J)
      (m := (x, 0))
  simpa [rightRetraction, sumMap] using h

theorem rightRetraction_on_right (J : JoinData (A := A)) (x : J.rightSubspace) :
    J.rightRetraction (J.rightSubspace.subtype x) = x := by
  have h := LinearMap.equivOfSurjective_apply
    (sumMap_surjective J) (right_kernel_compatibility J)
      (m := (0, x))
  simpa [rightRetraction, sumMap] using h

end JoinData

/-! ### Full proper effects and the inherited G2 law -/

def properEffect (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) :=
  {f : A →ₗ[ℝ] ℝ // proper C u f}

def sideProperEffect (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (U : Submodule ℝ A) :=
  {f : U →ₗ[ℝ] ℝ // proper (sideCone C U) (sideUnit u U) f}

def restrictEffect (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) (U : Submodule ℝ A) :
    properEffect C u → sideProperEffect C u U := fun f =>
      ⟨f.1.comp U.subtype, by
        intro x hx
        have hcx : (x : A) ∈ C := hx
        simpa [sideUnit] using f.2 (x : A) hcx⟩

def G2 (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) : Prop :=
  ∀ (p q r : pure C u),
    (∃ f, confirms C u p f ∧ f q = 0) →
    (∃ f, confirms C u p f ∧ f r = 0) →
    ∃ f, confirms C u p f ∧ f ((1 / 2 : ℝ) • ((q : A) + r)) = 0

/-! The final theorem below uses a compact side certificate.  Its fields are
the exact ROG support facts: every original positive generator lies on one of
the two sides, the side retraction sends each generator back into the original
cone, and the inherited unit cannot increase. -/

structure RetractionCertificate (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (J : JoinData (A := A)) where
  generators : Set A
  generates : C = PointedCone.hull ℝ generators
  maps_to_side : ∀ x ∈ generators,
    J.leftSubspace.subtype (J.leftRetraction x) ∈ C
  subunit : ∀ x ∈ generators,
    sideUnit u J.leftSubspace (J.leftRetraction x) ≤ u x
  pureLift : ∀ p : pure (sideCone C J.leftSubspace) (sideUnit u J.leftSubspace),
    ∃ q : pure C u,
    (q : A) = (p : A)

private theorem left_positive (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (J : JoinData (A := A)) (H : RetractionCertificate C u J) :
    ∀ x ∈ C, J.leftRetraction x ∈ sideCone C J.leftSubspace := by
  intro x hx
  rw [H.generates] at hx
  rcases (PointedCone.mem_hull_set.mp hx) with ⟨c, hc, hnonneg, hsum⟩
  change J.leftSubspace.subtype (J.leftRetraction x) ∈ C
  rw [← hsum]
  change J.leftSubspace.subtype
      (J.leftRetraction (∑ z ∈ c.support, c z • z)) ∈ C
  rw [map_sum]
  rw [map_sum]
  simp only [map_smul]
  change (∑ z ∈ c.support,
      c z • J.leftSubspace.subtype (J.leftRetraction z)) ∈ C
  exact C.sum_mem (fun z hz =>
    C.smul_mem (hnonneg z) (H.maps_to_side z (hc hz)))

private theorem left_subunit (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (J : JoinData (A := A)) (H : RetractionCertificate C u J) :
    ∀ x ∈ C, sideUnit u J.leftSubspace (J.leftRetraction x) ≤ u x := by
  intro x hx
  rw [H.generates] at hx
  rcases (PointedCone.mem_hull_set.mp hx) with ⟨c, hc, hnonneg, hsum⟩
  rw [← hsum]
  change u (J.leftSubspace.subtype
      (J.leftRetraction (∑ z ∈ c.support, c z • z))) ≤
    u (∑ z ∈ c.support, c z • z)
  repeat rw [map_sum]
  have hterm : ∀ z, z ∈ c.support →
      sideUnit u J.leftSubspace (J.leftRetraction z) ≤ u z := fun z hz => H.subunit z (hc hz)
  have hmul : ∀ z ∈ c.support, c z •
      sideUnit u J.leftSubspace (J.leftRetraction z) ≤ c z • u z := by
    intro z hz
    exact smul_le_smul_of_nonneg_left (hterm z hz) (hnonneg z)
  apply Finset.sum_le_sum
  intro z hz
  simpa [sideUnit, map_smul, smul_eq_mul] using hmul z hz

theorem extend_effect_left (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (J : JoinData (A := A)) (H : RetractionCertificate C u J)
    (g : J.leftSubspace →ₗ[ℝ] ℝ)
    (hg : proper (sideCone C J.leftSubspace) (sideUnit u J.leftSubspace) g) :
    proper C u (g.comp J.leftRetraction) := by
  intro x hx
  have hR := left_positive C u J H x hx
  have hU := hg (J.leftRetraction x) hR
  exact ⟨hU.1, hU.2.trans (left_subunit C u J H x hx)⟩

theorem restrict_extend_left (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (J : JoinData (A := A)) (g : J.leftSubspace →ₗ[ℝ] ℝ) :
    (g.comp J.leftRetraction).comp J.leftSubspace.subtype = g := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [J.leftRetraction_on_left]

theorem restrict_surjective_left (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (J : JoinData (A := A)) (H : RetractionCertificate C u J) :
    Function.Surjective (restrictEffect C u J.leftSubspace) := by
  intro g
  refine ⟨⟨g.1.comp J.leftRetraction, extend_effect_left C u J H g.1 g.2⟩, ?_⟩
  apply Subtype.ext
  exact restrict_extend_left C u J g.1

theorem inherit_G2_left (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (J : JoinData (A := A)) (H : RetractionCertificate C u J)
    (hG : G2 C u) :
    G2 (sideCone C J.leftSubspace) (sideUnit u J.leftSubspace) := by
  intro p q r hpq hpr
  obtain ⟨p0, hp0⟩ := H.pureLift p
  obtain ⟨q0, hq0⟩ := H.pureLift q
  obtain ⟨r0, hr0⟩ := H.pureLift r
  rcases hpq with ⟨f, hf, hfq⟩
  rcases hpr with ⟨g, hg, hgr⟩
  have hf' : proper C u (f.comp J.leftRetraction) := extend_effect_left C u J H f hf.1
  have hg' : proper C u (g.comp J.leftRetraction) := extend_effect_left C u J H g hg.1
  have hp' : (f.comp J.leftRetraction) (p0 : A) = 1 := by
    change f (J.leftRetraction (p0 : A)) = 1
    rw [hp0]
    rw [show J.leftRetraction (p : A) = p from J.leftRetraction_on_left p]
    exact hf.2
  have hp'' : (g.comp J.leftRetraction) (p0 : A) = 1 := by
    change g (J.leftRetraction (p0 : A)) = 1
    rw [hp0]
    rw [show J.leftRetraction (p : A) = p from J.leftRetraction_on_left p]
    exact hg.2
  have hq' : (f.comp J.leftRetraction) (q0 : A) = 0 := by
    change f (J.leftRetraction (q0 : A)) = 0
    rw [hq0]
    rw [show J.leftRetraction (q : A) = q from J.leftRetraction_on_left q]
    exact hfq
  have hr' : (g.comp J.leftRetraction) (r0 : A) = 0 := by
    change g (J.leftRetraction (r0 : A)) = 0
    rw [hr0]
    rw [show J.leftRetraction (r : A) = r from J.leftRetraction_on_left r]
    exact hgr
  obtain ⟨k, hk, hkm⟩ := hG p0 q0 r0 ⟨f.comp J.leftRetraction, ⟨hf', hp'⟩, hq'⟩
    ⟨g.comp J.leftRetraction, ⟨hg', hp''⟩, hr'⟩
  let kside : sideProperEffect C u J.leftSubspace :=
    restrictEffect C u J.leftSubspace ⟨k, hk.1⟩
  refine ⟨kside.1, ?_, ?_⟩
  · refine ⟨kside.2, ?_⟩
    simpa [kside, restrictEffect, hp0, J.leftRetraction_on_left] using hk.2
  · simpa [kside, restrictEffect, map_smul, map_add, hp0, hq0, hr0,
      J.leftRetraction_on_left] using hkm

/-! The right-hand statements are deliberately separate so that each side
can carry its own ROG generator certificate.  This is the symmetric half of
the source lemma, rather than an assumption that one certificate is silently
reused for both sides. -/

structure RightRetractionCertificate (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (J : JoinData (A := A)) where
  generators : Set A
  generates : C = PointedCone.hull ℝ generators
  maps_to_side : ∀ x ∈ generators,
    J.rightSubspace.subtype (J.rightRetraction x) ∈ C
  subunit : ∀ x ∈ generators,
    sideUnit u J.rightSubspace (J.rightRetraction x) ≤ u x
  pureLift : ∀ p : pure (sideCone C J.rightSubspace) (sideUnit u J.rightSubspace),
    ∃ q : pure C u,
    (q : A) = (p : A)

private theorem right_positive (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (J : JoinData (A := A)) (H : RightRetractionCertificate C u J) :
    ∀ x ∈ C, J.rightRetraction x ∈ sideCone C J.rightSubspace := by
  intro x hx
  rw [H.generates] at hx
  rcases (PointedCone.mem_hull_set.mp hx) with ⟨c, hc, hnonneg, hsum⟩
  change J.rightSubspace.subtype (J.rightRetraction x) ∈ C
  rw [← hsum]
  change J.rightSubspace.subtype
      (J.rightRetraction (∑ z ∈ c.support, c z • z)) ∈ C
  rw [map_sum]
  rw [map_sum]
  simp only [map_smul]
  change (∑ z ∈ c.support,
      c z • J.rightSubspace.subtype (J.rightRetraction z)) ∈ C
  exact C.sum_mem (fun z hz =>
    C.smul_mem (hnonneg z) (H.maps_to_side z (hc hz)))

private theorem right_subunit (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (J : JoinData (A := A)) (H : RightRetractionCertificate C u J) :
    ∀ x ∈ C, sideUnit u J.rightSubspace (J.rightRetraction x) ≤ u x := by
  intro x hx
  rw [H.generates] at hx
  rcases (PointedCone.mem_hull_set.mp hx) with ⟨c, hc, hnonneg, hsum⟩
  rw [← hsum]
  change u (J.rightSubspace.subtype
      (J.rightRetraction (∑ z ∈ c.support, c z • z))) ≤
    u (∑ z ∈ c.support, c z • z)
  repeat rw [map_sum]
  have hterm : ∀ z, z ∈ c.support →
      sideUnit u J.rightSubspace (J.rightRetraction z) ≤ u z :=
    fun z hz => H.subunit z (hc hz)
  have hmul : ∀ z ∈ c.support, c z •
      sideUnit u J.rightSubspace (J.rightRetraction z) ≤ c z • u z := by
    intro z hz
    exact smul_le_smul_of_nonneg_left (hterm z hz) (hnonneg z)
  apply Finset.sum_le_sum
  intro z hz
  simpa [sideUnit, map_smul, smul_eq_mul] using hmul z hz

/-! The supported cones are presented in two equivalent ways: as the image of
the original generating hull under the retraction, and as the exact ambient
cone cut down to the side subspace.  This is the abstract ROG form of
`L_Y ∩ PSD(U)` and `L_Z ∩ PSD(W)`. -/

def supportedConeLeft (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (J : JoinData (A := A)) (H : RetractionCertificate C u J) :
    PointedCone ℝ J.leftSubspace :=
  (PointedCone.hull ℝ H.generators).map J.leftRetraction

def supportedConeRight (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (J : JoinData (A := A)) (H : RightRetractionCertificate C u J) :
    PointedCone ℝ J.rightSubspace :=
  (PointedCone.hull ℝ H.generators).map J.rightRetraction

theorem supportedConeLeft_eq_sideCone (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (J : JoinData (A := A)) (H : RetractionCertificate C u J) :
    supportedConeLeft C u J H = sideCone C J.leftSubspace := by
  apply SetLike.ext
  intro y
  constructor
  · intro hy
    rcases PointedCone.mem_map.mp hy with ⟨x, hx, hxy⟩
    have hC : J.leftRetraction x ∈ sideCone C J.leftSubspace :=
      left_positive C u J H x (by rw [H.generates]; exact hx)
    rw [← hxy]
    exact hC
  · intro hy
    have hC : (y : A) ∈ C := hy
    rw [H.generates] at hC
    have hmap : J.leftRetraction (J.leftSubspace.subtype y) = y :=
      J.leftRetraction_on_left y
    exact PointedCone.mem_map.mpr ⟨J.leftSubspace.subtype y, hC, hmap⟩

theorem supportedConeRight_eq_sideCone (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (J : JoinData (A := A)) (H : RightRetractionCertificate C u J) :
    supportedConeRight C u J H = sideCone C J.rightSubspace := by
  apply SetLike.ext
  intro y
  constructor
  · intro hy
    rcases PointedCone.mem_map.mp hy with ⟨x, hx, hxy⟩
    have hC : J.rightRetraction x ∈ sideCone C J.rightSubspace :=
      right_positive C u J H x (by rw [H.generates]; exact hx)
    rw [← hxy]
    exact hC
  · intro hy
    have hC : (y : A) ∈ C := hy
    rw [H.generates] at hC
    have hmap : J.rightRetraction (J.rightSubspace.subtype y) = y :=
      J.rightRetraction_on_right y
    exact PointedCone.mem_map.mpr ⟨J.rightSubspace.subtype y, hC, hmap⟩

theorem extend_effect_right (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (J : JoinData (A := A)) (H : RightRetractionCertificate C u J)
    (g : J.rightSubspace →ₗ[ℝ] ℝ)
    (hg : proper (sideCone C J.rightSubspace) (sideUnit u J.rightSubspace) g) :
    proper C u (g.comp J.rightRetraction) := by
  intro x hx
  have hR := right_positive C u J H x hx
  have hU := hg (J.rightRetraction x) hR
  exact ⟨hU.1, hU.2.trans (right_subunit C u J H x hx)⟩

theorem restrict_extend_right (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (J : JoinData (A := A)) (g : J.rightSubspace →ₗ[ℝ] ℝ) :
    (g.comp J.rightRetraction).comp J.rightSubspace.subtype = g := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [J.rightRetraction_on_right]

theorem restrict_surjective_right (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (J : JoinData (A := A)) (H : RightRetractionCertificate C u J) :
    Function.Surjective (restrictEffect C u J.rightSubspace) := by
  intro g
  refine ⟨⟨g.1.comp J.rightRetraction, extend_effect_right C u J H g.1 g.2⟩, ?_⟩
  apply Subtype.ext
  exact restrict_extend_right C u J g.1

theorem inherit_G2_right (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (J : JoinData (A := A)) (H : RightRetractionCertificate C u J)
    (hG : G2 C u) :
    G2 (sideCone C J.rightSubspace) (sideUnit u J.rightSubspace) := by
  intro p q r hpq hpr
  obtain ⟨p0, hp0⟩ := H.pureLift p
  obtain ⟨q0, hq0⟩ := H.pureLift q
  obtain ⟨r0, hr0⟩ := H.pureLift r
  rcases hpq with ⟨f, hf, hfq⟩
  rcases hpr with ⟨g, hg, hgr⟩
  have hf' : proper C u (f.comp J.rightRetraction) :=
    extend_effect_right C u J H f hf.1
  have hg' : proper C u (g.comp J.rightRetraction) :=
    extend_effect_right C u J H g hg.1
  have hp' : (f.comp J.rightRetraction) (p0 : A) = 1 := by
    change f (J.rightRetraction (p0 : A)) = 1
    rw [hp0]
    rw [show J.rightRetraction (p : A) = p from J.rightRetraction_on_right p]
    exact hf.2
  have hp'' : (g.comp J.rightRetraction) (p0 : A) = 1 := by
    change g (J.rightRetraction (p0 : A)) = 1
    rw [hp0]
    rw [show J.rightRetraction (p : A) = p from J.rightRetraction_on_right p]
    exact hg.2
  have hq' : (f.comp J.rightRetraction) (q0 : A) = 0 := by
    change f (J.rightRetraction (q0 : A)) = 0
    rw [hq0]
    rw [show J.rightRetraction (q : A) = q from J.rightRetraction_on_right q]
    exact hfq
  have hr' : (g.comp J.rightRetraction) (r0 : A) = 0 := by
    change g (J.rightRetraction (r0 : A)) = 0
    rw [hr0]
    rw [show J.rightRetraction (r : A) = r from J.rightRetraction_on_right r]
    exact hgr
  obtain ⟨k, hk, hkm⟩ := hG p0 q0 r0
    ⟨f.comp J.rightRetraction, ⟨hf', hp'⟩, hq'⟩
    ⟨g.comp J.rightRetraction, ⟨hg', hp''⟩, hr'⟩
  let kside : sideProperEffect C u J.rightSubspace :=
    restrictEffect C u J.rightSubspace ⟨k, hk.1⟩
  refine ⟨kside.1, ?_, ?_⟩
  · refine ⟨kside.2, ?_⟩
    simpa [kside, restrictEffect, hp0, J.rightRetraction_on_right] using hk.2
  · simpa [kside, restrictEffect, map_smul, map_add, hp0, hq0, hr0,
      J.rightRetraction_on_right] using hkm

end D5.S3.Quantum.Foundation.LinearJoinRetraction

#print axioms D5.S3.Quantum.Foundation.LinearJoinRetraction.JoinData.leftRetraction
#print axioms D5.S3.Quantum.Foundation.LinearJoinRetraction.restrict_surjective_left
#print axioms D5.S3.Quantum.Foundation.LinearJoinRetraction.inherit_G2_left
#print axioms D5.S3.Quantum.Foundation.LinearJoinRetraction.restrict_surjective_right
#print axioms D5.S3.Quantum.Foundation.LinearJoinRetraction.inherit_G2_right
