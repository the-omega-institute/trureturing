/- GID: D5/S3/Geometry/AlgebraicBoundary/ConeSectionDegree
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/ConeSectionDegree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The specified positive unit has an actual kernel chart with exact minimum degree transport. -/

import D5.S3.Geometry.AlgebraicBoundary.ConeSectionBoundary

noncomputable section
open Set
open scoped Topology
namespace D5.S3.Geometry.AlgebraicBoundary.ConeSectionDegree

open private original_section_boundary
  from D5.S3.Geometry.AlgebraicBoundary.ConeSectionBoundary
open private sectionChart
  from D5.S3.Geometry.AlgebraicBoundary.ConeRadialGeometry
open private base_chart_geometry
  from D5.S3.Geometry.AlgebraicBoundary.ConeCompactBase
open private affinePullback chart_minimum_correspondence chart_boundary_lift
  chartHomogenize chartHomogenize_homogeneous chartHomogenize_ne_zero chartHomogenize_section
  from D5.S3.Geometry.AlgebraicBoundary.ConeBoundaryEquation

variable {ι : Type*} [Fintype ι]

private theorem original_section_degree {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    (c : E ≃L[ℝ] (ι → ℝ)) (C : ProperCone ℝ E)
    (hs : (C : ConvexCone ℝ E).Salient) (hfull : (interior (C : Set E)).Nonempty)
    (u : E →L[ℝ] ℝ) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hdim : 2 ≤ Module.finrank ℝ E) :
    let κ := Fin (Module.finrank ℝ u.ker)
    ∃ (b : E) (J : (κ → ℝ) →L[ℝ] E) (A : E →L[ℝ] (κ → ℝ)),
      u b = 1 ∧ b ∈ interior (C : Set E) ∧
      (∀ v, u (J v) = 0) ∧ A b = 0 ∧ (∀ v, A (J v) = v) ∧
      (∀ x, J (A x) = x - u x • b) ∧
      let B : Set (κ → ℝ) := {v | b + J v ∈ C}
      IsCompact B ∧ Convex ℝ B ∧ (interior B).Nonempty ∧ (frontier B).Nonempty ∧
      (∀ v, v ∈ frontier B ↔ b + J v ∈ frontier (C : Set E)) ∧
      (∀ (p : MvPolynomial ι ℝ) (d : ℕ), p ≠ 0 → p.IsHomogeneous d →
        (∀ x ∈ frontier (C : Set E), MvPolynomial.eval (c x) p = 0) →
        (∀ q : MvPolynomial ι ℝ, q ≠ 0 →
          (∀ x ∈ frontier (C : Set E), MvPolynomial.eval (c x) q = 0) →
            p.totalDegree ≤ q.totalDegree) →
        let f := affinePullback p (c b) (c.toContinuousLinearMap.comp J)
        f ≠ 0 ∧ f.totalDegree = p.totalDegree ∧
          (∀ v ∈ frontier B, MvPolynomial.eval v f = 0) ∧
          ∀ g : MvPolynomial κ ℝ, g ≠ 0 →
            (∀ v ∈ frontier B, MvPolynomial.eval v g = 0) → f.totalDegree ≤ g.totalDegree) ∧
      (∀ g : MvPolynomial κ ℝ, g ≠ 0 →
        (∀ v ∈ frontier B, MvPolynomial.eval v g = 0) →
        ∃ G : MvPolynomial ι ℝ, G ≠ 0 ∧ G.IsHomogeneous g.totalDegree ∧
          G.totalDegree = g.totalDegree ∧
          (∀ v, MvPolynomial.eval (c (b + J v)) G = MvPolynomial.eval v g) ∧
          ∀ x ∈ frontier (C : Set E), MvPolynomial.eval (c x) G = 0) := by
  classical
  dsimp only
  let κ := Fin (Module.finrank ℝ u.ker)
  obtain ⟨hc, _, ⟨b, hb, hbi⟩, _, _⟩ := original_section_boundary C hs hfull u hu
  let P : E →L[ℝ] u.ker :=
    (ContinuousLinearMap.id ℝ E - u.smulRight b).codRestrict u.ker
      (by intro x; simp [hb])
  have hP : ∀ x, (P x : E) = x - u x • b := fun _ => rfl
  let k : u.ker ≃L[ℝ] (κ → ℝ) := (Module.finBasis ℝ u.ker).equivFunL
  let J : (κ → ℝ) →L[ℝ] E := u.ker.subtypeL.comp k.symm.toContinuousLinearMap
  let A : E →L[ℝ] (κ → ℝ) := k.toContinuousLinearMap.comp P
  have hJ : ∀ v, u (J v) = 0 := fun v => (k.symm v).property
  have hAb : A b = 0 := by
    have hh : P b = 0 := by apply Subtype.ext; simp [hP, hb]
    simp [A, hh]
  have hAJ : ∀ v, A (J v) = v := by
    intro v
    have hh : P (J v) = k.symm v := by apply Subtype.ext; simp [hP, hJ, J]
    simp [A, hh]
  have hdecomp : ∀ x, J (A x) = x - u x • b := by
    intro x
    simpa [J, A] using hP x
  have hnontriv : Nontrivial u.ker := by
    rcases subsingleton_or_nontrivial u.ker with hsub | hnon
    · letI := hsub
      have hinj : Function.Injective u := by
        intro x y hxy
        have hx : P x = 0 := Subsingleton.elim _ _
        have hy : P y = 0 := Subsingleton.elim _ _
        have hx' : x = u x • b := by simpa [hP, sub_eq_zero] using congrArg Subtype.val hx
        have hy' : y = u y • b := by simpa [hP, sub_eq_zero] using congrArg Subtype.val hy
        rw [hx', hy', hxy]
      have hh := LinearMap.finrank_le_finrank_of_injective (f := u.toLinearMap) hinj
      simp only [Module.finrank_self] at hh
      omega
    · exact hnon
  letI := hnontriv
  letI : Nontrivial (κ → ℝ) := k.toEquiv.symm.nontrivial
  let K : Set u.ker := {v | b + (v : E) ∈ C}
  let B : Set (κ → ℝ) := {v | b + J v ∈ C}
  let e := sectionChart u b hb
  have hKc : IsCompact K := e.isClosedEmbedding.isCompact_preimage hc
  have hKB : k '' K = B := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [B, J, K] using hw
    · intro hv
      exact ⟨k.symm v, hv, k.apply_symm_apply v⟩
  have hBc : IsCompact B := hKB ▸ hKc.image k.continuous
  have hBv : Convex ℝ B :=
    (C.convex.translate_preimage_right b).linear_preimage J.toLinearMap
  have hgeo := base_chart_geometry C u b hb
  have hfr : ∀ v, v ∈ frontier B ↔ b + J v ∈ frontier (C : Set E) := by
    intro v
    have hh : frontier B = k '' frontier K := by
      rw [← hKB]
      exact (k.toHomeomorph.image_frontier K).symm
    rw [hh]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [J] using (hgeo.2 w).mp hw
    · intro hv
      exact ⟨k.symm v, (hgeo.2 _).mpr hv, k.apply_symm_apply v⟩
  have hBi : (interior B).Nonempty := by
    refine ⟨0, ?_⟩
    have hi : (0 : u.ker) ∈ interior K := (hgeo.1 0).mpr (by simpa using hbi)
    have hh : interior B = k '' interior K := by
      rw [← hKB]
      exact (k.toHomeomorph.image_interior K).symm
    rw [hh]
    exact ⟨0, hi, by simp⟩
  have hBf : (frontier B).Nonempty := nonempty_frontier_iff.mpr
    ⟨hBi.mono interior_subset, hBc.ne_univ⟩
  let D := C.comap c.symm.toContinuousLinearMap
  let uc := u.comp c.symm.toContinuousLinearMap
  let Jc := c.toContinuousLinearMap.comp J
  let Ac := A.comp c.symm.toContinuousLinearMap
  have hfrontD : frontier (D : Set (ι → ℝ)) = c.symm ⁻¹' frontier (C : Set E) :=
    (c.symm.toHomeomorph.preimage_frontier (C : Set E)).symm
  have hBD : {v : κ → ℝ | c b + Jc v ∈ D} = B := by ext v; simp [D, Jc, B]
  have huD : ∀ x ∈ D, x ≠ 0 → 0 < uc x := by
    intro x hx hx0
    apply hu (c.symm x) hx
    exact fun h => hx0 (c.symm.injective (by simpa using h))
  have hbc : uc (c b) = 1 := by simpa [uc] using hb
  have hJc : ∀ v, uc (Jc v) = 0 := by intro v; simpa [uc, Jc] using hJ v
  have hAcb : Ac (c b) = 0 := by simpa [Ac] using hAb
  have hAcJ : ∀ v, Ac (Jc v) = v := by intro v; simpa [Ac, Jc] using hAJ v
  have hdec : ∀ x, Jc (Ac x) = x - uc x • c b := by
    intro x
    simpa [Jc, Ac, uc, map_sub, map_smul] using congrArg c (hdecomp (c.symm x))
  have hfrD : ∀ v, v ∈ frontier {v : κ → ℝ | c b + Jc v ∈ D} ↔
      c b + Jc v ∈ frontier (D : Set (ι → ℝ)) := by
    intro v
    rw [hBD, hfrontD]
    simpa [Jc, map_add] using hfr v
  have hvanD : ∀ p : MvPolynomial ι ℝ,
      (∀ x ∈ frontier (C : Set E), MvPolynomial.eval (c x) p = 0) ↔
      ∀ x ∈ frontier (D : Set (ι → ℝ)), MvPolynomial.eval x p = 0 := by
    intro p
    constructor
    · intro h x hx
      simpa using h (c.symm x) (by simpa [hfrontD] using hx)
    · intro h x hx
      exact h (c x) (by simpa [hfrontD] using hx)
  refine ⟨b, J, A, hb, hbi, hJ, hAb, hAJ, hdecomp, hBc, hBv, hBi, hBf, hfr, ?_, ?_⟩
  · intro p d hp hhom hvan hmin
    have hm : ∀ q : MvPolynomial ι ℝ, q ≠ 0 →
        (∀ x ∈ frontier (D : Set (ι → ℝ)), MvPolynomial.eval x q = 0) →
        p.totalDegree ≤ q.totalDegree := fun q hq hqv => hmin q hq ((hvanD q).mpr hqv)
    simpa only [hBD] using chart_minimum_correspondence D uc huD (c b) hbc Jc Ac
      hJc hAcb hAcJ hdec hfrD (hBD.symm ▸ hBf) p hp hhom ((hvanD p).mp hvan) hm
  · intro g hg hgv
    have hgpos : 0 < g.totalDegree := by
      by_contra! h
      have heq := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h)
      obtain ⟨v, hv⟩ := hBf
      have hh := hgv v hv
      rw [heq, MvPolynomial.eval_C] at hh
      exact hg (heq.trans (by rw [hh, map_zero]))
    let G := chartHomogenize g uc Ac
    have hG : G ≠ 0 := chartHomogenize_ne_zero g hg uc (c b) hbc Jc Ac hJc hAcb hAcJ
    have hGh := chartHomogenize_homogeneous g uc Ac
    refine ⟨G, hG, hGh, hGh.totalDegree hG, ?_, ?_⟩
    · intro v
      simpa [Jc, map_add] using chartHomogenize_section g uc (c b) hbc Jc Ac hJc hAcb hAcJ v
    · apply (hvanD G).mpr
      apply chart_boundary_lift D uc huD (c b) hbc Jc Ac hdec hfrD g hgpos
      simpa only [hBD] using hgv

end D5.S3.Geometry.AlgebraicBoundary.ConeSectionDegree
