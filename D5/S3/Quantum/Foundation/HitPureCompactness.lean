/- GID: D5/S3/Quantum/Foundation/HitPureCompactness
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/HitPureCompactness
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: All original pure-label face incidences close the original pure locus. -/

import D5.S3.Quantum.Foundation.HitSectionGeneration
import D5.S3.Quantum.Foundation.ContinuousFrameSum

/-! Original all-label face incidence excludes nonpure accumulation points. -/

noncomputable section
open Set Filter Topology

namespace D5.S3.Quantum.Foundation.HitPureCompactness

open CircuitBalancedConfirmation FacetZeroGluing WholePairBallConfirmation
  HitSectionGeneration ContinuousFrameSum

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- Every original pure label hitting every actual pure-pair face makes the entire
original pure locus closed and compact. No ball, coefficient, support or reciprocity
premise is imposed. -/
theorem hit_pure_closed_compact (hc : IsClosed (C : Set V))
    (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hhit : ∀ a : pure C u, Hit C u a) :
    IsClosed (pure C u) ∧ IsCompact (pure C u) := by
  classical
  have hK := base_compact hc hu
  have hclosed : IsClosed (pure C u) := by
    apply isSeqClosed_iff_isClosed.mp
    intro an x han hax
    have hx : x ∈ base C u := hK.isClosed.mem_of_tendsto hax
      (Eventually.of_forall fun n => (han n).1)
    by_contra hxp
    let F := principalFace C x
    have hxF : x ∈ base F.toPointedCone u := ⟨mem_principalFace x hx.1, hx.2⟩
    have hcF : IsClosed (F.toPointedCone : Set V) := face_closed hc F
    have huF : ∀ y ∈ F.toPointedCone, y ≠ 0 → 0 < u y :=
      fun y hy => hu y (F.isFaceOf.le hy)
    have hKF := base_compact hcF huF
    have hext := face_base_extreme (u := u) F
    obtain ⟨p, hp⟩ := hKF.extremePoints_nonempty ⟨x, hxF⟩
    let pF : pure F.toPointedCone u := ⟨p, hp⟩
    have hhitF : Hit F.toPointedCone u pF := by
      intro r s hrs
      let rC : pure C u := ⟨r, hext.extremePoints_subset_extremePoints r.property⟩
      let sC : pure C u := ⟨s, hext.extremePoints_subset_extremePoints s.property⟩
      have hrsC : rC ≠ sC := by
        intro h
        apply hrs
        apply Subtype.ext
        exact congrArg (fun t : pure C u => (t : V)) h
      obtain ⟨b, hbN, hbpair⟩ := hhit ⟨p, hext.extremePoints_subset_extremePoints hp⟩ rC sC hrsC
      have hbF : b ∈ base F.toPointedCone u :=
        ⟨hbpair.2 F r.property.1.1 s.property.1.1, hbpair.1.2⟩
      have hbP : b ∈ pure F.toPointedCone u :=
        ⟨hbF, fun _ hy _ hz hseg => hbN.1.2 (hext.subset hy) (hext.subset hz) hseg⟩
      refine ⟨b, ⟨hbP, ?_⟩, hbF, ?_⟩
      · obtain ⟨_, e, he, heb⟩ := hbN.2
        exact ⟨hbF, e, ⟨fun y hy => he.1 y (F.isFaceOf.le hy), he.2⟩, heb⟩
      · intro G hrG hsG
        let G' : C.Face := ⟨G.toPointedCone, G.isFaceOf.trans F.isFaceOf⟩
        exact hbpair.2 G' hrG hsG
    have hgenF : base F.toPointedCone u = convexHull ℝ (pure F.toPointedCone u) := by
      simpa using (hit_section_generation hcF huF pF hhitF ⊤
        (fun _ _ => Submodule.mem_top)).2.1
    have hpair : (pure F.toPointedCone u).Nontrivial := by
      by_contra hn
      have hsub := Set.not_nontrivial_iff.mp hn
      have hsingle : base F.toPointedCone u ⊆ {p} := by
        rw [hgenF]
        exact convexHull_min (fun q hq => hsub hq hp) (convex_singleton p)
      have hxp' : x = p := hsingle hxF
      exact hxp (hxp' ▸ hext.extremePoints_subset_extremePoints hp)
    obtain ⟨r, hr, s, hs, hrs⟩ := hpair
    let rC : pure C u := ⟨r, hext.extremePoints_subset_extremePoints hr⟩
    let sC : pure C u := ⟨s, hext.extremePoints_subset_extremePoints hs⟩
    have hrsC : rC ≠ sC := fun h => hrs (congrArg Subtype.val h)
    choose bn hbnN hbnPair using fun n => hhit ⟨an n, han n⟩ rC sC hrsC
    choose en hen henb using fun n => (hbnN n).2.2
    have hbnF (n : ℕ) : bn n ∈ base F.toPointedCone u :=
      ⟨(hbnPair n).2 F hr.1.1 hs.1.1, (hbnPair n).1.2⟩
    obtain ⟨e, he, φ, hφ, helim⟩ := (effects_compact hu hg).tendsto_subseq
      (fun n => show (en n).toContinuousLinearMap ∈ effects C u from (hen n).1)
    have haseq := hax.comp hφ.tendsto_atTop
    have hev : Continuous (fun z : (V →L[ℝ] ℝ) × V => z.1 z.2) := by fun_prop
    have hex : e x = 1 := tendsto_nhds_unique
      ((hev.tendsto (e, x)).comp (helim.prodMk_nhds haseq))
      (by
        change Tendsto (fun n => en (φ n) (an (φ n))) atTop (𝓝 1)
        simpa only [(hen _).2] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
    have heb (n : ℕ) : e (bn n) = 1 := by
      obtain ⟨z, hz, r, s, hr0, hs0, hrs1, hseg⟩ := principal_extension hx (hbnF n)
      have hez : e z ≤ 1 := (he z (F.isFaceOf.le hz.1)).2.trans_eq hz.2
      have heb' : e (bn n) ≤ 1 := (he (bn n) (F.isFaceOf.le (hbnF n).1)).2.trans_eq (hbnF n).2
      have heq := congrArg e hseg
      simp only [map_add, map_smul, smul_eq_mul, hex] at heq
      nlinarith
    obtain ⟨b, hb, ψ, hψ, hblim⟩ := hK.tendsto_subseq
      (fun n => (hbnPair (φ n)).1)
    have heblim := (hev.tendsto (e, b)).comp
      ((helim.comp hψ.tendsto_atTop).prodMk_nhds hblim)
    have heb0 : e b = 0 := tendsto_nhds_unique heblim (by
      change Tendsto (fun n => en (φ (ψ n)) (bn (φ (ψ n)))) atTop (𝓝 0)
      simpa only [henb] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
    have heb1 : e b = 1 := tendsto_nhds_unique (e.continuous.tendsto b |>.comp hblim)
      (by
        change Tendsto (fun n => e (bn (φ (ψ n)))) atTop (𝓝 1)
        simpa only [heb] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
    linarith
  exact ⟨hclosed, hK.of_isClosed_subset hclosed extremePoints_subset⟩

end D5.S3.Quantum.Foundation.HitPureCompactness
