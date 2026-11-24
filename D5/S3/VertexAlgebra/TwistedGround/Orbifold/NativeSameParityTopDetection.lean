/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeSameParityTopDetection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeSameParityTopDetection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The integral Zhu coefficients detect the entire lawful same-parity field. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParityZhuTopBalance

/-!
Abe, arXiv:math/9907120v1, Proposition 2.10, on the same actual twisted parity
on both legs. Signed Borcherds and truncation for the fixed action give the span
of single fixed-mode translates of the top. The mixed commutator first moves
the input modes across the coefficient and then stabilizes the output span.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParity

open LatticeGeneratingFieldLocality LatticeInvolution LatticePositiveEnergy
open NativeOddTwistedIntertwiner (OddCarrier Twisted oddMode fixedAction twistedTop
  twistedTopGrade twistedTopReadout twistedTop_mode_span)
open StateFieldResidueReconstruction (integerBinomial)
open private ambientGradeReadout_self ambientGradeReadout_zero_of_signedGrade_ne
    fixedActionAt fixedActionAt_apply fixedAction_equal_degree_top lowering_kills_top
    theta_gradeProjection topReadout_raising_zero twisted_mode_irreducible twistedTop_nonzero
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTopDetection
open private oddPart oddPart_grade oddPart_on_odd
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddZhuTopBalance

noncomputable section

variable {D : LatticeData} {hu : IsUnit D.G.det} {s : Bool}

private theorem topReadout_zero_on_fixedMode_top (F : LawfulField D hu s)
    (seed : ∀ (n : ℤ) (b : OddCarrier D) (v : Twisted D hu s), v ∈ twistedTop D hu s →
      twistedTopReadout D hu s (F.coeff n b v) = 0)
    (a : FixedCarrier D) (p q : ℤ) (b : OddCarrier D) (v : Twisted D hu s)
    (hv : v ∈ twistedTop D hu s) :
    twistedTopReadout D hu s (F.coeff q b (fixedAction s a p v)) = 0 := by
  classical
  let P := twistedTopReadout D hu s
  let E := P.comp ((F.coeff q b).comp (fixedActionAt p v))
  have hom (c : FixedCarrier D) (h : ℤ) (hc : c.val ∈ grade D h) : E c = 0 := by
    change P (F.coeff q b (fixedActionAt p v c)) = 0
    rw [fixedActionAt_apply]
    rcases lt_trichotomy p (h - 1) with hr | he | hl
    · let term (i : ℕ) := integerBinomial p i • F.coeff (p+q-i) (oddMode D c i b) v
      obtain ⟨hfin, hcomm⟩ := mixed_commutator F c b v p q
      have hreadout := congrArg P hcomm
      change P (∑ᶠ i, term i) =
        P (fixedAction s c p (F.coeff q b v) - F.coeff q b (fixedAction s c p v)) at hreadout
      rw [map_finsum P (show Function.HasFiniteSupport term from hfin), map_sub P,
        topReadout_raising_zero c h p hc hr (F.coeff q b v), zero_sub] at hreadout
      have hterm (i : ℕ) : P (term i) = 0 := by
        have hz : P (F.coeff (p+q-i) (oddMode D c i b) v) = 0 :=
          seed (p+q-i) (oddMode D c i b) v hv
        change P (integerBinomial p i • F.coeff (p+q-i) (oddMode D c i b) v) = 0
        rw [map_smul P, hz, smul_zero]
      simp only [hterm, finsum_zero] at hreadout
      exact neg_eq_zero.mp hreadout.symm
    · exact seed q b _ (fixedAction_equal_degree_top c h p hc he v hv)
    · simp only [lowering_kills_top c h p hc hl v hv, map_zero]
  let part (h : ℤ) : FixedCarrier D :=
    (FixedGradedDuality.fixedGradeProjection D theta_gradeProjection h a).val
  have hsum : (∑ h ∈ stateEnergies D a.val, part h) = a :=
    FixedGradedDuality.fixedGradeProjection_sum D theta_gradeProjection a
  change P (F.coeff q b (fixedAction s a p v)) = 0
  rw [← fixedActionAt_apply p v a]
  change E a = 0
  rw [← hsum, map_sum]
  exact Finset.sum_eq_zero fun h _ =>
    hom (part h) h (FixedGradedDuality.fixedGradeProjection D theta_gradeProjection h a).property

private theorem coeff_eq_zero_of_topReadout_zero (hrank : 2 ≤ D.rank)
    (F : LawfulField D hu s)
    (seed : ∀ (n : ℤ) (b : OddCarrier D) (v : Twisted D hu s), v ∈ twistedTop D hu s →
      twistedTopReadout D hu s (F.coeff n b v) = 0) :
    F.coeff = 0 := by
  classical
  let P := twistedTopReadout D hu s
  have all_inputs (n : ℤ) (b : OddCarrier D) (v : Twisted D hu s) : P (F.coeff n b v) = 0 := by
    let L := P.comp (F.coeff n b)
    have hspan : Submodule.span ℂ ((twistedTop D hu s : Set (Twisted D hu s)) ∪
        {w : Twisted D hu s | ∃ (a : FixedCarrier D) (q : ℤ) (t : Twisted D hu s),
          t ∈ twistedTop D hu s ∧ w = fixedAction s a q t}) ≤ LinearMap.ker L := by
      apply Submodule.span_le.mpr
      intro w hw
      apply LinearMap.mem_ker.mpr
      rcases hw with hw | ⟨a, q, t, ht, rfl⟩
      · exact seed n b w hw
      · exact topReadout_zero_on_fixedMode_top F seed a q n b t ht
    rw [twistedTop_mode_span hrank] at hspan
    exact LinearMap.mem_ker.mp (hspan (Submodule.mem_top (x := v)))
  let generators : Set (Twisted D hu s) :=
    {w | ∃ (n : ℤ) (b : OddCarrier D) (v : Twisted D hu s), w = F.coeff n b v}
  let S : Submodule ℂ (Twisted D hu s) := Submodule.span ℂ generators
  have mem (n : ℤ) (b : OddCarrier D) (v : Twisted D hu s) : F.coeff n b v ∈ S :=
    Submodule.subset_span (show F.coeff n b v ∈ generators from ⟨n, b, v, rfl⟩)
  have hker : S ≤ LinearMap.ker P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, b, v, rfl⟩
    exact LinearMap.mem_ker.mpr (all_inputs n b v)
  have stable (a : FixedCarrier D) (p : ℤ) : S ≤ S.comap (fixedAction s a p) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨q, b, v, rfl⟩
    let term (i : ℕ) := integerBinomial p i • F.coeff (p+q-i) (oddMode D a i b) v
    obtain ⟨hfin, hcomm⟩ := mixed_commutator F a b v p q
    change (∑ᶠ i, term i) =
      fixedAction s a p (F.coeff q b v) - F.coeff q b (fixedAction s a p v) at hcomm
    have hsum : (∑ᶠ i, term i) ∈ S := by
      rw [finsum_eq_sum term (show Function.HasFiniteSupport term from hfin)]
      exact S.sum_mem (fun i _ => S.smul_mem _ (mem _ _ _))
    have hmode : (∑ᶠ i, term i) + F.coeff q b (fixedAction s a p v) =
        fixedAction s a p (F.coeff q b v) := eq_sub_iff_add_eq.mp hcomm
    change fixedAction s a p (F.coeff q b v) ∈ S
    rw [← hmode]
    exact S.add_mem hsum (mem _ _ _)
  have hbot : S = ⊥ := by
    rcases twisted_mode_irreducible hrank S (fun a p _ hv => stable a p hv) with hbot | htop
    · exact hbot
    · obtain ⟨w, hw, hne⟩ := twistedTop_nonzero (hu := hu) (s := s) hrank
      have hz : P w = 0 := LinearMap.mem_ker.mp (hker (htop.symm ▸ Submodule.mem_top))
      have hself : P w = w.val := ambientGradeReadout_self (twistedTopGrade s) w.val hw
      exact (hne (Subtype.ext (hself.symm.trans hz))).elim
  funext n
  apply LinearMap.ext
  intro b
  apply LinearMap.ext
  intro v
  have hm := mem n b v
  rw [hbot, Submodule.mem_bot] at hm
  simpa only [Pi.zero_apply, LinearMap.zero_apply] using hm

/-- The full integral field vanishes if each homogeneous source of weight `h`
has zero top readout at its physical mode `h - 1` on every input top. -/
theorem coeff_eq_zero_of_twistedZhuTopReadout_zero (hrank : 2 ≤ D.rank)
    (F : LawfulField D hu s)
    (hZhu : ∀ (h : ℤ) (b : OddCarrier D) (v : twistedTop D hu s),
      b.val ∈ grade D h →
      twistedTopReadout D hu s (F.coeff (topIndex h) b v.val) = 0) :
    F.coeff = 0 := by
  classical
  apply coeff_eq_zero_of_topReadout_zero hrank F
  intro n b v hv
  let P := twistedTopReadout D hu s
  let E := P.comp ((LinearMap.applyₗ v).comp (F.coeff n))
  let part (h : ℤ) := oddPart D (gradeProjection D h b.val)
  have hsum : (∑ h ∈ stateEnergies D b.val, part h) = b := by
    change (∑ h ∈ stateEnergies D b.val, oddPart D (gradeProjection D h b.val)) = b
    rw [← map_sum, sum_gradeProjections, oddPart_on_odd]
  change E b = 0
  rw [← hsum, map_sum]
  apply Finset.sum_eq_zero
  intro h _
  have hg : (part h).val ∈ grade D h :=
    oddPart_grade h ⟨gradeProjection D h b.val, gradeProjection_mem D h b.val⟩
  change P (F.coeff n (part h) v) = 0
  by_cases hn : n = topIndex h
  · rw [hn]
    exact hZhu h (part h) ⟨v, hv⟩ hg
  · exact ambientGradeReadout_zero_of_signedGrade_ne _ _ _
      (signed_grade F n h (twistedTopGrade s) (part h) v hg hv) (by
        simp only [topIndex] at hn
        omega)

end
end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParity
