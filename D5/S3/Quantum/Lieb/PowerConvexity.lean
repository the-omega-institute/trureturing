/- GID: D5/S3/Quantum/Lieb/PowerConvexity
   generality: G
   mirror-B: D5/B/S3/Quantum/Lieb/PowerConvexity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Consumed adapters for the attributed general C-star power convexity supplier. -/

module

public import D5.S3.Quantum.Lieb.JensenOperatorInequality

@[expose] public section

/- The proof supplier is LownerHeinzCore.power_Icc_one_two_operatorConvexOn_Ici,
ported in its source-owning module from Physlib b9043cc548ef6d63a28454cf3a57fb12a0c2e142,
QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LownerHeinzCore.lean.
Copyright Hayata Yamasaki; authors Kei Tsukamoto, Kento Mori, Hayata Yamasaki;
Apache-2.0, retained at docs/reports/inoutbalance/physlib-LICENSE.txt.
These consumed adapters add no new mathematical proof or originality claim. -/

noncomputable section
namespace D5.S3.Quantum.Lieb.PowerConvexity
universe u
open Set Real MeasureTheory
open scoped NNReal
variable {𝓐 : Type*} [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐]

/-- The general C-star conclusion is retained, including the trivial algebra.
The nontrivial case adapts the attributed upstream Core supplier. -/
theorem convexOn_rpow {p : ℝ} (hp : p ∈ Icc 1 2) :
    ConvexOn ℝ (Ici (0 : 𝓐)) (fun X => CFC.rpow X p) := by
  refine ⟨convex_Ici _, ?_⟩
  intro X hX Y hY s t hs ht hst
  cases subsingleton_or_nontrivial 𝓐 with
  | inl h =>
    letI := h
    exact le_of_eq (Subsingleton.elim _ _)
  | inr h =>
    letI := h
    have hs' : s = 1 - t := by linarith
    have ht1 : t ≤ 1 := by linarith
    have hspec (A : 𝓐) (hA : 0 ≤ A) : spectrum ℝ A ⊆ Ici (0 : ℝ) :=
      fun _ hx => spectrum_nonneg_of_nonneg hA hx
    have hh := LownerHeinzCore.power_Icc_one_two_operatorConvexOn_Ici (𝓐 := 𝓐) p hp
      hX.isSelfAdjoint hY.isSelfAdjoint ht ht1 (hspec X hX) (hspec Y hY)
    have hm : 0 ≤ (1 - t) • X + t • Y :=
      add_nonneg (smul_nonneg (sub_nonneg.mpr ht1) hX) (smul_nonneg ht hY)
    change cfc (fun x : ℝ => x ^ p) ((1 - t) • X + t • Y) ≤
      (1 - t) • cfc (fun x : ℝ => x ^ p) X + t • cfc (fun x : ℝ => x ^ p) Y at hh
    simpa only [hs', CFC.rpow_eq_pow, ← CFC.rpow_eq_cfc_real hm,
      ← CFC.rpow_eq_cfc_real hX, ← CFC.rpow_eq_cfc_real hY] using hh

/-- The uniform Jensen input genuinely quantifies over every complete complex Hilbert space. -/
theorem condIciAll_rpow {p : ℝ} (hp : p ∈ Icc 1 2) :
    JensenOperatorInequality.CondIciAll.{u} (fun x : ℝ => x ^ p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro K _ _ _ _
    intro X Y t hX hY ht0 ht1 hXs hYs
    have hX0 : (0 : LownerHeinzTheorem.L K) ≤ X :=
      (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) X (ha := hX)).2 hXs
    have hY0 : (0 : LownerHeinzTheorem.L K) ≤ Y :=
      (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) Y (ha := hY)).2 hYs
    have hm : 0 ≤ (1 - t) • X + t • Y :=
      add_nonneg (smul_nonneg (sub_nonneg.mpr ht1) hX0) (smul_nonneg ht0 hY0)
    have hh := (convexOn_rpow (𝓐 := LownerHeinzTheorem.L K) hp).2 hX0 hY0
      (sub_nonneg.mpr ht1) ht0 (by ring)
    change cfc (fun x : ℝ => x ^ p) ((1 - t) • X + t • Y) ≤
      (1 - t) • cfc (fun x : ℝ => x ^ p) X + t • cfc (fun x : ℝ => x ^ p) Y
    simpa only [CFC.rpow_eq_pow, ← CFC.rpow_eq_cfc_real hm, ← CFC.rpow_eq_cfc_real hX0,
      ← CFC.rpow_eq_cfc_real hY0] using hh
  · exact (Real.continuous_rpow_const (by linarith [hp.1])).continuousOn
  · simp only [Real.zero_rpow (by linarith [hp.1] : p ≠ 0), le_refl]

#print axioms convexOn_rpow
#print axioms condIciAll_rpow
end D5.S3.Quantum.Lieb.PowerConvexity
