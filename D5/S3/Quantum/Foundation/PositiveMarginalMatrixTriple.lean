/- GID: D5/S3/Quantum/Foundation/PositiveMarginalMatrixTriple
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/PositiveMarginalMatrixTriple
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A normalized spectator recovers two missing singleton marginals. -/

import D5.S3.Quantum.Foundation.PositiveMarginalMatrixComposition

/-!
# Missing singleton marginals of one actual triple

The positive preparations and four primitive global marginals satisfy
(24) of the Barnum–Hilgert Library note. Equations (25)–(27) give the
missing second singleton. The same recovered map composed with the actual
13 marginal gives the third singleton. The two returned binary contracts
are on the supplied preparations.
-/

noncomputable section
open scoped Matrix ComplexOrder MatrixOrder TensorProduct

namespace PositiveMarginalMatrixComposition

variable {a d : ℕ}

/-- Primitive data and all-vector laws (24) for one actual matrix triple. -/
structure TripleMarginals {a d e : ℕ}
    (M : H a →ₗ[ℝ] H a →ₗ[ℝ] H d) (L : H d →ₗ[ℝ] H a →ₗ[ℝ] H e)
    (r : H d →ₗ[ℝ] H a) (p12 p13 p23 : H e →ₗ[ℝ] H d) : Prop where
  posM : ∀ x y, x.val.PosSemidef → y.val.PosSemidef → (M x y).val.PosSemidef
  posL : ∀ z x, z.val.PosSemidef → x.val.PosSemidef → (L z x).val.PosSemidef
  posR : ∀ z, z.val.PosSemidef → (r z).val.PosSemidef
  pos12 : ∀ w, w.val.PosSemidef → (p12 w).val.PosSemidef
  pos13 : ∀ w, w.val.PosSemidef → (p13 w).val.PosSemidef
  pos23 : ∀ w, w.val.PosSemidef → (p23 w).val.PosSemidef
  tpR : ∀ z, tr (r z) = tr z
  tp12 : ∀ w, tr (p12 w) = tr w
  tp13 : ∀ w, tr (p13 w) = tr w
  tp23 : ∀ w, tr (p23 w) = tr w
  readR : ∀ x y, r (M x y) = tr y • x
  read12 : ∀ z x, p12 (L z x) = tr x • z
  read13 : ∀ x y z, p13 (L (M x y) z) = tr y • M x z
  read23 : ∀ x y z, p23 (L (M x y) z) = tr x • M y z

/-- A normalized spectator recovers the missing singleton marginals for
both applications of the binary theorem to the same actual pair and triple. -/
theorem triple_recover {e : ℕ} {M : H a →ₗ[ℝ] H a →ₗ[ℝ] H d}
    {L : H d →ₗ[ℝ] H a →ₗ[ℝ] H e} {r : H d →ₗ[ℝ] H a}
    {p12 p13 p23 : H e →ₗ[ℝ] H d} (h : TripleMarginals M L r p12 p13 p23)
    (hs : Spans M) (c : H a) (hc : c.val.PosSemidef) (ht : tr c = 1) :
    let r₂ := r.comp (p23.comp (L.flip c))
    let r₃ := r₂.comp p13
    Marginals M r r₂ ∧ Marginals L p12 r₃ := by
  dsimp only
  let r₂ := r.comp (p23.comp (L.flip c))
  change Marginals M r r₂ ∧ Marginals L p12 (r₂.comp p13)
  have hm : Marginals M r r₂ := by
    refine ⟨h.posM, h.posR, ?_, h.tpR, ?_, h.readR, ?_⟩
    · intro z hz
      exact h.posR _ (h.pos23 _ (h.posL z c hz hc))
    · intro z
      change tr (r (p23 (L z c))) = tr z
      rw [h.tpR, h.tp23, ← h.tp12 (L z c), h.read12]
      have htrace : tr (tr c • z) = tr c * tr z := by simp [tr, Matrix.trace_smul]
      rw [htrace, ht, one_mul]
    · intro x y
      change r (p23 (L (M x y) c)) = tr x • y
      rw [h.read23, map_smul, h.readR, ht, one_smul]
  refine ⟨hm, ⟨h.posL, h.pos12, ?_, h.tp12, ?_, h.read12, ?_⟩⟩
  · intro w hw
    exact hm.posB _ (h.pos13 w hw)
  · intro w
    change tr (r₂ (p13 w)) = tr w
    rw [hm.tpB, h.tp13]
  · intro z x
    let F : H d →ₗ[ℝ] H a := (r₂.comp p13).comp (L.flip x)
    let trace := Complex.reLm.comp ((Matrix.traceLinearMap (Fin d) ℝ ℂ).comp
      (D5.S3.Quantum.Measurement.BasisMeasurementProjection.HermitianSpace d).subtype)
    let G : H d →ₗ[ℝ] H a := (LinearMap.toSpanSingleton ℝ (H a) x).comp trace
    have he : F = G := by
      apply (LinearMap.cancel_right (lift_surjective hs)).mp
      apply TensorProduct.ext'
      intro u v
      simp only [LinearMap.comp_apply, TensorProduct.lift.tmul]
      change r₂ (p13 (L (M u v) x)) = tr (M u v) • x
      rw [h.read13, map_smul, hm.readB, trace_prep hm, smul_smul]
    exact LinearMap.congr_fun he z

end PositiveMarginalMatrixComposition
