/- GID: D5/S3/Zeros/GRH/Lib/Weil/Fock/RealData
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/Fock/RealData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.Fock.RealData. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/Fock/RealData.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.Construction.Projections
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Bargmann–Fock model of the harmonic (oscillator) representation of U(p,q) (known
result; see Lib.Weil.Fock.OscillatorPair). -/

variable {E n s} [Field E] [CMType E] [WeilData E] [Fintype n] (V : Space E n s) (v w f f')

namespace Space

/-- For v, w in the Fock space and f, f′ in 𝒮(V), ⟨v⊗f, w⊗f′⟩ = ⟨v,w⟩·⟨Pf, Pf′⟩, where
v⊗f = ∫v(y)ϱ(y)f dy over real vectors y and P is this operator for the Gaussian. -/
lemma dataInner_integrated : V.dataInner (V.integrated v f) (V.integrated w f') =
  realInner v w * V.dataInner (V.projReal f) (V.projReal f') := by
    simpa [mul_comm] using
      Heisenberg.IsVacuum.integral_form_eq_mul_modelInner (ν := .dirac ()) (fun _ ↦ .bilinearComp _
    (.flip _ f) (.flip _ f')) (by simp) (by simp [integrated_realHeisOp]) ..

/-- For v in the Fock space and f in 𝒮(V), θ(v ⊗ f) = ∫ v(y) f̃(y) dy, with f̃(x) = θ(ϱ(x)f), y
over real vectors in Fock coordinates with the measure `realMeasure`. -/
lemma theta_integrated : V.θ (V.integrated v f) = ∫ y, v y * f (realVec y) ∂realMeasure
  _ := by simp [integrated, Heisenberg.Rep.map_integrated_eq_integral]
