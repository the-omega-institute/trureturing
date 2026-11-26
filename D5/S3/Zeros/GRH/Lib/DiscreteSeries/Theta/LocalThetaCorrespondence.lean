/- GID: D5/S3/Zeros/GRH/Lib/DiscreteSeries/Theta/LocalThetaCorrespondence
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/DiscreteSeries/Theta/LocalThetaCorrespondence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.DiscreteSeries.Theta.LocalThetaCorrespondence. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/DiscreteSeries/Theta/LocalThetaCorrespondence.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Theta.HoweArgument
import D5.S3.Zeros.GRH.Lib.Weil.Fock.OscillatorPair
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Rigidity.KernelFixes
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Theta correspondence of discrete series for real unitary dual pairs, and joint
harmonics. Only matched parameters with large gaps are treated, on Fock space. The joint harmonic
exists and is unique up to scalar, its projection is fixed by the partner's projector, and the
projection of every polynomial vector is a compactly supported smoothing of it under the second
group. Source: J.-S. Li, Theta lifting for unitary representations with nonzero cohomology, Duke
Math. J. 61 (1990) 913-937; R. Howe, Transcending classical invariant theory, J. Amer. Math. Soc. 2
(1989); A. Paul, Howe correspondence for real unitary groups, J. Funct. Anal. 159 (1998).

This file: Local theta correspondence: positivity, fixed by partner projector, generation by the
joint harmonic. -/

namespace OscillatorPair

variable {R C I} [Fintype R] [Fintype C] [Fintype I] {η} {ε ε' l l' Φ} {T :
  @FockDualPair R C ε ε' I} {π π'}
  (hp : OscillatorPair (η := η) T π π') [Nonempty R] (hΦ : IsJointHarmonic T l l' Φ)
open Finset MeasureTheory Fintype GlModule Matrix.Norms.L2Operator
include hp

omit [Nonempty R] in
/-- If π, π' is an oscillator pair for T, then π', π is one for the data `FockDualPair.swap` T: rows
and columns exchanged, sign −σ, integers γ', γ. -/
lemma swap : OscillatorPair T.swap π' π := by grind [OscillatorPair, T.swap_swap]

include hΦ

/-- For an oscillator pair π, π' on Fock space and a joint harmonic Φ of parameters λ, λ', the
real part of ⟨Φ, π(e_λ)Φ⟩ is positive. -/
lemma re_inner_integratedRep_pos : 0 < (realInner Φ (integratedRep π l.dsKernel Φ)).re :=
  re_integratedRep_dsKernel_pos hΦ.hasLargeGap hp.unitary_rep hp.derives hΦ.2.2.2.2.1
  (hp.inner_pos Φ · hΦ.2.1 hΦ.2.2.2.1)

lemma isDerivedAction_integratedRep :
  IsDerivedAction π' ((integratedRep π l.dsKernel).1 ∘ₗ polyVector η) T.swap.oscRows :=
  let m := map_integratedRep hp.unitary_rep hΦ.hasLargeGap.integrable_norm_pow_smul_dsKernel; fun _
    _ ↦ funext (fun _ ↦ (m ..).trans
  ((m 1 _).trans congr(∫ _, _ • $(hp.3 ..) _)).symm) ▸ (hp.column_rep.derives ..).map_clm _

variable [Nonempty C]

attribute [-simp] nsmul_eq_mul zsmul_eq_mul ite_smul in
attribute [local simp] E smul_smul glOp DFunLike.ite_apply in
/-- Let π, π′ be an oscillator pair of ranks n, n′ ≥ 1, Φ a joint harmonic for matching λ, λ′.
If ‖g‖^{nn′}f(g) is integrable on U(diag ε′) and ∫ f(y)e_{λ′}(y⁻¹g) dy = e_{λ′}(g) for all
g, then π′(f) fixes π(e_λ)Φ. -/
lemma integratedRep_fix {f : _ → ℂ} (hf : Integrable fun g ↦ f g * ‖g.1.1‖ ^ card I) (hr : ∀ g, ∫ y,
    f y * l'.dsKernel (y⁻¹ * g) =
  l'.dsKernel g) : letI v := integratedRep π l.dsKernel Φ; integratedRep π' f v = v := by
  obtain ⟨q, Q, -, u, -, w, -⟩ := hp.swap, hΦ.swap, hΦ.2
  have := sum_congr _ _ w.1
  apply fun κ k ↦ integratedRep_fix_of_isKHighest Q.hasLargeGap q.unitary_rep
    (hp.isDerivedAction_integratedRep hΦ) hf u ((congrArg _ (eq_sub_of_add_eq' (c := κ • Φ)
    k)).trans (by simp [integratedRep_dsKernel_casimir hΦ.hasLargeGap hp.unitary_rep hp.derives,
    sub_smul])) (le_sub_left_of_add_le (a := κ) ((le_total ..).elim id (eq_casimirValue_of_ge
    hΦ.hasLargeGap hp.unitary_rep (T.swap_swap ▸ q.isDerivedAction_integratedRep Q) w
    (.trans (congrArg _ k.symm) (by simp [integratedRep_dsKernel_casimir Q.hasLargeGap q.unitary_rep
    q.derives, add_smul])) · ((q.re_inner_integratedRep_pos Q).ne ∘ by aesop) |>.le))) hr
  simp [↓casimir.eq_1, oscRows, ↓swap_oscRows_E, @eq_comm ℤˣ, apply_ite (raiseOp ..),
    apply_ite (lowerOp ..), ← smul_sum, ← Int.cast_mul, (canonical_commutation ..).2.2]
  rw [@sum_comm C _ C]
  simp_all [oscRows, ← smul_sum, ← sum_smul, ← eq_sub_iff_add_eq, @sum_comm R _ C,
    -LinearMap.coe_add, (canonical_commutation ..).2.1]
  match_scalars <;> simp; norm_cast

/-- For an oscillator pair π, π' on Fock space, a joint harmonic Φ of parameters λ, λ' and any
polynomial P, there is a compactly supported smooth α on the second group with π(e_λ)P =
π'(α)π(e_λ)Φ. -/
lemma exists_bump_integratedRep_eq P : ∃ α : Bumps ε', integratedRep π l.dsKernel (polyVector η P) =
  integratedRep π' (α.1.1 ·⁻¹) (integratedRep π l.dsKernel Φ) := by
  obtain ⟨d, v, ⟨⟩, ⟨⟩⟩ := hp.isDerivedAction_integratedRep hΦ, hp.column_rep.unitary_rep,
    exists_integration_by_parts hΦ.hasLargeGap hp.unitary_rep hp.derives,
    isKHighest_dsGenerator hΦ.gap.neg, hΦ.gap
  set ι := (integratedRep π _).1 ∘ₗ polyVector η
  let G := .proj 1 ∘ₗ smear _ (v.1 (ι Φ))
  have a α : _ = G α :=
    (map_integratedRep v (integrable_bump_inv_smul _ α) 1 (ι Φ)).trans (by aesop)
  refine ((hΦ.howe_argument (G.range.comap ι) (fun Y y ⟨β, e⟩ ↦
    ⟨bumpDeriv Y β, eq_unitaryLiePart_add_I_smul ε' Y ▸ by simp [G, map_add, fun Y ↦
    (d Y y).unique (by simpa [map_integratedRep v (integrable_bump_inv_smul ..) (π' _), ← e,
    ← a] using (hasDerivAt_smear _ β (v.1 _) (hasDerivAt_expU Y 1 0)))]⟩) ((hΦ.swap.hasLargeGap
    le_rfl).exists_bump_conv_dsKernel.imp (a · ▸ hp.integratedRep_fix hΦ
    (integrable_bump_inv_smul ..) ·)) (fun Q Y h k ↦ eq_unitaryLiePart_add_I_smul ε Y ▸
    by simp [ι, integratedRep_eq_zero_of_notMem_rootCone hΦ.hasLargeGap hp.unitary_rep hp.derives h
    k, ← ((hp.derives ..).map_clm _).deriv]) ?_
    ?_).ge (x := P) ⟨⟩).imp (a · ▸ symm) <;> simp +contextual [ι, *]
