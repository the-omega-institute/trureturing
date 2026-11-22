/- GID: D5/S3/Quantum/Divergence/ForwardHockeyStickIntegral
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/ForwardHockeyStickIntegral
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Forward hockey-stick integrals and the bounded-Loewner trace-log difference. -/

import D5.S3.Quantum.Divergence.UmegakiPencilIntegral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Forward hockey-stick integrals

The same fractional linear involution transforms both tails of Frenkel's pencil.
Under common two-sided Loewner bounds, equal respective trace masses let the two
forward profiles be subtracted and integrated over the bounded comparison interval.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix MeasureTheory RHLinalg Set
open scoped ComplexOrder ENNReal MatrixOrder Matrix.Norms.L2Operator Topology
open D5.S3.Quantum.Divergence.HockeyStickPencilIntegral
open D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy
open D5.S3.Quantum.Divergence.UmegakiPencilIntegral

namespace D5.S3.Quantum.Divergence.ForwardHockeyStickIntegral

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace of the positive part of `A - s • B`. -/
def forwardProfile {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (s : ℝ) : ℝ :=
  rtrace (hermPosPart (hA.sub (hB.smul (IsSelfAdjoint.all s))))

private theorem hermPosPart_eq_cfc {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    hermPosPart hX = X⁺ := by
  rw [CFC.posPart_def, cfcₙ_eq_cfc (hf0 := by simp), hX.cfc_eq]
  rfl

private theorem hermNegPart_eq_cfc {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    hermNegPart hX = X⁻ := by
  rw [CFC.negPart_def, cfcₙ_eq_cfc (hf0 := by simp), hX.cfc_eq]
  rfl

omit [DecidableEq n] in
private theorem rtrace_real_smul (c : ℝ) (X : Matrix n n ℂ) :
    rtrace (c • X) = c * rtrace X := by
  simp [rtrace, Matrix.trace_smul, Complex.real_smul]

private theorem continuous_forwardProfile {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : Continuous (forwardProfile hA hB) := by
  let X (s : ℝ) := A - s • B
  have hX (s : ℝ) : (X s).IsHermitian := hA.sub (hB.smul (IsSelfAdjoint.all s))
  have hc : Continuous X := by unfold X; fun_prop
  have hpart : Continuous (fun s => cfc (·⁺ : ℝ → ℝ) (X s)) :=
    Continuous.cfc_of_mem_nhdsSet _ (s := univ) Filter.univ_mem hc hX
      continuous_posPart.continuousOn
  have heq (s : ℝ) : forwardProfile hA hB s = (cfc (·⁺ : ℝ → ℝ) (X s)).trace.re := by
    rw [forwardProfile, hermPosPart_eq_cfc, CFC.posPart_def, cfcₙ_eq_cfc (hf0 := by simp)]
    rfl
  rw [show forwardProfile hA hB = _ from funext heq]
  exact Complex.continuous_re.comp hpart.matrix_trace

private def mobius (s : ℝ) : ℝ := s / (s - 1)

private theorem mobius_sub_one {s : ℝ} (hs : s ≠ 1) : mobius s - 1 = (s - 1)⁻¹ := by
  unfold mobius
  field_simp [sub_ne_zero.mpr hs]
  ring

private theorem mobius_involutive {s : ℝ} (hs : s ≠ 1) : mobius (mobius s) = s := by
  nth_rw 1 [mobius]
  rw [mobius_sub_one hs, div_inv_eq_mul, mobius, div_mul_cancel₀ _ (sub_ne_zero.mpr hs)]

private theorem mobius_maps_left : MapsTo mobius (Ioo 0 1) (Iio 0) :=
  fun _ hs => div_neg_of_pos_of_neg hs.1 (sub_neg.mpr hs.2)

private theorem mobius_maps_right : MapsTo mobius (Ioi 1) (Ioi 1) := by
  intro s hs
  have hs' : 1 < s := hs
  exact sub_pos.mp (by rw [mobius_sub_one hs'.ne']; exact inv_pos.mpr (sub_pos.mpr hs'))

private theorem mobius_image_left : mobius '' Ioo 0 1 = Iio 0 := by
  refine Subset.antisymm mobius_maps_left.image_subset ?_
  intro t ht
  have ht' : t < 0 := ht
  have ht1 : t < 1 := ht'.trans zero_lt_one
  refine ⟨mobius t, ⟨div_pos_of_neg_of_neg ht' (sub_neg.mpr ht1), ?_⟩, mobius_involutive ht1.ne⟩
  exact sub_neg.mp (by rw [mobius_sub_one ht1.ne]; exact inv_lt_zero'.mpr (sub_neg.mpr ht1))

private theorem mobius_image_right : mobius '' Ioi 1 = Ioi 1 := by
  refine Subset.antisymm mobius_maps_right.image_subset ?_
  intro t ht
  exact ⟨mobius t, mobius_maps_right ht, mobius_involutive (show 1 < t from ht).ne'⟩

private theorem mobius_change {S : Set ℝ} (hS : MeasurableSet S)
    (h1 : ∀ s ∈ S, s ≠ 1) (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in mobius '' S, f t) =
      ∫⁻ s in S, ENNReal.ofReal ((s - 1)⁻¹ ^ 2) * f (mobius s) := by
  have hd (s : ℝ) (hs : s ∈ S) : HasDerivWithinAt mobius (-((s - 1)⁻¹ ^ 2)) S s := by
    have h := (hasDerivAt_id s).div ((hasDerivAt_id s).sub_const 1) (sub_ne_zero.mpr (h1 s hs))
    have he : (1 * (s - 1) - s * 1) / (s - 1) ^ 2 = -((s - 1)⁻¹ ^ 2) := by
      rw [inv_pow]
      ring
    change HasDerivAt mobius ((1 * (s - 1) - s * 1) / (s - 1) ^ 2) s at h
    rw [he] at h
    exact h.hasDerivWithinAt
  have hi : InjOn mobius S := by
    intro s hs t ht h
    simpa only [mobius_involutive (h1 s hs), mobius_involutive (h1 t ht)] using congrArg mobius h
  simpa only [abs_neg, abs_of_nonneg (sq_nonneg (_ : ℝ))] using
    lintegral_image_eq_lintegral_abs_deriv_mul hS hd hi f

private theorem mobius_weight {s : ℝ} (hs : 0 < s) (h1 : s ≠ 1) :
    (s - 1)⁻¹ ^ 2 * (pencilWeight (mobius s) * |1 - mobius s|) = 1 / s := by
  have hm := mobius_sub_one h1
  have hd : |s - 1| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr h1)
  have he : |1 - mobius s| = |s - 1|⁻¹ := by rw [abs_sub_comm, hm, abs_inv]
  rw [pencilWeight, he, hm, mobius, abs_div, abs_of_pos hs, inv_pow]
  field_simp [hs.ne', hd]

private theorem negPart_pencil_mobius {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {s : ℝ} (hs : s ≠ 1) :
    let t := mobius s
    rtrace (hermNegPart (hA.add ((hB.sub hA).smul (IsSelfAdjoint.all t)))) =
      |1 - t| * (if s < 1 then forwardProfile hA hB s - rtrace (A - s • B)
        else forwardProfile hA hB s) := by
  dsimp only
  have hscalar : (1 - mobius s) * s = -mobius s := by
    unfold mobius
    field_simp [sub_ne_zero.mpr hs]
    ring
  have hpencil : A + mobius s • (B - A) = (1 - mobius s) • (A - s • B) := by
    rw [smul_sub, smul_sub, smul_smul, hscalar, neg_smul, sub_smul, one_smul]
    abel
  rw [hermNegPart_eq_cfc, hpencil]
  by_cases h : s < 1
  · have ht : 0 ≤ 1 - mobius s := by
      rw [sub_nonneg, ← sub_nonpos, mobius_sub_one hs]
      exact (inv_lt_zero'.mpr (sub_neg.mpr h)).le
    rw [ite_eq_left h, abs_of_nonneg ht, CFC.negPart_smul_of_nonneg ht, rtrace_real_smul]
    congr 1
    let hX := hA.sub (hB.smul (IsSelfAdjoint.all s))
    have hd := rtrace_sub_decomp hX
    rw [hermNegPart_eq_cfc hX] at hd
    unfold forwardProfile
    linarith
  · have ht : 1 - mobius s ≤ 0 := by
      rw [sub_nonpos, ← sub_nonneg, mobius_sub_one hs]
      exact (inv_pos.mpr (sub_pos.mpr (lt_of_le_of_ne (le_of_not_gt h) hs.symm))).le
    rw [ite_eq_right h, abs_of_nonpos ht, CFC.negPart_smul_of_nonpos ht, rtrace_real_smul,
      forwardProfile, hermPosPart_eq_cfc]

private theorem correctedTrace_nonneg {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosDef) :
    0 ≤ (A * (CFC.log A - cfc Real.log B)).trace.re - rtrace (A - B) := by
  let M := ‖A‖ + ‖B‖ + 1
  have hM : 0 < M := by unfold M; positivity
  have ceiling (X : Matrix n n ℂ) (hX : X.PosSemidef) (hx : ‖X‖ ≤ M) :
      X ≤ (M : ℂ) • 1 := by
    have he : algebraMap ℝ (Matrix n n ℂ) M = (M : ℂ) • 1 := by
      simp [Algebra.algebraMap_eq_smul_one]
    rw [← he]
    exact (CStarAlgebra.norm_le_iff_le_algebraMap X hM.le hX.nonneg).mp hx
  have hab := actual_matrix_spectral_ceiling_strong_klein A B hA hB.posSemidef M hM
    (ceiling A hA (by dsimp [M]; linarith [norm_nonneg B]))
    (ceiling B hB.posSemidef (by dsimp [M]; linarith [norm_nonneg A])) (fun v hv => by
      have hv' : v = 0 := hB.mulVec_injective (by simpa using hv)
      simp [hv'])
  have hn : 0 ≤ ((A - B)ᴴ * (A - B)).trace.re / (2 * M) :=
    div_nonneg (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg).1
      (by positivity)
  change 0 ≤ (A * (cfc Real.log A - cfc Real.log B)).trace.re - (A - B).trace.re
  rw [Matrix.trace_sub, Complex.sub_re]
  linarith only [hn.trans hab]

/-- The finite trace-log pairing equals two real forward-profile integrals and the
trace correction. Both real integrands are integrable on their respective tails. -/
theorem integral_forwardProfile_eq_umegaki {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosDef) :
    let E := forwardProfile hA.isHermitian hB.isHermitian
    IntegrableOn (fun s => (E s - rtrace (A - s • B)) / s) (Ioo 0 1) ∧
    IntegrableOn (fun s => E s / s) (Ioi 1) ∧
    (A * (CFC.log A - cfc Real.log B)).trace.re =
      (∫ s in Ioo (0 : ℝ) 1, (E s - rtrace (A - s • B)) / s) +
      (∫ s in Ioi (1 : ℝ), E s / s) + rtrace (A - B) := by
  dsimp only
  let ha := hA.isHermitian
  let hb := hB.isHermitian
  let E := forwardProfile ha hb
  let L (s : ℝ) := (E s - rtrace (A - s • B)) / s
  let R (s : ℝ) := E s / s
  let X (t : ℝ) := ha.add ((hb.sub ha).smul (IsSelfAdjoint.all t))
  let f (t : ℝ) := ENNReal.ofReal (pencilWeight t * rtrace (hermNegPart (X t)))
  let D := (A * (CFC.log A - cfc Real.log B)).trace.re
  let c := rtrace (A - B)
  have hp (s : ℝ) : 0 ≤ E s := by
    change 0 ≤ forwardProfile ha hb s
    rw [forwardProfile, rtrace_hermPosPart]
    exact Finset.sum_nonneg fun i _ => posPart_nonneg _
  have hn (s : ℝ) : 0 ≤ E s - rtrace (A - s • B) := by
    let h := ha.sub (hb.smul (IsSelfAdjoint.all s))
    change 0 ≤ rtrace (hermPosPart h) - rtrace (A - s • B)
    rw [rtrace_sub_decomp h, sub_sub_cancel, rtrace_hermNegPart]
    exact Finset.sum_nonneg fun i _ => negPart_nonneg _
  have hmul (s : ℝ) (hs : 0 < s) (h1 : s ≠ 1) :
      ENNReal.ofReal ((s - 1)⁻¹ ^ 2) * f (mobius s) =
        ENNReal.ofReal ((if s < 1 then E s - rtrace (A - s • B) else E s) / s) := by
    unfold f X
    rw [negPart_pencil_mobius ha hb h1, ← ENNReal.ofReal_mul (sq_nonneg _),
      ← mul_assoc (pencilWeight (mobius s)), ← mul_assoc, mobius_weight hs h1,
      one_div, mul_comm, ← div_eq_mul_inv]
  have hleft : (∫⁻ t in Iio (0 : ℝ), f t) = ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (L s) := by
    rw [← mobius_image_left, mobius_change measurableSet_Ioo (fun s hs => hs.2.ne)]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [hmul s hs.1 hs.2.ne, ite_eq_left hs.2]
  have hright : (∫⁻ t in Ioi (1 : ℝ), f t) = ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (R s) := by
    have hchange := mobius_change (S := Ioi 1) measurableSet_Ioi
      (fun s hs => (show 1 < s from hs).ne') f
    rw [mobius_image_right] at hchange
    rw [hchange]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : 1 < s := hs
    rw [hmul s (zero_lt_one.trans hs') hs'.ne', ite_eq_right hs'.asymm]
  have hcenter : (∫⁻ t in Icc (0 : ℝ) 1, f t) = 0 := by
    refine Eq.trans ?_ (lintegral_zero (μ := volume.restrict (Icc (0 : ℝ) 1)))
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hmat : (A + t • (B - A)).PosSemidef := by
      have he : A + t • (B - A) = (1 - t) • A + t • B := by
        rw [smul_sub, sub_smul, one_smul]
        abel
      rw [he]
      exact (hA.smul (sub_nonneg.mpr ht.2)).add (hB.posSemidef.smul ht.1)
    unfold f
    rw [hermNegPart_eq_cfc, (CFC.negPart_eq_zero_iff _ (X t)).mpr hmat.nonneg]
    simp [rtrace]
  have hcover : (Iio (0 : ℝ) ∪ Icc 0 1) ∪ Ioi 1 = univ := by
    ext t
    simp only [mem_union, mem_Iio, mem_Icc, mem_Ioi, mem_univ, iff_true]
    by_cases h : t < 0
    · exact Or.inl (Or.inl h)
    · exact (le_or_gt t 1).imp (fun ht => Or.inr ⟨le_of_not_gt h, ht⟩) id
  have hsum : (∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (L s)) +
      (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (R s)) = ENNReal.ofReal (D - c) := by
    rw [← hleft, ← hright]
    have hdis₀ : Disjoint (Iio (0 : ℝ)) (Icc 0 1) :=
      disjoint_left.mpr fun _ hx hy => (not_lt_of_ge hy.1) hx
    have hdis₁ : Disjoint (Iio (0 : ℝ) ∪ Icc 0 1) (Ioi 1) := by
      refine disjoint_left.mpr fun x hx hy => ?_
      exact (not_lt_of_ge (hx.elim (fun h => (h.trans zero_lt_one).le) And.right)) hy
    rw [← add_zero (∫⁻ t in Iio (0 : ℝ), f t), ← hcenter,
      ← lintegral_union measurableSet_Icc hdis₀, ← lintegral_union measurableSet_Ioi hdis₁,
      hcover, Measure.restrict_univ]
    exact lintegral_weighted_negPart_pencil_eq_umegaki hA hB
  have hfinite : (∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (L s)) +
      (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (R s)) ≠ ⊤ := by
    rw [hsum]
    exact ENNReal.ofReal_ne_top
  have hfiniteL : (∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (L s)) ≠ ⊤ := by
    intro h
    exact hfinite (by simp [h])
  have hfiniteR : (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (R s)) ≠ ⊤ := by
    intro h
    exact hfinite (by simp [h])
  have hE : Continuous E := continuous_forwardProfile ha hb
  have htrace : Continuous (fun s : ℝ => rtrace (A - s • B)) := by
    simp only [rtrace_sub, rtrace_real_smul]
    fun_prop
  have hLm : Measurable L := hE.measurable.sub htrace.measurable |>.div measurable_id
  have hRm : Measurable R := hE.measurable.div measurable_id
  have hLn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] L := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact div_nonneg (hn s) hs.1.le
  have hRn : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] R := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact div_nonneg (hp s) (zero_lt_one.trans (show 1 < s from hs)).le
  have hLi : IntegrableOn L (Ioo 0 1) :=
    (integrable_toReal_of_lintegral_ne_top hLm.ennreal_ofReal.aemeasurable hfiniteL).congr
      (hLn.mono fun _ hx => ENNReal.toReal_ofReal hx)
  have hRi : IntegrableOn R (Ioi 1) :=
    (integrable_toReal_of_lintegral_ne_top hRm.ennreal_ofReal.aemeasurable hfiniteR).congr
      (hRn.mono fun _ hx => ENNReal.toReal_ofReal hx)
  rw [← ofReal_integral_eq_lintegral_ofReal hLi hLn,
    ← ofReal_integral_eq_lintegral_ofReal hRi hRn,
    ← ENNReal.ofReal_add (integral_nonneg_of_ae hLn) (integral_nonneg_of_ae hRn)] at hsum
  have he := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_ofReal (add_nonneg (integral_nonneg_of_ae hLn) (integral_nonneg_of_ae hRn)),
    ENNReal.toReal_ofReal (correctedTrace_nonneg hA hB)] at he
  refine ⟨hLi, hRi, ?_⟩
  change D = (∫ s in Ioo (0 : ℝ) 1, L s) + (∫ s in Ioi (1 : ℝ), R s) + c
  linarith

#print axioms integral_forwardProfile_eq_umegaki

private theorem forwardProfile_eq_trace_of_le {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.PosSemidef) {s u : ℝ} (hs : s ≤ u) (hu : u • B ≤ A) :
    forwardProfile hA hB.isHermitian s = rtrace A - s * rtrace B := by
  have hps := (Matrix.le_iff.mp hu).add (hB.smul (sub_nonneg.mpr hs))
  have he : (A - u • B) + (u - s) • B = A - s • B := by rw [sub_smul]; abel
  rw [he] at hps
  rw [forwardProfile, hermPosPart_eq_cfc, (CFC.posPart_eq_self _).mpr hps.nonneg,
    rtrace_sub, rtrace_real_smul]

private theorem forwardProfile_eq_zero_of_ge {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.PosSemidef) {s v : ℝ} (hs : v ≤ s) (hv : A ≤ v • B) :
    forwardProfile hA hB.isHermitian s = 0 := by
  have hps := (Matrix.le_iff.mp hv).add (hB.smul (sub_nonneg.mpr hs))
  have he : (v • B - A) + (s - v) • B = s • B - A := by rw [sub_smul]; abel
  rw [he] at hps
  have hn : A - s • B ≤ 0 := by
    rw [← neg_nonneg, neg_sub]
    exact hps.nonneg
  let hX := hA.sub (hB.isHermitian.smul (IsSelfAdjoint.all s))
  rw [forwardProfile, hermPosPart_eq_cfc, ← CFC.negPart_neg,
    (CFC.negPart_eq_zero_iff _ hX.neg).mpr (neg_nonneg.mpr hn)]
  simp [rtrace]

variable {k : Type*} [Fintype k] [DecidableEq k]

/-- For two finite pairs with positive definite references, matching trace masses
and common Loewner bounds localize the signed profile difference to `[u,v]`. -/
theorem integral_forwardProfile_sub_eq_umegaki_sub
    {A B : Matrix n n ℂ} {C D : Matrix k k ℂ}
    (hA : A.PosSemidef) (hB : B.PosDef) (hC : C.PosSemidef) (hD : D.PosDef)
    (hmA : rtrace A = rtrace C) (hmB : rtrace B = rtrace D)
    {u v : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (hloAB : u • B ≤ A) (hhiAB : A ≤ v • B) (hloCD : u • D ≤ C) (hhiCD : C ≤ v • D) :
    let E := forwardProfile hA.isHermitian hB.isHermitian
    let F := forwardProfile hC.isHermitian hD.isHermitian
    EqOn E F (Iic u) ∧ EqOn E F (Ici v) ∧
    IntegrableOn (fun s => (E s - F s) / s) (Icc u v) ∧
    (A * (CFC.log A - cfc Real.log B)).trace.re -
      (C * (CFC.log C - cfc Real.log D)).trace.re =
      ∫ s in u..v, (E s - F s) / s := by
  dsimp only
  let E := forwardProfile hA.isHermitian hB.isHermitian
  let F := forwardProfile hC.isHermitian hD.isHermitian
  let g (s : ℝ) := (E s - F s) / s
  have hlo : EqOn E F (Iic u) := by
    intro s hs
    change forwardProfile hA.isHermitian hB.isHermitian s =
      forwardProfile hC.isHermitian hD.isHermitian s
    rw [forwardProfile_eq_trace_of_le hA.isHermitian hB.posSemidef hs hloAB,
      forwardProfile_eq_trace_of_le hC.isHermitian hD.posSemidef hs hloCD, hmA, hmB]
  have hhi : EqOn E F (Ici v) := by
    intro s hs
    change forwardProfile hA.isHermitian hB.isHermitian s =
      forwardProfile hC.isHermitian hD.isHermitian s
    rw [forwardProfile_eq_zero_of_ge hA.isHermitian hB.posSemidef hs hhiAB,
      forwardProfile_eq_zero_of_ge hC.isHermitian hD.posSemidef hs hhiCD]
  obtain ⟨hEL, hER, hEq⟩ := integral_forwardProfile_eq_umegaki hA hB
  obtain ⟨hFL, hFR, hFq⟩ := integral_forwardProfile_eq_umegaki hC hD
  let lE (s : ℝ) := (E s - rtrace (A - s • B)) / s
  let lF (s : ℝ) := (F s - rtrace (C - s • D)) / s
  let rE (s : ℝ) := E s / s
  let rF (s : ℝ) := F s / s
  have left_eq : (fun s => lE s - lF s) = g := by
    funext s
    simp only [lE, lF, g, rtrace_sub, rtrace_real_smul, hmA, hmB, ← sub_div]
    congr 1
    ring
  have right_eq : (fun s => rE s - rF s) = g := by
    funext s
    exact (sub_div _ _ _).symm
  have hLi : IntegrableOn g (Ioo 0 1) := left_eq ▸ hEL.sub hFL
  have hRi : IntegrableOn g (Ioi 1) := right_eq ▸ hER.sub hFR
  have hL'i : IntegrableOn g (Ioc 0 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hLi
  have hi : IntegrableOn g (Ioi 0) :=
    Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num) ▸ hL'i.union hRi
  have hsub : Icc u v ⊆ Ioi 0 := fun _ hx => hu.trans_le hx.1
  have hz : ∀ s ∈ Ioi (0 : ℝ) \ Icc u v, g s = 0 := by
    intro s hs
    rcases le_or_gt s u with hlu | hlu
    · simp [g, hlo hlu]
    · have huv' : v ≤ s := le_of_not_ge fun hsv => hs.2 ⟨hlu.le, hsv⟩
      simp [g, hhi huv']
  have hrestrict : (∫ s in Ioi (0 : ℝ), g s) = ∫ s in Icc u v, g s := by
    rw [← union_sdiff_cancel hsub]
    exact integral_union_eq_left_of_forall (measurableSet_Ioi.diff measurableSet_Icc) hz
  refine ⟨hlo, hhi, hi.mono_set hsub, ?_⟩
  change _ = ∫ s in u..v, g s
  rw [intervalIntegral.integral_of_le huv, ← integral_Icc_eq_integral_Ioc, ← hrestrict,
    ← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hL'i hRi,
    integral_Ioc_eq_integral_Ioo]
  nth_rw 1 [← left_eq]
  rw [integral_sub hEL hFL]
  rw [← right_eq, integral_sub hER hFR]
  rw [hEq, hFq, rtrace_sub A B, rtrace_sub C D, hmA, hmB]
  ring

#print axioms integral_forwardProfile_sub_eq_umegaki_sub

end D5.S3.Quantum.Divergence.ForwardHockeyStickIntegral
