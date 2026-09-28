/- GID: D5/S3/Quantum/Dynamics/CompressedResolventRemainder
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/CompressedResolventRemainder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compression has a positive cubic resolvent remainder bounded by leakage. -/

import Mathlib.Algebra.Ring.Invertible
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic.Abel
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Dynamics.CompressedResolventRemainder

open ContinuousLinearMap
open RCLike
open scoped InnerProductSpace

universe u

set_option linter.unusedVariables false in
set_option linter.flexible false in
set_option linter.constructorNameAsVariable false in
set_option linter.style.haveILetI false in
/-- The compression of a positive resolvent differs from the compressed resolvent by a positive
second-order excursion through the hidden subspace, with a cubic spectral-gap bound. -/
theorem compressed_resolvent_remainder
    {𝕜 R E : Type u} [RCLike 𝕜]
    [NormedAddCommGroup R] [InnerProductSpace 𝕜 R] [FiniteDimensional 𝕜 R]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (F : R →L[𝕜] E) (S : R →L[𝕜] R) (a u : ℝ) :
    letI : CompleteSpace R := FiniteDimensional.complete 𝕜 R
    letI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
    F.comp F.adjoint = 1 → IsSelfAdjoint S → 0 < a →
    (a : 𝕜) • (1 : R →L[𝕜] R) ≤ S → 0 ≤ u →
    let P : R →L[𝕜] R := F.adjoint.comp F
    let Q : R →L[𝕜] R := 1 - P
    let A : E →L[𝕜] E := F.comp (S.comp F.adjoint)
    let δ : ℝ := ‖F.comp (S.comp (Q.comp (S.comp F.adjoint)))‖
    let S₀ : R →L[𝕜] R := P.comp (S.comp P) + Q.comp (S.comp Q)
    let V : R →L[𝕜] R := S - S₀
    let R_u : R →L[𝕜] R := Ring.inverse (S + (u : 𝕜) • (1 : R →L[𝕜] R))
    let R_u₀ : R →L[𝕜] R := Ring.inverse (S₀ + (u : 𝕜) • (1 : R →L[𝕜] R))
    let A_u_inv : E →L[𝕜] E := Ring.inverse (A + (u : 𝕜) • (1 : E →L[𝕜] E))
    let D_u : E →L[𝕜] E := F.comp (R_u.comp F.adjoint) - A_u_inv
    R_u - R_u₀ = -(R_u₀.comp (V.comp R_u₀)) +
        R_u₀.comp (V.comp (R_u.comp (V.comp R_u₀))) ∧
      D_u =
        A_u_inv.comp (F.comp (S.comp (Q.comp (R_u.comp
          (Q.comp (S.comp (F.adjoint.comp A_u_inv))))))) ∧
      0 ≤ D_u ∧ ‖D_u‖ ≤ δ / (a + u) ^ 3 := by
  let _ : CompleteSpace R := FiniteDimensional.complete 𝕜 R
  let _ : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  intros hF _hS ha hSa hu P Q A δ S₀ V R_u R_u₀ A_u_inv D_u
  let G : E →L[𝕜] R := F.adjoint
  change R_u - R_u₀ = -(R_u₀.comp (V.comp R_u₀)) +
        R_u₀.comp (V.comp (R_u.comp (V.comp R_u₀))) ∧
      D_u =
        A_u_inv.comp (F.comp (S.comp (Q.comp (R_u.comp
          (Q.comp (S.comp (G.comp A_u_inv))))))) ∧
      0 ≤ D_u ∧ ‖D_u‖ ≤ δ / (a + u) ^ 3
  change F.comp G = 1 at hF
  let T : R →L[𝕜] R := S + (u : 𝕜) • 1
  let T₀ : R →L[𝕜] R := S₀ + (u : 𝕜) • 1
  let A_u : E →L[𝕜] E := A + (u : 𝕜) • 1
  have hSdiff : (S - (a : 𝕜) • (1 : R →L[𝕜] R)).IsPositive := hSa
  have hSadj : S.adjoint = S := by
    have hscalar : ((a : 𝕜) • (1 : R →L[𝕜] R)).IsPositive :=
      ContinuousLinearMap.IsPositive.smul_of_nonneg isPositive_one
        (RCLike.ofReal_nonneg.mpr ha.le)
    exact (show S.IsPositive by
      simpa only [sub_add_cancel] using hSdiff.add hscalar).isSelfAdjoint.adjoint_eq
  have hPadj : P.adjoint = P := by
    simp only [P, adjoint_comp, adjoint_adjoint]
  have hPcomp : P.comp P = P := by
    dsimp only [P]
    rw [comp_assoc, ← comp_assoc F G F, hF, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_comp]
  have hPstar : IsStarProjection P := by
    refine ⟨?_, hPadj⟩
    change P * P = P
    rw [ContinuousLinearMap.mul_def]
    exact hPcomp
  have hQstar : IsStarProjection Q := by
    simpa only [Q] using hPstar.one_sub
  have hQadj : Q.adjoint = Q := hQstar.isSelfAdjoint
  have hQcomp : Q.comp Q = Q := by
    rw [← ContinuousLinearMap.mul_def]
    exact hQstar.isIdempotentElem
  let B : R →L[𝕜] E := F.comp (S.comp Q)
  have hBadj : B.adjoint = Q.comp (S.comp G) := by
    simp only [B, adjoint_comp, G, hSadj, hQadj, comp_assoc]
  have hBadjNorm : ‖B.adjoint‖ = ‖B‖ := by
    exact ContinuousLinearMap.adjoint.norm_map B
  have hleakSq : ‖B‖ * ‖B‖ = δ := by
    have hBgram : B.adjoint.adjoint.comp B.adjoint =
        F.comp (S.comp (Q.comp (S.comp G))) := by
      rw [adjoint_adjoint, hBadj]
      dsimp only [B]
      simp only [comp_assoc]
      rw [← comp_assoc Q Q (S.comp G), hQcomp]
    calc
      ‖B‖ * ‖B‖ = ‖B.adjoint‖ * ‖B.adjoint‖ :=
        congrArg₂ (· * ·) hBadjNorm.symm hBadjNorm.symm
      _ = ‖B.adjoint.adjoint.comp B.adjoint‖ :=
        (norm_adjoint_comp_self B.adjoint).symm
      _ = ‖F.comp (S.comp (Q.comp (S.comp G)))‖ := congrArg norm hBgram
      _ = δ := rfl
  have hFP : F.comp P = F := by
    change F.comp (G.comp F) = F
    rw [← comp_assoc, hF, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_comp]
  have hPG : P.comp G = G := by
    change (G.comp F).comp G = G
    rw [comp_assoc, hF, ContinuousLinearMap.one_def,
      ContinuousLinearMap.comp_id]
  have hQG : Q.comp G = 0 := by
    change (1 - P).comp G = 0
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_comp, hPG, sub_self]
  have inverse_data_of_lower {H : Type u} [NormedAddCommGroup H]
      [InnerProductSpace 𝕜 H] [CompleteSpace H]
      (B : H →L[𝕜] H) (c : ℝ) (hc : 0 < c)
      (hcb : (c : 𝕜) • (1 : H →L[𝕜] H) ≤ B) :
      B.IsPositive ∧ IsUnit B ∧ ‖Ring.inverse B‖ ≤ c⁻¹ := by as_aux_lemma =>
    have hdiff : (B - (c : 𝕜) • (1 : H →L[𝕜] H)).IsPositive := hcb
    have hscalar : ((c : 𝕜) • (1 : H →L[𝕜] H)).IsPositive := by
      apply ContinuousLinearMap.IsPositive.smul_of_nonneg isPositive_one
      exact RCLike.ofReal_nonneg.mpr hc.le
    have hpos : B.IsPositive := by
      simpa only [sub_add_cancel] using hdiff.add hscalar
    have hinner : ∀ x : H, ‖x‖ ^ 2 * c ≤ ‖⟪B x, x⟫_𝕜‖ := by
      intro x
      calc
        ‖x‖ ^ 2 * c = re ⟪((c : 𝕜) • (1 : H →L[𝕜] H)) x, x⟫_𝕜 := by
          simp only [smul_apply, one_apply_eq_self, inner_smul_real_left,
            RCLike.smul_re, mul_comm]
          rw [norm_sq_eq_re_inner (𝕜 := 𝕜) x]
        _ ≤ re ⟪B x, x⟫_𝕜 := by
          have hx := hdiff.re_inner_nonneg_left x
          simpa only [sub_apply, inner_sub_left, map_sub, sub_nonneg] using hx
        _ ≤ ‖⟪B x, x⟫_𝕜‖ := RCLike.re_le_norm _
    have hunit : IsUnit B :=
      isUnit_of_forall_le_norm_inner_map B (c := ⟨c, hc.le⟩)
        (NNReal.coe_pos.mp hc) hinner
    have hanti : AntilipschitzWith (⟨c, hc.le⟩⁻¹) B :=
      antilipschitz_of_forall_le_inner_map B hc hinner
    have hcancel (x : H) : B (Ring.inverse B x) = x := by
      have hBinv : B.comp (Ring.inverse B) = 1 := by
        simpa only [ContinuousLinearMap.mul_def] using Ring.mul_inverse_cancel B hunit
      change (B.comp (Ring.inverse B)) x = x
      rw [hBinv, one_apply_eq_self]
    refine ⟨hpos, hunit, ?_⟩
    apply opNorm_le_bound _ (inv_nonneg.mpr hc.le)
    intro x
    have hx := ContinuousLinearMap.bound_of_antilipschitz B hanti (Ring.inverse B x)
    rw [hcancel x] at hx
    exact hx
  have hS₀diff : (S₀ - (a : 𝕜) • (1 : R →L[𝕜] R)).IsPositive := by
    have hPscalar : P.comp (((a : 𝕜) • (1 : R →L[𝕜] R)).comp P) =
        (a : 𝕜) • P := by
      rw [ContinuousLinearMap.one_def, ContinuousLinearMap.smul_comp,
        ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_smul]
      rw [hPcomp]
    have hQscalar : Q.comp (((a : 𝕜) • (1 : R →L[𝕜] R)).comp Q) =
        (a : 𝕜) • Q := by
      rw [ContinuousLinearMap.one_def, ContinuousLinearMap.smul_comp,
        ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_smul]
      rw [hQcomp]
    have hblock :
        P.comp ((S - (a : 𝕜) • (1 : R →L[𝕜] R)).comp P) +
            Q.comp ((S - (a : 𝕜) • (1 : R →L[𝕜] R)).comp Q) =
          S₀ - (a : 𝕜) • (1 : R →L[𝕜] R) := by
      simp only [S₀, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
        hPscalar, hQscalar]
      simp only [Q, smul_sub]
      abel
    rw [← hblock]
    simpa only [hPadj, hQadj] using
      (hSdiff.conj_adjoint P).add (hSdiff.conj_adjoint Q)
  have hAdiff : (A - (a : 𝕜) • (1 : E →L[𝕜] E)).IsPositive := by
    simpa only [A, G, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
      hF] using hSdiff.conj_adjoint F
  have hc : 0 < a + u := add_pos_of_pos_of_nonneg ha hu
  have hTlower : ((a + u : ℝ) : 𝕜) • (1 : R →L[𝕜] R) ≤ T := by
    change (T - ((a + u : ℝ) : 𝕜) • (1 : R →L[𝕜] R)).IsPositive
    simpa only [T, RCLike.ofReal_add, add_smul, add_sub_add_right_eq_sub] using hSdiff
  have hT₀lower : ((a + u : ℝ) : 𝕜) • (1 : R →L[𝕜] R) ≤ T₀ := by
    change (T₀ - ((a + u : ℝ) : 𝕜) • (1 : R →L[𝕜] R)).IsPositive
    simpa only [T₀, RCLike.ofReal_add, add_smul, add_sub_add_right_eq_sub] using hS₀diff
  have hAulower : ((a + u : ℝ) : 𝕜) • (1 : E →L[𝕜] E) ≤ A_u := by
    change (A_u - ((a + u : ℝ) : 𝕜) • (1 : E →L[𝕜] E)).IsPositive
    simpa only [A_u, RCLike.ofReal_add, add_smul, add_sub_add_right_eq_sub] using hAdiff
  obtain ⟨hTpos, hTunit, hRnorm⟩ := inverse_data_of_lower T (a + u) hc hTlower
  obtain ⟨hT₀pos, hT₀unit, _⟩ := inverse_data_of_lower T₀ (a + u) hc hT₀lower
  obtain ⟨hAupos, hAuunit, hAuinvnorm⟩ :=
    inverse_data_of_lower A_u (a + u) hc hAulower
  have hTR : T.comp R_u = 1 := by
    simpa only [ContinuousLinearMap.mul_def] using Ring.mul_inverse_cancel T hTunit
  have hT₀R : T₀.comp R_u₀ = 1 := by
    simpa only [ContinuousLinearMap.mul_def] using Ring.mul_inverse_cancel T₀ hT₀unit
  have hAuinvAu : A_u_inv.comp A_u = 1 := by
    simpa only [ContinuousLinearMap.mul_def] using Ring.inverse_mul_cancel A_u hAuunit
  have hRself : R_u.adjoint = R_u :=
    hTpos.isSelfAdjoint.ringInverse.adjoint_eq
  have hR₀self : R_u₀.adjoint = R_u₀ :=
    hT₀pos.isSelfAdjoint.ringInverse.adjoint_eq
  have hRpos : R_u.IsPositive := by
    simpa only [hRself, comp_assoc, hTR, ContinuousLinearMap.one_def,
      ContinuousLinearMap.comp_id] using hTpos.conj_adjoint R_u
  have hAuinvself : A_u_inv.adjoint = A_u_inv :=
    hAupos.isSelfAdjoint.ringInverse.adjoint_eq
  have hTsub : T - T₀ = V := by
    ext x
    simp only [T, T₀, V, add_apply, sub_apply, smul_apply, one_apply_eq_self]
    exact add_sub_add_right_eq_sub _ _ _
  have hleft : R_u - R_u₀ = -(R_u₀ * V * R_u) := by
    have h := Ring.inverse_sub_inverse
      (show IsUnit T₀ ↔ IsUnit T from ⟨fun _ => hTunit, fun _ => hT₀unit⟩)
    change R_u₀ - R_u = R_u₀ * (T - T₀) * R_u at h
    rw [hTsub] at h
    calc
      R_u - R_u₀ = -(R_u₀ - R_u) := (neg_sub R_u₀ R_u).symm
      _ = -(R_u₀ * V * R_u) := congrArg Neg.neg h
  have hright : R_u - R_u₀ = -(R_u * V * R_u₀) := by
    have h := Ring.inverse_sub_inverse
      (show IsUnit T ↔ IsUnit T₀ from ⟨fun _ => hT₀unit, fun _ => hTunit⟩)
    change R_u - R_u₀ = R_u * (T₀ - T) * R_u₀ at h
    calc
      R_u - R_u₀ = R_u * (T₀ - T) * R_u₀ := h
      _ = R_u * (-V) * R_u₀ := by
        rw [show T₀ - T = -V by
          calc
            T₀ - T = -(T - T₀) := (neg_sub T T₀).symm
            _ = -V := congrArg Neg.neg hTsub]
      _ = -(R_u * V * R_u₀) := by simp only [mul_neg, neg_mul]
  have hsecondMul : R_u - R_u₀ = -(R_u₀ * V * R_u₀) +
      R_u₀ * V * R_u * V * R_u₀ := by
    have hRexpand : R_u = R_u₀ - R_u * V * R_u₀ := by
      calc
        R_u = (R_u - R_u₀) + R_u₀ := (sub_add_cancel R_u R_u₀).symm
        _ = -(R_u * V * R_u₀) + R_u₀ := by rw [hright]
        _ = R_u₀ - R_u * V * R_u₀ := by
          rw [sub_eq_add_neg, add_comm]
    calc
      R_u - R_u₀ = -(R_u₀ * V * R_u) := hleft
      _ = -(R_u₀ * V * (R_u₀ - R_u * V * R_u₀)) :=
        congrArg (fun Z : R →L[𝕜] R => -(R_u₀ * V * Z)) hRexpand
      _ = -(R_u₀ * V * R_u₀) + R_u₀ * V * R_u * V * R_u₀ := by
        rw [mul_sub, neg_sub, sub_eq_add_neg, add_comm]
        simp only [mul_assoc]
  have hsecond : R_u - R_u₀ = -(R_u₀.comp (V.comp R_u₀)) +
      R_u₀.comp (V.comp (R_u.comp (V.comp R_u₀))) := by
    simpa only [ContinuousLinearMap.mul_def, comp_assoc] using hsecondMul
  clear hleft hright hsecondMul hTsub
  have hFQ : F.comp Q = 0 := by
    change F.comp (1 - P) = 0
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.one_def,
      ContinuousLinearMap.comp_id, hFP, sub_self]
  have hFP_apply (x : R) : F (P x) = F x := by
    change (F.comp P) x = F x
    rw [hFP]
  have hFQ_apply (x : R) : F (Q x) = 0 := by
    change (F.comp Q) x = 0
    rw [hFQ, zero_apply]
  have hVcross : V = (P.comp S).comp Q + (Q.comp S).comp P := by
    dsimp only [V, S₀, Q]
    simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
      ContinuousLinearMap.comp_id, comp_assoc]
    abel
  have hFV : F.comp V = (F.comp S).comp Q := by
    ext x
    rw [hVcross]
    simp only [ContinuousLinearMap.comp_apply, add_apply, map_add,
      hFP_apply, hFQ_apply, add_zero]
  have hVG : V.comp G = (Q.comp S).comp G := by
    rw [hVcross, ContinuousLinearMap.add_comp]
    simp only [comp_assoc, hQG, hPG, ContinuousLinearMap.comp_zero,
      zero_add]
  have hFVG : F.comp (V.comp G) = 0 := by
    rw [← comp_assoc, hFV]
    simp only [comp_assoc, hQG, ContinuousLinearMap.comp_zero]
  have hAuF : A_u.comp F = F.comp T₀ := by
    calc
      A_u.comp F = (F.comp S).comp P + (u : 𝕜) • F := by
        simp only [A_u, A, P, ContinuousLinearMap.add_comp,
          ContinuousLinearMap.smul_comp, ContinuousLinearMap.one_def,
          ContinuousLinearMap.id_comp, comp_assoc]
      _ = F.comp T₀ := by
        ext x
        simp only [T₀, S₀, ContinuousLinearMap.comp_apply,
          add_apply, smul_apply,
          one_apply_eq_self, map_add, map_smul]
        rw [hFP_apply, hFQ_apply, add_zero]
  have hAuinvF : A_u_inv.comp F = F.comp R_u₀ := by
    calc
      A_u_inv.comp F = (A_u_inv.comp F).comp (T₀.comp R_u₀) := by
        rw [hT₀R, ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
      _ = (A_u_inv.comp (F.comp T₀)).comp R_u₀ := by simp only [comp_assoc]
      _ = (A_u_inv.comp (A_u.comp F)).comp R_u₀ := by rw [hAuF]
      _ = ((A_u_inv.comp A_u).comp F).comp R_u₀ := by simp only [comp_assoc]
      _ = F.comp R_u₀ := by
        rw [hAuinvAu, ContinuousLinearMap.one_def,
          ContinuousLinearMap.id_comp]
  have hR₀G : R_u₀.comp G = G.comp A_u_inv := by
    simpa only [adjoint_comp, G, hAuinvself, hR₀self, adjoint_adjoint] using
      (congrArg ContinuousLinearMap.adjoint hAuinvF).symm
  have hFR₀G : F.comp (R_u₀.comp G) = A_u_inv := by
    calc
      F.comp (R_u₀.comp G) = (F.comp R_u₀).comp G := by
        simp only [comp_assoc]
      _ = (A_u_inv.comp F).comp G :=
        congrArg (fun C : R →L[𝕜] E => C.comp G) hAuinvF.symm
      _ = A_u_inv := by
        change A_u_inv.comp (F.comp G) = A_u_inv
        rw [hF, ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
  have hfirstVanishing : F.comp (R_u₀.comp (V.comp (R_u₀.comp G))) = 0 := by
    calc
      F.comp (R_u₀.comp (V.comp (R_u₀.comp G))) =
          (F.comp R_u₀).comp (V.comp (R_u₀.comp G)) := by
        simp only [comp_assoc]
      _ = (A_u_inv.comp F).comp (V.comp (G.comp A_u_inv)) := by
        rw [hAuinvF, hR₀G]
      _ = A_u_inv.comp ((F.comp (V.comp G)).comp A_u_inv) := by
        simp only [comp_assoc]
      _ = 0 := by
        rw [hFVG]
        rw [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
  have hcompressedDifference :
      F.comp (R_u.comp G) - A_u_inv = F.comp ((R_u - R_u₀).comp G) := by
    calc
      F.comp (R_u.comp G) - A_u_inv =
          F.comp (R_u.comp G) - F.comp (R_u₀.comp G) := by rw [hFR₀G]
      _ = F.comp ((R_u - R_u₀).comp G) := by
        simp only [ContinuousLinearMap.comp_sub,
          ContinuousLinearMap.sub_comp]
  have hFR₀V : F.comp (R_u₀.comp V) =
      ((A_u_inv.comp F).comp S).comp Q := by
    calc
      F.comp (R_u₀.comp V) = (F.comp R_u₀).comp V := by
        simp only [comp_assoc]
      _ = (A_u_inv.comp F).comp V :=
        congrArg (fun C : R →L[𝕜] E => C.comp V) hAuinvF.symm
      _ = A_u_inv.comp (F.comp V) := by simp only [comp_assoc]
      _ = A_u_inv.comp ((F.comp S).comp Q) := by rw [hFV]
      _ = ((A_u_inv.comp F).comp S).comp Q := by
        simp only [comp_assoc]
  have hVR₀G : V.comp (R_u₀.comp G) =
      ((Q.comp S).comp G).comp A_u_inv := by
    calc
      V.comp (R_u₀.comp G) = V.comp (G.comp A_u_inv) := by rw [hR₀G]
      _ = (V.comp G).comp A_u_inv := by simp only [comp_assoc]
      _ = ((Q.comp S).comp G).comp A_u_inv :=
        congrArg (fun C : E →L[𝕜] R => C.comp A_u_inv) hVG
  have hcompressedW : F.comp ((R_u - R_u₀).comp G) =
      (F.comp (R_u₀.comp V)).comp
        (R_u.comp (V.comp (R_u₀.comp G))) := by
    rw [hsecond]
    simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.neg_comp,
      ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_neg, comp_assoc,
      hfirstVanishing, neg_zero, zero_add]
  have hWfactor : (F.comp (R_u₀.comp V)).comp
        (R_u.comp (V.comp (R_u₀.comp G))) =
      A_u_inv.comp (F.comp (S.comp (Q.comp (R_u.comp
        (Q.comp (S.comp (G.comp A_u_inv))))))) := by
    rw [hFR₀V, hVR₀G]
    simp only [comp_assoc]
  have hremainderRaw : F.comp (R_u.comp G) - A_u_inv =
      A_u_inv.comp (F.comp (S.comp (Q.comp (R_u.comp
        (Q.comp (S.comp (G.comp A_u_inv))))))) :=
    by
      exact hcompressedDifference.trans (hcompressedW.trans hWfactor)
  clear hcompressedDifference hcompressedW hWfactor hFR₀V hVR₀G
    hfirstVanishing hFR₀G hR₀G hAuinvF hAuF hFVG hVG hFV hVcross
    hFP_apply hFQ_apply hFQ
  let H : E →L[𝕜] R := Q.comp (S.comp G)
  let X : E →L[𝕜] R := H.comp A_u_inv
  have hXadj : X.adjoint = A_u_inv.comp B := by
    dsimp only [X, H]
    rw [adjoint_comp, hAuinvself, ← hBadj, adjoint_adjoint]
  have hremainderX : F.comp (R_u.comp G) - A_u_inv =
      X.adjoint.comp (R_u.comp X) := by
    rw [hremainderRaw, hXadj]
    dsimp only [X, H, B]
    simp only [comp_assoc]
  have hpositive : 0 ≤ F.comp (R_u.comp G) - A_u_inv := by
    rw [hremainderX]
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).2
      (hRpos.adjoint_conj X)
  have hHiddenNorm : ‖H‖ = ‖B‖ := by
    dsimp only [H]
    rw [← hBadj]
    exact hBadjNorm
  clear hXadj hS₀diff hAdiff hTlower hT₀lower hAulower hTpos hTunit
    hT₀pos hT₀unit hAupos hAuunit hTR hT₀R hAuinvAu hRself hR₀self
    hRpos hAuinvself inverse_data_of_lower
  have hnormBound : ‖F.comp (R_u.comp G) - A_u_inv‖ ≤ δ / (a + u) ^ 3 := by as_aux_lemma =>
    rw [hremainderX]
    let xNorm : ℝ := ‖X‖
    have hXbound : xNorm ≤ ‖B‖ * (a + u)⁻¹ := by
      dsimp only [xNorm]
      calc
        ‖X‖ ≤ ‖H‖ * ‖A_u_inv‖ := by
          dsimp only [X]
          exact H.opNorm_comp_le A_u_inv
        _ = ‖B‖ * ‖A_u_inv‖ := by rw [hHiddenNorm]
        _ ≤ ‖B‖ * (a + u)⁻¹ :=
          mul_le_mul_of_nonneg_left hAuinvnorm (norm_nonneg B)
    have hcinv : 0 ≤ (a + u)⁻¹ := inv_nonneg.mpr hc.le
    have hBcinv : 0 ≤ ‖B‖ * (a + u)⁻¹ := mul_nonneg (norm_nonneg B) hcinv
    have hXR : xNorm * ‖R_u‖ ≤
        (‖B‖ * (a + u)⁻¹) * (a + u)⁻¹ :=
      mul_le_mul hXbound hRnorm (norm_nonneg R_u) hBcinv
    calc
      _ ≤ ‖X.adjoint‖ * ‖R_u.comp X‖ :=
        X.adjoint.opNorm_comp_le (R_u.comp X)
      _ ≤ ‖X.adjoint‖ * (‖R_u‖ * ‖X‖) :=
        mul_le_mul_of_nonneg_left
          (R_u.opNorm_comp_le X) (norm_nonneg X.adjoint)
      _ = xNorm * ‖R_u‖ * xNorm :=
        by
          dsimp only [xNorm]
          rw [ContinuousLinearMap.adjoint.norm_map]
          simp only [mul_assoc]
      _ ≤ (‖B‖ * (a + u)⁻¹) * (a + u)⁻¹ * (‖B‖ * (a + u)⁻¹) := by
        exact mul_le_mul hXR hXbound (norm_nonneg _)
          (mul_nonneg hBcinv hcinv)
      _ = δ / (a + u) ^ 3 := by
        rw [div_eq_mul_inv, ← hleakSq, ← inv_pow]
        simp only [pow_succ, pow_zero, one_mul]
        calc
          ‖B‖ * (a + u)⁻¹ * (a + u)⁻¹ * (‖B‖ * (a + u)⁻¹) =
              ‖B‖ * ((a + u)⁻¹ * ((a + u)⁻¹ * (‖B‖ * (a + u)⁻¹))) := by
            simp only [mul_assoc]
          _ = ‖B‖ * ((a + u)⁻¹ * (‖B‖ * ((a + u)⁻¹ * (a + u)⁻¹))) := by
            rw [mul_left_comm (a + u)⁻¹ ‖B‖ (a + u)⁻¹]
          _ = ‖B‖ * (‖B‖ * ((a + u)⁻¹ * ((a + u)⁻¹ * (a + u)⁻¹))) := by
            rw [mul_left_comm (a + u)⁻¹ ‖B‖ ((a + u)⁻¹ * (a + u)⁻¹)]
          _ = ‖B‖ * ‖B‖ *
              (((a + u)⁻¹ * (a + u)⁻¹) * (a + u)⁻¹) := by
            simp only [mul_assoc]
  exact ⟨hsecond, hremainderRaw, hpositive, hnormBound⟩

#print axioms compressed_resolvent_remainder

end D5.S3.Quantum.Dynamics.CompressedResolventRemainder
