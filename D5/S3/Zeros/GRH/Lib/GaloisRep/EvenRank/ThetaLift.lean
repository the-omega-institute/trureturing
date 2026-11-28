/- GID: D5/S3/Zeros/GRH/Lib/GaloisRep/EvenRank/ThetaLift
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GaloisRep/EvenRank/ThetaLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GaloisRep.EvenRank.ThetaLift. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GaloisRep/EvenRank/ThetaLift.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.LocalGL.Tadic.ChainLemma
import D5.S3.Zeros.GRH.Lib.GaloisRep.LocalGlobal.LocalTranslates
import D5.S3.Zeros.GRH.Lib.Weil.CompactLift.RallisFormula
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: the theta lift to larger rank, the step that reduces even rank to odd rank. Here a
non-zero theta lift in the convergent range from definite U(n) to U(n+s), s > n, replaces endoscopic
transfer. It keeps spherical places, and its Hecke polynomials are twisted and gain the string of a
character of U(1). Source: Blasius, Rogawski, Motives for Hilbert modular forms, Invent. Math. 114
(1993) and Shin, Ann. of Math. 173 (2011) for the idea (endoscopic transfer to odd rank); Harris,
Soudry, Taylor, Invent. Math. 112 (1993) for theta lifts with a varying character.

This file: Nonzero theta lift to larger rank; Hecke polynomials twisted and gaining a string. -/
seal Finset.univ Finset.sum Finset.prod

open AutChar Algebra Filter Fintype G Gf Matrix Polynomial Set Space Valued

attribute [local simp] onHom_snd stdLattice.mem_stdLattice mul_mem projOn_finHeisOp
  dataInner_finHeisOp finHeisOp_finHeisOp add_mem_cancel_right
  ite_mem mem_integralBox sum_mem matToVec

/-- Theta lift: for f ≠ 0 of rank n ≥ 1, weight (κ, e), s > n, b unramified of weight c ≤ e,
some F ≠ 0 of weight κ' on I_{n+s} is spherical where f is; its rescaled Hecke polynomial is
P·∏_{l<s}(X − θ_l(ϖ)), with θ_l given by `AutChar.HasWeight.toAlgebraic`.

Known result: Theta lift to larger rank, the step that reduces even rank to odd rank. -/
lemma exists_theta_lift_heckePoly {E n} [Field E] [CMType E] [WeilData E] [Fintype n] [Nonempty n]
  {κ κ' e s c}
  {b : AutChar E} (hb : b.HasWeight c 1) (hc : c ≤ e) (hκ : κ' = fun v h ↦ ite (h < card n) (κ v h)
  (ite (h = card n) (e v - c v).toNat 0)) (f : AlgForm n κ e) (h₀ : f.1 ≠ 0) (hs : card n < s) : ∃ F
  ∈ (stdSpace E (Fin (card n + s))).forms (κ', 0), F ≠ 0 ∧ ∀ {w}, f.1 ∈ sphericalAt
  (rightRegular ℂ ..) w → F ∈ sphericalAt (rightRegular ℂ ..) w ∧ ∀ {hw P}, HasHeckePolyAt f.1 w hw
  P → ∃ Q, HasHeckePolyAt F w hw Q ∧ Q.scaleRoots (heckeCoeff (hb.toAlgebraic s s).1.1 ∅ w) =
  P * ∏ l : Fin s, (X - C (heckeCoeff (hb.toAlgebraic (card n + s) (s - l)).1.1 ∅ w)) := by
  let W := stdSpace E (Fin (card n + s))
  let H : OpenSubgroup _ := ⟨rightStab f.1, f.2.1⟩
  obtain ⟨⟨x, _, _, ρ, _⟩, ⟨B, o, h₂⟩, N, _, h₃⟩ :=
    @exists_integral_isotropic_frame E n (Fin (card n + s)) _ _ _ _ _ (by simp; lia),
    exists_inf_trivialOn_le H.2, exists_principalLevel_subset H.mem_nhds_one
  let z := (N : E)⁻¹ • idem (SetLike.coe B).conjClosure
  -- a sharp datum for a level inside the stabiliser `H` of `f`, off the poles of `z`
  have ⟨_, _, _, L⟩ : ∃ F J c,
    IsSharp (S := stdSpace E n) (T := W) b {w | 1 < v (z w)} F (H.1 ⊓ J) c := by
    refine ⟨_, (MulAction.stabilizer ..).comap ((pairWeil (stdSpace ..) W ..).comp (.prod (.inr ..)
      1)).toHomUnits, _, by simp,
      finHeisOp_mem_finitePart (matToVec (z • x)) vacElem_mem_finitePart, fun A _ a ↦ by
      simp [← mul_assoc, *, (@idem_mul_mem_Ô _ _ _ A.conjClosure z).2 (by
      rintro _ (h | h) <;> simpa [← v_star_apply, z] using a.le_compl_left h)],
      fun g c ↦ .symm (ite_eq_iff'.2 ⟨(congrArg _ ·.1.2.symm), fun r ↦ ?_⟩), rfl, by tauto⟩
    set D := g⁻¹.1.1 - 1 with ← e; simp [sub_eq_iff_eq_add] at e
    erw [weilMatrixCoeff, pairWeil_apply, onHom_fin, omega_finHeisOp, omega_vacElem,
      ← dataInner_finHeisOp _ (-matToVec (z • x))]; simp
    erw [← projOn_vacElem, dataInner_projOn, map_projOn_eq_const _ (projOn _ ⊤ ∘L finHeisOp .. ∘L
      _), map_zero] <;> simp [rep_apply_apply]; intro u _ q; have q p := q (ρ p)
    simp [*, mulVec_eq_sum, sum_prod_type, mul_add, ← add_assoc] at q
    have K i j := mem_Ô.2 fun w ↦ (Finite.exists_max (v <| D · j w)).rec fun p a ↦ (a i).trans
      (not_lt.1 fun h ↦ h.not_ge (v.map_sub_le ((c w (by simpa [h.pos] using ((((v.comap (evalAt
      w)).leAddSubgroup _).add_mem_cancel_right (sum_mem (by simp [mul_le_of_le_one_of_le, *,
      mem_Ô.1]))).1 ((mem_Ô.1 (q p j) w).trans h.le)))).isIntMatrix_inv ..) (mem_Ô.1 (by simp) w)))
    simp (disch := simp [*]) at q; have k := inv_mem_iff (x := g).1 (mem_Kf.2 (by simp [*]))
    cases r ⟨⟨(mul_mem_cancel_left (h₃ ⟨componentOn_mem_Kf (inv_mem k), (⟨_, q · ·, by
      erw [← smul_def (N : E)]; simp [z, *, componentOn, U.cutAt, cutGL, sub_smul]; rfl⟩)⟩)).1
      (h₂ (by simp_all [componentOn_mem_Kf])), (pairWeil_apply ..).trans (.trans (by
      erw [omega_finHeisOp, ← map_smul, kronecker_mulVec_eq_matToVec, ← pairWeil_apply,
        pairWeil_eq_smul_of_projOn_eq ⊤] <;> simp [hb.apply_det_eq_one, *,
      x.mul_add, Dᴴ.mul_assoc, ↓vecToMat_matToVec, add_comm]) (congrArg _ (finHeisOp_vacElem (y :=
      matToVec (x * z • D)) fun _ ↦ sum_mem (by simp [*]))))⟩, k⟩
  obtain ⟨⟨_, h⟩, g⟩ := Exists.intro _ (isHCParam_hcParameter n κ e),
    isHCParam_hcParameter (Fin (card n + s)) κ' 0
  have p := ((IsHCParam.paramsCorrespond_iff (eb :=
    c) (by delta IsHCParam hcParameter diagramWeight at *; convert h <;> grind
    [Pi.le_def]) ⟨by grind [card_fin], by simp [hs.pos], rfl⟩).2 g).isEdge_jointHarmonic
  obtain ⟨A, y, rfl⟩ := (p.isArrow 1 b L.mem_finitePart).1, (toAlgForm (stdSpace ..) h).surjective f
  refine have Z z := h₀ (by simp [((rallis_inner_product_euler p (by simp; omega)).choose_spec.2 1 b
      L y fun _ ↦ (by simp [← ofAlgForm_toAlgForm h, algFormCoeff, ·.1 _])).1 (by aesop)]); ⟨_,
      (toAlgForm _ g _).2, Z, fun {w}
      W ↦ have K := L.vacuum_off {w} _ (by simp [z, smul_def, o w (by simpa [funext_iff, LE.le,
        H] using W)]); ⟨fun k ↦ congr($(toAlgForm_formRep ..).1).symm.trans (by
    rw [A.formRep_formLift 1, pairWeil_eq_smul_of_projOn_eq _ K] <;> simp),
        fun ⟨_, r, e, u⟩ ↦ have G := (isSphericalWith_toAlgForm_iff ..).2 (isSphericalWith_formLift
          (card_fin _) (by simp [CharUnramifiedAt]) (hb.charUnramifiedAt rfl rfl) ‹_› K A
          ((isSphericalWith_toAlgForm_iff ..).1 (isSphericalWith_of_heckeSplit W
          u))); have a := (exists_heckeSplit_eq_smul ..).choose_spec _ G; (fun K ↦
            ⟨_, K, eq_of_infinite_eval_eq _ _ (infinite_of_finite_compl
            ((eventually_cofinite_ne 0).mono fun x z ↦ ?_))⟩) ⟨G.1, _, rfl, a⟩⟩⟩
  rw [e, eval_mul, eval_heckePoly, ← mul_div_cancel₀ x, scaleRoots_eval_mul, (K.isMonicOfDegree
    Z).1, eval_heckePoly, ← mul_assoc, ← mul_pow,
    ((smul_left_inj Z).1 ((isSphericalWith_of_heckeSplit G.1 a).2 _ ▸ G.2 _ :)).trans (mul_comm ..),
    eval_prod, card_fin, pow_add, ← Fin.prod_const s, trivialHecke, mul_mul_mul_comm,
    Finset.prod_range, ← Finset.prod_mul_distrib] <;> congr! 3 <;> simp [frobValue, field,
    HasWeight.toAlgebraic, w.q_eq_sqrt_sq, HeckeChar.atUnif, heckeCoeff, AutChar.spaceChar,
    zpow_add₀, zpow_sub₀, zpow_mul (_ : ℂ), z]; ring
