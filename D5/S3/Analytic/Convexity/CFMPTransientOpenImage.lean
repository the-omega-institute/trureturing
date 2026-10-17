/-
SOURCE PREPARATION ONLY. This file has not been elaborated or compiled.
Owner: D5.S3.Geometry.Hyperideal.FourCycleExistence, dev
3346bf06d980da44036611432a1e9c77ff899da4; exact supplier snapshot SHA256
 a69b801ee76a5fcadb02390e0967fbdc440d0d9bd7ab9950765699b77132b814.
Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d (Lean v4.33.0).
Transient use of the original PRIVATE declarations only. No supplier proof copied.
No retained declaration or Describe is proposed. Parent owns all validation/admission.
-/
import D5.S3.Geometry.Hyperideal.FourCycleExistence
import Lean
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace

/- Resolve the actual imported private constant by its complete original user name.
   This avoids guessing the generated private numeric suffix. It returns that
   constant itself; it neither introduces an axiom nor reconstructs its proof.
   Import visibility and this elaborator still require the parent's exact check. -/
open Lean Elab Term in
local elab "original_decl% " id:ident : term => do
  let wanted := id.getId.eraseMacroScopes
  let env ← getEnv
  let mut candidates : Array Name := #[]
  for (name, _) in env.constants do
    if privateToUserName? name == some wanted then
      candidates := candidates.push name
  unless candidates.size == 1 do
    throwError "Expected exactly one original private declaration {wanted}; found {candidates.size}"
  let name := candidates[0]!
  let some ownerIdx := env.getModuleIdxFor? name
    | throwError "Original private declaration {name} is not imported"
  let some ownerImport := env.header.modules[ownerIdx]?
    | throwError "Missing imported module metadata for {name}"
  unless ownerImport.module == `D5.S3.Geometry.Hyperideal.FourCycleExistence do
    throwError "Unexpected owner module {ownerImport.module} for {name}"
  unless ownerImport.importAll && ownerImport.hasData do
    throwError "Expected import-all declaration data for owner {ownerImport.module}"
  return ← Lean.Meta.mkConstWithFreshMVarLevels name

-- BEGIN MAIN ANONYMOUS TARGET
theorem CFMP133_SourceOnly.bridge {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    (∀ (D : Set E) (T : E → E) (c : E) (r m : ℝ),
      0 < r → 0 < m → Metric.closedBall c r ⊆ D → ContinuousOn T D →
      (∀ x ∈ Metric.closedBall c r,
        m * ‖x - c‖ ^ 2 ≤ ⟪T x - T c, x - c⟫_ℝ) →
      ∀ y : E, ‖y - T c‖ < m * r →
        ∃ x : E, ‖x - c‖ < r ∧ T x = y) ∧
    (∀ (D : Set E) (T : E → E) (m : ℝ),
      0 < m → IsOpen D → ContinuousOn T D →
      (∀ x ∈ D, ∀ z ∈ D,
        m * ‖x - z‖ ^ 2 ≤ ⟪T x - T z, x - z⟫_ℝ) →
      IsOpen (T '' D) ∧
      (∀ x ∈ D, ∀ z ∈ D, m * ‖x - z‖ ≤ ‖T x - T z‖) ∧
      Set.InjOn T D ∧
      ∃ e : D ≃ (T '' D),
        (∀ x : D, (e x : E) = T (x : E)) ∧
        (∀ u v : T '' D,
          m * ‖(e.symm u : E) - (e.symm v : E)‖ ≤ ‖(u : E) - (v : E)‖ ∧
          ‖(e.symm u : E) - (e.symm v : E)‖ ≤ ‖(u : E) - (v : E)‖ / m)) ∧
    (∀ (D : Set E) (F : E → E),
      IsOpen D → ContinuousOn F D →
      (∀ x ∈ D, ∀ z ∈ D, 0 ≤ ⟪F x - F z, x - z⟫_ℝ) →
      IsOpen ((fun x => x + F x) '' D) ∧
      (∀ x ∈ D, ∀ z ∈ D, ‖x - z‖ ≤ ‖(x + F x) - (z + F z)‖) ∧
      Set.InjOn (fun x => x + F x) D ∧
      ∃ e : D ≃ ((fun x => x + F x) '' D),
        (∀ x : D, (e x : E) = (x : E) + F (x : E)) ∧
        (∀ u v : (fun x => x + F x) '' D,
          ‖(e.symm u : E) - (e.symm v : E)‖ ≤ ‖(u : E) - (v : E)‖) ∧
        LipschitzWith 1 e.symm) := by
  classical
  have hlocal : ∀ (D : Set E) (T : E → E) (c : E) (r m : ℝ),
      0 < r → 0 < m → Metric.closedBall c r ⊆ D → ContinuousOn T D →
      (∀ x ∈ Metric.closedBall c r,
        m * ‖x - c‖ ^ 2 ≤ ⟪T x - T c, x - c⟫_ℝ) →
      ∀ y : E, ‖y - T c‖ < m * r →
        ∃ x : E, ‖x - c‖ < r ∧ T x = y := by
    intro D T c r m hr hm hCD hT hmono y hy
    -- The denominator is positive even at the center.
    let a : E → ℝ := fun z => r / max r ‖z - c‖
    let P : E → E := fun z => c + a z • (z - c)
    have hden (z : E) : 0 < max r ‖z - c‖ :=
      hr.trans_le (le_max_left _ _)
    have ha (z : E) : 0 < a z := div_pos hr (hden z)
    have ha1 (z : E) : a z ≤ 1 :=
      (div_le_one (hden z)).2 (le_max_left _ _)
    have hPnorm (z : E) : ‖P z - c‖ = a z * ‖z - c‖ := by
      change ‖(c + a z • (z - c)) - c‖ = a z * ‖z - c‖
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (ha z)]
    have hPid (z : E) (hz : ‖z - c‖ ≤ r) : P z = z := by
      dsimp [P, a]
      rw [max_eq_left hz, div_self hr.ne', one_smul]
      abel
    have hPbound (z : E) : ‖P z - c‖ ≤ r := by
      by_cases hz : ‖z - c‖ ≤ r
      · rw [hPid z hz]
        exact hz
      · have hz' : r ≤ ‖z - c‖ := (le_of_not_ge hz)
        have hn : ‖z - c‖ ≠ 0 := (hr.trans_le hz').ne'
        rw [hPnorm]
        dsimp [a]
        simpa only [max_eq_right hz', div_mul_cancel₀ _ hn] using (le_rfl : r ≤ r)
    have hPmem (z : E) : P z ∈ Metric.closedBall c r := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hPbound z
    have hPfiber (z : E) (hz : ‖P z - c‖ < r) : z = P z := by
      have hzin : ‖z - c‖ ≤ r := by
        by_contra hn
        have hle : r ≤ ‖z - c‖ := le_of_not_ge hn
        have hne : ‖z - c‖ ≠ 0 := (hr.trans_le hle).ne'
        have heq : ‖P z - c‖ = r := by
          rw [hPnorm]
          dsimp [a]
          rw [max_eq_right hle, div_mul_cancel₀ _ hne]
        rw [heq] at hz
        exact (lt_irrefl r) hz
      exact (hPid z hzin).symm
    have hP : Continuous P := by
      have hsub : Continuous (fun z : E => z - c) := continuous_id.sub continuous_const
      have hmax : Continuous (fun z : E => max r ‖z - c‖) :=
        continuous_const.max hsub.norm
      have hac : Continuous a := continuous_const.div₀ hmax (fun z => (hden z).ne')
      exact continuous_const.add (hac.smul hsub)
    -- T is only used on the clipped closed ball, which is contained in D.
    have hTP : Continuous (fun z : E => T (P z)) :=
      hT.comp_continuous hP (fun z => hCD (hPmem z))
    let H : E → E := fun z => P (P z - (T (P z) - y))
    have hH : Continuous H := hP.comp (hP.sub (hTP.sub continuous_const))
    have hHmem (z : E) : H z ∈ Metric.closedBall c r := hPmem _

    -- U is an isometry into EuclideanSpace. L is only a continuous linear
    -- equivalence into the ordinary Pi space. No equality of their norms is used.
    let n := Module.finrank ℝ E
    let U : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) := (stdOrthonormalBasis ℝ E).repr
    let L : E ≃L[ℝ] (Fin n → ℝ) :=
      U.toContinuousLinearEquiv.trans
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ))
    have hcoord (v : E) (i : Fin n) : |L v i| ≤ ‖v‖ := by
      change |U v i| ≤ ‖v‖
      calc
        |U v i| = ‖U v i‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖U v‖ := PiLp.norm_apply_le (U v) i
        _ = ‖v‖ := U.norm_map v
    let A : (Fin n → ℝ) → E := fun u => c + L.symm (fun i => r * (2 * u i - 1))
    let B : E → (Fin n → ℝ) := fun z i => (L (z - c) i / r + 1) / 2
    have hAB (z : E) : A (B z) = z := by
      have hfun : (fun i : Fin n => r * (2 * B z i - 1)) = L (z - c) := by
        funext i
        dsimp [B]
        field_simp [hr.ne'] <;> ring
      change c + L.symm (fun i => r * (2 * B z i - 1)) = z
      rw [hfun, L.symm_apply_apply]
      abel
    have hA : Continuous A := by
      apply continuous_const.add
      apply L.symm.continuous.comp
      apply continuous_pi
      intro i
      exact continuous_const.mul ((continuous_const.mul (continuous_apply i)).sub continuous_const)
    have hB : Continuous B := by
      apply continuous_pi
      intro i
      exact ((((continuous_apply i).comp
        (L.continuous.comp (continuous_id.sub continuous_const))).div_const r).add
        continuous_const).div_const 2
    have hBmem (z : E) (hz : z ∈ Metric.closedBall c r) (i : Fin n) :
        B z i ∈ Set.Icc 0 1 := by
      have hnorm : ‖z - c‖ ≤ r := by
        simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
      have hbounds := abs_le.mp ((hcoord (z - c) i).trans hnorm)
      have hlo : -1 ≤ L (z - c) i / r := (le_div_iff₀ hr).2 (by nlinarith [hbounds.1])
      have hhi : L (z - c) i / r ≤ 1 := (div_le_iff₀ hr).2 (by nlinarith [hbounds.2])
      change 0 ≤ (L (z - c) i / r + 1) / 2 ∧ (L (z - c) i / r + 1) / 2 ≤ 1
      constructor <;> linarith
    -- The containing coordinate cube need not be a subset of D.
    let f : (original_decl% D5.S3.Geometry.Hyperideal.FourCycleExistence.Cube) n → (original_decl% D5.S3.Geometry.Hyperideal.FourCycleExistence.Cube) n := fun u =>
      ⟨B (H (A u.1)), hBmem _ (hHmem _)⟩
    have hf : Continuous f := by
      apply Continuous.subtype_mk
      exact hB.comp (hH.comp (hA.comp continuous_subtype_val))
    -- The only Brouwer/cube fixed-point invocation in this proof.
    obtain ⟨u, hu⟩ :=
      (original_decl% D5.S3.Geometry.Hyperideal.FourCycleExistence.cube_fixed_point) n f hf
    let x : E := A u.1
    have hHx : H x = x := by
      have heq := congrArg (fun v : (original_decl% D5.S3.Geometry.Hyperideal.FourCycleExistence.Cube) n => A v.1) hu
      change A (B (H (A u.1))) = A u.1 at heq
      rw [hAB] at heq
      exact heq
    have hxmem : x ∈ Metric.closedBall c r := by
      rw [← hHx]
      exact hHmem x
    have hxbound : ‖x - c‖ ≤ r := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hxmem
    have hPx : P x = x := hPid x hxbound
    have hfix : P (x - (T x - y)) = x := by
      simpa only [H, hPx] using hHx

    -- Exact scalar sign from the negative residual fixed point.
    let w := x - (T x - y)
    have hfixw : P w = x := hfix
    have hv : a w • (w - c) = x - c := by
      have heq := congrArg (fun z : E => z - c) hfixw
      simpa only [P, add_sub_cancel_left] using heq
    have hscalar :
        a w * (‖x - c‖ ^ 2 - ⟪T x - y, x - c⟫_ℝ) = ‖x - c‖ ^ 2 := by
      have hi := congrArg (fun z : E => ⟪z, x - c⟫_ℝ) hv
      have hw : w - c = (x - c) - (T x - y) := by dsimp [w]; abel
      rw [real_inner_smul_left, hw, inner_sub_left] at hi
      simpa only [real_inner_self_eq_norm_sq] using hi
    have hsign : ⟪T x - y, x - c⟫_ℝ ≤ 0 := by
      have hnonpos : (a w - 1) * ‖x - c‖ ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (ha1 w)) (sq_nonneg _)
      have hprod : a w * ⟪T x - y, x - c⟫_ℝ ≤ 0 := by nlinarith [hscalar]
      by_contra hpos
      have hp := mul_pos (ha w) (lt_of_not_ge hpos)
      linarith
    have hxstrict : ‖x - c‖ < r := by
      by_contra hnot
      have heq : ‖x - c‖ = r := le_antisymm hxbound (le_of_not_gt hnot)
      have hlower := hmono x hxmem
      have hcs := real_inner_le_norm (y - T c) (x - c)
      have hsplit : ⟪T x - y, x - c⟫_ℝ =
          ⟪T x - T c, x - c⟫_ℝ - ⟪y - T c, x - c⟫_ℝ := by
        rw [← inner_sub_left]
        congr 1
        abel
      have hgap : 0 < (m * r - ‖y - T c‖) * r :=
        mul_pos (sub_pos.mpr hy) hr
      rw [heq] at hlower hcs
      nlinarith [hsplit, hsign]
    have hwx : w = x := (hPfiber w (by simpa only [hfixw] using hxstrict)).trans hfixw
    have hzero : T x - y = 0 := by
      have heq : x - (T x - y) = x := hwx
      have heq' := congrArg (fun z : E => x - z) heq
      simpa only [sub_sub_cancel, sub_self] using heq'
    exact ⟨x, hxstrict, sub_eq_zero.mp hzero⟩

  have hglobal : ∀ (D : Set E) (T : E → E) (m : ℝ),
      0 < m → IsOpen D → ContinuousOn T D →
      (∀ x ∈ D, ∀ z ∈ D, m * ‖x - z‖ ^ 2 ≤ ⟪T x - T z, x - z⟫_ℝ) →
      IsOpen (T '' D) ∧
      (∀ x ∈ D, ∀ z ∈ D, m * ‖x - z‖ ≤ ‖T x - T z‖) ∧
      Set.InjOn T D ∧
      ∃ e : D ≃ (T '' D),
        (∀ x : D, (e x : E) = T (x : E)) ∧
        (∀ u v : T '' D,
          m * ‖(e.symm u : E) - (e.symm v : E)‖ ≤ ‖(u : E) - (v : E)‖ ∧
          ‖(e.symm u : E) - (e.symm v : E)‖ ≤ ‖(u : E) - (v : E)‖ / m) := by
    intro D T m hm hD hT hmono
    have hopen : IsOpen (T '' D) := by
      apply Metric.isOpen_iff.mpr
      rintro _ ⟨c, hc, rfl⟩
      obtain ⟨r, hr, hCD⟩ : ∃ r : ℝ, 0 < r ∧ Metric.closedBall c r ⊆ D :=
        Metric.nhds_basis_closedBall.mem_iff.mp (hD.mem_nhds hc)
      refine ⟨m * r, mul_pos hm hr, ?_⟩
      intro y hy
      have hy' : ‖y - T c‖ < m * r := by
        simpa only [Metric.mem_ball, dist_eq_norm] using hy
      obtain ⟨x, hx, hxy⟩ := hlocal D T c r m hr hm hCD hT
        (fun x hx => hmono x (hCD hx) c hc) y hy'
      refine ⟨x, hCD ?_, hxy⟩
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hx.le
    have hnorm : ∀ x ∈ D, ∀ z ∈ D, m * ‖x - z‖ ≤ ‖T x - T z‖ := by
      intro x hx z hz
      have h := (hmono x hx z hz).trans (real_inner_le_norm (T x - T z) (x - z))
      by_cases heq : x = z
      · subst z
        simp
      · have hn : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr heq)
        have hp : (m * ‖x - z‖) * ‖x - z‖ ≤ ‖T x - T z‖ * ‖x - z‖ := by
          nlinarith [h]
        exact le_of_mul_le_mul_right hp hn
    have hinj : Set.InjOn T D := by
      intro x hx z hz heq
      have h := hnorm x hx z hz
      rw [heq, sub_self, norm_zero] at h
      have hnle : ‖x - z‖ ≤ 0 :=
        le_of_mul_le_mul_left (by simpa only [mul_zero] using h) hm
      have hn : ‖x - z‖ = 0 := le_antisymm hnle (norm_nonneg _)
      exact sub_eq_zero.mp (norm_eq_zero.mp hn)
    let t : D → (T '' D) := fun x => ⟨T x.1, ⟨x.1, x.2, rfl⟩⟩
    have ht : Function.Bijective t := by
      constructor
      · intro x z heq
        apply Subtype.ext
        exact hinj x.2 z.2 (congrArg (fun u : T '' D => (u : E)) heq)
      · intro y
        rcases y.2 with ⟨x, hx, hxy⟩
        refine ⟨⟨x, hx⟩, ?_⟩
        apply Subtype.ext
        exact hxy
    let e : D ≃ (T '' D) := Equiv.ofBijective t ht
    have he (x : D) : (e x : E) = T (x : E) := rfl
    have hinv (u : T '' D) : T (e.symm u : E) = (u : E) := by
      rw [← he (e.symm u), e.apply_symm_apply]
    refine ⟨hopen, hnorm, hinj, e, he, ?_⟩
    intro u v
    have h := hnorm (e.symm u) (e.symm u).2 (e.symm v) (e.symm v).2
    rw [hinv u, hinv v] at h
    exact ⟨h, (le_div_iff₀ hm).2 (by nlinarith [h])⟩

  refine ⟨hlocal, hglobal, ?_⟩
  intro D F hD hF hmono
  let T : E → E := fun x => x + F x
  have hT : ContinuousOn T D := continuous_id.continuousOn.add hF
  have hstrong : ∀ x ∈ D, ∀ z ∈ D,
      (1 : ℝ) * ‖x - z‖ ^ 2 ≤ ⟪T x - T z, x - z⟫_ℝ := by
    intro x hx z hz
    have heq : T x - T z = (x - z) + (F x - F z) := by dsimp [T]; abel
    rw [heq, inner_add_left, real_inner_self_eq_norm_sq]
    have h := hmono x hx z hz
    linarith
  obtain ⟨hopen, hnorm, hinj, e, he, hinv⟩ := hglobal D T 1 (by norm_num) hD hT hstrong
  refine ⟨hopen, ?_, hinj, e, he, ?_, ?_⟩
  · intro x hx z hz
    simpa only [one_mul] using hnorm x hx z hz
  · intro u v
    simpa only [one_mul] using (hinv u v).1
  · apply LipschitzWith.of_dist_le_mul
    intro u v
    simpa only [Subtype.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
      using (hinv u v).1
-- END MAIN ANONYMOUS TARGET

/- AUDIT-ONLY projections: never retain these named wrappers in the repository. -/
noncomputable def CFMP133_SourceOnly.local_target
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :=
  (CFMP133_SourceOnly.bridge (E := E)).1

noncomputable def CFMP133_SourceOnly.open_inverse_target
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :=
  (CFMP133_SourceOnly.bridge (E := E)).2.1

noncomputable def CFMP133_SourceOnly.id_add_target
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :=
  (CFMP133_SourceOnly.bridge (E := E)).2.2

/- These are future Lean sanity checks. They have NOT been run. -/
theorem CFMP133_SourceOnly.sanity_dimension_zero
    (c y : EuclideanSpace ℝ (Fin 0)) :
    ∃ x : EuclideanSpace ℝ (Fin 0), ‖x - c‖ < 1 ∧ x = y := by
  have hyc : y = c := PiLp.ext (fun i => Fin.elim0 i)
  apply (CFMP133_SourceOnly.bridge (E := EuclideanSpace ℝ (Fin 0))).1
    Set.univ (fun x => x) c 1 1 (by norm_num) (by norm_num)
    (by intro x hx; trivial) continuous_id.continuousOn
    (by intro x hx; simp only [one_mul, real_inner_self_eq_norm_sq, le_refl]) y
  simpa only [hyc, sub_self, norm_zero, one_mul] using (zero_lt_one : (0 : ℝ) < 1)

theorem CFMP133_SourceOnly.sanity_bounded_identity :
    IsOpen ((fun x : ℝ => x + 0) '' Set.Ioo (-1 : ℝ) 1) ∧
    (∃ e : Set.Ioo (-1 : ℝ) 1 ≃ ((fun x : ℝ => x + 0) '' Set.Ioo (-1 : ℝ) 1),
      LipschitzWith 1 e.symm) ∧
    ¬ Function.Surjective (fun x : Set.Ioo (-1 : ℝ) 1 => (x : ℝ) + 0) := by
  obtain ⟨hopen, hnorm, hinj, e, he, hinv, hlip⟩ :=
    (CFMP133_SourceOnly.bridge (E := ℝ)).2.2 (Set.Ioo (-1 : ℝ) 1)
      (fun _ => (0 : ℝ)) isOpen_Ioo continuous_const.continuousOn
      (by intro x hx z hz; simp)
  refine ⟨hopen, ⟨e, hlip⟩, ?_⟩
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj 2
  have hxlt : (x : ℝ) < 1 := x.2.2
  simp only [add_zero] at hx
  linarith

/- Print the actual private identifier, original telescope and inherited axiom
   set without guessing a generated private name. No mathematical declaration
   is introduced by this command. -/
open Lean Elab Command in
local elab "#original_decl_queries " id:ident : command => do
  let wanted := id.getId.eraseMacroScopes
  let env ← getEnv
  let mut candidates : Array Name := #[]
  for (name, _) in env.constants do
    if privateToUserName? name == some wanted then
      candidates := candidates.push name
  unless candidates.size == 1 do
    throwError "Expected exactly one original private declaration {wanted}; found {candidates.size}"
  let name := candidates[0]!
  let some ownerIdx := env.getModuleIdxFor? name
    | throwError "Original private declaration {name} is not imported"
  let some ownerImport := env.header.modules[ownerIdx]?
    | throwError "Missing imported module metadata for {name}"
  unless ownerImport.module == `D5.S3.Geometry.Hyperideal.FourCycleExistence do
    throwError "Unexpected owner module {ownerImport.module} for {name}"
  unless ownerImport.importAll && ownerImport.hasData do
    throwError "Expected import-all declaration data for owner {ownerImport.module}"
  logInfo m!"ORIGINAL USER NAME: {wanted.toString}"
  logInfo m!"ORIGINAL PRIVATE IDENTITY: {name.toString}"
  logInfo m!"ORIGINAL OWNER MODULE: {ownerImport.module.toString}; index={ownerIdx.toNat}"
  logInfo m!"OWNER EFFECTIVE IMPORT: {reprStr ownerImport.toImport}; hasData={ownerImport.hasData}; irPhases={reprStr ownerImport.irPhases}"
  logInfo m!"ENV DIRECT IMPORT INPUTS: {reprStr env.header.imports}"
  let searchPath ← Lean.searchPathRef.get
  logInfo m!"SEARCH PATH INPUT: {reprStr searchPath}"
  let oleanCandidate ← Lean.SearchPath.findModuleWithExt searchPath "olean" ownerImport.module
  logInfo m!"OWNER OLEAN SEARCH-PATH CANDIDATE (not loaded-artifact attestation): {reprStr oleanCandidate}"
  logInfo "EXPECTED SOURCE PINS (not artifact attestation): owner=3346bf06d980da44036611432a1e9c77ff899da4; supplier SHA256=a69b801ee76a5fcadb02390e0967fbdc440d0d9bd7ab9950765699b77132b814; Mathlib=db584cd6d46c92f209a44c0f1c829460d327499d; Lean=v4.33.0"
  logInfo "LOADED ARTIFACT PROVENANCE: unverified; parent must record actual invocation, any ModuleSetup.imports?/importArts overrides, and hashes of every loaded owner artifact on Mac Studio."
  elabCommand (← `(command| #check @$(mkIdent name)))
  elabCommand (← `(command| #print $(mkIdent name)))
  elabCommand (← `(command| #print axioms $(mkIdent name)))

set_option pp.universes true
set_option pp.explicit true
#original_decl_queries D5.S3.Geometry.Hyperideal.FourCycleExistence.Cube
#original_decl_queries D5.S3.Geometry.Hyperideal.FourCycleExistence.cube_fixed_point
#check @CFMP133_SourceOnly.bridge
#check @CFMP133_SourceOnly.local_target
#check @CFMP133_SourceOnly.open_inverse_target
#check @CFMP133_SourceOnly.id_add_target
#check @CFMP133_SourceOnly.sanity_dimension_zero
#check @CFMP133_SourceOnly.sanity_bounded_identity
#print axioms CFMP133_SourceOnly.bridge
#print axioms CFMP133_SourceOnly.local_target
#print axioms CFMP133_SourceOnly.open_inverse_target
#print axioms CFMP133_SourceOnly.id_add_target
#print axioms CFMP133_SourceOnly.sanity_dimension_zero
#print axioms CFMP133_SourceOnly.sanity_bounded_identity
