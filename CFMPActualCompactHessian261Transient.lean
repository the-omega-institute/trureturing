import CFMPActualGlobalHessian260Transient
import Mathlib.Topology.Order.Compact

noncomputable section
universe u261 v261
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Matrix
open scoped BigOperators Topology ContDiff Matrix
open D5.S3.Geometry.Hyperideal.FourCycleCurvature
open CFMPGenuineLengthNeighborhood435Transient (genuine)
open CFMPOriginalPhysicalEdge237Transient (sourceAngle)
open CFMPOriginalCovolumeNeighborhood251Transient
open CFMPGlobalGenuineCovolume256Transient
open CFMPActualPhysicalHessian258Transient
open CFMPActualGlobalEnergy259Transient
open CFMPActualGlobalHessian260Transient

namespace CFMPActualCompactHessian261Transient

def physicalQuadratic (G : RealizationFamily) (a z : Lengths) : ℝ :=
  ∑ e : Fin 6, ∑ f : Fin 6, z e * physicalHessian G a e f * z f

theorem physicalQuadratic_dotProduct (G : RealizationFamily) (a z : Lengths) :
    physicalQuadratic G a z = dotProduct z ((physicalHessian G a).mulVec z) := by
  simp only [physicalQuadratic,dotProduct,Matrix.mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  ring

theorem physicalHessian_continuousOn (G : RealizationFamily) (hG : realizedFamily G) :
    ContinuousOn (physicalHessian G) {a : Lengths | genuine a} := by
  have hc : ContinuousOn
      (fun a : Lengths => fun e f : Fin 6 =>
        fderiv ℝ angleVector a (Pi.single f 1) e) {a : Lengths | genuine a} := by
    intro a ha
    have hs : ContDiffAt ℝ ∞ angleVector a := by
      apply contDiffAt_pi.mpr
      intro q
      exact CFMPOriginalGlobalSmoothCovolume103Transient.sourceAngle_smooth a ha q
    have hJ := hs.continuousAt_fderiv (by simp)
    have hM : ContinuousAt
        (fun b : Lengths => fun e f : Fin 6 =>
          fderiv ℝ angleVector b (Pi.single f 1) e) a := by
      apply continuousAt_pi.mpr
      intro e
      apply continuousAt_pi.mpr
      intro f
      exact (continuous_apply e).continuousAt.comp (hJ.clm_apply continuousAt_const)
    exact hM.continuousWithinAt
  apply hc.congr
  intro a ha
  ext e f
  exact (angleVector_matrix_actual G hG a ha e f).symm

theorem physicalHessian_choice_independent
    (F G : RealizationFamily) (hF : realizedFamily F) (hG : realizedFamily G)
    (a : Lengths) (ha : genuine a) : physicalHessian F a = physicalHessian G a := by
  rw [physicalHessian_eq_sourceJacobian F hF a ha,
    physicalHessian_eq_sourceJacobian G hG a ha]

theorem compact_actual_hessian_bounds
    (C : Set Lengths) (hC : IsCompact C) (hsub : C ⊆ {a : Lengths | genuine a}) :
    ∃ mu bound : ℝ, 0 < mu ∧ mu ≤ bound ∧
      ∀ (G : RealizationFamily), realizedFamily G →
        ∀ a ∈ C, ∀ z : Lengths,
          mu * (∑ q : Fin 6, (z q)^2) ≤ physicalQuadratic G a z ∧
          physicalQuadratic G a z ≤ bound * (∑ q : Fin 6, (z q)^2) := by
  classical
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let A : C → Matrix (Fin 6) (Fin 6) ℝ := fun a => physicalHessian wholeFamily a.val
  have hmat : Continuous A :=
    ((physicalHessian_continuousOn wholeFamily wholeFamily_realized).mono hsub).domRestrict
  let Q : C × EuclideanSpace ℝ (Fin 6) → ℝ := fun x =>
    dotProduct (fun q => x.2 q) ((A x.1).mulVec (fun q => x.2 q))
  let S : Set (C × EuclideanSpace ℝ (Fin 6)) :=
    Set.univ ×ˢ Metric.sphere 0 1
  have hS : IsCompact S :=
    isCompact_univ.prod (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 6)) 1)
  have hcoordU (i : Fin 6) :
      Continuous (fun x : C × EuclideanSpace ℝ (Fin 6) => x.2 i) :=
    (EuclideanSpace.proj i).continuous.comp continuous_snd
  have hcoordM (i j : Fin 6) :
      Continuous (fun x : C × EuclideanSpace ℝ (Fin 6) => A x.1 i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp (hmat.comp continuous_fst))
  have hQ : Continuous Q := by
    change Continuous (fun x : C × EuclideanSpace ℝ (Fin 6) =>
      ∑ i, x.2 i * (∑ j, A x.1 i j * x.2 j))
    apply continuous_finsetSum
    intro i _
    apply (hcoordU i).mul
    apply continuous_finsetSum
    intro j _
    exact (hcoordM i j).mul (hcoordU j)
  have hQpos : ∀ x ∈ S, 0 < Q x := by
    intro x hx
    have hunorm : ‖x.2‖ = 1 := by
      simpa only [Metric.mem_sphere,dist_zero_right] using hx.2
    have hne : (fun q => x.2 q) ≠ (0 : Lengths) := by
      intro hz
      have hu : x.2 = 0 := by
        apply PiLp.ext
        intro q
        exact congrFun hz q
      simp [hu] at hunorm
    simpa only [Q,A,star_trivial] using
      (physicalHessian_posDef wholeFamily wholeFamily_realized x.1.val
        (hsub x.1.property)).dotProduct_mulVec_pos hne
  obtain ⟨mu,hmu,hlow⟩ := hS.exists_forall_le' hQ.continuousOn hQpos
  obtain ⟨b,hb⟩ := hS.bddAbove_image hQ.continuousOn
  let bound : ℝ := max mu b
  have hunit (a : C) (u : EuclideanSpace ℝ (Fin 6)) (hu : ‖u‖ = 1) :
      mu ≤ Q (a,u) ∧ Q (a,u) ≤ bound := by
    have hmem : (a,u) ∈ S :=
      ⟨Set.mem_univ a,by simpa only [Metric.mem_sphere,dist_zero_right] using hu⟩
    exact ⟨hlow (a,u) hmem,(hb (Set.mem_image_of_mem Q hmem)).trans (le_max_right _ _)⟩
  have hscale (a : Lengths) (c : ℝ) (z : Lengths) :
      physicalQuadratic wholeFamily a (c • z) = c^2 * physicalQuadratic wholeFamily a z := by
    simp only [physicalQuadratic_dotProduct]
    rw [Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul]
    simp only [smul_eq_mul]
    ring
  have huniform (a : Lengths) (ha : a ∈ C) (z : Lengths) :
      mu * (∑ q : Fin 6, (z q)^2) ≤ physicalQuadratic wholeFamily a z ∧
      physicalQuadratic wholeFamily a z ≤ bound * (∑ q : Fin 6, (z q)^2) := by
    by_cases hz : z = 0
    · subst z
      simp [physicalQuadratic]
    · let x : EuclideanSpace ℝ (Fin 6) := WithLp.toLp 2 z
      have hx : x ≠ 0 := by
        intro h
        apply hz
        funext q
        exact congrArg (fun y : EuclideanSpace ℝ (Fin 6) => y q) h
      have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
      let u : EuclideanSpace ℝ (Fin 6) := ‖x‖⁻¹ • x
      have hu : ‖u‖ = 1 := by
        dsimp only [u]
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),inv_mul_cancel₀ hr.ne']
      have hzback : ‖x‖ • (fun q => u q) = z := by
        funext q
        change ‖x‖ * (‖x‖⁻¹ * z q) = z q
        rw [← mul_assoc,mul_inv_cancel₀ hr.ne',one_mul]
      have hmass : (∑ q : Fin 6, (z q)^2) = ‖x‖^2 :=
        (EuclideanSpace.real_norm_sq_eq x).symm
      have hrescale : physicalQuadratic wholeFamily a z = ‖x‖^2 * Q (⟨a,ha⟩,u) := by
        have hs := hscale a ‖x‖ (fun q => u q)
        rw [hzback] at hs
        simpa only [physicalQuadratic_dotProduct,Q,A] using hs
      obtain ⟨hlo,hhi⟩ := hunit ⟨a,ha⟩ u hu
      constructor
      · rw [hmass,hrescale]
        calc
          mu * ‖x‖^2 = ‖x‖^2 * mu := mul_comm _ _
          _ ≤ ‖x‖^2 * Q (⟨a,ha⟩,u) :=
            mul_le_mul_of_nonneg_left hlo (sq_nonneg ‖x‖)
      · rw [hmass,hrescale]
        calc
          ‖x‖^2 * Q (⟨a,ha⟩,u) ≤ ‖x‖^2 * bound :=
            mul_le_mul_of_nonneg_left hhi (sq_nonneg ‖x‖)
          _ = bound * ‖x‖^2 := mul_comm _ _
  refine ⟨mu,bound,hmu,le_max_left _ _,?_⟩
  intro G hG a ha z
  have heq : physicalQuadratic G a z = physicalQuadratic wholeFamily a z := by
    unfold physicalQuadratic
    rw [physicalHessian_choice_independent G wholeFamily hG wholeFamily_realized a (hsub ha)]
  rw [heq]
  exact huniform a ha z

theorem compact_actual_global_degree_bounds
    (C : Set Lengths) (hC : IsCompact C) (hsub : C ⊆ {a : Lengths | genuine a}) :
    ∃ mu bound : ℝ, 0 < mu ∧ mu ≤ bound ∧
      ∀ (T : Type u261) (E : Type v261) [Fintype T] [Fintype E] [DecidableEq E]
        (s : Incidence T E) (G : RealizationFamily), realizedFamily G →
        ∀ p : E → ℝ, (∀ t : T, localRead s t p ∈ C) →
          ∀ v : E → ℝ,
            mu * (∑ e : E, (degree s e : ℝ) * (v e)^2) ≤
              -(∑ e : E, v e * (fderiv ℝ (physicalCurvature s) p v) e) ∧
            -(∑ e : E, v e * (fderiv ℝ (physicalCurvature s) p v) e) ≤
              bound * (∑ e : E, (degree s e : ℝ) * (v e)^2) := by
  obtain ⟨mu,bound,hmu,hbound,hlocal⟩ := compact_actual_hessian_bounds C hC hsub
  refine ⟨mu,bound,hmu,hbound,?_⟩
  intro T E _ _ _ s G hG p hreads v
  exact negative_curvature_degree_bounds s G hG p (fun t => hsub (hreads t)) mu bound
    (fun t z => hlocal G hG _ (hreads t) z) v

end CFMPActualCompactHessian261Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualCompactHessian261Transient.physicalHessian_continuousOn,
      ``CFMPActualCompactHessian261Transient.compact_actual_hessian_bounds,
      ``CFMPActualCompactHessian261Transient.compact_actual_global_degree_bounds] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP261 compact actual Hessian theorem absent from checked environment: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP261 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP261 CHECKED {name} axioms={axioms}"
