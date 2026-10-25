import CFMPActualPhysicalHessian258Transient
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section
universe u259 v259
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped BigOperators Topology ContDiff
open D5.S3.Geometry.Hyperideal.FourCycleCurvature
open CFMPGenuineLengthNeighborhood435Transient (genuine)
open CFMPOriginalPhysicalEdge237Transient (sourceAngle)
open CFMPOriginalCovolumeNeighborhood251Transient
open CFMPOriginalCovolumeC1253Transient
open CFMPGlobalGenuineCovolume256Transient

namespace CFMPActualGlobalEnergy259Transient

variable {T : Type u259} {E : Type v259}
  [Fintype T] [Fintype E] [DecidableEq E]

def localRead (s : Incidence T E) (t : T) : (E → ℝ) →L[ℝ] Lengths :=
  ContinuousLinearMap.pi (fun q => ContinuousLinearMap.proj (s.edge t q))

def physicalEnergy (s : Incidence T E) (G : RealizationFamily) (p : E → ℝ) : ℝ :=
  (∑ t : T, physicalCovolume G (localRead s t p)) - 2 * Real.pi * ∑ e : E, p e

def physicalCurvature (s : Incidence T E) (p : E → ℝ) : E → ℝ :=
  curvature s (fun e => Real.cosh (p e))

def globalGenuine (s : Incidence T E) : Set (E → ℝ) :=
  {p | ∀ t : T, genuine (localRead s t p)}

theorem occurrence_angle (s : Incidence T E) (p : E → ℝ) (o : T × Fin 6) :
    sourceAngle (localRead s o.1 p) o.2 =
      angle s (fun e => Real.cosh (p e)) o := by
  rfl

theorem occurrence_regroup
    (s : Incidence T E) (F : T × Fin 6 → ℝ) (v : E → ℝ) :
    (∑ t : T, ∑ q : Fin 6, F (t,q) * v (s.edge t q)) =
      ∑ e : E, (∑ o ∈ star s e, F o) * v e := by
  classical
  calc
    _ = ∑ o : T × Fin 6, F o * v (source s o) := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = ∑ e : E, ∑ o ∈ star s e, F o * v e := by
      symm
      calc
        _ = ∑ e : E, ∑ o ∈ star s e, F o * v (source s o) := by
          apply Finset.sum_congr rfl
          intro e _
          apply Finset.sum_congr rfl
          intro o ho
          rw [(Finset.mem_filter.mp ho).2]
        _ = _ := by
          simpa only [D5.S3.Geometry.Hyperideal.FourCycleCurvature.star] using
            Finset.sum_fiberwise (Finset.univ : Finset (T × Fin 6))
              (source s) (fun o => F o * v (source s o))
    _ = _ := by simp only [Finset.sum_mul]

theorem physicalEnergy_hasFDerivAt
    (s : Incidence T E) (G : RealizationFamily) (hG : realizedFamily G)
    (p : E → ℝ) (hp : p ∈ globalGenuine s) :
    HasFDerivAt (physicalEnergy s G)
      (∑ e : E, (-physicalCurvature s p e) •
        (ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ)) p := by
  classical
  have hlocal (t : T) :
      HasFDerivAt (fun a : E → ℝ => physicalCovolume G (localRead s t a))
        ((sourceDifferential (localRead s t p)).comp (localRead s t)) p := by
    exact ((physicalCovolume_contDiffOn_genuine G hG).2 _ (hp t)).comp p
      (localRead s t).hasFDerivAt
  have hsum : HasFDerivAt
      (fun a : E → ℝ => ∑ t : T, physicalCovolume G (localRead s t a))
      (∑ t : T, (sourceDifferential (localRead s t p)).comp (localRead s t)) p :=
    HasFDerivAt.fun_sum (fun t _ => hlocal t)
  have hlin : HasFDerivAt (fun a : E → ℝ => 2 * Real.pi * ∑ e : E, a e)
      ((2 * Real.pi) • ∑ e : E,
        (ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ)) p := by
    simpa only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.proj_apply] using
      (∑ e : E, (ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ)).hasFDerivAt.const_mul
        (2 * Real.pi)
  have hmap :
      (∑ t : T, (sourceDifferential (localRead s t p)).comp (localRead s t)) -
        (2 * Real.pi) • ∑ e : E, (ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ) =
      ∑ e : E, (-physicalCurvature s p e) •
        (ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ) := by
    ext v
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply,smul_eq_mul,sourceDifferential_apply]
    have hg := occurrence_regroup s
      (fun o => angle s (fun e => Real.cosh (p e)) o) v
    have heq :
        (∑ t : T, ∑ q : Fin 6, sourceAngle (localRead s t p) q * localRead s t v q) =
        ∑ e : E, (∑ o ∈ star s e, angle s (fun e => Real.cosh (p e)) o) * v e := by
      convert hg using 1 <;> rfl
    rw [heq]
    simp only [physicalCurvature,curvature,neg_sub,sub_mul,Finset.sum_sub_distrib,
      Finset.mul_sum]
  rw [← hmap]
  exact hsum.sub hlin

theorem physicalEnergy_smoothOn
    (s : Incidence T E) (G : RealizationFamily) (hG : realizedFamily G) :
    ContDiffOn ℝ ∞ (physicalEnergy s G) (globalGenuine s) := by
  classical
  have hlocal (t : T) : ContDiffOn ℝ ∞
      (fun p : E → ℝ => physicalCovolume G (localRead s t p)) (globalGenuine s) := by
    exact (CFMPActualPhysicalHessian258Transient.physicalCovolume_smoothOn G hG).comp
      (localRead s t).contDiff.contDiffOn (fun p hp => hp t)
  have hsum : ContDiffOn ℝ ∞
      (fun p : E → ℝ => ∑ t : T, physicalCovolume G (localRead s t p))
      (globalGenuine s) := ContDiffOn.sum (fun t _ => hlocal t)
  have hlin : ContDiffOn ℝ ∞ (fun p : E → ℝ => 2 * Real.pi * ∑ e : E, p e)
      (globalGenuine s) := by
    fun_prop
  exact hsum.sub hlin

theorem physicalEnergy_choice_independent
    (s : Incidence T E) (F G : RealizationFamily)
    (hF : realizedFamily F) (hG : realizedFamily G)
    (p : E → ℝ) (hp : p ∈ globalGenuine s) :
    physicalEnergy s F p = physicalEnergy s G p := by
  unfold physicalEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  exact physicalCovolume_choice_independent F G hF hG _ (hp t)

theorem physicalEnergy_multiplicative_dissipation
    (s : Incidence T E) (G : RealizationFamily) (hG : realizedFamily G)
    (l : ℝ → E → ℝ) (t : ℝ) (hlt : l t ∈ globalGenuine s)
    (hl : HasDerivAt l (fun e => l t e * physicalCurvature s (l t) e) t) :
    HasDerivAt (fun r => physicalEnergy s G (l r))
      (-∑ e : E, l t e * (physicalCurvature s (l t) e)^2) t := by
  have hd := (physicalEnergy_hasFDerivAt s G hG (l t) hlt).comp_hasDerivAt t hl
  convert! hd using 1
  try simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,neg_mul,Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem physicalEnergy_degree_normalized_dissipation
    (s : Incidence T E) (G : RealizationFamily) (hG : realizedFamily G)
    (l : ℝ → E → ℝ) (t : ℝ) (hlt : l t ∈ globalGenuine s)
    (hl : HasDerivAt l (fun e => physicalCurvature s (l t) e / (degree s e : ℝ)) t) :
    HasDerivAt (fun r => physicalEnergy s G (l r))
      (-∑ e : E, (physicalCurvature s (l t) e)^2 / (degree s e : ℝ)) t := by
  have hd := (physicalEnergy_hasFDerivAt s G hG (l t) hlt).comp_hasDerivAt t hl
  convert! hd using 1
  try simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,neg_mul,Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  ring

end CFMPActualGlobalEnergy259Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualGlobalEnergy259Transient.physicalEnergy_hasFDerivAt,
      ``CFMPActualGlobalEnergy259Transient.physicalEnergy_smoothOn,
      ``CFMPActualGlobalEnergy259Transient.physicalEnergy_choice_independent,
      ``CFMPActualGlobalEnergy259Transient.physicalEnergy_multiplicative_dissipation,
      ``CFMPActualGlobalEnergy259Transient.physicalEnergy_degree_normalized_dissipation] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP259 actual global energy theorem absent from checked environment: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP259 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP259 CHECKED {name} axioms={axioms}"
