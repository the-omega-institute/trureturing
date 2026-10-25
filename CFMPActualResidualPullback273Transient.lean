import CFMPActualFlatNeighborhood272Transient
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology ContDiff
open CFMPOriginalCovolumeNeighborhood251Transient
open CFMPOriginalCovolumeC1253Transient (sourceDifferential)
open CFMPGlobalGenuineCovolume256Transient
open CFMPGenuineLengthNeighborhood435Transient (genuine genuine_open)
open CFMPActualExtendedAngle268Transient
open CFMPActualFlatCoordinates271Transient

namespace CFMPActualResidualPullback273Transient

def basePositive : Set Chart := {p | ∀ j, 0 < p.1 j}

/-- Pull back the actual six-angle covector after subtracting the affine
primitive of this same native flat sector. -/
def residual (k : Fin 3) (p : Chart) : Chart →L[ℝ] ℝ :=
  (sourceDifferential (unflatten (k.castAdd 3) p) - flatDifferential k).comp
    (fderiv ℝ (unflatten (k.castAdd 3)) p)

def chartEnergy (G : RealizationFamily) (k : Fin 3) (p : Chart) : ℝ :=
  physicalCovolume G (unflatten (k.castAdd 3) p) -
    flatPrimitive k (unflatten (k.castAdd 3) p)

theorem basePositive_open : IsOpen basePositive := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  exact Filter.eventually_all.mpr (fun j =>
    ((continuous_apply j).comp continuous_fst).continuousAt.eventually (Ioi_mem_nhds (hp j)))

theorem residual_continuousAt (k : Fin 3) (p : Chart) (hp : p ∈ basePositive)
    (hh : 0 < p.2 + CFMPActualFlatGraph269Transient.lengthThreshold p.1) :
    ContinuousAt (residual k) p := by
  have hφ := unflatten_contDiffAt (k.castAdd 3) p hp
  have hsource := sourceDifferential_continuousAt_positive
    (unflatten (k.castAdd 3) p) (unflatten_positive _ p hp hh)
  exact ((hsource.comp hφ.continuousAt).sub continuousAt_const).clm_comp
    (hφ.continuousAt_fderiv (by simp))

theorem residual_zero_nonneg (k : Fin 3) (p : Chart) (hp : p ∈ basePositive)
    (hh : 0 < p.2 + CFMPActualFlatGraph269Transient.lengthThreshold p.1)
    (hr : 0 ≤ p.2) : residual k p = 0 := by
  have hsector := (native_sector_iff_nonneg k p hp hh).mpr hr
  simp only [residual, sourceDifferential_eq_flat _ (unflatten_positive _ p hp hh) k hsector,
    sub_self, ContinuousLinearMap.zero_comp]

theorem residual_smoothAt_genuine (k : Fin 3) (p : Chart) (hp : p ∈ basePositive)
    (hg : genuine (unflatten (k.castAdd 3) p)) :
    ContDiffAt ℝ ∞ (residual k) p := by
  have hφ := unflatten_contDiffAt (k.castAdd 3) p hp
  have hsource : ContDiffAt ℝ ∞ sourceDifferential (unflatten (k.castAdd 3) p) :=
    (CFMPActualPhysicalHessian258Transient.sourceDifferential_smoothOn _ hg).contDiffAt
      (genuine_open.mem_nhds hg)
  exact ((hsource.comp p hφ).sub contDiffAt_const).clm_comp
    (hφ.fderiv_right (m := ∞) (by simp))

/-- The primitive used on the genuine side is the same physical covolume,
composed with the actual chart and with its flat affine part subtracted. -/
theorem chartEnergy_hasFDerivAt (G : RealizationFamily) (hG : realizedFamily G)
    (k : Fin 3) (p : Chart) (hp : p ∈ basePositive)
    (hg : genuine (unflatten (k.castAdd 3) p)) :
    HasFDerivAt (chartEnergy G k) (residual k p) p := by
  have hφ := (unflatten_contDiffAt (k.castAdd 3) p hp).differentiableAt (by simp)
  have hphysical := (physicalCovolume_contDiffOn_genuine G hG).2 _ hg
  have hflat := flatPrimitive_hasFDerivAt k (unflatten (k.castAdd 3) p)
  exact (hphysical.sub hflat).comp p hφ.hasFDerivAt

theorem residual_hasFDerivAt_genuine (k : Fin 3) (p : Chart) (hp : p ∈ basePositive)
    (hg : genuine (unflatten (k.castAdd 3) p)) :
    HasFDerivAt (residual k) (fderiv ℝ (residual k) p) p :=
  ((residual_smoothAt_genuine k p hp hg).differentiableAt (by simp)).hasFDerivAt

theorem residual_derivative_symmetric (k : Fin 3) (p : Chart) (hp : p ∈ basePositive)
    (hg : genuine (unflatten (k.castAdd 3) p)) (v w : Chart) :
    fderiv ℝ (residual k) p v w = fderiv ℝ (residual k) p w v := by
  have hφ := (unflatten_contDiffAt (k.castAdd 3) p hp).continuousAt
  have hgen : ∀ᶠ q in 𝓝 p, genuine (unflatten (k.castAdd 3) q) :=
    hφ.eventually (genuine_open.mem_nhds hg)
  have hgradient : ∀ᶠ q in 𝓝 p,
      HasFDerivAt (chartEnergy wholeFamily k) (residual k q) q := by
    filter_upwards [basePositive_open.mem_nhds hp, hgen] with q hq hqg
    exact chartEnergy_hasFDerivAt wholeFamily wholeFamily_realized k q hq hqg
  exact second_derivative_symmetric_of_eventually hgradient
    (residual_hasFDerivAt_genuine k p hp hg) v w

end CFMPActualResidualPullback273Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualResidualPullback273Transient.residual_continuousAt,
      ``CFMPActualResidualPullback273Transient.residual_zero_nonneg,
      ``CFMPActualResidualPullback273Transient.chartEnergy_hasFDerivAt,
      ``CFMPActualResidualPullback273Transient.residual_derivative_symmetric] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP273 actual residual pullback absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP273 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP273 CHECKED {name} axioms={axioms}"
