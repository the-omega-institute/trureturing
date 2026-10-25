import CFMPGlobalGenuineCovolume256Transient
import CFMPActualAnglePositive257Transient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Matrix BigOperators Topology ContDiff MatrixOrder
open CFMPOriginalPhysicalEdge237Transient (sourceAngle)
open CFMPGenuineLengthNeighborhood435Transient (genuine genuine_open)
open CFMPOriginalCovolumeNeighborhood251Transient
open CFMPOriginalCovolumeC1253Transient
open CFMPGlobalGenuineCovolume256Transient

namespace CFMPActualPhysicalHessian258Transient

def physicalHessian (G : RealizationFamily) (a : Lengths) : Matrix (Fin 6) (Fin 6) ℝ :=
  fun e f => fderiv ℝ
    (fun p : Lengths => fderiv ℝ (physicalCovolume G) p (Pi.single e 1)) a
    (Pi.single f 1)

theorem sourceDifferential_smoothOn :
    ContDiffOn ℝ ∞ sourceDifferential {a : Lengths | genuine a} := by
  unfold sourceDifferential
  apply ContDiffOn.sum
  intro q _
  intro a ha
  have hs : ContDiffAt ℝ ∞ (fun p : Lengths => sourceAngle p q) a :=
    CFMPOriginalGlobalSmoothCovolume103Transient.sourceAngle_smooth a ha q
  exact (hs.smul_const (ContinuousLinearMap.proj q : Lengths →L[ℝ] ℝ)).contDiffWithinAt

theorem physicalCovolume_smoothOn (G : RealizationFamily) (hG : realizedFamily G) :
    ContDiffOn ℝ ∞ (physicalCovolume G) {a : Lengths | genuine a} := by
  have hd := (physicalCovolume_contDiffOn_genuine G hG).2
  apply (contDiffOn_infty_iff_fderiv_of_isOpen genuine_open).2
  refine ⟨fun a ha => (hd a ha).differentiableAt.differentiableWithinAt,?_⟩
  exact sourceDifferential_smoothOn.congr (fun a ha => (hd a ha).fderiv)

theorem physical_gradient_coordinate
    (G : RealizationFamily) (hG : realizedFamily G)
    (a : Lengths) (ha : genuine a) (e : Fin 6) :
    fderiv ℝ (physicalCovolume G) a (Pi.single e 1) = sourceAngle a e := by
  rw [((physicalCovolume_contDiffOn_genuine G hG).2 a ha).fderiv]
  simp [sourceDifferential,Pi.single_apply]

theorem physicalHessian_eq_sourceJacobian
    (G : RealizationFamily) (hG : realizedFamily G)
    (a : Lengths) (ha : genuine a) :
    physicalHessian G a = fun e f : Fin 6 =>
      fderiv ℝ (fun p : Lengths => sourceAngle p e) a (Pi.single f 1) := by
  ext e f
  have heq : (fun p : Lengths => fderiv ℝ (physicalCovolume G) p (Pi.single e 1))
      =ᶠ[𝓝 a] (fun p : Lengths => sourceAngle p e) := by
    filter_upwards [genuine_open.mem_nhds ha] with p hp
    exact physical_gradient_coordinate G hG p hp e
  exact congrArg (fun L : Lengths →L[ℝ] ℝ => L (Pi.single f 1))
    (heq.fderiv_eq (𝕜 := ℝ))

theorem physicalHessian_posDef
    (G : RealizationFamily) (hG : realizedFamily G)
    (a : Lengths) (ha : genuine a) : Matrix.PosDef (physicalHessian G a) := by
  rw [physicalHessian_eq_sourceJacobian G hG a ha]
  exact CFMPActualJacobianPositive148.actualJacobian_posDef a ha

theorem exists_actual_smooth_positive_covolume :
    ∃ G : RealizationFamily, realizedFamily G ∧
      ContDiffOn ℝ ∞ (physicalCovolume G) {a : Lengths | genuine a} ∧
      (∀ a, genuine a → Matrix.PosDef (physicalHessian G a)) ∧
      (∀ F : RealizationFamily, realizedFamily F →
        ∀ a, genuine a → physicalCovolume F a = physicalCovolume G a) := by
  refine ⟨wholeFamily,wholeFamily_realized,
    physicalCovolume_smoothOn wholeFamily wholeFamily_realized,
    (fun a ha => physicalHessian_posDef wholeFamily wholeFamily_realized a ha),?_⟩
  intro F hF a ha
  exact physicalCovolume_choice_independent F wholeFamily hF wholeFamily_realized a ha

end CFMPActualPhysicalHessian258Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualPhysicalHessian258Transient.physicalCovolume_smoothOn,
      ``CFMPActualPhysicalHessian258Transient.physicalHessian_eq_sourceJacobian,
      ``CFMPActualPhysicalHessian258Transient.physicalHessian_posDef,
      ``CFMPActualPhysicalHessian258Transient.exists_actual_smooth_positive_covolume] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP258 actual physical theorem absent from checked environment: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP258 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP258 CHECKED {name} axioms={axioms}"
