import CFMPOriginalCovolumeNeighborhood251Transient
import CFMPContinuousLineDerivative252Transient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Matrix BigOperators Topology ContDiff ENNReal Matrix.Norms.Elementwise
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPAnchoredSmoothFrame435Transient
open CFMPOriginalPhysicalEdge237Transient
open CFMPOriginalCovolumeNeighborhood251Transient

namespace CFMPOriginalCovolumeC1253Transient

def sourceDifferential (a : Lengths) : Lengths →L[ℝ] ℝ :=
  ∑ q : Fin 6, sourceAngle a q • (ContinuousLinearMap.proj q : Lengths →L[ℝ] ℝ)

theorem sourceDifferential_apply (a v : Lengths) :
    sourceDifferential a v = ∑ q : Fin 6, sourceAngle a q * v q := by
  simp [sourceDifferential]

theorem sourceDifferential_continuousOn
    (U : Set Lengths)
    (hg : ∀ a ∈ U, CFMPGenuineLengthNeighborhood435Transient.genuine a) :
    ContinuousOn sourceDifferential U := by
  unfold sourceDifferential
  apply continuousOn_finsetSum
  intro q _
  have hc : ContinuousOn (fun a : Lengths => sourceAngle a q) U := by
    intro a ha
    have hcos := CFMPGenuineLengthNeighborhood435Transient.sourceCosine_continuousAt
      a (hg a ha).1 q
    have hangle : ContinuousAt (fun b : Lengths => sourceAngle b q) a := by
      exact Real.continuous_arccos.continuousAt.comp hcos
    exact hangle.continuousWithinAt
  exact hc.smul continuousOn_const

theorem same_family_covolume_contDiffOn
    (U : Set Lengths) (G : RealizationFamily) (hU : IsOpen U)
    (hg : ∀ a ∈ U, CFMPGenuineLengthNeighborhood435Transient.genuine a)
    (hpaths : ∀ (l : ℝ → Lengths) (dl : Lengths) (t : ℝ),
      ContDiffAt ℝ 1 l t → HasDerivAt l dl t → l t ∈ U →
      HasDerivAt (fun s => physicalCovolume G (l s))
        (∑ q : Fin 6, sourceAngle (l t) q * dl q) t) :
    ContDiffOn ℝ 1 (physicalCovolume G) U ∧
      ∀ a ∈ U, HasFDerivAt (physicalCovolume G) (sourceDifferential a) a := by
  have hline (a v : Lengths) (t : ℝ) (ht : a + t • v ∈ U) :
      HasDerivAt (fun s : ℝ => physicalCovolume G (a + s • v))
        (sourceDifferential (a + t • v) v) t := by
    have hsm : ContDiffAt ℝ 1 (fun s : ℝ => a + s • v) t := by
      fun_prop
    have hd : HasDerivAt (fun s : ℝ => a + s • v) v t := by
      convert! ((hasDerivAt_id t).smul_const v).const_add a using 1 <;>
        simp only [one_smul, id_eq]
    simpa only [sourceDifferential_apply] using
      hpaths (fun s => a + s • v) v t hsm hd ht
  exact CFMPContinuousLineDerivative252Transient.contDiffOn_one_of_continuous_line_field
    hU hline (sourceDifferential_continuousOn U hg)

theorem exists_original_covolume_C1_neighborhood
    (l0 : Lengths) (hl0 : ∀ i, 0 < l0 i)
    (M0 : Matrix (Fin 4) (Fin 4) ℝ) (hm0 : M0.det ≠ 0)
    (hg0 : M0 * J * M0.transpose = lengthGram l0)
    (f : cutBody l0 → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Fin 4 → ℝ, y = (radial l0 w.val) ᵥ* M0 ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (hgen : CFMPGenuineLengthNeighborhood435Transient.genuine l0) :
    ∃ (U : Set Lengths) (G : RealizationFamily),
      l0 ∈ U ∧ IsOpen U ∧
      (∀ a ∈ U, CFMPGenuineLengthNeighborhood435Transient.genuine a) ∧
      ContDiffOn ℝ ∞ (frame M0) U ∧ frame M0 l0 = M0 ∧ G l0 = f ∧
      (∀ a ∈ U, realizationContract M0 G a) ∧
      ContDiffOn ℝ 1 (physicalCovolume G) U ∧
      ∀ a ∈ U, HasFDerivAt (physicalCovolume G) (sourceDifferential a) a := by
  obtain ⟨U,G,h0,hU,hgenU,hsm,hanchor,hfanchor,hgeom,hpaths⟩ :=
    exists_original_covolume_neighborhood l0 hl0 M0 hm0 hg0 f hf hgen
  have hc := same_family_covolume_contDiffOn U G hU hgenU hpaths
  exact ⟨U,G,h0,hU,hgenU,hsm,hanchor,hfanchor,hgeom,hc.1,hc.2⟩

end CFMPOriginalCovolumeC1253Transient

run_cmd do
  let name := ``CFMPOriginalCovolumeC1253Transient.exists_original_covolume_C1_neighborhood
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP253 actual C1 covolume absent from checked environment"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP253 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP253 CHECKED {name} axioms={axioms}"
