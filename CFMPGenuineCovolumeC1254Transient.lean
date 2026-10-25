import CFMPOriginalCovolumeC1253Transient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Matrix BigOperators Topology ContDiff ENNReal Matrix.Norms.Elementwise
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPAnchoredSmoothFrame435Transient
open CFMPOriginalCovolumeNeighborhood251Transient
open CFMPOriginalCovolumeC1253Transient

namespace CFMPGenuineCovolumeC1254Transient

/-- Every genuine original length vector has a neighborhood carrying an actual
radial realization family whose normalized physical covolume has the source
angle differential. The base frame and realization are constructed. -/
theorem exists_genuine_physical_covolume_C1
    (l0 : Lengths) (hg : CFMPGenuineLengthNeighborhood435Transient.genuine l0) :
    ∃ (M0 : Matrix (Fin 4) (Fin 4) ℝ) (U : Set Lengths) (G : RealizationFamily),
      0 < M0.det ∧ l0 ∈ U ∧ IsOpen U ∧
      (∀ a ∈ U, CFMPGenuineLengthNeighborhood435Transient.genuine a) ∧
      ContDiffOn ℝ ∞ (frame M0) U ∧ frame M0 l0 = M0 ∧
      (∀ a ∈ U, realizationContract M0 G a) ∧
      ContDiffOn ℝ 1 (physicalCovolume G) U ∧
      ∀ a ∈ U, HasFDerivAt (physicalCovolume G) (sourceDifferential a) a := by
  have hc : -1 < cosine (Real.cosh (l0 0)) (Real.cosh (l0 1)) (Real.cosh (l0 2))
      (Real.cosh (l0 3)) (Real.cosh (l0 4)) (Real.cosh (l0 5)) ∧
      cosine (Real.cosh (l0 0)) (Real.cosh (l0 1)) (Real.cosh (l0 2))
        (Real.cosh (l0 3)) (Real.cosh (l0 4)) (Real.cosh (l0 5)) < 1 := by
    convert hg.2 0 using 1 <;> rfl
  obtain ⟨M,hrows,hdet,_,f,_,_,_,_,hf⟩ :=
    (shared_radial_body l0 hg.1).2.2.2.2.2.2.2.2.2 hc
  have hGram : M * J * M.transpose = lengthGram l0 := by
    ext i j
    simpa [J,Matrix.mul_apply,lorentz,Fin.sum_univ_four] using hrows i j
  obtain ⟨U,G,h0,hU,hgenU,hsm,hanchor,_,hgeom,hC1,hd⟩ :=
    exists_original_covolume_C1_neighborhood l0 hg.1 M hdet.ne' hGram f hf hg
  exact ⟨M,U,G,hdet,h0,hU,hgenU,hsm,hanchor,hgeom,hC1,hd⟩

end CFMPGenuineCovolumeC1254Transient

run_cmd do
  let name := ``CFMPGenuineCovolumeC1254Transient.exists_genuine_physical_covolume_C1
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP254 genuine physical C1 covolume absent from checked environment"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP254 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP254 CHECKED {name} axioms={axioms}"
