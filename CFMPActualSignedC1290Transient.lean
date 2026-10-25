import CFMPActualClosedOrthant289Transient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped BigOperators Topology ContDiff
open CFMPOriginalCovolumeNeighborhood251Transient (Lengths)
open CFMPOriginalPhysicalEdge237Transient (sourceAngle)
open CFMPOriginalCovolumeC1253Transient (sourceDifferential sourceDifferential_apply)
open CFMPActualZeroAngle288Transient
open CFMPActualClosedOrthant289Transient (nonnegativeLengths)

namespace CFMPActualSignedC1290Transient

/-- Closed sign quadrants overlap at all zero coordinates. -/
def quadrant (S : Finset (Fin 6)) : Set Lengths :=
  {a | ∀ q, if q ∈ S then 0 ≤ a q else a q ≤ 0}

def mask (S : Finset (Fin 6)) : Lengths →L[ℝ] Lengths :=
  ContinuousLinearMap.pi (fun q =>
    if q ∈ S then (ContinuousLinearMap.proj q : Lengths →L[ℝ] ℝ) else 0)

theorem mask_apply (S : Finset (Fin 6)) (a : Lengths) (q : Fin 6) :
    mask S a q = if q ∈ S then a q else 0 := by
  by_cases hq : q ∈ S <;> simp [mask,hq]

theorem quadrant_closed (S : Finset (Fin 6)) : IsClosed (quadrant S) := by
  have heq : quadrant S = ⋂ q : Fin 6,
      {a : Lengths | if q ∈ S then 0 ≤ a q else a q ≤ 0} := by
    ext a
    simp [quadrant]
  rw [heq]
  apply isClosed_iInter
  intro q
  by_cases hq : q ∈ S
  · simpa only [hq,ite_true] using isClosed_le continuous_const (continuous_apply q)
  · simpa only [hq,ite_false] using isClosed_le (continuous_apply q) continuous_const

theorem positivePart_eq_mask (S : Finset (Fin 6)) (a : Lengths) (ha : a ∈ quadrant S) :
    positivePart a = mask S a := by
  funext q
  rw [mask_apply]
  by_cases hq : q ∈ S
  · have h := ha q
    simp only [hq,ite_true] at h ⊢
    exact max_eq_right h
  · have h := ha q
    simp only [hq,ite_false] at h ⊢
    exact max_eq_left h

theorem mask_mapsTo_nonnegative (S : Finset (Fin 6)) :
    MapsTo (mask S) (quadrant S) nonnegativeLengths := by
  intro a ha q
  rw [← positivePart_eq_mask S a ha]
  exact le_max_left _ _

/-- Every omitted coordinate is zero at the masked point, so its original
angle coefficient is zero. This also handles all overlaps of quadrants. -/
theorem sourceDifferential_comp_mask (S : Finset (Fin 6)) (a : Lengths) :
    (sourceDifferential (mask S a)).comp (mask S) = sourceDifferential (mask S a) := by
  ext v
  rw [ContinuousLinearMap.comp_apply,sourceDifferential_apply,sourceDifferential_apply]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : q ∈ S
  · simp only [mask_apply,hq,ite_true]
  · have hz : mask S a q = 0 := by simp only [mask_apply,hq,ite_false]
    simp only [sourceAngle_eq_zero_of_zero _ q hz,zero_mul]

def positivePartExtension (g : Lengths → ℝ) (a : Lengths) : ℝ := g (positivePart a)

/-- Equal covectors on finitely many closed sign quadrants give the full
ambient derivative, including at their intersections. -/
theorem positivePartExtension_hasFDerivAt
    (g : Lengths → ℝ)
    (hg : ∀ a ∈ nonnegativeLengths,
      HasFDerivWithinAt g (sourceDifferential a) nonnegativeLengths a)
    (a : Lengths) :
    HasFDerivAt (positivePartExtension g) (extendedDifferential a) a := by
  classical
  have hquad (S : Finset (Fin 6)) :
      HasFDerivWithinAt (positivePartExtension g) (extendedDifferential a) (quadrant S) a := by
    by_cases ha : a ∈ quadrant S
    · have hmap := mask_mapsTo_nonnegative S
      have hcomp := (hg _ (hmap ha)).comp a (mask S).hasFDerivWithinAt hmap
      have hcovector : (sourceDifferential (mask S a)).comp (mask S) =
          extendedDifferential a := by
        rw [sourceDifferential_comp_mask,← positivePart_eq_mask S a ha]
        rfl
      apply (hcomp.congr_fderiv hcovector).congr' _ ha
      intro b hb
      exact congrArg g (positivePart_eq_mask S b hb)
    · exact HasFDerivWithinAt.of_notMem_closure
        (by simpa only [(quadrant_closed S).closure_eq] using ha)
  have hfinite (T : Finset (Finset (Fin 6))) :
      HasFDerivWithinAt (positivePartExtension g) (extendedDifferential a)
        (⋃ S ∈ T, quadrant S) a := by
    induction T using Finset.induction_on with
    | empty => simpa using
        (HasFDerivWithinAt.empty : HasFDerivWithinAt
          (positivePartExtension g) (extendedDifferential a) ∅ a)
    | @insert S T hST ih =>
        have heq : (⋃ R ∈ insert S T, quadrant R) = quadrant S ∪ (⋃ R ∈ T, quadrant R) := by
          ext b
          simp
        rw [heq]
        exact (hquad S).union ih
  have hcover : (⋃ S ∈ (Finset.univ : Finset (Finset (Fin 6))), quadrant S) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro b
    let S : Finset (Fin 6) := Finset.univ.filter (fun q => 0 ≤ b q)
    apply mem_iUnion.mpr
    refine ⟨S,mem_iUnion.mpr ⟨Finset.mem_univ S,?_⟩⟩
    intro q
    by_cases hq : 0 ≤ b q
    · simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and,hq,ite_true] using hq
    · simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and,hq,ite_false] using
        (le_of_not_ge hq)
  have hfull := hfinite Finset.univ
  rw [hcover] at hfull
  exact hfull.hasFDerivAt (by simp)

theorem positivePartExtension_contDiff
    (g : Lengths → ℝ)
    (hg : ∀ a ∈ nonnegativeLengths,
      HasFDerivWithinAt g (sourceDifferential a) nonnegativeLengths a) :
    ContDiff ℝ 1 (positivePartExtension g) :=
  contDiff_one_iff_hasFDerivAt.mpr
    ⟨extendedDifferential,extendedDifferential_continuous,
      positivePartExtension_hasFDerivAt g hg⟩

end CFMPActualSignedC1290Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualSignedC1290Transient.sourceDifferential_comp_mask,
      ``CFMPActualSignedC1290Transient.positivePartExtension_hasFDerivAt,
      ``CFMPActualSignedC1290Transient.positivePartExtension_contDiff] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP290 signed actual C1 extension absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP290 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP290 CHECKED {name} axioms={axioms}"
