/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateGhost
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateGhost
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An unused all-ones state preserves the actual visible law and supports a null-word rectangle. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStatePresentation
import Mathlib.MeasureTheory.Constructions.Projective

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Function
open scoped BigOperators Matrix Classical
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open MarkedPredictiveQuotient OriginalMarkedLaw OriginalLawTrimming TwelveStatePresentation

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateGhost

instance : MeasurableSpace (Option Hidden) := ⊤
instance : MeasurableSingletonClass (Option Hidden) := ⟨fun _ => trivial⟩

/-- None is the unused all-ones ghost; every original state is retained as some i. -/
def ghostMatrix (x : Bool) : Matrix (Option Hidden) (Option Hidden) ℝ
  | some i, some j => marked x i j
  | none, none => if x then 1 else 0
  | _, _ => 0

def ghostMass : Option Hidden → ℝ
  | some i => mass i
  | none => 0

/-- The exact thirteen-state padding of the original twelve-state parameter. -/
def parameter : Presentation (Option Hidden) where
  initial := ghostMass
  matrix := ghostMatrix
  initial_nonneg i := by
    cases i with
    | none => exact le_rfl
    | some i => exact TwelveStatePresentation.parameter.initial_nonneg i
  initial_sum := by simpa [TwelveStatePresentation.parameter,ghostMass,Fintype.sum_option] using TwelveStatePresentation.parameter.initial_sum
  matrix_nonneg x i j := by
    cases i with
    | none => cases j <;> cases x <;> norm_num [ghostMatrix]
    | some i =>
      cases j with
      | none => exact le_rfl
      | some j => exact TwelveStatePresentation.parameter.matrix_nonneg x i j
  stochastic i := by
    cases i with
    | none => norm_num [ghostMatrix,Fintype.sum_option]
    | some i => simpa [TwelveStatePresentation.parameter,ghostMatrix,Fintype.sum_option,← Finset.sum_add_distrib] using
        TwelveStatePresentation.parameter.stochastic i
  stationary j := by
    cases j with
    | none => simp [ghostMass,ghostMatrix,Fintype.sum_option]
    | some j => simpa [TwelveStatePresentation.parameter,ghostMass,ghostMatrix,Fintype.sum_option] using
        TwelveStatePresentation.parameter.stationary j
  no11 := by
    simpa [TwelveStatePresentation.parameter,ghostMass,ghostMatrix,Matrix.mul_apply,Fintype.sum_option] using
      TwelveStatePresentation.parameter.no11

private theorem word_blocks (n : ℕ) (w : Fin n → Bool) :
    (∀ i j, wordMatrix ghostMatrix n w (some i) (some j) = wordMatrix marked n w i j) ∧
    (∀ i, wordMatrix ghostMatrix n w (some i) none = 0) ∧
    (∀ j, wordMatrix ghostMatrix n w none (some j) = 0) ∧
    wordMatrix ghostMatrix n w none none = if ∀ k, w k = true then 1 else 0 := by
  induction n with
  | zero => simp [wordMatrix,Matrix.one_apply]
  | succ n ih =>
    obtain ⟨hss,hsn,hns,hnn⟩ := ih (Fin.tail w)
    simp only [wordMatrix,Matrix.mul_apply,Fintype.sum_option,ghostMatrix]
    refine ⟨?_,?_,?_,?_⟩
    · intro i j
      simp only [hss,hns,mul_zero,zero_add]
    · intro i
      simp [hsn]
    · intro j
      simp [hns]
    · rw [hnn]
      have he : (∀ k : Fin (n+1), w k = true) ↔ w 0 = true ∧ ∀ k, Fin.tail w k = true := by
        exact Fin.forall_fin_succ
      simp only [he]
      cases hb : w 0 <;> simp [hb]

private theorem future_blocks (n : ℕ) (w : Fin n → Bool) (i : Hidden) :
    futureMass ghostMatrix (some i) n w = futureMass marked i n w := by
  simp only [futureMass,Fintype.sum_option,(word_blocks n w).1,
    (word_blocks n w).2.1,zero_add]

private theorem cylinder_masses (t : ℤ) (n : ℕ) (w : Fin n → Bool) :
    (visibleLaw parameter : Measure _).real (visibleCylinder t n w) =
      (visible : Measure _).real (visibleCylinder t n w) := by
  have hghost := visible_masses parameter (jointLaw parameter : Measure _)
    (same_law_trimming parameter).1 t n w
  have hbase := visible_masses TwelveStatePresentation.parameter
    (joint : Measure _) (same_law_trimming TwelveStatePresentation.parameter).1 t n w
  change (visibleLaw parameter : Measure _).real (visibleCylinder t n w) = _ at hghost
  change (visible : Measure _).real (visibleCylinder t n w) = _ at hbase
  rw [hghost,hbase]
  change (∑ i : Option Hidden, ghostMass i * futureMass ghostMatrix i n w) = _
  simp only [Fintype.sum_option,ghostMass,zero_mul,zero_add,future_blocks]
  rfl

/-- Equality of all original integer-origin finite output cylinders determines the
complete bilateral output measure. This helper is consumed by the ghost and trimming results. -/
theorem visible_eq_of_cylinders (μ ν : Measure (ℤ → Bool)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hc : ∀ (t : ℤ) (n : ℕ) (w : Fin n → Bool),
      μ.real (visibleCylinder t n w) = ν.real (visibleCylinder t n w)) : μ = ν := by
  let P := fun I : Finset ℤ => ν.map I.restrict
  haveI : ∀ I, IsFiniteMeasure (P I) := fun I => Measure.isFiniteMeasure_map _ _
  apply IsProjectiveLimit.unique (P := P) ?_ (fun I => rfl)
  intro I
  let n : ℕ := I.sup Int.natAbs
  let window : (ℤ → Bool) → (Fin (2*n+1) → Bool) := fun z k => z (-(n : ℤ)+k.val)
  let select : (Fin (2*n+1) → Bool) → ((i : I) → Bool) := fun w i =>
    w ⟨(i.val+(n : ℤ)).toNat,by
      have h := Finset.le_sup (f := Int.natAbs) i.property
      have hab := Int.natAbs_eq i.val
      omega⟩
  have he : I.restrict = select ∘ window := by
    funext z i
    have h := Finset.le_sup (f := Int.natAbs) i.property
    have hab := Int.natAbs_eq i.val
    change z i.val = z (-(n : ℤ) + ((i.val+(n : ℤ)).toNat : ℤ))
    congr 1
    omega
  have hwin : μ.map window = ν.map window := by
    apply Measure.ext_of_singleton
    intro w
    have hm : Measurable window := by fun_prop
    rw [Measure.map_apply hm (measurableSet_singleton w),
      Measure.map_apply hm (measurableSet_singleton w)]
    have hew : window ⁻¹' {w} = visibleCylinder (-(n : ℤ)) (2*n+1) w := by
      ext z
      simp [window,visibleCylinder,funext_iff]
    rw [hew]
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
      (hc (-(n : ℤ)) (2*n+1) w)
  rw [he,← Measure.map_map (by fun_prop : Measurable select) (by fun_prop : Measurable window),
    hwin,Measure.map_map (by fun_prop : Measurable select) (by fun_prop : Measurable window)]
  exact congrArg (fun f => ν.map f) he.symm

private theorem visible_eq : (visibleLaw parameter : Measure (ℤ → Bool)) = visible :=
  visible_eq_of_cylinders _ _ cylinder_masses

/-- The unused state preserves the whole original visible law, although the illegal word 11
has zero actual mass and its nonzero product has exactly the positive singleton ghost support. -/
theorem actual_ghost_counterexample :
    Fintype.card (Option Hidden) = 13 ∧
    (visibleLaw parameter : Measure (ℤ → Bool)) = visible ∧
    (∀ t : ℤ, (visibleLaw parameter : Measure _).real
      (visibleCylinder t 2 (fun _ => true)) = 0) ∧
    (∀ i j : Option Hidden, (ghostMatrix true * ghostMatrix true) i j =
      if i = none ∧ j = none then 1 else 0) := by
  refine ⟨by decide,visible_eq,?_,?_⟩
  · intro t
    have hp := (actual_visible_support t 2 (fun _ => true))
    have hn : ¬ Legal 2 (fun _ => true) := by simp [Legal,Allowed,Fin.tail]
    exact le_antisymm (le_of_not_gt fun h => hn (hp.mp (by rwa [cylinder_masses] at h)))
      ENNReal.toReal_nonneg
  · intro i j
    cases i with
    | none => cases j <;> simp [ghostMatrix,Matrix.mul_apply,Fintype.sum_option]
    | some i =>
      cases j with
      | none => simp [ghostMatrix,Matrix.mul_apply,Fintype.sum_option]
      | some j =>
        change _ = 0
        simp only [ghostMatrix,Matrix.mul_apply,Fintype.sum_option,mul_zero,zero_add]
        simp only [marked,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
        simp [next,prob]

#print axioms actual_ghost_counterexample
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateGhost
