/- GID: D5/S3/Estimation/DecisionRisk/StochasticDescentLumpability
   generality: G
   mirror-B: D5/B/S3/Estimation/DecisionRisk/StochasticDescentLumpability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Zero defect characterizes strong lumpability and yields an exact quotient kernel. -/

import D5.S3.Estimation.DecisionRisk.DescentDefectBounds

/- Library-search audit trail (2026-08-25):
   * `rg -n -F 'descent_defect_zero_iff_strongly_lumpable' D5
     Golden/Frozen/accepted` had no hits.
   * `rg -n -i 'lumpab|StronglyLumpable|strongly_lumpable' D5
     Golden/Frozen/accepted` had no hits, public or private.
   * All five existing `D5/S3/Estimation/DecisionRisk` digests were read. They concern
     descent-error bounds, experiment/posterior separation, Bayes-risk floors, Blackwell
     garbling, and posterior sufficiency; none states zero defect iff strong lumpability.
   * `D5.S3.TotalVariation.Metric.total_variation_eq_zero_iff` publicly proves separation for
     arbitrary finite real functions, so the forward implication reuses it directly.
   * The reverse implication uses only `Finset.sup'_le`, diagonal nonemptiness of the finite
     supremum, and `totalVariation p p = 0`; no stochasticity assumption is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.DecisionRisk.StochasticDescentLumpability

open D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.Pinsker

/-- A kernel is strongly lumpable along `q` when its rows are constant on every fiber of `q`. -/
def StronglyLumpable {X B : Type*} (q : X -> B) (K : X -> B -> Real) : Prop :=
  forall x y, q x = q y -> K x = K y

/-- An exact quotient kernel reproduces every source row through the readout map. -/
def ExactQuotientKernel {X B : Type*} (q : X -> B) (K : X -> B -> Real) : Prop :=
  exists Kbar : B -> B -> Real, forall x, K x = Kbar (q x)

/-- The finite same-fiber descent defect vanishes exactly for strongly lumpable kernels. -/
theorem descent_defect_zero_iff_strongly_lumpable
    {X B : Type*} [Fintype X] [Nonempty X] [Fintype B]
    (q : X -> B) (K : X -> B -> Real) :
    descentDefect q K = 0 <-> StronglyLumpable q K := by
  classical
  constructor
  · intro hzero x y hfiber
    apply (total_variation_eq_zero_iff (K x) (K y)).mp
    have hrow_le : totalVariation (K x) (K y) <= descentDefect q K := by
      unfold descentDefect
      have hpair :=
        Finset.le_sup'
          (fun pair : X × X =>
            if q pair.1 = q pair.2 then totalVariation (K pair.1) (K pair.2) else 0)
          (Finset.mem_univ (x, y))
      calc
        totalVariation (K x) (K y) =
            (if q (x, y).1 = q (x, y).2 then
              totalVariation (K (x, y).1) (K (x, y).2) else 0) := by
          rw [if_pos hfiber]
        _ ≤ descentDefect q K := hpair
    exact le_antisymm (hzero ▸ hrow_le) (total_variation_nonneg (K x) (K y))
  · intro hlump
    unfold descentDefect
    apply le_antisymm
    · apply Finset.sup'_le
      intro pair _
      by_cases hfiber : q pair.1 = q pair.2
      · rw [if_pos hfiber, hlump pair.1 pair.2 hfiber]
        simp [totalVariation]
      · simp [hfiber]
    · let x : X := Classical.choice (inferInstance : Nonempty X)
      have hdiag :=
        Finset.le_sup'
          (fun pair : X × X =>
            if q pair.1 = q pair.2 then totalVariation (K pair.1) (K pair.2) else 0)
          (Finset.mem_univ (x, x))
      calc
        0 = (if q (x, x).1 = q (x, x).2 then
              totalVariation (K (x, x).1) (K (x, x).2) else 0) := by
          rw [if_pos rfl]
          simp [totalVariation]
        _ ≤ Finset.univ.sup' ⟨(x, x), Finset.mem_univ _⟩
            (fun pair : X × X =>
              if q pair.1 = q pair.2 then
                totalVariation (K pair.1) (K pair.2) else 0) := hdiag

/-- Fiberwise row equality is equivalent to factorization through an exact quotient kernel. -/
theorem strongly_lumpable_iff_exact_quotient_kernel
    {X B : Type*} (q : X -> B) (K : X -> B -> Real) :
    StronglyLumpable q K <-> ExactQuotientKernel q K := by
  classical
  constructor
  · intro hlump
    let Kbar : B -> B -> Real := fun b =>
      if hexists : exists x, q x = b then
        K (Classical.choose hexists)
      else fun _ => 0
    refine ⟨Kbar, ?_⟩
    intro x
    have hexists : exists y, q y = q x := ⟨x, rfl⟩
    rw [show Kbar (q x) = K (Classical.choose hexists) by simp [Kbar, hexists]]
    exact hlump x (Classical.choose hexists) (Classical.choose_spec hexists).symm
  · rintro ⟨Kbar, hexact⟩ x y hfiber
    rw [hexact x, hexact y, hfiber]

/-- An exact quotient kernel has zero uniform descent error. -/
theorem uniform_descent_error_eq_zero_of_exact_quotient_kernel
    {X B : Type*} [Fintype X] [Nonempty X] [Fintype B]
    (q : X -> B) (K : X -> B -> Real) (Kbar : B -> B -> Real)
    (hexact : forall x, K x = Kbar (q x)) :
    uniformDescentError q K Kbar = 0 := by
  classical
  unfold uniformDescentError
  apply le_antisymm
  · apply Finset.sup'_le
    intro x _
    rw [hexact x]
    simp [totalVariation]
  · let x : X := Classical.choice (inferInstance : Nonempty X)
    have hrow :=
      Finset.le_sup'
        (fun y : X => totalVariation (K y) (Kbar (q y)))
        (Finset.mem_univ x)
    calc
      0 = totalVariation (K x) (Kbar (q x)) := by
        rw [hexact x]
        simp [totalVariation]
      _ ≤ Finset.univ.sup' ⟨x, Finset.mem_univ _⟩
          (fun y : X => totalVariation (K y) (Kbar (q y))) := hrow

/-- A strongly lumpable kernel admits an exact quotient with zero uniform descent error. -/
theorem strongly_lumpable_has_zero_uniform_descent_error
    {X B : Type*} [Fintype X] [Nonempty X] [Fintype B]
    (q : X -> B) (K : X -> B -> Real) (hlump : StronglyLumpable q K) :
    exists Kbar : B -> B -> Real,
      (forall x, K x = Kbar (q x)) /\ uniformDescentError q K Kbar = 0 := by
  rcases (strongly_lumpable_iff_exact_quotient_kernel q K).mp hlump with
    ⟨Kbar, hexact⟩
  exact ⟨Kbar, hexact, uniform_descent_error_eq_zero_of_exact_quotient_kernel
    q K Kbar hexact⟩

/-- At zero defect, the general half-defect lower bound becomes nonnegativity. -/
theorem best_descent_error_nonneg_of_zero_defect
    {X B : Type*} [Fintype X] [Nonempty X] [Fintype B]
    (q : X -> B) (K : X -> B -> Real) (hK : IsRowStochastic K)
    (hzero : descentDefect q K = 0) :
    0 <= bestDescentError q K := by
  simpa [hzero] using best_descent_error_lower_bound q K hK

example :
    descentDefect (fun _ : Bool => false) (fun _ _ : Bool => (0 : Real)) = 0 := by
  apply (descent_defect_zero_iff_strongly_lumpable _ _).2
  intro x y _
  rfl

#print axioms descent_defect_zero_iff_strongly_lumpable

end D5.S3.Estimation.DecisionRisk.StochasticDescentLumpability
