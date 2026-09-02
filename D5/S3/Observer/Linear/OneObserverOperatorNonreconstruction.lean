/- GID: D5/S3/Observer/Linear/OneObserverOperatorNonreconstruction
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/OneObserverOperatorNonreconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One squared operator reading is reflection-invariant and cannot reconstruct direction. -/

import Mathlib

/- Library-search audit trail (2026-09-02):
   * D5 name and body-shape searches for a squared observer operator,
     reflection ambiguity, derivative recovery, and one-reading
     non-reconstruction found related observer results but no exact theorem or
     existing construction with body `(H - t I)^2`.
   * Pinned Mathlib searches found the component results
     `HasDerivAt.smul_const` and `HasDerivAt.unique`, plus the linear
     endomorphism ring operations, but no packaged theorem with these clauses.
   * Searches across the installed third-party Lean packages found no exact
     theorem or construction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Linear.OneObserverOperatorNonreconstruction

/-- The operator-valued squared-distance reading at observer position `t`,
constructed directly from the directed operator and the identity map. -/
def observerSquare {V : Type*} [AddCommGroup V] [Module Real V]
    (H : Module.End Real V) (t : Real) : Module.End Real V :=
  (H - t • LinearMap.id) ^ 2

/-- A single squared-distance operator reading is invariant under reflection
and cannot reconstruct every directed operator. The strong pointwise
derivative and any second noncoincident observer reading each recover the
direction explicitly. -/
theorem one_observer_operator_nonreconstruction
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V] [Nontrivial V]
    (t : Real) :
    (¬ ∃ reconstruct : Module.End Real V → Module.End Real V,
        ∀ H : Module.End Real V, reconstruct (observerSquare H t) = H) ∧
      (∀ H : Module.End Real V,
        observerSquare ((2 * t) • LinearMap.id - H) t = observerSquare H t) ∧
      (∀ H D : Module.End Real V,
        (∀ x : V, HasDerivAt (fun s : Real => observerSquare H s x) (D x) t) →
          D = (2 : Real) • (t • LinearMap.id - H) ∧
            t • LinearMap.id - (2 : Real)⁻¹ • D = H) ∧
      (∀ (H : Module.End Real V) (h : Real), h ≠ 0 →
        t • LinearMap.id +
            (2 * h)⁻¹ •
              (observerSquare H t - observerSquare H (t + h) +
                h ^ 2 • LinearMap.id) = H) := by
  have reflectedReading : ∀ H : Module.End Real V,
      observerSquare ((2 * t) • LinearMap.id - H) t = observerSquare H t := by
    intro H
    unfold observerSquare
    rw [show
      (2 * t) • (LinearMap.id : Module.End Real V) - H - t • LinearMap.id =
        -(H - t • LinearMap.id) by module]
    simp only [pow_two, neg_mul, mul_neg, neg_neg]
  have computedDerivative : ∀ (H : Module.End Real V) (x : V),
      HasDerivAt (fun s : Real => observerSquare H s x)
        (((2 : Real) •
          (t • (LinearMap.id : Module.End Real V) - H)) x) t := by
    intro H x
    have hconstant : HasDerivAt (fun _ : Real => H (H x)) 0 t :=
      hasDerivAt_const t _
    have hlinear : HasDerivAt (fun s : Real => s • H x) (H x) t := by
      convert (hasDerivAt_id t).smul_const (H x) using 1 <;> simp
    have hquadratic :
        HasDerivAt (fun s : Real => s ^ 2 • x) (((2 : Real) * t) • x) t := by
      simpa using (hasDerivAt_pow 2 t).smul_const x
    rw [show (fun s : Real => observerSquare H s x) =
        fun s : Real => H (H x) - s • H x - s • H x + s ^ 2 • x by
      funext s
      simp [observerSquare, pow_two, Module.End.mul_apply]
      module]
    convert ((hconstant.sub hlinear).sub hlinear).add hquadratic using 1
    · ext s
      rfl
    · change (2 : Real) • (t • x - H x) =
        (0 - H x - H x) + (2 * t) • x
      module
  have secondObserver : ∀ (H : Module.End Real V) (h : Real), h ≠ 0 →
      t • LinearMap.id +
          (2 * h)⁻¹ •
            (observerSquare H t - observerSquare H (t + h) +
              h ^ 2 • LinearMap.id) = H := by
    intro H h hh
    have shiftedSquare :
        observerSquare H (t + h) =
          observerSquare H t - (2 * h) • (H - t • LinearMap.id) +
            h ^ 2 • LinearMap.id := by
      ext x
      simp [observerSquare, pow_two, Module.End.mul_apply]
      module
    rw [shiftedSquare]
    have bracket :
        observerSquare H t -
            (observerSquare H t - (2 * h) • (H - t • LinearMap.id) +
              h ^ 2 • LinearMap.id) + h ^ 2 • LinearMap.id =
          (2 * h) • (H - t • LinearMap.id) := by
      module
    rw [bracket]
    have twoh : 2 * h ≠ 0 := mul_ne_zero (by norm_num) hh
    rw [inv_smul_smul₀ twoh]
    module
  refine ⟨?_, reflectedReading, ?_, secondObserver⟩
  · rintro ⟨reconstruct, recovers⟩
    let positive : Module.End Real V := (t + 1) • LinearMap.id
    let negative : Module.End Real V := (t - 1) • LinearMap.id
    have sameReading : observerSquare positive t = observerSquare negative t := by
      dsimp [positive, negative]
      ext x
      simp [observerSquare, pow_two, Module.End.mul_apply]
      module
    have operatorsEqual : positive = negative := by
      calc
        positive = reconstruct (observerSquare positive t) := (recovers positive).symm
        _ = reconstruct (observerSquare negative t) := congrArg reconstruct sameReading
        _ = negative := recovers negative
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have valuesEqual := DFunLike.congr_fun operatorsEqual x
    dsimp [positive, negative] at valuesEqual
    have twoX : (2 : Real) • x = 0 := by
      calc
        (2 : Real) • x = (t + 1) • x - (t - 1) • x := by module
        _ = 0 := sub_eq_zero.mpr valuesEqual
    exact hx ((smul_eq_zero.mp twoX).resolve_left (by norm_num))
  · intro H D hD
    have derivativeEqual : D = (2 : Real) • (t • LinearMap.id - H) := by
      ext x
      exact (hD x).unique (computedDerivative H x)
    refine ⟨derivativeEqual, ?_⟩
    rw [derivativeEqual]
    module

#print axioms observerSquare
#print axioms one_observer_operator_nonreconstruction

end D5.S3.Observer.Linear.OneObserverOperatorNonreconstruction
