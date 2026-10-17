import D5.S3.Analytic.Convexity.CFMPTransientFullInversePrimitive
import D5.S3.Analytic.Convexity.CFMPTransientPotentialRecovery

/-!
Transient exact final consumer. Source only: NOT elaborated, compiled, kernel
checked, axiom audited, admitted, or proposed as canonical repository content.
Target: Lean v4.33.0 / Mathlib db584cd6d46c92f209a44c0f1c829460d327499d.

The two imports are the exact supplied modules, with their transitive immutable
suppliers. The parent owns mechanical sibling-import translation and validation.
There is exactly one invocation of the full inverse-primitive assembly below.
Its e, G, and Q remain the same objects through recovery; no new inverse or
primitive is selected. Every declaration here is a temporary consumer only.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped Topology InnerProductSpace

namespace CFMP147Transient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The full potential-existence conclusion on the original D. U is arbitrary;
the only F-derivative premise is actual symmetric differentiability on U.
The total potential, its derivative everywhere on D, and its convexity on all D
are outputs. No point of D or positive-dimensionality witness is requested. -/
theorem exists_full_potential
    {D U : Set E} {F : E → E}
    (hDopen : IsOpen D) (hDconv : Convex ℝ D) (hFcont : ContinuousOn F D)
    (hMono : ∀ x ∈ D, ∀ y ∈ D, 0 ≤ inner ℝ (F x - F y) (x - y))
    (hF : ∀ x ∈ U, ∃ A : E →L[ℝ] E,
      HasFDerivAt F A x ∧ ∀ u v, inner ℝ (A u) v = inner ℝ u (A v))
    (hFinite : (F '' (D \ U)).Finite) :
    ∃ P : E → ℝ,
      (∀ x ∈ D, HasFDerivAt P (innerSL ℝ (F x)) x) ∧ ConvexOn ℝ D P := by
  classical
  let T : E → E := fun x => x + F x
  let imageOmega : Set E := T '' D
  -- One unpacking of B2 → B1 → B3 → B4, retaining the actual object agreements.
  obtain ⟨hOmega, e, he, G, Q, _hGdef, hG, _hRestrict, _hMaps, hInv, _hLip, hQ⟩ :=
    CFMP144Transient.exists_full_inverse_primitive
      (D := D) (U := U) (F := F) hDopen hDconv hFcont hMono hF hFinite

  -- Keep both directions for this very G. The forward direction is the actual
  -- supplied equation. The reverse direction uses e.symm_apply_apply directly;
  -- it does not infer a left inverse from a right inverse or assume injectivity.
  have hSameInverse :
      (∀ y ∈ imageOmega, T (G y) = y) ∧
      (∀ x ∈ D, G (T x) = x) := by
    constructor
    · intro y hy
      change G y + F (G y) = y
      exact hInv y hy
    · intro x hx
      let xD : D := ⟨x, hx⟩
      let yOmega : imageOmega := ⟨T x, ⟨x, hx, rfl⟩⟩
      have hePoint : e xD = yOmega := by
        apply Subtype.ext
        exact he xD
      calc
        G (T x) = (e.symm yOmega : E) := hG yOmega
        _ = (e.symm (e xD) : E) :=
          congrArg (fun z : imageOmega => (e.symm z : E)) hePoint.symm
        _ = x := congrArg (fun z : D => (z : E)) (e.symm_apply_apply xD)

  -- These are definitional equalities of the literal maps and literal images,
  -- recorded explicitly before crossing the recovery module's interface.
  have hTdef : TransientPotentialRecovery.T F = T := by
    funext x
    rfl
  have hImageDef : TransientPotentialRecovery.T F '' D = imageOmega := by
    rw [hTdef]
  have hOmegaRecovery : IsOpen (TransientPotentialRecovery.T F '' D) := by
    rw [hImageDef]
    exact hOmega
  have hInvRecovery : ∀ x ∈ D, G (TransientPotentialRecovery.T F x) = x := by
    rw [hTdef]
    exact hSameInverse.2
  have hQRecovery : ∀ z ∈ TransientPotentialRecovery.T F '' D,
      HasFDerivAt Q (innerSL ℝ (G z)) z := by
    rw [hImageDef]
    exact hQ

  -- The potential uses precisely the Q just unpacked, even off D.
  let P : E → ℝ := fun x =>
    inner ℝ x (T x) - Q (T x) - (1 / 2 : ℝ) * ‖x‖ ^ 2
  have hPdef : P = TransientPotentialRecovery.P F Q := by
    funext x
    rfl
  refine ⟨P, ?_⟩
  rw [hPdef]
  exact TransientPotentialRecovery.recover (D := D) (F := F) (G := G) (Q := Q)
    hDopen hDconv hFcont hMono hOmegaRecovery hInvRecovery hQRecovery

/-- The original open-U/subset-D/symmetric-PSD setting. Only the PSD component
is projected away when invoking the core; no derivative is postulated anew. -/
theorem original_setting_full_potential
    {D U : Set E} {F : E → E}
    (hDopen : IsOpen D) (hDconv : Convex ℝ D) (hFcont : ContinuousOn F D)
    (hMono : ∀ x ∈ D, ∀ y ∈ D, 0 ≤ inner ℝ (F x - F y) (x - y))
    (_hUopen : IsOpen U) (_hUD : U ⊆ D)
    (hF : ∀ x ∈ U, ∃ A : E →L[ℝ] E,
      HasFDerivAt F A x ∧
      (∀ u v, inner ℝ (A u) v = inner ℝ u (A v)) ∧
      ∀ v, 0 ≤ inner ℝ (A v) v)
    (hFinite : (F '' (D \ U)).Finite) :
    ∃ P : E → ℝ,
      (∀ x ∈ D, HasFDerivAt P (innerSL ℝ (F x)) x) ∧ ConvexOn ℝ D P := by
  apply exists_full_potential (D := D) (U := U) (F := F)
    hDopen hDconv hFcont hMono
  · intro x hx
    obtain ⟨A, hA, hSym, _hPSD⟩ := hF x hx
    exact ⟨A, hA, hSym⟩
  · exact hFinite

end CFMP147Transient

end
