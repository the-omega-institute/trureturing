/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SpinWindowMarginals
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SpinWindowMarginals
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary supported spin events have consistent finite marginals and disjoint independence. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteMarginals
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SpinWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
namespace SpinWindow

def SupportedOn (V : Finset ℤ) (E : Set Spins) : Prop :=
  ∀ S R : Spins, (∀ i ∈ V, S i = R i) → (S ∈ E ↔ R ∈ E)

/-- Enlarging a finite coordinate window preserves every event supported in the old window. -/
theorem prob_enlarge (β : Bias) (V W : Finset ℤ) (hVW : V ⊆ W)
    (E : Set Spins) (hE : SupportedOn V E) : prob β W E = prob β V E := by
  let A : Finset W := V.subtype (· ∈ W)
  let e : A ≃ V :=
    { toFun := fun a => ⟨a.val.val, Finset.mem_subtype.mp a.property⟩
      invFun := fun v => ⟨⟨v, hVW v.property⟩, Finset.mem_subtype.mpr v.property⟩
      left_inv := by intro a; rfl
      right_inv := by intro a; rfl }
  let E' : Set (A → Bool) := {τ | extend V (fun v => τ (e.symm v)) ∈ E}
  have he : {σ : W → Bool | extend W σ ∈ E} =
      {σ : W → Bool | FiniteSpinLaw.restrict A σ ∈ E'} := by
    ext σ
    apply hE
    intro i hi
    simp [E', FiniteSpinLaw.restrict, e, extend_apply, hi, hVW hi]
  unfold prob
  rw [he, FiniteSpinLaw.restriction_mass]
  exact FiniteSpinLaw.reindex_mass β e {τ : V → Bool | extend V τ ∈ E}

/-- Two spin events on disjoint finite coordinates are independent in any containing window. -/
theorem prob_independent (β : Bias) (V A B : Finset ℤ) (hA : A ⊆ V) (hB : B ⊆ V)
    (hd : Disjoint A B) (E F : Set Spins) (hE : SupportedOn A E) (hF : SupportedOn B F) :
    prob β V (E ∩ F) = prob β V E * prob β V F := by
  let A' : Finset V := A.subtype (· ∈ V)
  let B' : Finset V := B.subtype (· ∈ V)
  have hd' : Disjoint A' B' := by
    apply Finset.disjoint_left.mpr
    intro i hiA hiB
    exact Finset.disjoint_left.mp hd (Finset.mem_subtype.mp hiA) (Finset.mem_subtype.mp hiB)
  apply FiniteSpinLaw.disjoint_event_mass β A' B' hd'
  · intro σ τ h
    apply hE
    intro i hi
    have hh := h ⟨i, hA hi⟩ (Finset.mem_subtype.mpr hi)
    simpa only [extend_apply V σ i (hA hi), extend_apply V τ i (hA hi)] using hh
  · intro σ τ h
    apply hF
    intro i hi
    have hh := h ⟨i, hB hi⟩ (Finset.mem_subtype.mpr hi)
    simpa only [extend_apply V σ i (hB hi), extend_apply V τ i (hB hi)] using hh

end SpinWindow
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
