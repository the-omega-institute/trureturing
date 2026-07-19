/- GID: D5/S3/Quantum/ObserverAlgebra
   generality: G
   mirror-B: D5/B/S3/Quantum/ObserverAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Formalize finite observer read-update covariance and noncommutativity. -/

import Mathlib

namespace D5.S3.Quantum.ObserverAlgebra

/-- Amplitudes carried by a register indexed by `index`. -/
abbrev Register (index : Type*) := index -> Complex

/-- Pointwise multiplication by an address-dependent observable. -/
def readObservable {index : Type*} (f : index -> Complex) (psi : Register index) :
    Register index :=
  fun i => f i * psi i

/-- Pullback of a register state along an explicitly supplied reversible update. -/
def observerUpdate {index : Type*} (tau : Equiv.Perm index) (psi : Register index) :
    Register index :=
  fun i => psi (tau.symm i)

/-- Reversible updates act covariantly on pointwise read observables. -/
theorem observer_update_covariant_group_skeleton {index : Type*}
    (tau sigma : Equiv.Perm index) (f : index -> Complex) (psi : Register index) :
    observerUpdate (Equiv.refl index) psi = psi ∧
      observerUpdate (tau.trans sigma) psi =
        observerUpdate sigma (observerUpdate tau psi) ∧
      observerUpdate tau.symm (observerUpdate tau psi) = psi ∧
      observerUpdate tau (readObservable f psi) =
        readObservable (fun i => f (tau.symm i)) (observerUpdate tau psi) := by
  constructor
  · funext i
    rfl
  constructor
  · funext i
    rfl
  constructor
  · funext i
    simp [observerUpdate]
  · funext i
    rfl

/-- A changed read value and a nonzero amplitude witness noncommutativity. -/
theorem observer_read_update_noncommutative {index : Type*}
    (tau : Equiv.Perm index) (f : index -> Complex) (psi : Register index) (i : index)
    (hRead : f (tau.symm i) ≠ f i) (hState : psi (tau.symm i) ≠ 0) :
    observerUpdate tau (readObservable f psi) ≠
      readObservable f (observerUpdate tau psi) := by
  intro hCommute
  apply hRead
  apply mul_right_cancel₀ hState
  simpa [observerUpdate, readObservable] using congrFun hCommute i

/-- In the register representation, the read-update commutator is the translated
observable difference multiplied by the updated register. -/
theorem observer_read_update_commutator_formula {index : Type*}
    (tau : Equiv.Perm index) (f : index -> Complex) (psi : Register index) :
    observerUpdate tau (readObservable f psi) -
        readObservable f (observerUpdate tau psi) =
      fun i => (f (tau.symm i) - f i) * psi (tau.symm i) := by
  funext i
  simp [observerUpdate, readObservable]
  ring

end D5.S3.Quantum.ObserverAlgebra
