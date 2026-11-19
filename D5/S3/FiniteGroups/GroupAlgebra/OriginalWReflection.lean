/- GID: D5/S3/FiniteGroups/GroupAlgebra/OriginalWReflection
   generality: E
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/OriginalWReflection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RepresentationTheory.Intertwining, mathlib/module/Mathlib.LinearAlgebra.TensorPower.Symmetric]
   utility: none
   digest: Tensor reflection for actual dual symmetric powers of an arbitrary faithful two-dimensional elementary-abelian representation. -/

import D5.S3.FiniteGroups.GroupAlgebra.OriginalWClassification
import D5.S3.FiniteGroups.GroupAlgebra.EmbeddedTensorReflection

/-!
Elmer--Kadr Conjecture 3.7(b), for the actual positive-index modules
V_i = (Sym^(i-1) W)^*. The normal form supplies the additive embedding;
the symmetric-power quotient equivalence and the original relative-ideal
transport remove every coordinate choice from the conclusion.

The polynomial recurrence follows the mechanism of the published proof of
Corollary 1.3; no novelty claim is made. Unlike the corrected assertion (a),
this reflection has no total-index, low-residue-sum, or no-carry condition.
The original P and X witnesses retain their unrestricted dimensions.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.OriginalWReflection

open D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrTensorCounterexample
open D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrTensorCounterexample.SymmetricPowerTranslation
open D5.S3.FiniteGroups.GroupAlgebra.OriginalWClassification
open Module

universe uE

variable {K W : Type} [Field K] [AddCommGroup W] [Module K W]
  {E : Type uE} [AddCommGroup E] [Fintype E] [Nontrivial E]
  {p : ℕ} [Fact p.Prime] [CharP K p] [FiniteDimensional K W]

/-- Reflection for the actual faithful two-dimensional module and its
ordinary dual symmetric powers. The conclusion has no chosen basis,
embedding, polynomial-model, or relative-transport hypothesis. -/
theorem originalW_tensor_reflection
    (hE : ∀ e : E, p • e = 0) (hdim : finrank K W = 2)
    (rho : Representation K (Multiplicative E) W) (hrho : Function.Injective rho)
    (a b u v : ℕ) (hu : u < p) (hv : v < p)
    (hi : 0 < p * a + u) (hj : 0 < p * b + v)
    (hiq : p * a + u < Fintype.card E) (hjq : p * b + v < Fintype.card E) :
    RelativeStableIso
      (originalMAction rho p (Fintype.card E / p) (Fact.out : p.Prime).pos)
      (originalTAction rho (p * a + p - u) (p * b + p - v)
        (by omega) (by omega))
      (originalTAction rho (p * a + u) (p * b + v) hi hj) := by
  obtain ⟨alpha, halpha, _primalModels, dualModels⟩ :=
    SymmetricPowerTranslation.exists_faithful_polynomial_models hE hdim rho hrho
  let eV : ∀ (i : ℕ) (hi : 0 < i),
      (originalVAction rho i hi).Equiv
        ((dualAction K i).comp alpha.toMultiplicative) := by
    intro i hi
    cases i with
    | zero => omega
    | succ n => simpa [originalVAction, OriginalV] using
        (Classical.choice (dualModels n))
  let eM : (originalMAction rho p (Fintype.card E / p)
      (Fact.out : p.Prime).pos).Equiv
      ((PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p)
        (Fintype.card E / p)).comp alpha.toMultiplicative) :=
    directSumCongr (fun r : Fin (Fintype.card E / p) =>
      eV (p * (r.val + 1)) (Nat.mul_pos (Fact.out : p.Prime).pos (Nat.succ_pos _)))
  let eT : ∀ (i j : ℕ) (hi : 0 < i) (hj : 0 < j),
      (originalTAction rho i j hi hj).Equiv
        (Representation.tprod ((dualAction K i).comp alpha.toMultiplicative)
          ((dualAction K j).comp alpha.toMultiplicative)) :=
    fun i j hi hj => tensorCongr (eV i hi) (eV j hj)
  exact relativeStableIso_transport eM.symm
    (eT (p * a + p - u) (p * b + p - v) (by omega) (by omega)).symm
    (eT (p * a + u) (p * b + v) hi hj).symm
    (EmbeddedTensorReflection.tensor_reflection alpha halpha a b u v hu hv hiq hjq)

end D5.S3.FiniteGroups.GroupAlgebra.OriginalWReflection
