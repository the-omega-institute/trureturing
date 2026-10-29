/- GID: D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ArchimedeanTimeRigidity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PrimitiveLifts/ArchimedeanTimeRigidity
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Continuous Archimedean time maps without target p-torsion are injective or zero. -/

import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Topology.Separation.Basic
import Mathlib.Tactic.NormNum

/-! Division-closed kernels give continuous time rigidity over Archimedean ordered fields. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.PrimitiveLifts.ArchimedeanTimeRigidity

universe u v

/-- A nonzero continuous time homomorphism has no nonzero period when its target
has no nonzero element annihilated by one fixed natural number greater than one.
The target group need not be commutative or have continuous group operations. -/
theorem continuous_addHom_injective_or_eq_zero
    {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [TopologicalSpace K] [OrderTopology K] [Archimedean K]
    {A : Type v} [AddGroup A] [TopologicalSpace A] [T1Space A]
    (p : ℕ) (hp : 1 < p) (hpt : ∀ x : A, p • x = 0 → x = 0)
    (f : K →+ A) (hf : Continuous f) : Function.Injective f ∨ f = 0 := by
  by_cases hbot : f.ker = ⊥
  · exact Or.inl (f.ker_eq_bot_iff.mp hbot)
  right
  have hpK : (1 : K) < p := by exact_mod_cast hp
  have hp0 : (0 : K) < p := zero_lt_one.trans hpK
  have hdense : Dense (f.ker : Set K) := by
    apply f.ker.dense_of_no_min hbot
    rintro ⟨a, ha⟩
    have hb : a / (p : K) ∈ f.ker := by
      change f (a / (p : K)) = 0
      apply hpt
      rw [← map_nsmul]
      have hdiv : p • (a / (p : K)) = a := by
        rw [nsmul_eq_mul, mul_div_cancel₀ _ (ne_of_gt hp0)]
      rw [hdiv]
      exact ha.1.1
    exact (not_le_of_gt (div_lt_self ha.1.2 hpK))
      (ha.2 ⟨hb, div_pos ha.1.2 hp0⟩)
  have hclosed : IsClosed (f.ker : Set K) :=
    isClosed_singleton.preimage hf
  apply AddMonoidHom.ker_eq_top_iff.mp
  apply SetLike.coe_injective
  change (f.ker : Set K) = Set.univ
  rw [← hclosed.closure_eq, hdense.closure_eq]

#print axioms continuous_addHom_injective_or_eq_zero

end D5.S3.ConceptDynamics.Coding.PrimitiveLifts.ArchimedeanTimeRigidity
