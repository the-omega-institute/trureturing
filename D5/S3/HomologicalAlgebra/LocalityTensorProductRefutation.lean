/- GID: D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation
   generality: I
   mirror-B: D5/B/S3/HomologicalAlgebra/LocalityTensorProductRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.claim; result=D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.result; claim=D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.claim
   digest: Six projected lines give counterexamples to both locality tensor conjectures. -/

import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module

noncomputable section

namespace D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation

 def IsLocalityVectorSpace (K : Type) {E : Type} [Field K] [AddCommGroup E] [Module K E]
    (r : E → E → Prop) : Prop :=
  Symmetric r ∧ r 0 0 ∧ ∀ U : Set E,
    ∃ S : Submodule K E, (S : Set E) = {x | ∀ u ∈ U, r u x}

 def localityProduct {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    (r : E → E → Prop) (V W : Submodule K E) : Set (E × E) :=
  {p | p.1 ∈ V ∧ p.2 ∈ W ∧ r p.1 p.2}

 def pairRel {E : Type} (r : E → E → Prop) (p q : E × E) : Prop :=
  r p.1 q.1 ∧ r p.2 q.2

 def spanRel {K X : Type} [Zero K] (s : X → X → Prop) (a b : X →₀ K) : Prop :=
  ∀ x ∈ a.support, ∀ y ∈ b.support, s x y

 def bilRelations {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    (V W : Submodule K E) : Submodule K (E × E →₀ K) :=
  Submodule.span K {f |
    (∃ a ∈ V, ∃ b ∈ V, ∃ x ∈ W,
      f = Finsupp.single (a + b, x) 1 - Finsupp.single (a, x) 1 -
        Finsupp.single (b, x) 1) ∨
    (∃ a ∈ V, ∃ x ∈ W, ∃ y ∈ W,
      f = Finsupp.single (a, x + y) 1 - Finsupp.single (a, x) 1 -
        Finsupp.single (a, y) 1) ∨
    (∃ a ∈ V, ∃ x ∈ W, ∃ k : K,
      f = Finsupp.single (k • a, x) 1 - k • Finsupp.single (a, x) 1) ∨
    (∃ a ∈ V, ∃ x ∈ W, ∃ k : K,
      f = Finsupp.single (a, k • x) 1 - k • Finsupp.single (a, x) 1)}

 def freeSpan {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    (r : E → E → Prop) (V W : Submodule K E) : Submodule K (E × E →₀ K) :=
  Finsupp.supported K K (localityProduct r V W)

 def bilIdeal {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    (r : E → E → Prop) (V W : Submodule K E) : Submodule K (E × E →₀ K) :=
  bilRelations V W ⊓ freeSpan r V W

 def localityTensor {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    (r : E → E → Prop) (V W : Submodule K E) : Type :=
  freeSpan r V W ⧸ (bilIdeal r V W).comap (freeSpan r V W).subtype

 def quotientRel {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    (r : E → E → Prop) (V W : Submodule K E) (a b : localityTensor r V W) : Prop :=
  ∃ u v : freeSpan r V W, Submodule.Quotient.mk u = a ∧
    Submodule.Quotient.mk v = b ∧ spanRel (pairRel r) u.1 v.1

 def LocalityCompatible {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    (r : E → E → Prop) (W : Submodule K E) : Prop :=
  ∀ x y z, ∀ w ∈ W, r x y → r (x + w) z →
    ∃ w' ∈ W, r (x + w') y ∧ r (x + w') z

 def TensorConjecture : Prop :=
  ∀ (K E : Type) [Field K] [AddCommGroup E] [Module K E]
    (r : E → E → Prop) (V W : Submodule K E),
    IsLocalityVectorSpace K r → IsLocalityVectorSpace K (quotientRel r V W)

 def PairConjecture : Prop :=
  ∀ (K E : Type) [Field K] [AddCommGroup E] [Module K E]
    (r : E → E → Prop) (V W : Submodule K E), IsLocalityVectorSpace K r →
    LocalityCompatible (fun a b : freeSpan r V W => spanRel (pairRel r) a.1 b.1)
      ((bilIdeal r V W).comap (freeSpan r V W).subtype)

 def claim : Prop := TensorConjecture ∨ PairConjecture

private def project : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v := ![v 0, v 1, v 2]
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl

private def direction (i : Fin 6) : Fin 3 → ℝ :=
  ![![0, 1, 0], ![1, 1, 0], ![1, -1, 0], ![0, 0, 1], ![1, 0, 1], ![1, 0, -1]] i

private def line (i : Fin 6) : Submodule ℝ (Fin 3 → ℝ) :=
  Submodule.span ℝ {direction i}

private def rel (v t : Fin 5 → ℝ) : Prop :=
  (project v = 0 ∨ project t = 0 ∨ ∃ i, project v ∈ line i ∧ project t ∈ line i) ∧
    v 3 * t 2 = 0 ∧ t 3 * v 2 = 0 ∧ v 4 * t 1 = 0 ∧ t 4 * v 1 = 0

private def e (i : Fin 5) : Fin 5 → ℝ := Pi.single i 1

private def X (k : Fin 5) : (Fin 5 → ℝ) × (Fin 5 → ℝ) →₀ ℝ :=
  (1 / 2 : ℝ) • Finsupp.single (e 0 + e k, e 0 + e k) 1 +
    (1 / 2 : ℝ) • Finsupp.single (e 0 - e k, e 0 - e k) 1 -
    Finsupp.single (e k, e k) 1

private def Y (i : Fin 5) : (Fin 5 → ℝ) × (Fin 5 → ℝ) →₀ ℝ :=
  Finsupp.single (e i, e i) 1

private def phi (i : Fin 5) :
    ((Fin 5 → ℝ) × (Fin 5 → ℝ) →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun p => p.1 i * p.2 i)

private theorem line_unique {v : Fin 3 → ℝ} (hv : v ≠ 0) {i j : Fin 6}
    (hi : v ∈ line i) (hj : v ∈ line j) : i = j := by
  sorry

private theorem rel_locality : IsLocalityVectorSpace ℝ rel := by
  sorry

private theorem X_supported (k : Fin 5) (hk : k = 1 ∨ k = 2) :
    X k ∈ freeSpan rel (⊤ : Submodule ℝ (Fin 5 → ℝ)) ⊤ := by
  sorry

private theorem Y_supported (i : Fin 5) (hi : i = 3 ∨ i = 4) :
    Y i ∈ freeSpan rel (⊤ : Submodule ℝ (Fin 5 → ℝ)) ⊤ := by
  sorry

private theorem X_difference :
    X 2 - X 1 ∈ bilRelations (⊤ : Submodule ℝ (Fin 5 → ℝ)) ⊤ := by
  sorry

private theorem X_related (k i : Fin 5) (h : (k = 1 ∧ i = 3) ∨ (k = 2 ∧ i = 4)) :
    spanRel (pairRel rel) (X k) (Y i) := by
  sorry

private theorem phi_vanishes (i : Fin 5) {a} (ha :
    a ∈ bilRelations (⊤ : Submodule ℝ (Fin 5 → ℝ)) ⊤) : phi i a = 0 := by
  sorry

private theorem phi_values : phi 0 (X 1) = 1 ∧ phi 3 (Y 3 + Y 4) = 1 ∧
    phi 4 (Y 3 + Y 4) = 1 := by
  sorry

private theorem phi_support (i : Fin 5) {a} (ha : phi i a ≠ 0) :
    ∃ p ∈ a.support, p.1 i * p.2 i ≠ 0 := by
  sorry

private theorem key_obstruction {v t : Fin 5 → ℝ} (h : rel v t)
    (h0 : v 0 * t 0 ≠ 0) : v 1 ≠ 0 ∨ v 2 ≠ 0 := by
  sorry

private theorem pair_refuted : ¬ PairConjecture := by
  sorry

private theorem tensor_refuted : ¬ TensorConjecture := by
  sorry

 theorem result : ¬ claim := by
  intro h
  rcases h with h | h
  · exact tensor_refuted h
  · exact pair_refuted h

end D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation
