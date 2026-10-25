/- GID: D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation
   generality: I
   mirror-B: D5/B/S3/HomologicalAlgebra/LocalityTensorProductRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.claim; result=D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.result; claim=D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.claim
   digest: Six projected lines give counterexamples to both locality tensor conjectures. -/

import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith

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

abbrev localityTensor {K E : Type} [Field K] [AddCommGroup E] [Module K E]
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
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hi
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hj
  have hn : a ≠ 0 := by
    intro h
    apply hv
    rw [← ha, h, zero_smul]
  have h0 := congrFun (ha.trans hb.symm) 0
  have h1 := congrFun (ha.trans hb.symm) 1
  have h2 := congrFun (ha.trans hb.symm) 2
  fin_cases i <;> fin_cases j <;>
    norm_num [direction, Pi.smul_apply, smul_eq_mul] at h0 h1 h2 ⊢ <;>
    (exfalso; apply hn; linarith)

private def projectedPolar (v : Fin 5 → ℝ) : Submodule ℝ (Fin 5 → ℝ) where
  carrier := {t | project v = 0 ∨ project t = 0 ∨
    ∃ i, project v ∈ line i ∧ project t ∈ line i}
  zero_mem' := Or.inr (Or.inl (map_zero project))
  add_mem' := by
    intro t u ht hu
    change project v = 0 ∨ project (t + u) = 0 ∨
      ∃ i, project v ∈ line i ∧ project (t + u) ∈ line i
    change project v = 0 ∨ project u = 0 ∨
      ∃ i, project v ∈ line i ∧ project u ∈ line i at hu
    by_cases hv : project v = 0
    · exact Or.inl hv
    rcases ht with ht | ht | ⟨i, hi, hit⟩
    · exact (hv ht).elim
    · simpa only [map_add, ht, zero_add] using hu
    rcases hu with hu | hu | ⟨j, hj, hju⟩
    · exact (hv hu).elim
    · exact Or.inr (Or.inr ⟨i, hi, by rw [map_add, hu, add_zero]; exact hit⟩)
    have hij := line_unique hv hi hj
    subst j
    exact Or.inr (Or.inr ⟨i, hi, by simpa using (line i).add_mem hit hju⟩)
  smul_mem' := by
    intro c t ht
    rcases ht with ht | ht | ⟨i, hi, hit⟩
    · exact Or.inl ht
    · exact Or.inr (Or.inl (by rw [map_smul, ht, smul_zero]))
    · exact Or.inr (Or.inr ⟨i, hi, by simpa using (line i).smul_mem c hit⟩)

private def singletonPolar (v : Fin 5 → ℝ) : Submodule ℝ (Fin 5 → ℝ) where
  carrier := {t | rel v t}
  zero_mem' := by change rel v 0; unfold rel; simp only [map_zero, Pi.zero_apply, mul_zero, zero_mul]; tauto
  add_mem' := by
    intro t u ht hu
    refine ⟨(projectedPolar v).add_mem ht.1 hu.1, ?_⟩
    rcases ht with ⟨_, h1, h2, h3, h4⟩
    rcases hu with ⟨_, g1, g2, g3, g4⟩
    simp only [Pi.add_apply, mul_add, add_mul, h1, h2, h3, h4, g1, g2, g3, g4,
      zero_add, and_self]
  smul_mem' := by
    intro c t ht
    refine ⟨(projectedPolar v).smul_mem c ht.1, ?_⟩
    rcases ht with ⟨_, h1, h2, h3, h4⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    constructor
    · calc v 3 * (c * t 2) = c * (v 3 * t 2) := by ring
           _ = 0 := by rw [h1, mul_zero]
    constructor
    · rw [mul_assoc, h2, mul_zero]
    constructor
    · calc v 4 * (c * t 1) = c * (v 4 * t 1) := by ring
           _ = 0 := by rw [h3, mul_zero]
    · rw [mul_assoc, h4, mul_zero]

private theorem rel_locality : IsLocalityVectorSpace ℝ rel := by
  refine ⟨?_, ?_, ?_⟩
  · intro v t h
    rcases h with ⟨hp, h1, h2, h3, h4⟩
    refine ⟨?_, h2, h1, h4, h3⟩
    rcases hp with hp | hp | ⟨i, hi, hj⟩
    · exact Or.inr (Or.inl hp)
    · exact Or.inl hp
    · exact Or.inr (Or.inr ⟨i, hj, hi⟩)
  · exact (singletonPolar 0).zero_mem
  · intro U
    refine ⟨sInf (singletonPolar '' U), ?_⟩
    ext t
    simp only [SetLike.mem_coe, Submodule.mem_sInf, Set.mem_image,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    rfl

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
  unfold bilRelations at ha
  induction ha using Submodule.span_induction with
  | mem f hf =>
    rcases hf with ⟨a, _, b, _, x, _, rfl⟩ | ⟨a, _, x, _, y, _, rfl⟩ |
      ⟨a, _, x, _, k, rfl⟩ | ⟨a, _, x, _, k, rfl⟩ <;>
      simp only [phi, map_sub, map_smul, Finsupp.linearCombination_single,
        one_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring
  | zero => exact map_zero _
  | add a b _ _ ha hb => rw [map_add, ha, hb, zero_add]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

private theorem phi_values : phi 0 (X 1) = 1 ∧ phi 3 (Y 3 + Y 4) = 1 ∧
    phi 4 (Y 3 + Y 4) = 1 := by
  norm_num [phi, X, Y, e, Pi.single_apply]

private theorem phi_support (i : Fin 5) {a} (ha : phi i a ≠ 0) :
    ∃ p ∈ a.support, p.1 i * p.2 i ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  apply ha
  unfold phi
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro p hp
  rw [h p hp, smul_zero]

private theorem key_obstruction {v t : Fin 5 → ℝ} (h : rel v t)
    (h0 : v 0 * t 0 ≠ 0) : v 1 ≠ 0 ∨ v 2 ≠ 0 := by
  have hv : v 0 ≠ 0 := (mul_ne_zero_iff.mp h0).1
  have ht : t 0 ≠ 0 := (mul_ne_zero_iff.mp h0).2
  rcases h.1 with hp | hp | ⟨i, hi, _⟩
  · exact (hv (congrFun hp 0)).elim
  · exact (ht (congrFun hp 0)).elim
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hi
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  by_contra hn
  push_neg at hn
  fin_cases i <;> norm_num [direction, project, Pi.smul_apply, smul_eq_mul] at h0 h1 h2
  all_goals apply hv; linarith [hn.1, hn.2]

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
