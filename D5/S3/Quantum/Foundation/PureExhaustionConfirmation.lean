/- GID: D5/S3/Quantum/Foundation/PureExhaustionConfirmation
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/PureExhaustionConfirmation
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Pure-point exhaustion on the full original carrier gives an attained mixed-state comparison and complementary least confirming effects. -/

import D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Foundation.PureExhaustionConfirmation

open D5.S3.Quantum.Foundation.CircuitBalancedConfirmation

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A]

/-! The continuous-linear-map presentation is used only to expose the finite-
dimensional topology needed for compactness. The repository's source-facing
objects remain `proper`, `confirms`, and `comparison` on linear maps. -/

def cProper (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (f : A →L[ℝ] ℝ) : Prop :=
  ∀ x ∈ C, 0 ≤ f x ∧ f x ≤ u x

def cConfirms (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) (p : A)
    (f : A →L[ℝ] ℝ) : Prop := cProper C u f ∧ f p = 1

def cComparison (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) (p x : A) : ℝ :=
  sInf {r | ∃ f : A →L[ℝ] ℝ, cConfirms C u p f ∧ f x = r}

private theorem cProper_eq_set (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) :
    {f : A →L[ℝ] ℝ | cProper C u f} =
      {f : A →L[ℝ] ℝ | ∀ x : C, 0 ≤ f x ∧ f x ≤ u x} := by
  ext f
  constructor
  · intro hf x
    exact hf x.1 x.2
  · intro hf x hx
    exact hf ⟨x, hx⟩

private theorem cProper_closed (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) :
    IsClosed {f : A →L[ℝ] ℝ | cProper C u f} := by
  rw [cProper_eq_set]
  have h0 : IsClosed (⋂ x : C, {f : A →L[ℝ] ℝ | 0 ≤ f x}) :=
    isClosed_iInter (fun x : C => isClosed_le continuous_const
      (ContinuousLinearMap.apply ℝ ℝ (x : A)).continuous)
  have h1 : IsClosed (⋂ x : C, {f : A →L[ℝ] ℝ | f x ≤ u x}) :=
    isClosed_iInter (fun x : C => isClosed_le
      (ContinuousLinearMap.apply ℝ ℝ (x : A)).continuous continuous_const)
  rw [show {f : A →L[ℝ] ℝ | ∀ x : C, 0 ≤ f x ∧ f x ≤ u x} =
      (⋂ x : C, {f : A →L[ℝ] ℝ | 0 ≤ f x}) ∩
        (⋂ x : C, {f : A →L[ℝ] ℝ | f x ≤ u x}) by
    ext f
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, forall_and]]
  exact h0.inter h1

private theorem pure_representation
    (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤) :
    ∀ i : Fin (Module.finrank ℝ A),
      ∃ (s : Finset A) (c : A → ℝ),
        (↑s : Set A) ⊆ pure C u ∧ Function.support c ⊆ (↑s : Set A) ∧
          (∑ a ∈ s, c a • a) = Module.finBasis ℝ A i := by
  intro i
  have hK := base_compact hclosed hstrict
  have hP := pure_span hK hstrict hspan
  obtain ⟨c, s, hs, hcs, hsum⟩ := Submodule.mem_span_iff_exists_finset_subset.mp
    (by rw [hP]; trivial : Module.finBasis ℝ A i ∈ Submodule.span ℝ (pure C u))
  exact ⟨s, c, hs, hcs, hsum⟩

private theorem cProper_basis_bound
    (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ f : A →L[ℝ] ℝ, cProper C u f →
        ‖f‖ ≤ Fintype.card (Fin (Module.finrank ℝ A)) •
          ‖((Module.finBasis ℝ A).equivFunL : A →L[ℝ] (Fin (Module.finrank ℝ A) → ℝ))‖ * M := by
  classical
  choose s c hs hcs hsum using pure_representation C u hclosed hstrict hspan
  let M : ℝ := ∑ i : Fin (Module.finrank ℝ A), ∑ a ∈ s i, ‖c i a‖
  have hM : 0 ≤ M := by
    dsimp [M]
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun a _ => abs_nonneg _))
  refine ⟨M, hM, ?_⟩
  intro f hf
  apply Module.Basis.opNorm_le (Module.finBasis ℝ A) hM
  intro i
  have hterm (a : A) (ha : a ∈ s i) : ‖f (c i a • a)‖ ≤ ‖c i a‖ := by
    have haP : a ∈ pure C u := hs i ha
    have haC := (pure_mem ⟨a, haP⟩).1
    have hau := (pure_mem ⟨a, haP⟩).2
    have hfa := hf a haC
    have hnorm : ‖f a‖ ≤ 1 := by
      rw [Real.norm_eq_abs]
      exact (abs_le.2 ⟨by linarith [hfa.1], hau ▸ hfa.2⟩)
    calc
      ‖f (c i a • a)‖ = ‖c i a • f a‖ := by rw [map_smul]
      _ = ‖c i a‖ * ‖f a‖ := norm_smul _ _
      _ ≤ ‖c i a‖ * 1 := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ = ‖c i a‖ := mul_one _
  have hbi : ‖f (Module.finBasis ℝ A i)‖ ≤ ∑ a ∈ s i, ‖c i a‖ := by
    rw [← hsum i, map_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a ha => hterm a ha)
  exact hbi.trans (Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin (Module.finrank ℝ A) => ∑ a ∈ s j, ‖c j a‖)
    (fun j _ => Finset.sum_nonneg (fun a _ => norm_nonneg _)) (Finset.mem_univ i))

theorem proper_compact
    (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤) :
    IsCompact {f : A →L[ℝ] ℝ | cProper C u f} := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨cProper_closed C u, ?_⟩
  obtain ⟨M, hM, hbound⟩ := cProper_basis_bound C u hclosed hstrict hspan
  refine isBounded_iff_forall_norm_le.mpr ⟨
    Fintype.card (Fin (Module.finrank ℝ A)) •
      ‖((Module.finBasis ℝ A).equivFunL : A →L[ℝ] (Fin (Module.finrank ℝ A) → ℝ))‖ * M, ?_⟩
  intro f hf
  exact hbound f hf

theorem face_compact
    (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤) (p : pure C u) :
    IsCompact {f : A →L[ℝ] ℝ | cConfirms C u p f} := by
  apply (proper_compact C u hclosed hstrict hspan).inter_right
  exact isClosed_eq
    (ContinuousLinearMap.apply ℝ ℝ (p : A)).continuous continuous_const

theorem face_nonempty
    (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x) (p : pure C u) :
    ({f : A →L[ℝ] ℝ | cConfirms C u p f} : Set (A →L[ℝ] ℝ)).Nonempty := by
  refine ⟨u.toContinuousLinearMap, ?_⟩
  refine ⟨?_, ?_⟩
  · intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    · exact ⟨(hstrict x hx hx0).le, le_rfl⟩
  · simpa [cProper] using (pure_mem p).2

theorem cComparison_eq_comparison
    (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) (p x : A) :
    cComparison C u p x = comparison C u p x := by
  apply congrArg sInf
  ext r
  constructor
  · rintro ⟨f, hf, hfx⟩
    exact ⟨f.toLinearMap, ⟨fun y hy => hf.1 y hy, hf.2⟩, hfx⟩
  · rintro ⟨f, hf, hfx⟩
    exact ⟨LinearMap.toContinuousLinearMap f, ⟨fun y hy => hf.1 y hy, hf.2⟩, hfx⟩

theorem comparison_attained
    (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤)
    (p : pure C u) (x : A) (hx : x ∈ C) :
    ∃ f : A →ₗ[ℝ] ℝ, confirms C u p f ∧ f x = comparison C u p x := by
  obtain ⟨f, hf, hmin⟩ := (face_compact C u hclosed hstrict hspan p).exists_isMinOn
    (face_nonempty C u hstrict p)
    ((ContinuousLinearMap.apply ℝ ℝ x).continuous.continuousOn)
  have hbounded : BddBelow {r : ℝ | ∃ g : A →L[ℝ] ℝ,
      cConfirms C u p g ∧ g x = r} := ⟨0, by
    rintro r ⟨g, hg, rfl⟩
    exact (hg.1 x hx).1⟩
  refine ⟨f.toLinearMap, ⟨fun y hy => hf.1 y hy, hf.2⟩, ?_⟩
  rw [← cComparison_eq_comparison C u p x]
  apply le_antisymm
  · refine le_csInf (s := {r : ℝ | ∃ g : A →L[ℝ] ℝ,
      cConfirms C u p g ∧ g x = r}) ?_ ?_
    · obtain ⟨g, hg⟩ := face_nonempty C u hstrict p
      exact ⟨g x, g, hg, rfl⟩
    · intro r hr
      obtain ⟨g, hg, hgr⟩ := hr
      have hfg : f x ≤ g x := hmin hg
      exact hgr ▸ hfg
  · exact csInf_le hbounded ⟨f, hf, rfl⟩

private theorem cComparison_lower
    (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hspan : Submodule.span ℝ (C : Set A) = ⊤)
    (p : pure C u) {x : A} (hx : x ∈ C) :
    0 ≤ cComparison C u p x := by
  refine le_csInf (s := {r : ℝ | ∃ f : A →L[ℝ] ℝ,
    cConfirms C u p f ∧ f x = r}) ?_ ?_
  · obtain ⟨f, hf⟩ := face_nonempty C u hstrict p
    exact ⟨f x, f, hf, rfl⟩
  · rintro r ⟨f, hf, hfx⟩
    exact hfx ▸ (hf.1 x hx).1

private theorem cComparison_upper
    (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x) (p : pure C u) {x : A} (hx : x ∈ C) :
    cComparison C u p x ≤ u x := by
  have hu : cConfirms C u p u.toContinuousLinearMap := by
    refine ⟨?_, ?_⟩
    · intro y hy
      by_cases hy0 : y = 0
      · simp [hy0]
      · exact ⟨(hstrict y hy hy0).le, le_rfl⟩
    · simp [cProper, (pure_mem p).2]
  exact csInf_le (s := {r : ℝ | ∃ f : A →L[ℝ] ℝ,
    cConfirms C u p f ∧ f x = r})
    ⟨0, by rintro r ⟨f, hf, hfx⟩; exact hfx ▸ (hf.1 x hx).1⟩
    ⟨u.toContinuousLinearMap, hu, rfl⟩

private theorem cComparison_le_of_confirms
    (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hspan : Submodule.span ℝ (C : Set A) = ⊤)
    (p : pure C u) {x : A} (hx : x ∈ C) (f : A →L[ℝ] ℝ)
    (hf : cConfirms C u p f) : cComparison C u p x ≤ f x := by
  exact csInf_le ⟨0, fun _ ⟨g, hg, hgx⟩ => hgx ▸ (hg.1 x hx).1⟩ ⟨f, hf, rfl⟩

private theorem cComparison_self
    (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x) (hspan : Submodule.span ℝ (C : Set A) = ⊤)
    (p : pure C u) : cComparison C u p (p : A) = 1 := by
  apply le_antisymm
  · exact cComparison_upper C u hstrict p (pure_mem p).1 |>.trans_eq (pure_mem p).2
  · refine le_csInf (s := {r : ℝ | ∃ f : A →L[ℝ] ℝ,
      cConfirms C u p f ∧ f (p : A) = r}) ?_ ?_
    · obtain ⟨f, hf⟩ := face_nonempty C u hstrict p
      exact ⟨f (p : A), f, hf, rfl⟩
    · rintro r ⟨f, hf, hfx⟩
      rw [← hfx, ← hf.2]

private theorem cComparison_concave
    (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤)
    (p : pure C u) (n : ℕ) (q : Fin n → pure C u) (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i * cComparison C u p (q i : A)) ≤
      cComparison C u p (∑ i, w i • (q i : A)) := by
  refine le_csInf (s := {r : ℝ | ∃ f : A →L[ℝ] ℝ,
      cConfirms C u p f ∧ f (∑ i, w i • (q i : A)) = r}) ?_ ?_
  · obtain ⟨f, hf⟩ := face_nonempty C u hstrict p
    exact ⟨f (∑ i, w i • (q i : A)), f, hf, rfl⟩
  · intro r hr
    obtain ⟨f, hf, rfl⟩ := hr
    have hsum : ∀ i, cComparison C u p (q i : A) ≤ f (q i : A) := fun i =>
      cComparison_le_of_confirms C u hclosed hstrict hspan p (pure_mem (q i)).1 f hf
    calc
      ∑ i, w i * cComparison C u p (q i : A) ≤ ∑ i, w i * f (q i : A) := by
        exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hsum i) (hw i)
      _ = f (∑ i, w i • (q i : A)) := by
        simp only [map_sum, map_smul, smul_eq_mul]

def purePairRelation (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (p q : pure C u) : Prop :=
  ∀ r : pure C u, cComparison C u p (r : A) + cComparison C u q (r : A) = 1

private theorem pair_relation_mixed
    (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤)
    (p q : pure C u) (hrel : purePairRelation C u p q) :
    ∀ x ∈ base C u,
      cComparison C u p x + cComparison C u q x = 1 := by
  have hpq0 : cComparison C u q (p : A) = 0 := by
    have h := hrel p
    rw [cComparison_self C u hclosed hstrict hspan p] at h
    linarith
  obtain ⟨fq, hfq, hfp⟩ := comparison_attained C u hclosed hstrict hspan q (p : A)
    (pure_mem p).1
  have hfp0 : fq p = 0 := by
    rw [hfp, ← cComparison_eq_comparison C u q (p : A), hpq0]
  let Fq : A →L[ℝ] ℝ := LinearMap.toContinuousLinearMap fq
  let Fp : A →L[ℝ] ℝ := u.toContinuousLinearMap - Fq
  have hFq : cConfirms C u q Fq := by
    refine ⟨fun x hx => hfq.1 x hx, ?_⟩
    simpa [Fq] using hfq.2
  have hFq0 : Fq p = 0 := by simpa [Fq] using hfp0
  have hFp : cConfirms C u p Fp := by
    refine ⟨?_, ?_⟩
    · intro x hx
      have hq := hfq.1 x hx
      refine ⟨?_, ?_⟩
      · change 0 ≤ u x - fq x
        linarith
      · change u x - fq x ≤ u x
        linarith
    · simp [Fp, hFq0, (pure_mem p).2]
  let PFace := {f : A →L[ℝ] ℝ // cConfirms C u p f}
  let QFace := {f : A →L[ℝ] ℝ // cConfirms C u q f}
  have hclosedS : IsClosed {x : A | ∀ f : PFace, ∀ g : QFace, 1 ≤ f.1 x + g.1 x} := by
    rw [show {x : A | ∀ f : PFace, ∀ g : QFace, 1 ≤ f.1 x + g.1 x} =
        (⋂ f : PFace, ⋂ g : QFace, {x : A | 1 ≤ f.1 x + g.1 x}) by
      ext x
      simp]
    exact isClosed_iInter (fun f => isClosed_iInter (fun g =>
      isClosed_le continuous_const (f.1.continuous.add g.1.continuous)))
  have hsubsetS : convexHull ℝ (pure C u) ⊆
      {x : A | ∀ f : PFace, ∀ g : QFace, 1 ≤ f.1 x + g.1 x} := by
    apply convexHull_min
    · intro r hr f g
      have hp := cComparison_le_of_confirms C u hclosed hstrict hspan p
        (pure_mem ⟨r, hr⟩).1 f.1 f.2
      have hq := cComparison_le_of_confirms C u hclosed hstrict hspan q
        (pure_mem ⟨r, hr⟩).1 g.1 g.2
      linarith [hrel ⟨r, hr⟩]
    · intro x hx y hy a b ha hb hab f g
      have hxf := hx f g
      have hyf := hy f g
      calc
        1 ≤ a * (f.1 x + g.1 x) + b * (f.1 y + g.1 y) := by
          linarith [mul_le_mul_of_nonneg_left hxf ha,
            mul_le_mul_of_nonneg_left hyf hb]
        _ = f.1 (a • x + b • y) + g.1 (a • x + b • y) := by
          simp only [map_add, map_smul, smul_eq_mul]
          ring
  have hbaseS : base C u ⊆
      {x : A | ∀ f : PFace, ∀ g : QFace, 1 ≤ f.1 x + g.1 x} := by
    rw [← closure_convexHull_extremePoints (base_compact hclosed hstrict)
      (base_convex C u)]
    exact closure_minimal hsubsetS hclosedS
  intro x hx
  obtain ⟨ep, hep, hepx⟩ := comparison_attained C u hclosed hstrict hspan p x hx.1
  obtain ⟨eq, heq, heqx⟩ := comparison_attained C u hclosed hstrict hspan q x hx.1
  have hpoint := hbaseS hx ⟨LinearMap.toContinuousLinearMap ep,
      ⟨fun y hy => hep.1 y hy, by simpa using hep.2⟩⟩ ⟨LinearMap.toContinuousLinearMap eq,
      ⟨fun y hy => heq.1 y hy, by simpa using heq.2⟩⟩
  have hlower : 1 ≤ comparison C u p x + comparison C u q x := by
    simpa [hepx, heqx] using hpoint
  have hupper : comparison C u p x + comparison C u q x ≤ 1 := by
    have hp := cComparison_le_of_confirms C u hclosed hstrict hspan p hx.1
      (LinearMap.toContinuousLinearMap (u - fq))
        ⟨by
          intro y hy
          have hq := hfq.1 y hy
          exact ⟨by simpa [sub_apply] using hq.2, by simpa [sub_apply] using hq.1⟩,
          by simpa [sub_apply, hfp0, (pure_mem p).2]⟩
    have hq := cComparison_le_of_confirms C u hclosed hstrict hspan q hx.1 Fq hFq
    have hc := add_le_add hp hq
    have hFq_apply : ∀ y, Fq y = fq y := by intro y; rfl
    rw [hFq_apply x] at hc
    have hc' : comparison C u p x + comparison C u q x ≤ 1 := by
      rw [← cComparison_eq_comparison C u p x, ← cComparison_eq_comparison C u q x]
      simpa [hx.2] using hc
    exact hc'
  have hlower' := hlower
  rw [← cComparison_eq_comparison C u p x] at hlower'
  rw [← cComparison_eq_comparison C u q x] at hlower'
  have hupper' := hupper
  rw [← cComparison_eq_comparison C u p x] at hupper'
  rw [← cComparison_eq_comparison C u q x] at hupper'
  linarith [hlower', hupper']

private theorem pair_affine_one
    (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤)
    (p q : pure C u) (hrel : purePairRelation C u p q)
    (n : ℕ) (z : Fin n → pure C u) (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    cComparison C u p (∑ i, w i • (z i : A)) =
      ∑ i, w i * cComparison C u p (z i : A) := by
  have hxC : (∑ i, w i • (z i : A)) ∈ C :=
    C.sum_mem (fun i _ => C.smul_mem (hw i) (pure_mem (z i)).1)
  have hxu : u (∑ i, w i • (z i : A)) = 1 := by
    simp only [map_sum, map_smul, smul_eq_mul, (pure_mem (z _)).2, mul_one, hw1]
  have hx : (∑ i, w i • (z i : A)) ∈ base C u := ⟨hxC, hxu⟩
  have hcp := cComparison_concave C u hclosed hstrict hspan p n z w hw
  have hcq := cComparison_concave C u hclosed hstrict hspan q n z w hw
  have hsumx := pair_relation_mixed C u hclosed hstrict hspan p q hrel _ hx
  have hpure : ∑ i, w i *
      (cComparison C u p (z i : A) + cComparison C u q (z i : A)) = 1 := by
    calc
      _ = ∑ i, w i * 1 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hrel (z i)]
      _ = 1 := by simpa [hw1]
  simp only [mul_add, Finset.sum_add_distrib] at hpure
  linarith

private theorem relation_preserved
    (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) (p0 : pure C u)
    (hAff : ∀ (n : ℕ) (z : Fin n → pure C u) (w : Fin n → ℝ),
      (∀ i, 0 ≤ w i) → (∑ i, w i = 1) →
      cComparison C u p0 (∑ i, w i • (z i : A)) =
        ∑ i, w i * cComparison C u p0 (z i : A))
    {ι : Type*} [Fintype ι] (q : ι → pure C u) (c : ι → ℝ)
    (hc : (∑ i, c i • (q i : A)) = 0) :
    ∑ i, c i * cComparison C u p0 (q i : A) = 0 := by
  classical
  let a : ι → ℝ := fun i => max (c i) 0
  let b : ι → ℝ := fun i => max (-c i) 0
  have hab (i : ι) : a i - b i = c i := max_zero_sub_max_neg_zero_eq_self _
  have hc0 : ∑ i, c i = 0 := by
    have hh := congrArg u hc
    simpa only [map_sum, map_smul, smul_eq_mul, (pure_mem _).2, mul_one, map_zero] using hh
  have hmasses : ∑ i, a i = ∑ i, b i := by
    apply sub_eq_zero.mp
    simpa only [← Finset.sum_sub_distrib, hab] using hc0
  have hvectors : ∑ i, a i • (q i : A) = ∑ i, b i • (q i : A) := by
    apply sub_eq_zero.mp
    simpa only [← Finset.sum_sub_distrib, ← sub_smul, hab] using hc
  let m := 1 + ∑ i, a i
  have hm : 0 < m := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun i _ => le_max_right (c i) 0))
  let q' : Option ι → pure C u := fun i => i.elim p0 q
  let a' : Option ι → ℝ := fun i => i.elim 1 a
  let b' : Option ι → ℝ := fun i => i.elim 1 b
  have ha' : ∀ i, 0 ≤ a' i := by
    intro i
    cases i with
    | none => exact zero_le_one
    | some i => exact le_max_right _ _
  have hb' : ∀ i, 0 ≤ b' i := by
    intro i
    cases i with
    | none => exact zero_le_one
    | some i => exact le_max_right _ _
  have hsa : ∑ i, a' i = m := by simp [a', m, Fintype.sum_option]
  have hsb : ∑ i, b' i = m := by simp [b', m, Fintype.sum_option, hmasses]
  have hmix : (∑ i, (a' i / m) • (q' i : A)) =
      ∑ i, (b' i / m) • (q' i : A) := by
    simp only [div_eq_inv_mul, mul_smul, ← Finset.smul_sum]
    congr 1
    simpa [a', b', q', Fintype.sum_option] using
      congrArg (fun z : A => (p0 : A) + z) hvectors
  have hwa : ∑ i, a' i / m = 1 := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul, hsa, mul_inv_cancel₀ hm.ne']
  have hwb : ∑ i, b' i / m = 1 := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul, hsb, mul_inv_cancel₀ hm.ne']
  let e := Fintype.equivFin (Option ι)
  have hleft := hAff (Fintype.card (Option ι)) (fun j => q' (e.symm j))
    (fun j => a' (e.symm j) / m)
    (fun j => div_nonneg (ha' _) hm.le) (e.symm.sum_comp (fun i => a' i / m) |>.trans hwa)
  have hright := hAff (Fintype.card (Option ι)) (fun j => q' (e.symm j))
    (fun j => b' (e.symm j) / m)
    (fun j => div_nonneg (hb' _) hm.le) (e.symm.sum_comp (fun i => b' i / m) |>.trans hwb)
  have hleft' : cComparison C u p0 (∑ i, (a' i / m) • (q' i : A)) =
      ∑ i, (a' i / m) * cComparison C u p0 (q' i : A) := by
    rw [show (∑ j, (a' (e.symm j) / m) • (q' (e.symm j) : A)) =
        ∑ i, (a' i / m) • (q' i : A) from e.symm.sum_comp (fun i => (a' i / m) • (q' i : A)),
      show (∑ j, (a' (e.symm j) / m) * cComparison C u p0 (q' (e.symm j) : A)) =
        ∑ i, (a' i / m) * cComparison C u p0 (q' i : A) from
          e.symm.sum_comp (fun i => (a' i / m) * cComparison C u p0 (q' i : A))] at hleft
    exact hleft
  have hright' : cComparison C u p0 (∑ i, (b' i / m) • (q' i : A)) =
      ∑ i, (b' i / m) * cComparison C u p0 (q' i : A) := by
    rw [show (∑ j, (b' (e.symm j) / m) • (q' (e.symm j) : A)) =
        ∑ i, (b' i / m) • (q' i : A) from e.symm.sum_comp (fun i => (b' i / m) • (q' i : A)),
      show (∑ j, (b' (e.symm j) / m) * cComparison C u p0 (q' (e.symm j) : A)) =
        ∑ i, (b' i / m) * cComparison C u p0 (q' i : A) from
          e.symm.sum_comp (fun i => (b' i / m) * cComparison C u p0 (q' i : A))] at hright
    exact hright
  rw [hmix, hright'] at hleft'
  have heq : ∑ i, a' i * cComparison C u p0 (q' i : A) =
      ∑ i, b' i * cComparison C u p0 (q' i : A) := by
    have hh := congrArg (fun r : ℝ => r * m) hleft'
    simpa only [Finset.sum_mul, div_mul_eq_mul_div, div_mul_cancel₀ _ hm.ne'] using hh.symm
  have hcancel : ∑ i, a i * cComparison C u p0 (q i : A) =
      ∑ i, b i * cComparison C u p0 (q i : A) := by
    simpa [a', b', q', Fintype.sum_option] using heq
  have hh := sub_eq_zero.mpr hcancel
  simpa only [← Finset.sum_sub_distrib, ← sub_mul, hab] using hh

theorem pure_exhaustion_entry
    (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤)
    (p q : pure C u) (hrel : purePairRelation C u p q) :
    p ≠ q ∧
    (∃ f : A →ₗ[ℝ] ℝ, confirms C u q f ∧ f p = 0) ∧
    (∀ x ∈ base C u, comparison C u p x + comparison C u q x = 1) ∧
    ∃ ep eq : A →ₗ[ℝ] ℝ,
      confirms C u p ep ∧ confirms C u q eq ∧
      (∀ f, confirms C u p f → ∀ x ∈ C, ep x ≤ f x) ∧
      (∀ f, confirms C u q f → ∀ x ∈ C, eq x ≤ f x) ∧
      (∀ x ∈ C, comparison C u p x = ep x) ∧
      (∀ x ∈ C, comparison C u q x = eq x) ∧
      ep + eq = u := by
  have hK := base_compact hclosed hstrict
  have hmixed := pair_relation_mixed C u hclosed hstrict hspan p q hrel
  have hAffP : ∀ (n : ℕ) (z : Fin n → pure C u) (w : Fin n → ℝ),
      (∀ i, 0 ≤ w i) → (∑ i, w i = 1) →
      cComparison C u p (∑ i, w i • (z i : A)) =
        ∑ i, w i * cComparison C u p (z i : A) := by
    intro n z w hw hw1
    exact pair_affine_one C u hclosed hstrict hspan p q hrel n z w hw hw1
  have hAffQ : ∀ (n : ℕ) (z : Fin n → pure C u) (w : Fin n → ℝ),
      (∀ i, 0 ≤ w i) → (∑ i, w i = 1) →
      cComparison C u q (∑ i, w i • (z i : A)) =
        ∑ i, w i * cComparison C u q (z i : A) := by
    intro n z w hw hw1
    apply pair_affine_one C u hclosed hstrict hspan q p
      (fun r => by simpa [add_comm] using hrel r) n z w hw hw1
  have hbalP : balanced (pure C u) (fun r => cComparison C u p (r : A)) := by
    intro s c hc
    exact relation_preserved C u p hAffP (fun i : s => i.1) c hc.2.1
  have hbalQ : balanced (pure C u) (fun r => cComparison C u q (r : A)) := by
    intro s c hc
    exact relation_preserved C u q hAffQ (fun i : s => i.1) c hc.2.1
  obtain ⟨ep, hep⟩ := descends hbalP (pure_span hK hstrict hspan)
  obtain ⟨eq, heq⟩ := descends hbalQ (pure_span hK hstrict hspan)
  have hconfP : confirms C u p ep := by
    refine ⟨cone_bound hK hstrict (fun r => ?_), ?_⟩
    · rw [hep r]
      exact ⟨cComparison_lower C u hclosed hstrict hspan p (pure_mem r).1,
        by simpa [(pure_mem r).2] using cComparison_upper C u hstrict p (pure_mem r).1⟩
    · rw [hep p]
      exact cComparison_self C u hclosed hstrict hspan p
  have hconfQ : confirms C u q eq := by
    refine ⟨cone_bound hK hstrict (fun r => ?_), ?_⟩
    · rw [heq r]
      exact ⟨cComparison_lower C u hclosed hstrict hspan q (pure_mem r).1,
        by simpa [(pure_mem r).2] using cComparison_upper C u hstrict q (pure_mem r).1⟩
    · rw [heq q]
      exact cComparison_self C u hclosed hstrict hspan q
  have hleastP : ∀ f, confirms C u p f → ∀ x ∈ C, ep x ≤ f x := by
    intro f hf x hx
    have hn : ∀ r : pure C u, 0 ≤ (f - ep) r := by
      intro r
      have hle := cComparison_le_of_confirms C u hclosed hstrict hspan p
        (pure_mem r).1 (LinearMap.toContinuousLinearMap f)
        ⟨fun y hy => hf.1 y hy, by simpa using hf.2⟩
      simpa [LinearMap.sub_apply, hep r] using hle
    have h := nonneg_on_cone hK hstrict hn x hx
    simpa [LinearMap.sub_apply] using h
  have hleastQ : ∀ f, confirms C u q f → ∀ x ∈ C, eq x ≤ f x := by
    intro f hf x hx
    have hn : ∀ r : pure C u, 0 ≤ (f - eq) r := by
      intro r
      have hle := cComparison_le_of_confirms C u hclosed hstrict hspan q
        (pure_mem r).1 (LinearMap.toContinuousLinearMap f)
        ⟨fun y hy => hf.1 y hy, by simpa using hf.2⟩
      simpa [LinearMap.sub_apply, heq r] using hle
    have h := nonneg_on_cone hK hstrict hn x hx
    simpa [LinearMap.sub_apply] using h
  have hcompP : ∀ x ∈ C, comparison C u p x = ep x := by
    intro x hx
    rw [← cComparison_eq_comparison C u p x]
    apply le_antisymm
    · exact cComparison_le_of_confirms C u hclosed hstrict hspan p hx
        (LinearMap.toContinuousLinearMap ep) ⟨fun y hy => hconfP.1 y hy, by simpa using hconfP.2⟩
    · apply le_csInf (s := {r : ℝ | ∃ f : A →L[ℝ] ℝ,
        cConfirms C u p f ∧ f x = r})
      · obtain ⟨f, hf⟩ := face_nonempty C u hstrict p
        exact ⟨f x, f, hf, rfl⟩
      · rintro r ⟨f, hf, hfx⟩
        exact hfx ▸ hleastP f.toLinearMap
          ⟨fun y hy => hf.1 y hy, by simpa using hf.2⟩ (x := x) hx
  have hcompQ : ∀ x ∈ C, comparison C u q x = eq x := by
    intro x hx
    rw [← cComparison_eq_comparison C u q x]
    apply le_antisymm
    · exact cComparison_le_of_confirms C u hclosed hstrict hspan q hx
        (LinearMap.toContinuousLinearMap eq) ⟨fun y hy => hconfQ.1 y hy, by simpa using hconfQ.2⟩
    · apply le_csInf (s := {r : ℝ | ∃ f : A →L[ℝ] ℝ,
        cConfirms C u q f ∧ f x = r})
      · obtain ⟨f, hf⟩ := face_nonempty C u hstrict q
        exact ⟨f x, f, hf, rfl⟩
      · rintro r ⟨f, hf, hfx⟩
        exact hfx ▸ hleastQ f.toLinearMap
          ⟨fun y hy => hf.1 y hy, by simpa using hf.2⟩ (x := x) hx
  have hsum : ep + eq = u := by
    apply LinearMap.ext_on (pure_span hK hstrict hspan)
    intro r hr
    let rr : pure C u := ⟨r, hr⟩
    calc
      (ep + eq) r = cComparison C u p r + cComparison C u q r := by
        change ep (rr : A) + eq (rr : A) =
          cComparison C u p (rr : A) + cComparison C u q (rr : A)
        rw [hep rr, heq rr]
      _ = 1 := hrel rr
      _ = u r := (pure_mem rr).2.symm
  have hpq : p ≠ q := by
    intro hpq
    have h := hrel p
    rw [hpq] at h
    rw [cComparison_self C u hclosed hstrict hspan q] at h
    linarith
  have hzero : ∃ f : A →ₗ[ℝ] ℝ, confirms C u q f ∧ f p = 0 := by
    obtain ⟨f, hf, hfx⟩ := comparison_attained C u hclosed hstrict hspan q (p : A)
      (pure_mem p).1
    refine ⟨f, hf, ?_⟩
    rw [hfx, ← cComparison_eq_comparison C u q (p : A)]
    have h := hrel p
    rw [cComparison_self C u hclosed hstrict hspan p] at h
    linarith
  have hmixed' : ∀ x ∈ base C u,
      comparison C u p x + comparison C u q x = 1 := by
    intro x hx
    simpa only [cComparison_eq_comparison] using hmixed x hx
  exact ⟨hpq, hzero, hmixed', ep, eq, hconfP, hconfQ, hleastP, hleastQ,
    hcompP, hcompQ, hsum⟩


end D5.S3.Quantum.Foundation.PureExhaustionConfirmation
