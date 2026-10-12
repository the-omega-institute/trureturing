/- GID: D5/S3/Geometry/AlphaGeometry/CoordinateCurvatureMajorization
   generality: G
   mirror-B: D5/B/S3/Geometry/AlphaGeometry/CoordinateCurvatureMajorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict positive T-transform chains for spectral cube-root curvature. -/

/-
admission_basis: escape-witness
escape_witness: spectral_moreMixed_strict
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15716
DTR reading: DTR-Unregistered. No Reg mirror is delivered. The source-family registration lacks a law-violating variation, whole-family slot sensitivity, and actual observational-dependence proofs.
The positive chain is the frozen LogScalarCurvatureMonotone.moreMixed_positive_chain. The permutation-or-strict-step invariant and its strict curvature consumer are the retained content.
Direct frozen dependencies: the declaration identities below.
F1: D5/S3/Geometry/AlphaGeometry/LogScalarCurvatureMonotone.moreMixed_positive_chain; declaration statement_id=sha256:f19ea714dc2955a566704efc00c1ce31eb52e2401a946d90a2c48a02479565f6
F2: D5/S3/Geometry/AlphaGeometry/MajorizationTransfer.IsTTransform; declaration statement_id=sha256:42e55cff12a5c9f54284d516691bb017d9d7182af2419124015df29f459afefc
F3: D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.P; declaration statement_id=sha256:a10d641664aaff2022a38c921d56a39f9764079f2823390614fec9abe97aa86d
F4: D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.P_evalSum; declaration statement_id=sha256:7754691acf8f98426f2359983e218acaea91f977130664f3d71b32bc3cdf3e47
F5: D5/S3/Geometry/AlphaGeometry/PairCurvatureInequality.coordinateB_le_sum_sq; declaration statement_id=sha256:13e938553d0487fbdba26676b6929f9f746a6568371cb9df26c2616d69dc626a
F6: D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.PositiveT; declaration statement_id=sha256:6af391fa094c3e0f33c4f7c75181c22e1e3e1c7a571edd9abd444a08b4d0b83a
F7: D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.moreMixed; declaration statement_id=sha256:565b9b70d03155f061b4fe949164aa173255e7ceac42365730d8420ff3c7616a
F8: D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.simplex; declaration statement_id=sha256:c3964d9a4646b69a3c4c6a66ca1cb9591d79f2dcbb20c146af611d50469eeed8
Per-declaration classification; non-proposition definitions carry no content claim.
proof_shape: StrictT: bind-only; escape_witness: none; consumers: CoordinateCurvatureMajorization.positiveT_perm_or_strict, CoordinateCurvatureMajorization.chain_perm_or_strict, CoordinateCurvatureMajorization.moreMixed_strict_step, CoordinateCurvatureMajorization.strict_t_transform, CoordinateCurvatureMajorization.positiveT_monotone, CoordinateCurvatureMajorization.spectral_moreMixed_strict; frozen_dependencies: none
proof_shape: permutation_refl: bind-only; escape_witness: none; consumers: CoordinateCurvatureMajorization.positiveT_perm_or_strict, CoordinateCurvatureMajorization.chain_perm_or_strict; frozen_dependencies: none
proof_shape: permutation_trans: bind-only; escape_witness: none; consumers: CoordinateCurvatureMajorization.chain_perm_or_strict; frozen_dependencies: none
proof_shape: ttransform_equal_values: bind-only; escape_witness: none; consumers: CoordinateCurvatureMajorization.positiveT_perm_or_strict; frozen_dependencies: none
proof_shape: positiveT_perm_or_strict: bind-only; escape_witness: none; consumers: CoordinateCurvatureMajorization.chain_perm_or_strict, CoordinateCurvatureMajorization.positiveT_monotone; frozen_dependencies: F2,F6
proof_shape: chain_perm_or_strict: content; escape_witness: CoordinateCurvatureMajorization.chain_perm_or_strict; consumers: CoordinateCurvatureMajorization.moreMixed_strict_step; frozen_dependencies: F2,F6
proof_shape: moreMixed_strict_step: content; escape_witness: CoordinateCurvatureMajorization.chain_perm_or_strict; consumers: CoordinateCurvatureMajorization.spectral_moreMixed_strict; frozen_dependencies: F1,F2,F6,F7,F8
proof_shape: mixPair_swap: bind-only; escape_witness: none; consumers: CoordinateCurvatureMajorization.strict_t_transform; frozen_dependencies: none
proof_shape: strict_t_transform: content; escape_witness: CubeRootSpectralMonotonicity.Pair.strict_t_transform_any_pair; consumers: CoordinateCurvatureMajorization.positiveT_monotone, CoordinateCurvatureMajorization.spectral_moreMixed_strict; frozen_dependencies: F3,F4,F5
proof_shape: permutation_invariant: bind-only; escape_witness: none; consumers: CoordinateCurvatureMajorization.positiveT_monotone; frozen_dependencies: F3,F4
proof_shape: positiveT_monotone: content; escape_witness: CubeRootSpectralMonotonicity.Pair.strict_t_transform_any_pair; consumers: CoordinateCurvatureMajorization.chain_monotone; frozen_dependencies: F2,F3,F4,F5,F6
proof_shape: chain_monotone: content; escape_witness: CubeRootSpectralMonotonicity.Pair.strict_t_transform_any_pair; consumers: CoordinateCurvatureMajorization.spectral_moreMixed_monotone, CoordinateCurvatureMajorization.spectral_moreMixed_strict; frozen_dependencies: F2,F3,F4,F5,F6
proof_shape: spectral_moreMixed_monotone: content; escape_witness: CubeRootSpectralMonotonicity.Pair.strict_t_transform_any_pair; consumers: QuantumCubeRootScalarCurvatureMonotone.result; frozen_dependencies: F1,F2,F3,F4,F5,F6,F7,F8
proof_shape: spectral_moreMixed_strict: content; escape_witness: CoordinateCurvatureMajorization.spectral_moreMixed_strict; consumers: QuantumCubeRootScalarCurvatureMonotone.result; frozen_dependencies: F1,F2,F3,F4,F5,F6,F7,F8
-/


import D5.S3.Geometry.AlphaGeometry.CubeRootSpectralMonotonicity
import D5.S3.Geometry.AlphaGeometry.LogScalarCurvatureMonotone

noncomputable section
open scoped BigOperators Topology
open Filter
namespace D5.S3.Geometry.AlphaGeometry.CoordinateCurvatureMajorization

open D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing
open D5.S3.Geometry.AlphaGeometry.MajorizationTransfer.FiniteVector
open D5.S3.Geometry.AlphaGeometry.CubeRootSpectralMonotonicity.Vector
open D5.S3.Geometry.AlphaGeometry.CubeRootSpectralMonotonicity.Pair
private def StrictT {n : ℕ} (p q : Fin n → ℝ) : Prop :=
  ∃ (i j : Fin n) (t : ℝ), 0 < t ∧ t < 1 ∧ p i ≠ p j ∧ q = ((1-t) • p+t • (p ∘ Equiv.swap i j))

private lemma permutation_refl {n : ℕ} (p : Fin n → ℝ) : (∃ π : Equiv.Perm (Fin n), p = p ∘ π) :=
  ⟨1,by simp⟩

private lemma permutation_trans {n : ℕ} {p q r : Fin n → ℝ}
    (h₁ : (∃ π : Equiv.Perm (Fin n), q = p ∘ π)) (h₂ : (∃ π : Equiv.Perm (Fin n), r = q ∘ π)) : (∃ π : Equiv.Perm (Fin n), r = p ∘ π) := by
  rcases h₁ with ⟨π,rfl⟩
  rcases h₂ with ⟨σ,rfl⟩
  exact ⟨σ.trans π,rfl⟩

private lemma ttransform_equal_values {n : ℕ} (x : Fin n → ℝ) (i j : Fin n) (t : ℝ)
    (hij : x i = x j) : ((1-t) • x+t • (x ∘ Equiv.swap i j)) = x := by
  ext k
  by_cases hki : k = i
  · subst k
    simp [hij]
    ring
  by_cases hkj : k = j
  · subst k
    simp [hij]
    ring
  · simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
    ring

private lemma positiveT_perm_or_strict {n : ℕ} {p q : Fin n → ℝ} (h : PositiveT p q) :
    (∃ π : Equiv.Perm (Fin n), q = p ∘ π) ∨ StrictT p q := by
  rcases h.1 with ⟨i,j,t,ht0,ht1,hq⟩
  by_cases ht : t = 0
  · left
    subst t
    simpa [hq] using permutation_refl p
  by_cases ht' : t = 1
  · left
    refine ⟨Equiv.swap i j,?_⟩
    simpa [ht'] using hq
  by_cases hij : p i = p j
  · left
    have he : q = p := by
      rw [hq]
      exact ttransform_equal_values p i j t hij
    simpa [he] using permutation_refl p
  · right
    exact ⟨i,j,t,lt_of_le_of_ne ht0 (Ne.symm ht),lt_of_le_of_ne ht1 ht',hij,
      hq⟩

private lemma chain_perm_or_strict {n : ℕ} {p q : Fin n → ℝ}
    (h : Relation.ReflTransGen PositiveT p q) :
    (∃ π : Equiv.Perm (Fin n), q = p ∘ π) ∨ ∃ a b : Fin n → ℝ,
      Relation.ReflTransGen PositiveT p a ∧ PositiveT a b ∧ StrictT a b ∧
        Relation.ReflTransGen PositiveT b q := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl x => exact Or.inl (permutation_refl x)
  | single h =>
    rcases positiveT_perm_or_strict h with hp | hs
    · exact Or.inl hp
    · exact Or.inr ⟨_,_,Relation.ReflTransGen.refl,h,hs,Relation.ReflTransGen.refl⟩
  | trans h₁ h₂ ih₁ ih₂ =>
    rcases ih₁ with hp₁ | ⟨a,b,hpa,hab,hs,hbm⟩
    · rcases ih₂ with hp₂ | ⟨a,b,hma,hab,hs,hbq⟩
      · exact Or.inl (permutation_trans hp₁ hp₂)
      · exact Or.inr ⟨a,b,h₁.trans hma,hab,hs,hbq⟩
    · exact Or.inr ⟨a,b,hpa,hab,hs,hbm.trans h₂⟩

private theorem moreMixed_strict_step {n : ℕ} (p q : Fin n → ℝ)
    (hp : p ∈ simplex n) (hq : q ∈ simplex n) (hm : moreMixed q p)
    (hnp : ¬ (∃ π : Equiv.Perm (Fin n), q = p ∘ π)) :
    ∃ a b : Fin n → ℝ, Relation.ReflTransGen PositiveT p a ∧
      PositiveT a b ∧ StrictT a b ∧ Relation.ReflTransGen PositiveT b q := by
  exact (chain_perm_or_strict (D5.S3.Geometry.AlphaGeometry.LogScalarCurvatureMonotone.moreMixed_positive_chain q p hq hp hm)).resolve_left hnp

private lemma mixPair_swap {n : ℕ} (p : Fin n → ℝ) (i j : Fin n) (t : ℝ) :
    ((1-t) • p+t • (p ∘ Equiv.swap i j)) = ((1-t) • p+t • (p ∘ Equiv.swap j i)) := by
  rw [Equiv.swap_comm]

private theorem strict_t_transform {n : ℕ} (hn : 2 ≤ n) (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) {q : Fin n → ℝ} (h : StrictT p q) :
    lambdaRatio p < lambdaRatio q := by
  rcases h with ⟨i,j,t,ht0,ht1,hij,rfl⟩
  rcases lt_or_gt_of_ne hij with hij | hij
  · rw [mixPair_swap]
    exact strict_t_transform_any_pair n hn p hp j i hij t ht0 ht1
  · exact strict_t_transform_any_pair n hn p hp i j hij t ht0 ht1

private theorem permutation_invariant {n : ℕ} (p q : Fin n → ℝ) (h : (∃ π : Equiv.Perm (Fin n), q = p ∘ π)) :
    lambdaRatio q = lambdaRatio p := by
  rcases h with ⟨π,rfl⟩
  exact lambdaRatio_perm p π

private lemma positiveT_monotone {n : ℕ} (hn : 2 ≤ n) {p q : Fin n → ℝ}
    (h : PositiveT p q) : lambdaRatio p ≤ lambdaRatio q := by
  rcases positiveT_perm_or_strict h with he | hs
  · exact (permutation_invariant p q he).symm.le
  · exact (strict_t_transform hn p h.2.1 hs).le

private lemma chain_monotone {n : ℕ} (hn : 2 ≤ n) {p q : Fin n → ℝ}
    (h : Relation.ReflTransGen PositiveT p q) : lambdaRatio p ≤ lambdaRatio q := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl x => exact le_rfl
  | single ht => exact positiveT_monotone hn ht
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem spectral_moreMixed_monotone {n : ℕ} (hn : 2 ≤ n) (p q : Fin n → ℝ)
    (hp : p ∈ simplex n) (hq : q ∈ simplex n) (hm : moreMixed q p) :
    lambdaRatio p ≤ lambdaRatio q := by
  exact chain_monotone hn
    (D5.S3.Geometry.AlphaGeometry.LogScalarCurvatureMonotone.moreMixed_positive_chain q p hq hp hm)

theorem spectral_moreMixed_strict {n : ℕ} (hn : 2 ≤ n) (p q : Fin n → ℝ)
    (hp : p ∈ simplex n) (hq : q ∈ simplex n) (hm : moreMixed q p)
    (hnp : ¬ ∃ π : Equiv.Perm (Fin n), q = p ∘ π) :
    lambdaRatio p < lambdaRatio q := by
  obtain ⟨a,b,hpa,hab,hs,hbq⟩ := moreMixed_strict_step p q hp hq hm hnp
  exact lt_of_le_of_lt (chain_monotone hn hpa)
    (lt_of_lt_of_le (strict_t_transform hn a hab.2.1 hs) (chain_monotone hn hbq))


end D5.S3.Geometry.AlphaGeometry.CoordinateCurvatureMajorization
