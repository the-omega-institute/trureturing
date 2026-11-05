/- GID: D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation
   generality: I
   mirror-B: D5/B/S3/HomologicalAlgebra/LocalityTensorProductRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.claim; result=D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.result; claim=D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation.claim
   digest: Six projected lines refute both conjectures for componentwise and four-way locality. -/

import Mathlib.Tactic

noncomputable section

namespace D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation

def IsLocalityVectorSpace (K : Type) {E : Type} [Field K] [AddCommGroup E] [Module K E]
    (r : E → E → Prop) : Prop :=
  (∀ ⦃x y⦄, r x y → r y x) ∧ r 0 0 ∧ ∀ U : Set E,
    ∃ S : Submodule K E, (S : Set E) = {x | ∀ u ∈ U, r u x}

def localityProduct {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    (r : E → E → Prop) (V W : Submodule K E) : Set (E × E) :=
  {p | p.1 ∈ V ∧ p.2 ∈ W ∧ r p.1 p.2}

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

/-- Pairwise locality of all four entries from arXiv:2506.09493v1, LOC.tex,
lines 220 and 743–747. The six pairs include those inside each generator. -/
def fourWay (E : Type) (r : E → E → Prop) (p q : E × E) : Prop :=
  r p.1 p.2 ∧ r p.1 q.1 ∧ r p.1 q.2 ∧ r p.2 q.1 ∧ r p.2 q.2 ∧ r q.1 q.2

def quotientRel {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    (r : E → E → Prop) (s : E × E → E × E → Prop)
    (V W : Submodule K E) (a b : localityTensor r V W) : Prop :=
  Relation.Map (fun u v : freeSpan r V W => spanRel s u.1 v.1)
    Submodule.Quotient.mk Submodule.Quotient.mk a b

def LocalityCompatible {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    (r : E → E → Prop) (W : Submodule K E) : Prop :=
  ∀ x y z, ∀ w ∈ W, r x y → r (x + w) z →
    ∃ w' ∈ W, r (x + w') y ∧ r (x + w') z

def TensorConjecture (s : ∀ E : Type, (E → E → Prop) → E × E → E × E → Prop) : Prop :=
  ∀ (K E : Type) [Field K] [CharZero K] [AddCommGroup E] [Module K E]
    (r : E → E → Prop) (V W : Submodule K E),
    IsLocalityVectorSpace K r → IsLocalityVectorSpace K (quotientRel r (s E r) V W)

def PairConjecture (s : ∀ E : Type, (E → E → Prop) → E × E → E × E → Prop) : Prop :=
  ∀ (K E : Type) [Field K] [CharZero K] [AddCommGroup E] [Module K E]
    (r : E → E → Prop) (V W : Submodule K E), IsLocalityVectorSpace K r →
    LocalityCompatible (fun a b : freeSpan r V W => spanRel (s E r) a.1 b.1)
      ((bilIdeal r V W).comap (freeSpan r V W).subtype)

def claim : Prop :=
  TensorConjecture (fun _ r => Prod.RProd r r) ∨ TensorConjecture fourWay ∨
    PairConjecture (fun _ r => Prod.RProd r r) ∨ PairConjecture fourWay

private def project : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  LinearMap.funLeft ℝ ℝ (Fin.castAdd 2)

private def direction (i : Fin 6) : Fin 3 → ℝ :=
  ![![0, 1, 0], ![1, 1, 0], ![1, -1, 0], ![0, 0, 1], ![1, 0, 1], ![1, 0, -1]] i

private def line (i : Fin 6) : Submodule ℝ (Fin 3 → ℝ) :=
  Submodule.span ℝ {direction i}

private def rel (v t : Fin 5 → ℝ) : Prop :=
  (project v = 0 ∨ project t = 0 ∨ ∃ i, project v ∈ line i ∧ project t ∈ line i) ∧
    v 3 * t 2 = 0 ∧ t 3 * v 2 = 0 ∧ v 4 * t 1 = 0 ∧ t 4 * v 1 = 0

private def X (k : Fin 5) : (Fin 5 → ℝ) × (Fin 5 → ℝ) →₀ ℝ :=
  (1 / 2 : ℝ) • Finsupp.single (Pi.single 0 1 + Pi.single k 1, Pi.single 0 1 + Pi.single k 1) 1 +
    (1 / 2 : ℝ) • Finsupp.single (Pi.single 0 1 - Pi.single k 1, Pi.single 0 1 - Pi.single k 1) 1 -
    Finsupp.single (Pi.single k 1, Pi.single k 1) 1

private def Y (i : Fin 5) : (Fin 5 → ℝ) × (Fin 5 → ℝ) →₀ ℝ :=
  Finsupp.single (Pi.single i 1, Pi.single i 1) 1

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
    norm_num [direction.eq_1, Pi.smul_apply, smul_eq_mul] at h0 h1 h2 ⊢ <;>
    (exfalso; apply hn; linarith)

private def projectedPolar (v : Fin 5 → ℝ) : Submodule ℝ (Fin 5 → ℝ) := by
  classical
  exact if project v = 0 then ⊤ else
    if h : ∃ i, project v ∈ line i then (line h.choose).comap project
    else LinearMap.ker project

private theorem mem_projectedPolar {v t : Fin 5 → ℝ} :
    t ∈ projectedPolar v ↔ project v = 0 ∨ project t = 0 ∨
      ∃ i, project v ∈ line i ∧ project t ∈ line i := by
  classical
  rw [projectedPolar.eq_1]
  split_ifs with hv hi
  · simp only [Submodule.mem_top, hv, true_or]
  · rw [Submodule.mem_comap]
    constructor
    · intro ht
      exact Or.inr (Or.inr ⟨hi.choose, hi.choose_spec, ht⟩)
    · rintro (h | h | ⟨i, hit, ht⟩)
      · exact (hv h).elim
      · rw [h]; exact (line hi.choose).zero_mem
      · simpa only [line_unique hv hit hi.choose_spec] using ht
  · rw [LinearMap.mem_ker]
    constructor
    · intro ht
      exact Or.inr (Or.inl ht)
    · rintro (h | h | ⟨i, hit, _⟩)
      · exact (hv h).elim
      · exact h
      · exact (hi ⟨i, hit⟩).elim

private def singletonPolar (v : Fin 5 → ℝ) : Submodule ℝ (Fin 5 → ℝ) :=
  projectedPolar v ⊓
    (LinearMap.ker ((v 3) • (LinearMap.proj 2 : (Fin 5 → ℝ) →ₗ[ℝ] ℝ)) ⊓
    (LinearMap.ker ((v 2) • (LinearMap.proj 3 : (Fin 5 → ℝ) →ₗ[ℝ] ℝ)) ⊓
    (LinearMap.ker ((v 4) • (LinearMap.proj 1 : (Fin 5 → ℝ) →ₗ[ℝ] ℝ)) ⊓
      LinearMap.ker ((v 1) • (LinearMap.proj 4 : (Fin 5 → ℝ) →ₗ[ℝ] ℝ)))))

private theorem mem_singletonPolar {v t : Fin 5 → ℝ} : t ∈ singletonPolar v ↔ rel v t := by
  simp only [singletonPolar.eq_1, Submodule.mem_inf, mem_projectedPolar, LinearMap.mem_ker,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, rel.eq_1,
    mul_comm (v 2) (t 3), mul_comm (v 1) (t 4)]

private theorem rel_locality : IsLocalityVectorSpace ℝ rel := by
  refine ⟨?_, ?_, ?_⟩
  · intro v t h
    rcases h with ⟨hp, h1, h2, h3, h4⟩
    refine ⟨?_, h2, h1, h4, h3⟩
    rcases hp with hp | hp | ⟨i, hi, hj⟩
    · exact Or.inr (Or.inl hp)
    · exact Or.inl hp
    · exact Or.inr (Or.inr ⟨i, hj, hi⟩)
  · exact mem_singletonPolar.mp (singletonPolar 0).zero_mem
  · intro U
    refine ⟨sInf (singletonPolar '' U), ?_⟩
    ext t
    simp only [SetLike.mem_coe, Set.mem_setOf_eq, Submodule.mem_sInf, Set.mem_image,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_singletonPolar]

private theorem diagonal_supported (v : Fin 5 → ℝ) (i : Fin 6)
    (hp : project v = direction i) (h3 : v 3 = 0) (h4 : v 4 = 0) :
    Finsupp.single (v, v) 1 ∈ freeSpan rel (⊤ : Submodule ℝ (Fin 5 → ℝ)) ⊤ := by
  apply Finsupp.single_mem_supported
  refine ⟨Submodule.mem_top, Submodule.mem_top, ?_⟩
  unfold rel
  refine ⟨Or.inr (Or.inr ⟨i, ?_, ?_⟩), ?_⟩
  · rw [hp]; exact Submodule.mem_span_singleton_self _
  · rw [hp]; exact Submodule.mem_span_singleton_self _
  · simp only [h3, h4, zero_mul, and_self]

private theorem X_supported (k : Fin 5) (hk : k = 1 ∨ k = 2) :
    X k ∈ freeSpan rel (⊤ : Submodule ℝ (Fin 5 → ℝ)) ⊤ := by
  rcases hk with rfl | rfl
  · unfold X
    apply Submodule.sub_mem
    · apply Submodule.add_mem
      · apply Submodule.smul_mem; apply diagonal_supported _ 1 <;>
        solve
        | norm_num [Pi.single_apply]
        | ext j; fin_cases j <;>
            norm_num [project.eq_1, direction.eq_1, Pi.single_apply]
      · apply Submodule.smul_mem; apply diagonal_supported _ 2 <;>
        solve
        | norm_num [Pi.single_apply]
        | ext j; fin_cases j <;>
            norm_num [project.eq_1, direction.eq_1, Pi.single_apply]
    · apply diagonal_supported _ 0 <;>
        solve
        | norm_num [Pi.single_apply]
        | ext j; fin_cases j <;>
            norm_num [project.eq_1, direction.eq_1, Pi.single_apply]
  · unfold X
    apply Submodule.sub_mem
    · apply Submodule.add_mem
      · apply Submodule.smul_mem; apply diagonal_supported _ 4 <;>
        solve
        | norm_num [Pi.single_apply]
        | ext j; fin_cases j <;>
            norm_num [project.eq_1, direction.eq_1, Pi.single_apply]
      · apply Submodule.smul_mem; apply diagonal_supported _ 5 <;>
        solve
        | norm_num [Pi.single_apply]
        | ext j; fin_cases j <;>
            norm_num [project.eq_1, direction.eq_1, Pi.single_apply]
    · apply diagonal_supported _ 3 <;>
        solve
        | norm_num [Pi.single_apply]
        | ext j; fin_cases j <;>
            norm_num [project.eq_1, direction.eq_1, Pi.single_apply]

private theorem Y_supported (i : Fin 5) (hi : i = 3 ∨ i = 4) :
    Y i ∈ freeSpan rel (⊤ : Submodule ℝ (Fin 5 → ℝ)) ⊤ := by
  unfold Y
  apply Finsupp.single_mem_supported
  refine ⟨Submodule.mem_top, Submodule.mem_top, ?_⟩
  rcases hi with rfl | rfl <;>
    norm_num [rel.eq_1, project.eq_1, Pi.single_apply,
      funext_iff, Fin.forall_fin_succ]

private theorem X_support_cases (k : Fin 5) {p} (hp : p ∈ (X k).support) :
    p = (Pi.single 0 1 + Pi.single k 1, Pi.single 0 1 + Pi.single k 1) ∨
      p = (Pi.single 0 1 - Pi.single k 1, Pi.single 0 1 - Pi.single k 1) ∨
      p = (Pi.single k 1, Pi.single k 1) := by
  classical
  unfold X at hp
  rcases Finset.mem_union.mp (Finsupp.support_sub hp) with hp | hp
  · rcases Finset.mem_union.mp (Finsupp.support_add hp) with hp | hp
    · exact Or.inl (Finset.mem_singleton.mp
        (Finsupp.support_single_subset (Finsupp.support_smul hp)))
    · exact Or.inr (Or.inl (Finset.mem_singleton.mp
        (Finsupp.support_single_subset (Finsupp.support_smul hp))))
  · exact Or.inr (Or.inr (Finset.mem_singleton.mp (Finsupp.support_single_subset hp)))

private theorem X_polarization (k : Fin 5) :
    X k - Y 0 ∈ bilRelations (⊤ : Submodule ℝ (Fin 5 → ℝ)) ⊤ := by
  let S := bilRelations (⊤ : Submodule ℝ (Fin 5 → ℝ)) ⊤
  let B (a x : Fin 5 → ℝ) := Finsupp.single (a, x) (1 : ℝ)
  let L (a b x : Fin 5 → ℝ) := B (a + b) x - B a x - B b x
  let R (a x y : Fin 5 → ℝ) := B a (x + y) - B a x - B a y
  let C (a x : Fin 5 → ℝ) := B (-a) x + B a x
  let D (a x : Fin 5 → ℝ) := B a (-x) + B a x
  have hL a b x : L a b x ∈ S :=
    Submodule.subset_span (Or.inl ⟨a, Submodule.mem_top, b, Submodule.mem_top,
      x, Submodule.mem_top, rfl⟩)
  have hR a x y : R a x y ∈ S :=
    Submodule.subset_span (Or.inr (Or.inl ⟨a, Submodule.mem_top, x, Submodule.mem_top,
      y, Submodule.mem_top, rfl⟩))
  have hC a x : C a x ∈ S := by
    have h : B ((-1 : ℝ) • a) x - (-1 : ℝ) • B a x ∈ S :=
      Submodule.subset_span (Or.inr (Or.inr (Or.inl ⟨a, Submodule.mem_top,
        x, Submodule.mem_top, -1, rfl⟩)))
    simpa only [neg_one_smul, sub_neg_eq_add] using h
  have hD a x : D a x ∈ S := by
    have h : B a ((-1 : ℝ) • x) - (-1 : ℝ) • B a x ∈ S :=
      Submodule.subset_span (Or.inr (Or.inr (Or.inr ⟨a, Submodule.mem_top,
        x, Submodule.mem_top, -1, rfl⟩)))
    simpa only [neg_one_smul, sub_neg_eq_add] using h
  let a := (Pi.single 0 1 : Fin 5 → ℝ)
  let b := (Pi.single k 1 : Fin 5 → ℝ)
  have hp := S.add_mem (S.add_mem (hL a b (a + b)) (hR a a b)) (hR b a b)
  have hm := S.add_mem (S.add_mem (hL a (-b) (a - b)) (hR a a (-b)))
    (hR (-b) a (-b))
  have hs := S.sub_mem (S.add_mem (S.add_mem (S.add_mem hm (hD a b))
    (hC b a)) (hC b (-b))) (hD b b)
  have h := S.smul_mem (1 / 2 : ℝ) (S.add_mem hp hs)
  convert h using 1 <;>
    dsimp only [X, Y, a, b, L, R, C, D, B] <;>
    simp only [← sub_eq_add_neg] <;> module

private theorem X_difference :
    X 2 - X 1 ∈ bilRelations (⊤ : Submodule ℝ (Fin 5 → ℝ)) ⊤ := by
  have h := (bilRelations (⊤ : Submodule ℝ (Fin 5 → ℝ)) ⊤).sub_mem
    (X_polarization 2) (X_polarization 1)
  simpa only [sub_sub_sub_cancel_right] using h

private theorem X_related
    (s : (Fin 5 → ℝ) × (Fin 5 → ℝ) → (Fin 5 → ℝ) × (Fin 5 → ℝ) → Prop)
    (hd : ∀ v w, rel v v → rel w w → rel v w → s (v, v) (w, w))
    (k i : Fin 5) (h : (k = 1 ∧ i = 3) ∨ (k = 2 ∧ i = 4)) :
    spanRel s (X k) (Y i) := by
  classical
  intro p hp q hq
  have hpp := ((X_supported k (h.elim (fun h => Or.inl h.1)
    (fun h => Or.inr h.1))) hp).2.2
  have hqq := ((Y_supported i (h.elim (fun h => Or.inl h.2)
    (fun h => Or.inr h.2))) hq).2.2
  have hq : q = (Pi.single i 1, Pi.single i 1) := ((Finsupp.mem_support_single _ _ _).mp hq).1
  subst q
  rcases X_support_cases k hp with rfl | rfl | rfl
  all_goals apply hd _ _ hpp hqq
  all_goals
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    norm_num [rel.eq_1, project.eq_1, Pi.single_apply,
      funext_iff, Fin.forall_fin_succ]

private theorem phi_vanishes (i : Fin 5) {a} (ha :
    a ∈ bilRelations (⊤ : Submodule ℝ (Fin 5 → ℝ)) ⊤) : phi i a = 0 := by
  unfold bilRelations at ha
  induction ha using Submodule.span_induction with
  | mem f hf =>
    rcases hf with ⟨a, _, b, _, x, _, rfl⟩ | ⟨a, _, x, _, y, _, rfl⟩ |
      ⟨a, _, x, _, k, rfl⟩ | ⟨a, _, x, _, k, rfl⟩ <;>
      simp only [phi.eq_1, map_sub, map_smul, Finsupp.linearCombination_single,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring
  | zero => exact map_zero _
  | add a b _ _ ha hb => rw [map_add, ha, hb, zero_add]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

private theorem phi_values : phi 0 (X 1) = 1 ∧ phi 3 (Y 3 + Y 4) = 1 ∧
    phi 4 (Y 3 + Y 4) = 1 := by
  norm_num [phi.eq_1, X.eq_1, Y.eq_1, Pi.single_apply]

private theorem phi_support (i : Fin 5) {a} (ha : phi i a ≠ 0) :
    ∃ p ∈ a.support, p.1 i * p.2 i ≠ 0 := by
  classical
  unfold phi at ha
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at ha
  obtain ⟨p, hp, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  refine ⟨p, hp, ?_⟩
  intro hz
  exact hterm (by rw [hz, smul_zero])

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
  push Not at hn
  fin_cases i <;> norm_num [direction.eq_1, project.eq_1, Pi.smul_apply, smul_eq_mul] at h0 h1 h2
  all_goals apply hv; linarith [hn.1, hn.2]

private theorem no_joint_related
    (a b c : freeSpan rel (⊤ : Submodule ℝ (Fin 5 → ℝ)) ⊤)
    (ha : phi 0 a.1 ≠ 0) (hb : phi 3 b.1 ≠ 0) (hc : phi 4 c.1 ≠ 0)
    (hab : spanRel (Prod.RProd rel rel) a.1 b.1) (hac : spanRel (Prod.RProd rel rel) a.1 c.1) :
    False := by
  obtain ⟨p, hp, hp0⟩ := phi_support 0 ha
  obtain ⟨q, hq, hq3⟩ := phi_support 3 hb
  obtain ⟨t, ht, ht4⟩ := phi_support 4 hc
  have hpq : rel p.1 q.1 := by cases hab p hp q hq with | intro h _ => exact h
  have hpt : rel p.1 t.1 := by cases hac p hp t ht with | intro h _ => exact h
  have h2 : p.1 2 = 0 := (mul_eq_zero.mp hpq.2.2.1).resolve_left
    (mul_ne_zero_iff.mp hq3).1
  have h1 : p.1 1 = 0 := (mul_eq_zero.mp hpt.2.2.2.2).resolve_left
    (mul_ne_zero_iff.mp ht4).1
  have hl : p ∈ localityProduct rel (⊤ : Submodule ℝ (Fin 5 → ℝ)) ⊤ :=
    a.2 hp
  exact (key_obstruction hl.2.2 hp0).elim (fun h => h h1) (fun h => h h2)

private theorem phi_quotient (i : Fin 5)
    {a b : freeSpan rel (⊤ : Submodule ℝ (Fin 5 → ℝ)) ⊤}
    (h : (Submodule.Quotient.mk a : localityTensor rel ⊤ ⊤) =
      Submodule.Quotient.mk b) : phi i a.1 = phi i b.1 := by
  have hm : a - b ∈ (bilIdeal (K := ℝ) rel ⊤ ⊤).comap
      (freeSpan (K := ℝ) rel ⊤ ⊤).subtype := (Submodule.Quotient.eq _).mp h
  have hz : phi i (a.1 - b.1) = 0 := phi_vanishes i hm.1
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

private theorem pair_refuted
    (s : ∀ E : Type, (E → E → Prop) → E × E → E × E → Prop)
    (hm : ∀ {p q}, s (Fin 5 → ℝ) rel p q → Prod.RProd rel rel p q)
    (hd : ∀ v w, rel v v → rel w w → rel v w →
      s (Fin 5 → ℝ) rel (v, v) (w, w)) : ¬ PairConjecture s := by
  intro H
  let x : freeSpan rel (⊤ : Submodule ℝ (Fin 5 → ℝ)) ⊤ :=
    ⟨X 1, X_supported 1 (Or.inl rfl)⟩
  let x' : freeSpan rel (⊤ : Submodule ℝ (Fin 5 → ℝ)) ⊤ :=
    ⟨X 2, X_supported 2 (Or.inr rfl)⟩
  let y : freeSpan rel (⊤ : Submodule ℝ (Fin 5 → ℝ)) ⊤ :=
    ⟨Y 3, Y_supported 3 (Or.inl rfl)⟩
  let z : freeSpan rel (⊤ : Submodule ℝ (Fin 5 → ℝ)) ⊤ :=
    ⟨Y 4, Y_supported 4 (Or.inr rfl)⟩
  have hw : x' - x ∈ (bilIdeal rel ⊤ ⊤).comap (freeSpan rel ⊤ ⊤).subtype :=
    ⟨X_difference, (x' - x).2⟩
  have hxy : spanRel (s (Fin 5 → ℝ) rel) x.1 y.1 :=
    X_related _ hd 1 3 (Or.inl ⟨rfl, rfl⟩)
  have hxz : spanRel (s (Fin 5 → ℝ) rel) (x + (x' - x)).1 z.1 := by
    rw [show x + (x' - x) = x' by module]
    exact X_related _ hd 2 4 (Or.inr ⟨rfl, rfl⟩)
  obtain ⟨w, hw, hwy, hwz⟩ := H ℝ (Fin 5 → ℝ) rel ⊤ ⊤ rel_locality
    x y z (x' - x) hw hxy hxz
  have ha : phi 0 (x + w).1 = 1 := by
    change phi 0 (X 1 + w.1) = 1
    have hw0 : phi 0 w.1 = 0 := phi_vanishes 0 hw.1
    rw [map_add, phi_values.1, hw0, add_zero]
  apply no_joint_related (x + w) y z _ _ _
    (fun p hp q hq => hm (hwy p hp q hq)) (fun p hp q hq => hm (hwz p hp q hq))
  · rw [ha]; norm_num
  · norm_num [y, Y.eq_1, phi.eq_1, Pi.single_apply]
  · norm_num [z, Y.eq_1, phi.eq_1, Pi.single_apply]

private theorem tensor_refuted
    (s : ∀ E : Type, (E → E → Prop) → E × E → E × E → Prop)
    (hm : ∀ {p q}, s (Fin 5 → ℝ) rel p q → Prod.RProd rel rel p q)
    (hd : ∀ v w, rel v v → rel w w → rel v w →
      s (Fin 5 → ℝ) rel (v, v) (w, w)) : ¬ TensorConjecture s := by
  intro H
  let x : freeSpan rel (⊤ : Submodule ℝ (Fin 5 → ℝ)) ⊤ :=
    ⟨X 1, X_supported 1 (Or.inl rfl)⟩
  let x' : freeSpan rel (⊤ : Submodule ℝ (Fin 5 → ℝ)) ⊤ :=
    ⟨X 2, X_supported 2 (Or.inr rfl)⟩
  let y : freeSpan rel (⊤ : Submodule ℝ (Fin 5 → ℝ)) ⊤ :=
    ⟨Y 3, Y_supported 3 (Or.inl rfl)⟩
  let z : freeSpan rel (⊤ : Submodule ℝ (Fin 5 → ℝ)) ⊤ :=
    ⟨Y 4, Y_supported 4 (Or.inr rfl)⟩
  let I : Submodule ℝ (freeSpan rel (⊤ : Submodule ℝ (Fin 5 → ℝ)) ⊤) :=
    (bilIdeal rel ⊤ ⊤).comap (freeSpan rel ⊤ ⊤).subtype
  let q := I.mkQ
  have heq : q x' = q x := (Submodule.Quotient.eq I).mpr
    ⟨X_difference, (x' - x).2⟩
  have hxy : quotientRel rel (s (Fin 5 → ℝ) rel) ⊤ ⊤ (q x) (q y) :=
    ⟨x, y, X_related _ hd 1 3 (Or.inl ⟨rfl, rfl⟩), rfl, rfl⟩
  have hxz : quotientRel rel (s (Fin 5 → ℝ) rel) ⊤ ⊤ (q x) (q z) :=
    ⟨x', z, X_related _ hd 2 4 (Or.inr ⟨rfl, rfl⟩), heq, rfl⟩
  obtain ⟨S, hS⟩ := (H ℝ (Fin 5 → ℝ) rel ⊤ ⊤ rel_locality).2.2 {q x}
  have hy : q y ∈ S := by
    change q y ∈ (S : Set (localityTensor rel ⊤ ⊤))
    rw [hS]
    intro u hu
    obtain rfl := Set.mem_singleton_iff.mp hu
    exact hxy
  have hz : q z ∈ S := by
    change q z ∈ (S : Set (localityTensor rel ⊤ ⊤))
    rw [hS]
    intro u hu
    obtain rfl := Set.mem_singleton_iff.mp hu
    exact hxz
  have hyz : quotientRel rel (s (Fin 5 → ℝ) rel) ⊤ ⊤ (q x) (q (y + z)) := by
    have h := S.add_mem hy hz
    change q y + q z ∈ (S : Set (localityTensor rel ⊤ ⊤)) at h
    rw [hS] at h
    rw [map_add]
    exact h (q x) (Set.mem_singleton _)
  obtain ⟨a, b, hab, ha, hb⟩ := hyz
  have ha0 : phi 0 a.1 = 1 := (phi_quotient 0 ha).trans phi_values.1
  have hb3 : phi 3 b.1 = 1 := (phi_quotient 3 hb).trans phi_values.2.1
  have hb4 : phi 4 b.1 = 1 := (phi_quotient 4 hb).trans phi_values.2.2
  apply no_joint_related a b b _ _ _
    (fun p hp q hq => hm (hab p hp q hq)) (fun p hp q hq => hm (hab p hp q hq))
  · rw [ha0]; norm_num
  · rw [hb3]; norm_num
  · rw [hb4]; norm_num

theorem result : ¬ claim := by
  have cd : ∀ v w, rel v v → rel w w → rel v w →
      Prod.RProd rel rel (v, v) (w, w) :=
    fun _ _ _ _ h => ⟨h, h⟩
  have fm : ∀ {p q}, fourWay (Fin 5 → ℝ) rel p q → Prod.RProd rel rel p q :=
    fun h => ⟨h.2.1, h.2.2.2.2.1⟩
  have fd : ∀ v w, rel v v → rel w w → rel v w →
      fourWay (Fin 5 → ℝ) rel (v, v) (w, w) :=
    fun _ _ hv hw h => ⟨hv, h, h, h, h, hw⟩
  exact not_or.mpr ⟨tensor_refuted (fun _ r => Prod.RProd r r) (fun h => h) cd, not_or.mpr
    ⟨tensor_refuted fourWay fm fd, not_or.mpr
      ⟨pair_refuted (fun _ r => Prod.RProd r r) (fun h => h) cd,
        pair_refuted fourWay fm fd⟩⟩⟩

end D5.S3.HomologicalAlgebra.LocalityTensorProductRefutation
