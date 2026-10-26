/- GID: D5/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Perfect homogeneous one-generator extensions exist exactly at differential order one. -/

import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

noncomputable section

namespace D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra

open MvPolynomial
open scoped BigOperators

/-- All multi-indices of total order at most `k`, each occurring once. -/
def I (d k : ℕ) : Finset (Fin d →₀ ℕ) :=
  (Finsupp.finite_of_degree_le (σ := Fin d) k).toFinset

/-- Ordinary iterated partial differentiation, in increasing coordinate order. -/
def pderivMulti {K : Type*} [Field K] {d : ℕ} (α : Fin d →₀ ℕ) :
    MvPolynomial (Fin d) K →ₗ[K] MvPolynomial (Fin d) K :=
  ((List.finRange d).map fun i => (pderiv i).toLinearMap ^ α i).prod

/-- The complete generalized Wronskian, with rows indexed by differential multi-indices. -/
def wronskian {K : Type*} [Field K] {d k : ℕ}
    (f : I d k → MvPolynomial (Fin d) K) : MvPolynomial (Fin d) K :=
  Matrix.det (fun α β => pderivMulti α.val (f β))

/-- The sum of all polynomials of total degree at most `k` and the line through `p`. -/
def lonely {K : Type*} [Field K] {d k : ℕ} (p : MvPolynomial (Fin d) K) :
    Submodule K (MvPolynomial (Fin d) K) :=
  restrictTotalDegree (Fin d) K k ⊔ K ∙ p

/-- Perfectness means that all Wronskian brackets span the entire polynomial subspace. -/
def perfect {K : Type*} [Field K] {d k : ℕ} (p : MvPolynomial (Fin d) K) : Prop :=
  Submodule.span K {w | ∃ f : I d k → MvPolynomial (Fin d) K,
    (∀ β, f β ∈ lonely (k := k) p) ∧ wronskian f = w} = lonely (k := k) p

/-- The source question over every characteristic-zero field and in every base dimension. -/
def claim : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (d k : ℕ), 2 ≤ d → 1 ≤ k →
    ((∃ p : MvPolynomial (Fin d) K,
      p ≠ 0 ∧ p.IsHomogeneous (k + 1) ∧ perfect (k := k) p) ↔ k = 1)

private lemma mem_I {d k : ℕ} {α : Fin d →₀ ℕ} :
    α ∈ I d k ↔ α.degree ≤ k := Set.Finite.mem_toFinset _

private lemma lonely_eq_span {K : Type*} [Field K] {d k : ℕ}
    (p : MvPolynomial (Fin d) K) :
    lonely (k := k) p = Submodule.span K
      (Set.range fun b : Option (I d k) => b.elim p (fun α => monomial α.val 1)) := by
  classical
  rw [lonely, restrictTotalDegree, restrictSupport_eq_span, Option.range_elim,
    Submodule.span_insert, sup_comm]
  congr 1
  congr 1
  ext f
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range, Subtype.exists, mem_I,
    exists_prop, Finsupp.degree_apply, Finsupp.sum]

private def wronskianMultilinear {K : Type*} [Field K] (d k : ℕ) :
    MultilinearMap K (fun _ : I d k => MvPolynomial (Fin d) K)
      (MvPolynomial (Fin d) K) :=
  (Matrix.detRowAlternating.toMultilinearMap.restrictScalars K).compLinearMap
    (fun _ => LinearMap.pi fun α : I d k => pderivMulti α.val)

private lemma wronskianMultilinear_apply {K : Type*} [Field K] {d k : ℕ}
    (f : I d k → MvPolynomial (Fin d) K) :
    wronskianMultilinear d k f = wronskian f := by
  change Matrix.det (fun β α => pderivMulti α.val (f β)) = _
  exact Matrix.det_transpose _

private lemma bracket_mem_span_basis {K : Type*} [Field K] {d k : ℕ}
    (p : MvPolynomial (Fin d) K) (f : I d k → MvPolynomial (Fin d) K)
    (hf : ∀ β, f β ∈ lonely (k := k) p) :
    wronskian f ∈ Submodule.span K {w | ∃ b : I d k → Option (I d k),
      wronskian (fun β => (b β).elim p (fun α => monomial α.val 1)) = w} := by
  classical
  rw [lonely_eq_span] at hf
  choose c hc using fun β => (Submodule.mem_span_range_iff_exists_fun K).mp (hf β)
  rw [← wronskianMultilinear_apply, ← funext hc,
    MultilinearMap.map_sum]
  apply Submodule.sum_mem
  intro b _
  rw [MultilinearMap.map_smul_univ, wronskianMultilinear_apply]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

private lemma weight_one_int {d : ℕ} (α : Fin d →₀ ℕ) :
    Finsupp.weight (fun _ => (1 : ℤ)) α = (α.degree : ℤ) := by
  rw [Finsupp.weight_eq_sum, Finsupp.degree_eq_sum]
  simp only [nsmul_eq_mul, mul_one, Nat.cast_sum]

private lemma homogeneous_int {K : Type*} [Field K] {d n : ℕ}
    {f : MvPolynomial (Fin d) K} (hf : f.IsHomogeneous n) :
    f.IsWeightedHomogeneous (fun _ => (1 : ℤ)) n := by
  intro α hα
  rw [weight_one_int]
  have h := hf hα
  change Finsupp.weight (fun _ => (1 : ℕ)) α = n at h
  rw [← Finsupp.degree_eq_weight_one] at h
  exact congrArg Nat.cast h

private lemma iterated_partial_int {K : Type*} [Field K] {d : ℕ}
    (i : Fin d) (r : ℕ) {n : ℤ} {f : MvPolynomial (Fin d) K}
    (hf : f.IsWeightedHomogeneous (fun _ => (1 : ℤ)) n) :
    (((pderiv i).toLinearMap ^ r) f).IsWeightedHomogeneous
      (fun _ => (1 : ℤ)) (n - r) := by
  induction r with
  | zero => simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero, sub_zero] using hf
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact ih.pderiv (by push_cast; ring)

private lemma partials_list_int {K : Type*} [Field K] {d : ℕ}
    (α : Fin d →₀ ℕ) (l : List (Fin d)) {n : ℤ} {f : MvPolynomial (Fin d) K}
    (hf : f.IsWeightedHomogeneous (fun _ => (1 : ℤ)) n) :
    (((l.map fun i => (pderiv i).toLinearMap ^ α i).prod) f).IsWeightedHomogeneous
      (fun _ => (1 : ℤ)) (n - (l.map fun i => (α i : ℤ)).sum) := by
  induction l with
  | nil => simpa only [List.map_nil, List.prod_nil, List.sum_nil, Module.End.one_apply,
      sub_zero] using hf
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.sum_cons]
    convert iterated_partial_int i (α i) ih using 1 <;> ring

private lemma pderivMulti_int {K : Type*} [Field K] {d : ℕ}
    (α : Fin d →₀ ℕ) {n : ℤ} {f : MvPolynomial (Fin d) K}
    (hf : f.IsWeightedHomogeneous (fun _ => (1 : ℤ)) n) :
    (pderivMulti α f).IsWeightedHomogeneous (fun _ => (1 : ℤ)) (n - α.degree) := by
  rw [pderivMulti]
  convert partials_list_int α (List.finRange d) hf using 1
  rw [Finsupp.degree_eq_sum, Nat.cast_sum, Fin.sum_univ_def]

private lemma wronskian_homogeneous {K : Type*} [Field K] {d k : ℕ}
    (f : I d k → MvPolynomial (Fin d) K) (n : I d k → ℕ)
    (hf : ∀ β, (f β).IsHomogeneous (n β)) :
    (wronskian f).IsHomogeneous ((∑ β, n β) - ∑ α : I d k, α.val.degree) := by
  classical
  have ht : (wronskian f).IsWeightedHomogeneous (fun _ => (1 : ℤ))
      ((∑ β, (n β : ℤ)) - ∑ α : I d k, (α.val.degree : ℤ)) := by
    rw [wronskian]
    erw [Matrix.det_apply']
    apply IsWeightedHomogeneous.sum
    intro σ _
    apply IsWeightedHomogeneous.C_mul
    convert IsWeightedHomogeneous.prod Finset.univ
      (fun β => pderivMulti (σ β).val (f β))
      (fun β => (n β : ℤ) - (σ β).val.degree)
      (fun β _ => pderivMulti_int (σ β).val (homogeneous_int (hf β))) using 1
    rw [Finset.sum_sub_distrib]
    congr 1
    exact (Equiv.sum_comp σ (fun α : I d k => (α.val.degree : ℤ))).symm
  intro α hα
  have he := ht hα
  rw [weight_one_int, ← Nat.cast_sum, ← Nat.cast_sum] at he
  have hh : α.degree = (∑ β, n β) - ∑ α : I d k, α.val.degree := by omega
  change Finsupp.weight (fun _ => (1 : ℕ)) α = _
  rw [← Finsupp.degree_eq_weight_one]
  exact hh

private def omission {ι : Type*} (a : Option ι) : ι ≃ {b : Option ι // b ≠ a} := by
  classical
  exact Equiv.optionSubtype a ⟨Equiv.swap none a, Equiv.swap_apply_left _ _⟩

private lemma wronskian_permute {K : Type*} [Field K] {d k : ℕ}
    (f : I d k → MvPolynomial (Fin d) K) (σ : Equiv.Perm (I d k)) :
    wronskian (f ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : K) • wronskian f := by
  classical
  rw [wronskian, wronskian]
  change ((Matrix.of (fun α β : I d k => pderivMulti α.val (f β))).submatrix id σ).det = _
  rw [Matrix.det_permute', MvPolynomial.smul_eq_C_mul]
  congr 1

private lemma omission_reindex {ι : Type*} [Fintype ι] (b : ι → Option ι)
    (hb : Function.Injective b) :
    ∃ (a : Option ι) (σ : Equiv.Perm ι), ∀ i, b i = (omission a (σ i)).val := by
  classical
  obtain ⟨a, ha, hu⟩ :=
    Fintype.existsUnique_notMem_image_of_injective_of_card_eq_add_one b hb (by simp)
  have hba : ∀ i, b i ≠ a := by
    intro i hi
    exact ha (hi ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  let c : ι → ι := fun i => (omission a).symm ⟨b i, hba i⟩
  have hc : Function.Injective c := by
    intro i j h
    apply hb
    exact congrArg Subtype.val ((omission a).symm.injective h)
  refine ⟨a, Equiv.ofBijective c hc.bijective_of_finite, fun i => ?_⟩
  exact congrArg Subtype.val ((omission a).apply_symm_apply ⟨b i, hba i⟩).symm

private def omittedBracket {K : Type*} [Field K] {d k : ℕ}
    (p : MvPolynomial (Fin d) K) (a : Option (I d k)) : MvPolynomial (Fin d) K :=
  wronskian (fun i => (omission a i).val.elim p (fun α => monomial α.val 1))

private lemma omittedBracket_homogeneous {K : Type*} [Field K] {d k : ℕ}
    {p : MvPolynomial (Fin d) K} (hp : p.IsHomogeneous (k + 1)) (a : Option (I d k)) :
    (omittedBracket p a).IsHomogeneous (a.elim 0 (fun α => k + 1 - α.val.degree)) := by
  classical
  let n : Option (I d k) → ℕ := fun b => b.elim (k + 1) (fun α => α.val.degree)
  have hs : (∑ i : I d k, n (omission a i).val) + n a =
      (k + 1) + ∑ α : I d k, α.val.degree := by
    have h := Fintype.sum_eq_add_sum_subtype_ne n a
    rw [← (omission a).sum_comp] at h
    rw [Fintype.sum_option] at h
    dsimp only [n, Option.elim] at h ⊢
    omega
  have hh : ∀ i : I d k,
      ((omission a i).val.elim p (fun α => monomial α.val 1)).IsHomogeneous
        (n (omission a i).val) := by
    intro i
    cases h : (omission a i).val with
    | none => exact hp
    | some α => exact isHomogeneous_monomial 1 rfl
  rw [omittedBracket]
  convert wronskian_homogeneous
    (fun i => (omission a i).val.elim p (fun α => monomial α.val 1))
    (fun i => n (omission a i).val) hh using 1
  cases a with
  | none => dsimp only [n, Option.elim] at hs ⊢; omega
  | some α =>
    have hα := mem_I.mp α.property
    dsimp only [n, Option.elim] at hs ⊢
    omega

private lemma bracket_mem_span_omissions {K : Type*} [Field K] {d k : ℕ}
    (p : MvPolynomial (Fin d) K) (b : I d k → Option (I d k)) :
    wronskian (fun i => (b i).elim p (fun α => monomial α.val 1)) ∈
      Submodule.span K (Set.range (omittedBracket (k := k) p)) := by
  classical
  by_cases hb : Function.Injective b
  · obtain ⟨a, σ, hσ⟩ := omission_reindex b hb
    have he : (fun i => (b i).elim p (fun α => monomial α.val 1)) =
        (fun i => (omission a i).val.elim p (fun α => monomial α.val 1)) ∘ σ := by
      funext i
      rw [hσ i]
      rfl
    rw [he, wronskian_permute]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hb
    have hz : wronskian (fun i => (b i).elim p (fun α => monomial α.val 1)) = 0 := by
      rw [wronskian]
      apply Matrix.det_zero_of_column_eq hne
      intro α
      rw [hij]
    rw [hz]
    exact Submodule.zero_mem _

private lemma projected_bracket_bound {K : Type*} [Field K] {d k : ℕ}
    (hk : 2 ≤ k) {p : MvPolynomial (Fin d) K} (hp : p.IsHomogeneous (k + 1))
    (f : I d k → MvPolynomial (Fin d) K) (hf : ∀ β, f β ∈ lonely (k := k) p) :
    homogeneousComponent k (wronskian f) ∈ Submodule.span K
      (Set.range fun i : Fin d => omittedBracket (k := k) p
        (some ⟨Finsupp.single i 1, mem_I.mpr (by simp; omega)⟩)) := by
  classical
  let s := Submodule.span K (Set.range (omittedBracket (k := k) p))
  have hmem : wronskian f ∈ s :=
    (Submodule.span_le.mpr (by
      rintro w ⟨b, rfl⟩
      exact bracket_mem_span_omissions p b)) (bracket_mem_span_basis p f hf)
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hmem
  · rintro w ⟨a, rfl⟩
    cases a with
    | none =>
      have hz : homogeneousComponent k (omittedBracket (k := k) p none) = 0 :=
        (homogeneousComponent_of_mem (omittedBracket_homogeneous hp none)).trans
          (if_neg (by omega : k ≠ 0))
      exact hz.symm ▸ Submodule.zero_mem _
    | some α =>
      by_cases hα : α.val.degree = 1
      · obtain ⟨i, hi⟩ := Finsupp.range_single_one.ge hα
        have he : α = ⟨Finsupp.single i 1, mem_I.mpr (by simp; omega)⟩ :=
          Subtype.ext hi.symm
        have hhom : (omittedBracket p (some α)).IsHomogeneous k := by
          convert omittedBracket_homogeneous hp (some α) using 1
          dsimp only [Option.elim]
          omega
        have hc := homogeneousComponent_eq_self hhom
        exact hc.symm ▸ Submodule.subset_span ⟨i, congrArg
          (fun α : I d k => omittedBracket p (some α)) he.symm⟩
      · have hdeg := mem_I.mp α.property
        have hz : homogeneousComponent k (omittedBracket p (some α)) = 0 :=
          (homogeneousComponent_of_mem (omittedBracket_homogeneous hp (some α))).trans
            (if_neg (by dsimp only [Option.elim]; omega))
        exact hz.symm ▸ Submodule.zero_mem _
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [map_smul]
    exact Submodule.smul_mem _ c hx

private lemma upper_order_obstruction {K : Type*} [Field K] [CharZero K]
    {d k : ℕ} (hd : 2 ≤ d) (hk : 2 ≤ k) (p : MvPolynomial (Fin d) K)
    (hh : p.IsHomogeneous (k + 1)) :
    ¬ perfect (k := k) p := by
  classical
  intro hperfect
  rw [perfect] at hperfect
  let v : Fin d → MvPolynomial (Fin d) K := fun i => omittedBracket (k := k) p
    (some ⟨Finsupp.single i 1, mem_I.mpr (by simp; omega)⟩)
  let s := Submodule.span K (↑(Finset.univ.image v) : Set (MvPolynomial (Fin d) K))
  have hs : s = Submodule.span K (Set.range v) := by
    simp only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hproj : ∀ t ∈ lonely (k := k) p, homogeneousComponent k t ∈ s := by
    intro t ht
    rw [← hperfect] at ht
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ht
    · rintro w ⟨f, hf, rfl⟩
      rw [hs]
      exact projected_bracket_bound hk hh f hf
    · rw [map_zero]; exact s.zero_mem
    · intro x y _ _ hx hy; rw [map_add]; exact s.add_mem hx hy
    · intro c x _ hx; rw [map_smul]; exact s.smul_mem c hx
  let i₀ : Fin d := ⟨0, by omega⟩
  let i₁ : Fin d := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := by
    intro h
    have he : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  let μ : Option (Fin d) → Fin d →₀ ℕ := fun b =>
    b.elim (Finsupp.single i₀ (k - 1) + Finsupp.single i₁ 1) (fun i => Finsupp.single i k)
  have hμ : Function.Injective μ := by
    have hm : ∀ j, μ none ≠ μ (some j) := by
      intro j he
      by_cases hj : j = i₀
      · have h := congrArg (fun α => α i₁) he
        simp [μ, hj, Finsupp.single_apply, h01, h01.symm] at h
      · have h := congrArg (fun α => α i₀) he
        simp [μ, Finsupp.single_apply, hj, h01.symm] at h
        omega
    intro a b h
    cases a with
    | none => cases b with
      | none => rfl
      | some j => exact (hm j h).elim
    | some i => cases b with
      | none => exact (hm i h.symm).elim
      | some j =>
        exact congrArg some (Finsupp.single_left_injective (by omega : k ≠ 0) h)
  have hdeg : ∀ a, (μ a).degree = k := by
    intro a
    cases a <;> simp only [μ, Option.elim_none, Option.elim_some, map_add,
      Finsupp.degree_single] <;> omega
  have hm : ∀ a, (monomial (μ a) 1 : MvPolynomial (Fin d) K) ∈ s := by
    intro a
    have ht : (monomial (μ a) 1 : MvPolynomial (Fin d) K) ∈ lonely (k := k) p := by
      rw [lonely]
      apply Submodule.mem_sup_left
      rw [mem_restrictTotalDegree, totalDegree_monomial _ one_ne_zero]
      change (μ a).degree ≤ k
      exact (hdeg a).le
    have h := hproj _ ht
    rwa [homogeneousComponent_eq_self (isHomogeneous_monomial 1 (hdeg a))] at h
  have hi := (basisMonomials (Fin d) K).linearIndependent.comp μ hμ
  have hfinite : Module.Finite K s := Module.Finite.span_finset K _
  have hdim := @LinearIndependent.fintype_card_le_finrank K s _ _ _ _ hfinite
    (Option (Fin d)) _ _ (hi.codRestrict s hm)
  have hcard : Module.finrank K s ≤ d :=
    (finrank_span_finset_le_card _).trans
      (Finset.card_image_le.trans_eq (by simp))
  simp only [Fintype.card_option, Fintype.card_fin] at hdim
  omega

private lemma quadratic_construction {K : Type*} [Field K] [CharZero K]
    {d : ℕ} (hd : 2 ≤ d)
    (hb : ∀ (p : MvPolynomial (Fin d) K) (f : I d 1 → MvPolynomial (Fin d) K),
      (∀ β, f β ∈ lonely (k := 1) p) →
      wronskian f ∈ Submodule.span K {w | ∃ b : I d 1 → Option (I d 1),
        wronskian (fun β => (b β).elim p (fun α => monomial α.val 1)) = w}) :
    ∃ p : MvPolynomial (Fin d) K,
      p ≠ 0 ∧ p.IsHomogeneous 2 ∧ perfect (k := 1) p := by
  sorry

theorem result : claim := by
  intro K _ _ d k hd hk
  constructor
  · rintro ⟨p, hp, hh, hperfect⟩
    by_contra hne
    have hk2 : 2 ≤ k := by omega
    exact upper_order_obstruction hd hk2 p hh hperfect
  · rintro rfl
    exact quadratic_construction hd bracket_mem_span_basis

end D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra
