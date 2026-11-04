/- GID: D5/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/WronskianPerfectLonelyAlgebra
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Perfect homogeneous one-generator extensions exist exactly at differential order one. -/

import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution

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
  simpa only [Nat.cast_one, ← Finsupp.degree_eq_weight_one] using
    D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution.weight_intCast (fun _ => 1) α

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
      (fun β _ => pderivMulti_int (σ β).val
        (D5.S3.Quantum.Algebra.WeightedPolynomialSubstitution.homogeneous_intCast (hf β))) using 1
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

private lemma omission_val {ι : Type*} (a : Option ι) (i : ι) :
    (omission a i).val = (by classical exact Equiv.swap none a (some i)) := by
  classical
  exact Equiv.coe_optionSubtype_apply_apply _ _ _

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

private lemma pderivMulti_zero {K : Type*} [Field K] {d : ℕ}
    (f : MvPolynomial (Fin d) K) : pderivMulti 0 f = f := by
  rw [pderivMulti]
  simp only [Finsupp.coe_zero, Pi.zero_apply, pow_zero, List.map_const', List.prod_replicate,
    one_pow, Module.End.one_apply]

private lemma pderivMulti_single {K : Type*} [Field K] {d : ℕ}
    (i : Fin d) (f : MvPolynomial (Fin d) K) :
    pderivMulti (Finsupp.single i 1) f = pderiv i f := by
  rw [pderivMulti, List.prod_map_eq_pow_single i]
  · simp only [List.count_finRange, Finsupp.single_eq_same, pow_one]
    rfl
  · intro j hji _
    rw [Finsupp.single_eq_of_ne hji, pow_zero]

private def affineIndex (d : ℕ) : Option (Fin d) ≃ I d 1 := by
  classical
  refine Equiv.ofBijective (fun b => b.elim
    ⟨0, mem_I.mpr (by simp)⟩ (fun i => ⟨Finsupp.single i 1, mem_I.mpr (by simp)⟩)) ⟨?_, ?_⟩
  · intro a b h
    have he := congrArg Subtype.val h
    cases a with
    | none => cases b with
      | none => rfl
      | some j =>
        have hh := congrArg Finsupp.degree he
        simp only [Option.elim_none, Option.elim_some, map_zero, Finsupp.degree_single] at hh
        omega
    | some i => cases b with
      | none =>
        have hh := congrArg Finsupp.degree he
        simp only [Option.elim_none, Option.elim_some, map_zero, Finsupp.degree_single] at hh
        omega
      | some j =>
        exact congrArg some (Finsupp.single_left_injective one_ne_zero he)
  · intro α
    have hα := mem_I.mp α.property
    by_cases hz : α.val.degree = 0
    · exact ⟨none, Subtype.ext ((Finsupp.degree_eq_zero_iff _).mp hz).symm⟩
    · obtain ⟨i, hi⟩ := Finsupp.range_single_one.ge (show α.val.degree = 1 by omega)
      exact ⟨some i, Subtype.ext hi⟩

private lemma first_order_matrix {K : Type*} [Field K] {d : ℕ}
    (f : I d 1 → MvPolynomial (Fin d) K) :
    wronskian f = Matrix.det (fun a b : Option (Fin d) =>
      a.elim (f (affineIndex d b)) (fun i => pderiv i (f (affineIndex d b)))) := by
  classical
  rw [wronskian]
  have h := Matrix.det_submatrix_equiv_self (affineIndex d)
    (Matrix.of (fun α β : I d 1 => pderivMulti α.val (f β)))
  refine h.symm.trans (congrArg Matrix.det ?_)
  apply Matrix.ext
  intro a b
  cases a with
  | none => exact pderivMulti_zero _
  | some i => exact pderivMulti_single i _

private lemma affineIndex_monomial {K : Type*} [Field K] {d : ℕ}
    (a : Option (Fin d)) :
    (monomial (affineIndex d a).val 1 : MvPolynomial (Fin d) K) = a.elim 1 X := by
  cases a with
  | none => exact map_one C
  | some i => rfl

private lemma omittedBracket_none {K : Type*} [Field K] {d k : ℕ}
    (p : MvPolynomial (Fin d) K) :
    omittedBracket (k := k) p none = wronskian (fun α : I d k => monomial α.val 1) := by
  rw [omittedBracket]
  congr 1

private lemma omittedBracket_some {K : Type*} [Field K] {d k : ℕ}
    (p : MvPolynomial (Fin d) K) (β : I d k) :
    omittedBracket p (some β) =
      wronskian (Function.update (fun α : I d k => monomial α.val 1) β p) := by
  classical
  rw [omittedBracket]
  congr 1
  funext i
  rw [omission_val]
  by_cases hi : i = β
  · subst i; simp
  · simp [Equiv.swap_apply_of_ne_of_ne, hi, Function.update_of_ne hi]

private lemma first_order_evaluations {K : Type*} [Field K] {d : ℕ}
    (p : MvPolynomial (Fin d) K) (hp : p.IsHomogeneous 2) :
    wronskian (K := K) (fun α : I d 1 => monomial α.val 1) = 1 ∧
      ∀ β : I d 1, wronskian (Function.update (fun α : I d 1 => monomial α.val 1) β p) =
        ((affineIndex d).symm β).elim (-p) (fun i => pderiv i p) := by
  classical
  let e := affineIndex d
  let b : Option (Fin d) → MvPolynomial (Fin d) K := fun a => a.elim 1 X
  let m : Matrix (Option (Fin d)) (Option (Fin d)) (MvPolynomial (Fin d) K) :=
    Matrix.of fun a j => a.elim (b j) (fun i => pderiv i (b j))
  let c : Option (Fin d) → MvPolynomial (Fin d) K := fun a =>
    a.elim (-p) (fun i => pderiv i p)
  have hb : ∀ a, (monomial (e a).val 1 : MvPolynomial (Fin d) K) = b a := by
    intro a
    exact affineIndex_monomial a
  have hrow : (∑ j : Option (Fin d), b j •
      (1 : Matrix (Option (Fin d)) (Option (Fin d)) (MvPolynomial (Fin d) K)) j) = b := by
    funext j
    simpa only [Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      congrFun (Matrix.vecMul_one b) j
  have hm : m.det = 1 := by
    have he : m = (1 : Matrix (Option (Fin d)) (Option (Fin d))
        (MvPolynomial (Fin d) K)).updateRow none b := by
      apply Matrix.ext
      intro a j
      cases a with
      | none => rw [Matrix.updateRow_self]; rfl
      | some i =>
        rw [Matrix.updateRow_ne (Option.some_ne_none i)]
        cases j <;> simp [m, b, Matrix.one_apply, pderiv_X, Pi.single_apply, eq_comm]
    rw [he]
    have h := Matrix.det_updateRow_sum
      (1 : Matrix (Option (Fin d)) (Option (Fin d)) (MvPolynomial (Fin d) K)) none b
    rw [hrow, Matrix.det_one] at h
    simpa only [b, Option.elim_none, smul_eq_mul, mul_one] using h
  have hc : ∀ a, a.elim p (fun i => pderiv i p) = ∑ j, c j * m a j := by
    intro a
    cases a with
    | none =>
      simp only [Fintype.sum_option, c, m, b, Matrix.of_apply, Option.elim_none,
        Option.elim_some, mul_one]
      have he := hp.sum_X_mul_pderiv
      rw [show (∑ i, pderiv i p * X i) = ∑ i, X i * pderiv i p by
        apply Finset.sum_congr rfl; intro i _; exact mul_comm _ _, he]
      simp only [two_nsmul]
      abel
    | some i =>
      simp [c, m, b, Fintype.sum_option, pderiv_X, Pi.single_apply]
  constructor
  · rw [first_order_matrix]
    have he : (Matrix.of (fun a j : Option (Fin d) =>
        a.elim (monomial (e j).val 1) (fun i => pderiv i (monomial (e j).val 1)))) = m := by
      apply Matrix.ext
      intro a j
      cases a <;> simp only [m, Matrix.of_apply, Option.elim_none, Option.elim_some, hb]
    exact (congrArg Matrix.det he).trans hm
  · intro β
    rw [first_order_matrix]
    have he : (Matrix.of (fun a j : Option (Fin d) =>
        a.elim (Function.update (fun α : I d 1 => monomial α.val 1) β p (e j))
          (fun i => pderiv i
            (Function.update (fun α : I d 1 => monomial α.val 1) β p (e j))))) =
        m.updateCol (e.symm β) (fun a => a.elim p (fun i => pderiv i p)) := by
      apply Matrix.ext
      intro a j
      by_cases hj : j = e.symm β
      · subst j
        simp only [Matrix.updateCol_self, Matrix.of_apply, Equiv.apply_symm_apply,
          Function.update_self]
      · have hje : e j ≠ β := fun h => hj (e.eq_symm_apply.mpr h)
        rw [Matrix.updateCol_ne hj]
        simp only [Matrix.of_apply, Function.update_of_ne hje, hb]
        rfl
    have hc' : (fun a => a.elim p (fun i => pderiv i p)) =
        (fun a => ∑ j, c j • m a j) := by
      funext a
      simpa only [smul_eq_mul] using hc a
    refine (congrArg Matrix.det he).trans ?_
    rw [hc', Matrix.det_updateCol_sum, hm, smul_eq_mul, mul_one]

private lemma quadratic_construction {K : Type*} [Field K] [CharZero K]
    {d : ℕ} (hd : 2 ≤ d) :
    ∃ p : MvPolynomial (Fin d) K,
      p ≠ 0 ∧ p.IsHomogeneous 2 ∧ perfect (k := 1) p := by
  classical
  let q : MvPolynomial (Fin d) K := ∑ i : Fin d, X i ^ 2
  have hq : q.IsHomogeneous 2 := by
    apply IsHomogeneous.sum
    intro i _
    simpa only [Nat.one_mul] using (isHomogeneous_X K i).pow 2
  have hder : ∀ i : Fin d, pderiv i q = (2 : K) • X i := by
    intro i
    simp [q, pderiv_pow, pderiv_X, Pi.single_apply, mul_ite, smul_eq_C_mul]
    exact (map_ofNat C 2).symm
  have hne : q ≠ 0 := by
    intro hz
    have he := hder ⟨0, by omega⟩
    rw [hz, map_zero] at he
    exact (smul_ne_zero two_ne_zero (X_ne_zero _)) he.symm
  refine ⟨q, hne, hq, ?_⟩
  obtain ⟨hdet, hupdate⟩ := first_order_evaluations q hq
  have hmono : ∀ a : Option (I d 1), a.elim q (fun α => monomial α.val 1) ∈
      lonely (k := 1) q := by
    intro a
    rw [lonely_eq_span]
    exact Submodule.subset_span ⟨a, rfl⟩
  have hbase : ∀ a : Option (Fin d), a.elim 1 X ∈ lonely (k := 1) q := by
    intro a
    have h := hmono (some (affineIndex d a))
    simpa only [Option.elim_some, affineIndex_monomial] using h
  have homit : ∀ a : Option (I d 1), omittedBracket q a ∈ lonely (k := 1) q := by
    intro a
    cases a with
    | none => rw [omittedBracket_none, hdet]; exact hbase none
    | some β =>
      rw [omittedBracket_some, hupdate]
      generalize (affineIndex d).symm β = a
      cases a with
      | none => exact Submodule.neg_mem _ (hmono none)
      | some i =>
        change pderiv i q ∈ lonely (k := 1) q
        rw [hder]
        exact Submodule.smul_mem _ _ (hbase (some i))
  let s := Submodule.span K {w | ∃ f : I d 1 → MvPolynomial (Fin d) K,
    (∀ β, f β ∈ lonely (k := 1) q) ∧ wronskian f = w}
  have hin : ∀ a : Option (I d 1), omittedBracket q a ∈ s := by
    intro a
    exact Submodule.subset_span ⟨_, (fun β => hmono (omission a β).val), rfl⟩
  have hone : (1 : MvPolynomial (Fin d) K) ∈ s := by
    have h := hin none
    rwa [omittedBracket_none, hdet] at h
  have hqmem : q ∈ s := by
    have h := hin (some (affineIndex d none))
    rw [omittedBracket_some, hupdate, Equiv.symm_apply_apply] at h
    exact neg_neg q ▸ s.neg_mem h
  have hx : ∀ i : Fin d, (X i : MvPolynomial (Fin d) K) ∈ s := by
    intro i
    have h := hin (some (affineIndex d (some i)))
    rw [omittedBracket_some, hupdate, Equiv.symm_apply_apply] at h
    change pderiv i q ∈ s at h
    rw [hder] at h
    have hc := s.smul_mem (2 : K)⁻¹ h
    simpa only [smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : K) ≠ 0), one_smul] using hc
  change s = lonely (k := 1) q
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro w ⟨f, hf, rfl⟩
    refine (Submodule.span_le.mpr ?_) (bracket_mem_span_basis q f hf)
    rintro w ⟨b, rfl⟩
    exact (Submodule.span_le.mpr (by rintro w ⟨a, rfl⟩; exact homit a))
      (bracket_mem_span_omissions q b)
  · rw [lonely_eq_span]
    apply Submodule.span_le.mpr
    rintro w ⟨a, rfl⟩
    cases a with
    | none => exact hqmem
    | some α =>
      obtain ⟨a, rfl⟩ := (affineIndex d).surjective α
      change (monomial (affineIndex d a).val 1 : MvPolynomial (Fin d) K) ∈ s
      rw [affineIndex_monomial]
      cases a with
      | none => exact hone
      | some i => exact hx i

theorem result : claim := by
  intro K _ _ d k hd hk
  constructor
  · rintro ⟨p, hp, hh, hperfect⟩
    by_contra hne
    have hk2 : 2 ≤ k := by omega
    exact upper_order_obstruction hd hk2 p hh hperfect
  · rintro rfl
    exact quadratic_construction hd

end D5.S3.HomologicalAlgebra.WronskianPerfectLonelyAlgebra
