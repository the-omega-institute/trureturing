/- GID: D5/S3/Combinatorics/Partitions/SpechtYoungPolynomialGram
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtYoungPolynomialGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Young permutation averaging and complete homogeneous coordinates of actual Specht multiplicity Gram matrices. -/

/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. Authors: The Tau Ceti contributors.
Selected arguments from TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156:
GroupTheory/Perm/FiberSubgroup, RingTheory/MvPolynomial/Symmetric/Complete,
RingTheory/MvPolynomial/Symmetric/PowerSum and
RepresentationTheory/Symmetric/PermutationModule/PowerSum.
The existing D5 fibre quotient, invariant-colouring power sum and literal Young
subgroup constructions supply the prerequisites. The final coefficient comparison
uses the actual Specht completeness and multiplicity Gram identity.
License, exact selection, adaptations, consumers and retirement:
Library/FiniteGroups/tauceti2026spechtpolytabloids.md.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24542.
-/
import D5.S3.Combinatorics.Partitions.SpechtYoungCompleteness
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.Data.Finset.Sym

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
noncomputable section
open scoped BigOperators
namespace TauCeti
open Equiv Finset MvPolynomial

section FibreCount
variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
private theorem natCard_fiberSubgroup (f : α → ι) :
    Nat.card (fiberSubgroup f) = ∏ i, (#{a | f a = i}).factorial := by
  classical
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun σ => by
      rw [mem_fiberSubgroup, funext_iff]; rfl :
      fiberSubgroup f ≃ {g : Equiv.Perm α // f ∘ g = f}),
    Nat.card_eq_fintype_card, DomMulAct.stabilizer_card]
  simp only [Fintype.card_subtype]

private theorem exists_forall_card_filter_eq {d : ι → ℕ} (hd : ∑ i, d i = Fintype.card α) :
    ∃ f : α → ι, ∀ i, #{a | f a = i} = d i := by
  -- label the points of `α` by the points of `Σ i, Fin (d i)` and colour each by its block
  let e := Fintype.equivOfCardEq (show Fintype.card α = Fintype.card (Σ i, Fin (d i)) by
    simp [hd])
  refine ⟨fun a => (e a).1, fun i => ?_⟩
  rw [← Fintype.card_subtype, Fintype.card_congr (e.subtypeEquiv fun a => Iff.rfl :
      {a // (e a).1 = i} ≃ {x : Σ i, Fin (d i) // x.1 = i}),
    Fintype.card_congr (Equiv.sigmaSubtype i), Fintype.card_fin]

private theorem sum_natCard_fiberSubgroup_smul [DecidableEq α] {M : Type*} [AddCommMonoid M]
    (F : (ι → ℕ) → M) :
    ∑ f : α → ι, Nat.card (fiberSubgroup f) • F (fun i => #{a | f a = i}) =
      (Fintype.card α).factorial • ∑ d ∈ piAntidiag univ (Fintype.card α), F d := by
  set c : (α → ι) → ι → ℕ := fun f i => #{a | f a = i} with hc_def
  have hc : ∀ f ∈ (univ : Finset (α → ι)), c f ∈ piAntidiag univ (Fintype.card α) :=
    fun f _ => by
      rw [mem_piAntidiag]
      refine ⟨?_, fun i _ => mem_univ i⟩
      rw [hc_def]
      exact (card_eq_sum_card_fiberwise fun a _ => mem_univ (f a)).symm
  -- group the colourings by their fiber-size functions
  rw [← sum_fiberwise_of_maps_to hc, smul_sum]
  refine sum_congr rfl fun d hd => ?_
  rw [sum_congr rfl fun f hf => by
    rw [show (fun i => #{a | f a = i}) = d from (mem_filter.1 hf).2], ← sum_smul]
  congr 1
  -- the colourings with fiber sizes `d` are the rearrangements of one of them, `f₀`
  obtain ⟨f₀, hf₀⟩ := exists_forall_card_filter_eq (α := α) ((mem_piAntidiag.1 hd).1)
  have hfib : ∀ f ∈ univ.filter fun f => c f = d,
      Nat.card (fiberSubgroup f) = Nat.card (fiberSubgroup f₀) := fun f hf => by
    rw [natCard_fiberSubgroup, natCard_fiberSubgroup]
    exact prod_congr rfl fun i _ => by
      rw [show #{a | f a = i} = d i from congrFun (mem_filter.1 hf).2 i, hf₀]
  rw [sum_congr rfl hfib, sum_const, smul_eq_mul]
  have hq : #(univ.filter fun f => c f = d) = Nat.card (Equiv.Perm α ⧸ fiberSubgroup f₀) := by
    rw [Nat.card_congr (quotientFiberSubgroupEquiv f₀), ← Fintype.card_subtype,
      Nat.card_eq_fintype_card]
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun f => ?_)
    rw [hc_def, funext_iff]
    refine forall_congr' fun i => ?_
    rw [← hf₀ i]
    -- the two sides differ only in the instance deciding equality of colours
    convert Iff.rfl
  rw [hq, ← Subgroup.card_eq_card_quotient_mul_card_subgroup, Nat.card_eq_fintype_card,
    Fintype.card_perm]

end FibreCount

theorem hsymm_eq_sum_piAntidiag {σ : Type*} [Fintype σ] [DecidableEq σ] (R : Type*)
    [CommSemiring R] (d : ℕ) :
    MvPolynomial.hsymm σ R d =
      ∑ γ ∈ Finset.piAntidiag (Finset.univ : Finset σ) d,
        ∏ i, (MvPolynomial.X i : MvPolynomial σ R) ^ γ i := by
  rw [← Finset.map_sym_eq_piAntidiag, Finset.sum_map, Finset.sym_univ, MvPolynomial.hsymm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.prod_multiset_map_count]
  refine Finset.prod_subset (Finset.subset_univ _) fun i _ hi => ?_
  rw [Multiset.count_eq_zero_of_notMem (by simpa using hi), pow_zero]

section Average
variable {σ α : Type*} [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]
  (R : Type*) [CommSemiring R] {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem sum_card_smul_psumPart_partition (r : ι → ℕ) (hr : ∑ i, r i = Fintype.card α) :
    ∑ π : Perm α, #{c : α → ι | c ∘ π = c ∧ ∀ i, #{a | c a = i} = r i} •
        psumPart σ R π.partition =
      (Fintype.card α).factorial • ∏ i, hsymm σ R (r i) := by
  -- a pair of colourings, one fixed by `π` with fibers of sizes `r` and one fixed by `π`, is a
  -- colouring by pairs fixed by `π` whose first coordinate has fibers of sizes `r`
  have h1 : ∀ π : Perm α,
      #{c : α → ι | c ∘ π = c ∧ ∀ i, #{a | c a = i} = r i} • psumPart σ R π.partition =
        ∑ h : α → ι × σ, if h ∘ π = h ∧ ∀ i, #{a | (h a).1 = i} = r i
          then ∏ a, (X (h a).2 : MvPolynomial σ R) else 0 := fun π => by
    rw [psumPart_partition_eq_sum_prod_X, ← sum_const, ← sum_product', ← sum_filter]
    refine sum_equiv (arrowProdEquivProdArrow α (fun _ => ι) (fun _ => σ)).symm (fun x => ?_)
      fun x _ => rfl
    simp only [mem_product, mem_filter, mem_univ, true_and, funext_iff, Function.comp_apply,
      arrowProdEquivProdArrow, coe_fn_symm_mk, Prod.ext_iff, forall_and]
    tauto
  -- the term of a colouring by pairs, read off its fiber sizes `A : ι × σ → ℕ`
  let F : (ι × σ → ℕ) → MvPolynomial σ R := fun A =>
    if ∀ i, ∑ s, A (i, s) = r i then ∏ s, X s ^ ∑ i, A (i, s) else 0
  have h2 : ∀ h : α → ι × σ,
      (∑ π : Perm α, if h ∘ π = h ∧ ∀ i, #{a | (h a).1 = i} = r i
        then ∏ a, (X (h a).2 : MvPolynomial σ R) else 0) =
        Nat.card (fiberSubgroup h) • F fun k => #{a | h a = k} := fun h => by
    have hcard : Nat.card (fiberSubgroup h) = #{π : Perm α | h ∘ π = h} := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun π => by
        rw [mem_fiberSubgroup, funext_iff]; rfl)
    -- the fibers of the two coordinates of `h` are unions of fibers of `h`
    have hfst : ∀ i, #{a | (h a).1 = i} = ∑ s, #{a | h a = (i, s)} := fun i => by
      rw [card_eq_sum_card_fiberwise (f := fun a => (h a).2) (t := univ) fun _ _ => mem_univ _]
      exact sum_congr rfl fun s _ => by
        rw [filter_filter]
        exact congrArg card (filter_congr fun a _ => by simp [Prod.ext_iff])
    have hsnd : ∀ s, #{a | (h a).2 = s} = ∑ i, #{a | h a = (i, s)} := fun s => by
      rw [card_eq_sum_card_fiberwise (f := fun a => (h a).1) (t := univ) fun _ _ => mem_univ _]
      exact sum_congr rfl fun i _ => by
        rw [filter_filter]
        exact congrArg card (filter_congr fun a _ => by simp [Prod.ext_iff, and_comm])
    have hX : ∏ a, (X (h a).2 : MvPolynomial σ R) = ∏ s, X s ^ #{a | (h a).2 = s} := by
      rw [← prod_fiberwise univ fun a => (h a).2]
      exact prod_congr rfl fun s _ => by
        rw [prod_congr rfl fun a ha => by rw [(mem_filter.1 ha).2], prod_const]
    simp only [F, ← hfst, ← hsnd, ← hX, hcard]
    split_ifs with hC
    · simp only [hC, implies_true, and_true]
      rw [← sum_filter, sum_const]
    · simp [hC]
  rw [sum_congr rfl fun π _ => h1 π, sum_comm, sum_congr rfl fun h _ => h2 h,
    sum_natCard_fiberSubgroup_smul]
  congr 1
  -- a fiber-size function with the right row sums is a family of exponent vectors, one per row
  simp only [F]
  rw [← sum_filter]
  simp_rw [hsymm_eq_sum_piAntidiag]
  rw [prod_univ_sum]
  refine sum_nbij' (fun A i s => A (i, s)) (fun D p => D p.1 p.2) (fun A hA => ?_)
    (fun D hD => ?_) (fun _ _ => rfl) (fun _ _ => rfl) (fun A _ => ?_)
  · rw [mem_filter] at hA
    simp only [Fintype.mem_piFinset, mem_piAntidiag, mem_univ, implies_true, and_true]
    exact hA.2
  · simp only [Fintype.mem_piFinset, mem_piAntidiag, mem_univ, implies_true, and_true] at hD
    simp only [mem_filter, mem_piAntidiag, mem_univ, implies_true, and_true, hD]
    rw [Fintype.sum_prod_type]
    simp only [hD, hr]
  · rw [prod_comm]
    exact prod_congr rfl fun s _ => (prod_pow_eq_pow_sum _ _ _).symm

end Average

section YoungAverage
variable {σ : Type*} [Fintype σ] (R : Type*) [CommSemiring R] {n : ℕ}
theorem sum_card_fixedPoints_smul_psumPart_partition [DecidableEq σ] (ν : n.Partition) :
    ∑ π : Perm (Fin n), Nat.card {q : Perm (Fin n) ⧸ youngSubgroup ν // π • q = q} •
        psumPart σ R π.partition = n.factorial • hsymmPart σ R ν := by
  have hr : ∑ i, #{a | youngBlock ν a = i} = Fintype.card (Fin n) :=
    (card_eq_sum_card_fiberwise fun a _ => mem_univ (youngBlock ν a)).symm
  have key := sum_card_smul_psumPart_partition (σ := σ) R _ hr
  rw [show n.factorial = (Fintype.card (Fin n)).factorial by rw [Fintype.card_fin]]
  convert key using 3 with π
  · rw [youngSubgroup_eq_fiberSubgroup, card_fixedPoints_quotient_fiberSubgroup]
    -- the two counts differ only in the instance deciding equality of rows
    convert rfl
  · -- the rows of `ν` have the sizes of its parts
    rw [hsymmPart]
    conv_lhs => rw [← Multiset.sort_eq ν.parts (· ≥ ·)]
    rw [Multiset.map_coe, Multiset.prod_coe, ← Fin.prod_univ_fun_getElem]
    refine prod_congr rfl fun i _ => congrArg _ ?_
    rw [← Fintype.card_subtype, ← Fintype.card_congr (youngBlockEquiv ν i), Fintype.card_fin]

end YoungAverage

variable {n : ℕ}

/-- The complete homogeneous coefficient is the Gram entry of the actual Specht-to-Young
Hom dimensions. The alphabet need only record the column partition, regardless of degree. -/
theorem coeff_hsymmPart_partWeight_eq_sum_multiplicity_mul {σ : Type*} [Fintype σ]
    (ν ξ : n.Partition) (hξ : ξ.parts.card ≤ Fintype.card σ) :
    (hsymmPart σ ℂ ν).coeff (partWeight σ ξ) =
      ∑ μ : n.Partition,
        ((Module.finrank ℂ (spechtModuleℂ μ ⟶ permutationModuleℂ ν) : ℂ) *
          (Module.finrank ℂ (spechtModuleℂ μ ⟶ permutationModuleℂ ξ) : ℂ)) := by
  classical
  have key := congrArg (fun p : MvPolynomial σ ℂ => p.coeff (partWeight σ ξ))
    (sum_card_fixedPoints_smul_psumPart_partition (σ := σ) ℂ ν)
  simp only [← Nat.cast_smul_eq_nsmul ℂ, coeff_sum, coeff_smul, smul_eq_mul,
    coeff_partWeight_psumPart_partition ℂ _ ξ hξ] at key
  have hg := sum_char_permutationModuleℂ_mul_char_permutationModuleℂ ν ξ
  simp only [char_permutationModuleℂ] at hg
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  exact mul_left_cancel₀ hf (key.symm.trans hg)

end TauCeti
end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
