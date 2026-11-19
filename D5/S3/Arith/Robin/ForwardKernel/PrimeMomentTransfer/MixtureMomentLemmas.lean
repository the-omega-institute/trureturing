/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MixtureMomentLemmas
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MixtureMomentLemmas
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Finite algebraic moment data and arbitrary-order biased-cube moment comparisons. -/

/-
proof_shape: FifthData: definition.
proof_shape: inj_sum_product_bound: content
  (consumers: SixthOrderTopPairingRefutation.top_order_bound,
  TopOrderObstructionCore.mixture_uniform_leading_bound_all).
proof_shape: subsetDistinct_univ: bind-only
  (consumers: SixthOrderTopPairingRefutation.top_order_bound,
  TopOrderObstructionFamily.top_order_transfer_fails).
proof_shape: subset_unit_moment: bind-only
  (consumers: SixthOrderTopPairingRefutation.model_unit_pair,
  SixthOrderTopPairingRefutation.model_four_defect_lower,
  TopOrderObstructionCore.mixture_propagation_limit).
proof_shape: distinct_pair_formula: bind-only (consumer: subset_pair_formula).
proof_shape: subset_pair_formula: bind-only
  (consumers: SixthOrderTopPairingRefutation.top_order_bound,
  TopOrderObstructionCore.mixture_uniform_leading_bound_all).
escape_witness: inj_sum_product_bound bounds the arbitrary-order collision cost
  by choose(r,2) N^(r-1) through the descending-factorial recurrence.
admission_basis: escape-witness.
-/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.BiasedCubeMixture
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PairingDefectAlgebra
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.QuadraticFourthExpansion

/-! Algebraic moment data and finite-mixture identities at arbitrary order. -/

open scoped BigOperators Topology
open Filter

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

namespace FifthOrderTopOnlyRefutation

/-- One finite algebraic moment model, with all types in universe zero. -/
structure FifthData where
  ι : Type
  [fintype : Fintype ι]
  [decidableEq : DecidableEq ι]
  A : Type
  [commRing : CommRing A]
  [algebra : Algebra ℝ A]
  ℓ : A →ₗ[ℝ] ℝ
  Y : ι → A
  a : ℝ
  b : ℝ
  H : ℝ
  L : ℝ

attribute [instance] FifthData.fintype FifthData.decidableEq FifthData.commRing FifthData.algebra

end FifthOrderTopOnlyRefutation

/-- Removing noninjective assignments costs at most `choose(r,2)*N^(r-1)`
for arbitrary positive order `r` and at least `r` available indices. -/
theorem inj_sum_product_bound (r N : ℕ) (hr : 1 ≤ r) (hN : r ≤ N)
    (g : Fin r → Fin N → ℝ) (hg : ∀ i d, |g i d| ≤ 1) :
    |(∑ x : Fin r → Fin N with Function.Injective x, ∏ i, g i (x i)) -
        ∏ i, ∑ d, g i d| ≤ (r.choose 2 : ℝ) * (N : ℝ)^(r - 1) := by
  classical
  let all : Finset (Fin r → Fin N) := Finset.univ
  let good : Finset (Fin r → Fin N) := all.filter Function.Injective
  let bad : Finset (Fin r → Fin N) := all.filter (fun x => ¬Function.Injective x)
  have hsplit :
      (∑ x : Fin r → Fin N with Function.Injective x, ∏ i, g i (x i)) +
        ∑ x : Fin r → Fin N with ¬Function.Injective x, ∏ i, g i (x i) =
        ∑ x : Fin r → Fin N, ∏ i, g i (x i) := by
    exact Finset.sum_filter_add_sum_filter_not _ Function.Injective _
  have hall : (∑ x : Fin r → Fin N, ∏ i, g i (x i)) = ∏ i, ∑ d, g i d := by
    rw [← Fintype.prod_sum]
  have hcardbad : (bad.card : ℝ) ≤ (r.choose 2 : ℝ) * (N : ℝ)^(r - 1) := by
    have hcardgood : good.card = N.descFactorial r := by
      let e : {x : Fin r → Fin N // Function.Injective x} ≃ (Fin r ↪ Fin N) :=
        { toFun := fun x => ⟨x.1, x.2⟩
          invFun := fun x => ⟨x, x.injective⟩
          left_inv := by intro x; rfl
          right_inv := by intro x; rfl }
      have he := Fintype.card_congr e
      rw [Fintype.card_embedding_eq] at he
      simpa only [good, all, Fintype.card_subtype, Fintype.card_fin] using he
    have hcardall : all.card = N ^ r := by simp [all, Fintype.card_fun]
    have hdisj : Disjoint good bad := by
      apply Finset.disjoint_left.mpr
      intro x hxg hxb
      exact (Finset.mem_filter.mp hxb).2 (Finset.mem_filter.mp hxg).2
    have hunion : good ∪ bad = all := by
      ext x
      simp only [good, bad, all, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and]
      tauto
    have hc : good.card + bad.card = all.card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    rw [hcardall, hcardgood] at hc
    have hcast : (N.descFactorial r : ℝ) + (bad.card : ℝ) = (N : ℝ)^r := by
      exact_mod_cast hc
    have herror : ∀ j : ℕ, j ≤ N →
        (N : ℝ)^j - (N.descFactorial j : ℝ) ≤
          (j.choose 2 : ℝ) * (N : ℝ)^(j-1) := by
      intro j
      induction j with
      | zero =>
          intro hj
          simp
      | succ j ih =>
          intro hj
          by_cases hj0 : j = 0
          · subst j
            simp
          have hjpos : 1 ≤ j := by omega
          have hrec : (N.descFactorial (j+1) : ℝ) =
              ((N : ℝ) - j) * (N.descFactorial j : ℝ) := by
            rw [Nat.descFactorial_succ, Nat.cast_mul,
              Nat.cast_sub (by omega : j ≤ N)]
          have hdesc : (N.descFactorial j : ℝ) ≤ (N : ℝ)^j := by
            exact_mod_cast Nat.descFactorial_le_pow N j
          have hpow : (N : ℝ) * (N : ℝ)^(j-1) = (N : ℝ)^j := by
            rw [← pow_succ', Nat.sub_add_cancel hjpos]
          have hchooseNat : (j+1).choose 2 = j + j.choose 2 := by
            simpa only [Nat.choose_one_right] using Nat.choose_succ_succ j 1
          have hchoose : ((j+1).choose 2 : ℝ) = (j : ℝ) + (j.choose 2 : ℝ) := by
            exact_mod_cast hchooseNat
          calc
            _ = (N : ℝ) * ((N : ℝ)^j - (N.descFactorial j : ℝ)) +
                (j : ℝ) * (N.descFactorial j : ℝ) := by
              rw [hrec, pow_succ']
              ring
            _ ≤ (N : ℝ) * ((j.choose 2 : ℝ) * (N : ℝ)^(j-1)) +
                (j : ℝ) * (N : ℝ)^j :=
              add_le_add
                (mul_le_mul_of_nonneg_left (ih (by omega)) (by positivity))
                (mul_le_mul_of_nonneg_left hdesc (by positivity))
            _ = ((j+1).choose 2 : ℝ) * (N : ℝ)^((j+1)-1) := by
              rw [Nat.add_sub_cancel, hchoose]
              calc
                _ = (j.choose 2 : ℝ) * ((N : ℝ) * (N : ℝ)^(j-1)) +
                    (j : ℝ) * (N : ℝ)^j := by ring
                _ = _ := by rw [hpow]; ring
    have herr := herror r hN
    linarith

  have hbad :
      |∑ x : Fin r → Fin N with ¬Function.Injective x, ∏ i, g i (x i)| ≤
        (r.choose 2 : ℝ) * (N : ℝ)^(r - 1) := by
    calc
      _ ≤ ∑ x : Fin r → Fin N with ¬Function.Injective x, |∏ i, g i (x i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x : Fin r → Fin N with ¬Function.Injective x, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [Finset.abs_prod]
        exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun i _ => hg i (x i))
      _ = (bad.card : ℝ) := by simp [bad, all]
      _ ≤ _ := hcardbad
  have he : (∑ x : Fin r → Fin N with Function.Injective x, ∏ i, g i (x i)) -
      ∏ i, ∑ d, g i d =
      -(∑ x : Fin r → Fin N with ¬Function.Injective x, ∏ i, g i (x i)) := by
    rw [← hall]
    linarith
  rw [he, abs_neg]
  exact hbad


namespace SixthOrderTopPairingRefutation

lemma subsetDistinct_univ {k N : ℕ} (ℓ : ((Fin N → Bool) → ℝ) →ₗ[ℝ] ℝ)
    (Y : Fin N → (Fin N → Bool) → ℝ) (g : Fin k → Fin N → ℝ) :
    subsetDistinctMoment ℓ Y g (Finset.univ : Finset (Fin k)) =
      distinctIndexMoment ℓ Y g := by
  classical
  let e : (Finset.univ : Finset (Fin k)) ≃ Fin k :=
    { toFun := Subtype.val
      invFun := fun i => ⟨i, Finset.mem_univ i⟩
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  rw [subsetDistinctMoment, ← retained_assignment_reindex ℓ Y Finset.univ g]
  convert assignment_moment_reindex ℓ Y e (fun i => g i.val) using 1
  unfold distinctIndexMoment
  apply Finset.sum_congr
  · ext x
    simp
  · intro x hx
    rfl

lemma subset_unit_moment {κ : Type} [Fintype κ] {k : ℕ}
    (zValue zWeight : κ → ℝ) (N : ℕ) (U : Finset (Fin k)) :
    subsetDistinctMoment (mixtureFunctional N zValue zWeight) (modelY N)
      (fun (_ : Fin k) (_ : Fin N) => (1 : ℝ)) U =
      ((∑ z : κ, zWeight z * zValue z ^ U.card) / Real.sqrt N ^ U.card) * (N.descFactorial U.card : ℝ) := by
  classical
  have hc : (Finset.univ.filter (Function.Injective : (Fin (Fintype.card U) → Fin N) → Prop)).card =
      N.descFactorial (Fintype.card U) := by
    let e : {x : Fin (Fintype.card U) → Fin N // Function.Injective x} ≃ (Fin (Fintype.card U) ↪ Fin N) :=
      { toFun := fun x => ⟨x.1, x.2⟩
        invFun := fun x => ⟨x, x.injective⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    have he := Fintype.card_congr e
    rw [Fintype.card_embedding_eq] at he
    simpa only [Fintype.card_subtype, Fintype.card_fin] using he
  have hR : subsetDistinctMoment (mixtureFunctional N zValue zWeight) (modelY N)
      (fun (_ : Fin k) (_ : Fin N) => (1 : ℝ)) U =
      distinctIndexMoment (mixtureFunctional N zValue zWeight) (modelY N)
        (fun (_ : Fin (Fintype.card U)) (_ : Fin N) => (1 : ℝ)) := by
    unfold subsetDistinctMoment distinctIndexMoment
    simp only [Fintype.card_coe]
    apply Finset.sum_congr
    · ext x
      simp
    · intro x hx
      rfl
  rw [hR, mixture_distinct_moments]
  simp only [Finset.prod_const_one, Finset.sum_const,
    nsmul_eq_mul, mul_one, hc, Fintype.card_coe]

lemma distinct_pair_formula {κ : Type} [Fintype κ]
    (zValue zWeight : κ → ℝ) (N : ℕ) (f h : Fin N → ℝ) :
    distinctIndexMoment (mixtureFunctional N zValue zWeight) (modelY N) ![f, h] =
      ((∑ z : κ, zWeight z * zValue z ^ 2) / (N : ℝ)) *
        ((∑ d, f d) * (∑ d, h d) - ∑ d, f d * h d) := by
  classical
  have hsum :
      (∑ x : Fin 2 → Fin N with Function.Injective x, ∏ i, ![f, h] i (x i)) =
        ∑ d, ∑ e with d ≠ e, f d * h e := by
    simpa [Fin.prod_univ_two] using (sum_two (fun d e => f d * h e))
  have hoff : (∑ d, ∑ e with d ≠ e, f d * h e) =
      (∑ d, f d) * (∑ e, h e) - ∑ d, f d * h d := by
    simpa [Finset.sum_filter, Fintype.sum_mul_sum] using
      (FiolArbitraryTreePair.sum_off_diagonal (fun d e => f d * h e))
  rw [mixture_distinct_moments, hsum]
  rw [Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)]
  rw [hoff]

lemma subset_pair_formula {κ : Type} [Fintype κ] {α : Type*} [Fintype α] [DecidableEq α]
    (zValue zWeight : κ → ℝ) (N : ℕ) (g : α → Fin N → ℝ)
    (e : Finset (α)) (he : e.card = 2) :
    subsetDistinctMoment (mixtureFunctional N zValue zWeight) (modelY N) g e =
      ((∑ z : κ, zWeight z * zValue z ^ 2) / (N : ℝ)) *
        ((∏ i ∈ e, ∑ d, g i d) - ∑ d, ∏ i ∈ e, g i d) := by
  classical
  let v : e ≃ Fin 2 := Fintype.equivOfCardEq (by simpa using he)
  let q : Fin 2 → Fin N → ℝ := fun j => g (v.symm j).val
  have hR : subsetDistinctMoment (mixtureFunctional N zValue zWeight) (modelY N) g e =
      distinctIndexMoment (mixtureFunctional N zValue zWeight) (modelY N) q := by
    unfold subsetDistinctMoment
    rw [← retained_assignment_reindex (mixtureFunctional N zValue zWeight) (modelY N) e g]
    convert assignment_moment_reindex (mixtureFunctional N zValue zWeight) (modelY N) v
      (fun i => g i.val) using 1
    unfold distinctIndexMoment
    apply Finset.sum_congr
    · ext x
      simp
    · intro x hx
      rfl
  rw [hR]
  have hq : q = ![q 0, q 1] := by funext j; fin_cases j <;> rfl
  rw [hq, distinct_pair_formula zValue zWeight]
  have hp : (∏ i ∈ e, ∑ d, g i d) =
      (∑ d, q 0 d) * (∑ d, q 1 d) := by
    simp only [q]
    rw [← Finset.prod_attach e]
    have hprod : (∏ i : e, ∑ d, g i.val d) =
        ∏ j : Fin 2, ∑ d, q j d := by
      apply Fintype.prod_equiv v
      intro i
      simp [q]
    simpa only [Finset.attach_eq_univ, Fin.prod_univ_two] using hprod
  have ht : (∑ d, ∏ i ∈ e, g i d) = ∑ d, q 0 d * q 1 d := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [← Finset.prod_attach e]
    have hprod : (∏ i : e, g i.val d) = ∏ j : Fin 2, q j d := by
      apply Fintype.prod_equiv v
      intro i
      simp [q]
    simpa only [Finset.attach_eq_univ, Fin.prod_univ_two] using hprod
  rw [← hp, ← ht]

end SixthOrderTopPairingRefutation

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
