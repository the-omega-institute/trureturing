/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIITypeAUniformProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIITypeAUniformProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Products.PartIISLnSmallFieldProduct
import D5.S3.FiniteGroups.NikolovSegal.TypeA.Products.PartIISLnBareLargeFieldProduct

/-! Combine the PROVED large-field/all-rank and bounded-field/large-rank
branches into one genuine uniform bare type-A scalar PRODUCT length.
Ordered identity padding is proved for the actual arbitrary beta/e tuple.
This family theorem is NOT the all-finite-simple supplier. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace NikolovSegal.PartIITypeAUniformProduct
open Matrix
universe u

theorem scalar_product_append {S : Type u} [Group S] {q A B : ℕ}
    (beta : Fin (A+B) → MulAut S) (e : Fin (A+B) → ℕ)
    (cover : PartIIScalarProductInput q A (fun i => beta (i.castAdd B))
      (fun i => e (i.castAdd B))) :
    PartIIScalarProductInput q (A+B) beta e := by
  intro he
  obtain ⟨y,hy⟩ := cover (fun i => he (i.castAdd B))
  let yp : Fin (A+B) → S := Fin.append y (fun _ : Fin B => 1)
  refine ⟨yp,?_⟩
  intro target
  obtain ⟨c,hc⟩ := hy target
  let cp : Fin (A+B) → S := Fin.append c (fun _ : Fin B => 1)
  refine ⟨cp,?_⟩
  have hf : (fun i => (cp i)⁻¹*((beta i*MulAut.conj (yp i)⁻¹)^(q/e i)) (cp i))=
      Fin.append
        (fun i : Fin A => (c i)⁻¹*((beta (i.castAdd B)*MulAut.conj (y i)⁻¹)^(q/e (i.castAdd B))) (c i))
        (fun _ : Fin B => 1) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [cp,yp,Fin.append_left]
    · simp only [cp,yp,Fin.append_right,inv_one,map_one,one_mul]
  rw [hf]
  simpa only [orderedProduct,List.ofFn_fin_append,List.prod_append,
    List.ofFn_const,List.prod_replicate,one_pow,mul_one] using hc

/-- ONE chosen positive scalar PRODUCT length precedes EVERY finite field,
EVERY sufficiently large actual rank and EVERY bare SLn beta/divisor tuple.
Both cardinal2 and unbounded fields are included with the original q/e. -/
theorem actual_uniform_all_field_large_rank_SLn_scalar_product
    (q : ℕ) (hq : 0<q) :
    ∃ M rankCutoff : ℕ, 0<M ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      ∀ n : ℕ, rankCutoff≤n →
      ∀ beta : Fin M → MulAut (SpecialLinearGroup (Fin n) F),
      ∀ e : Fin M → ℕ, PartIIScalarProductInput q M beta e := by
  obtain ⟨L,C,hL,hlarge⟩ := PartIISLnBareLargeFieldProduct.actual_uniform_bare_SLn_scalar_product q hq
  obtain ⟨S,T,hS,hsmall⟩ := PartIISLnSmallFieldProduct.actual_uniform_bare_SLn_bounded_field_scalar_product
    q hq (C+1) (by omega)
  refine ⟨L+S,T+4,by omega,?_⟩
  intro F _ _ _ n hn beta e
  by_cases hc : C<Fintype.card F
  · obtain ⟨k,rfl⟩ : ∃ k, n=k+4 := ⟨n-4,by omega⟩
    exact scalar_product_append beta e (hlarge F hc k
      (fun i => beta (i.castAdd S)) (fun i => e (i.castAdd S)))
  · have hF : Fintype.card F≤C+1 := by omega
    revert beta e
    rw [Nat.add_comm L S]
    intro beta e
    apply scalar_product_append beta e
    intro he
    exact hsmall F hF n (by omega) (fun i => beta (i.castAdd L))
      (fun i => e (i.castAdd L)) he

/-- Intrinsic PSLn counterpart with identical uniform quantifier order.
Every action and correction lives in the quotient; no beta lift is assumed. -/
theorem actual_uniform_all_field_large_rank_PSLn_scalar_product
    (q : ℕ) (hq : 0<q) :
    ∃ M rankCutoff : ℕ, 0<M ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      ∀ n : ℕ, rankCutoff≤n →
      ∀ beta : Fin M → MulAut (ProjectiveSpecialLinearGroup (Fin n) F),
      ∀ e : Fin M → ℕ, PartIIScalarProductInput q M beta e := by
  obtain ⟨L,C,hL,hlarge⟩ := PartIISLnBareLargeFieldProduct.actual_uniform_bare_PSLn_scalar_product q hq
  obtain ⟨S,T,hS,hsmall⟩ := PartIISLnSmallFieldProduct.actual_uniform_bare_PSLn_bounded_field_scalar_product
    q hq (C+1) (by omega)
  refine ⟨L+S,T+4,by omega,?_⟩
  intro F _ _ _ n hn beta e
  by_cases hc : C<Fintype.card F
  · obtain ⟨k,rfl⟩ : ∃ k, n=k+4 := ⟨n-4,by omega⟩
    exact scalar_product_append beta e (hlarge F hc k
      (fun i => beta (i.castAdd S)) (fun i => e (i.castAdd S)))
  · have hF : Fintype.card F≤C+1 := by omega
    revert beta e
    rw [Nat.add_comm L S]
    intro beta e
    apply scalar_product_append beta e
    intro he
    exact hsmall F hF n (by omega) (fun i => beta (i.castAdd L))
      (fun i => e (i.castAdd L)) he

private theorem SLn_card_matrix_bound (F : Type u) [Field F] [Fintype F] (n : ℕ) :
    Nat.card (SpecialLinearGroup (Fin n) F)≤Fintype.card F^(n*n) := by
  classical
  have hc := Fintype.card_le_of_injective
    (fun g : SpecialLinearGroup (Fin n) F => g.val) Subtype.val_injective
  have hm : Fintype.card (Matrix (Fin n) (Fin n) F)=Fintype.card F^(n*n) := by
    simp only [Matrix,Fintype.card_fun,Fintype.card_fin,← Nat.pow_mul]
  rw [hm] at hc
  simpa only [Nat.card_eq_fintype_card] using hc

theorem actual_PSLn_card_upper_bound (F : Type u) [Field F] [Fintype F] (n : ℕ) :
    Nat.card (ProjectiveSpecialLinearGroup (Fin n) F)≤Fintype.card F^(n*n) := by
  have hc := Nat.card_le_card_of_surjective
    (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)))
    (QuotientGroup.mk'_surjective (Subgroup.center (SpecialLinearGroup (Fin n) F)))
  exact hc.trans (SLn_card_matrix_bound F n)

private theorem bounded_field_rank_card (F : Type u) [Field F] [Fintype F]
    (n K T : ℕ) (hF : Fintype.card F≤K) (hK : 0<K) (hn : n≤T) :
    Fintype.card F^(n*n)≤K^(T*T) :=
  (Nat.pow_le_pow_left hF _).trans (Nat.pow_le_pow_right hK (Nat.mul_le_mul hn hn))

/-- Actual uniform type-A scalar theorem with a GROUP-CARDINALITY cutoff,
all ranks n>=4 and EVERY field. Small field AND small rank exceptions are
excluded by a PROVED actual matrix cardinal bound, not by an exhaustion or
bounded-group-order premise. M and C precede every group and beta/e tuple. -/
theorem actual_uniform_bare_SLn_scalar_product_by_group_card
    (q : ℕ) (hq : 0<q) :
    ∃ M C : ℕ, 0<M ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F], ∀ k : ℕ,
      C<Nat.card (SpecialLinearGroup (Fin (k+4)) F) →
      ∀ beta : Fin M → MulAut (SpecialLinearGroup (Fin (k+4)) F),
      ∀ e : Fin M → ℕ, PartIIScalarProductInput q M beta e := by
  obtain ⟨H,T,hH,hhigh⟩ := actual_uniform_all_field_large_rank_SLn_scalar_product q hq
  obtain ⟨L,K,hL,hlarge⟩ := PartIISLnBareLargeFieldProduct.actual_uniform_bare_SLn_scalar_product q hq
  refine ⟨H+L,(K+1)^(T*T),by omega,?_⟩
  intro F _ _ _ k hcard beta e
  by_cases hn : T≤k+4
  · exact scalar_product_append beta e (hhigh F (k+4) hn
      (fun i => beta (i.castAdd L)) (fun i => e (i.castAdd L)))
  · have hfield : K<Fintype.card F := by
      by_contra hh
      have hf : Fintype.card F≤K+1 := by omega
      have hc := (SLn_card_matrix_bound F (k+4)).trans
        (bounded_field_rank_card F (k+4) (K+1) T hf (by omega) (by omega))
      omega
    revert beta e
    rw [Nat.add_comm H L]
    intro beta e
    exact scalar_product_append beta e (hlarge F hfield k
      (fun i => beta (i.castAdd H)) (fun i => e (i.castAdd H)))

/-- Intrinsic PSLn type-A input at one fixed positive width and group-card
cutoff, before all fields/ranks/actions. This is full family coverage for
n>=4, including F2, rather than a merely shifted/local class range. -/
theorem actual_uniform_bare_PSLn_scalar_product_by_group_card
    (q : ℕ) (hq : 0<q) :
    ∃ M C : ℕ, 0<M ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F], ∀ k : ℕ,
      C<Nat.card (ProjectiveSpecialLinearGroup (Fin (k+4)) F) →
      ∀ beta : Fin M → MulAut (ProjectiveSpecialLinearGroup (Fin (k+4)) F),
      ∀ e : Fin M → ℕ, PartIIScalarProductInput q M beta e := by
  obtain ⟨H,T,hH,hhigh⟩ := actual_uniform_all_field_large_rank_PSLn_scalar_product q hq
  obtain ⟨L,K,hL,hlarge⟩ := PartIISLnBareLargeFieldProduct.actual_uniform_bare_PSLn_scalar_product q hq
  refine ⟨H+L,(K+1)^(T*T),by omega,?_⟩
  intro F _ _ _ k hcard beta e
  by_cases hn : T≤k+4
  · exact scalar_product_append beta e (hhigh F (k+4) hn
      (fun i => beta (i.castAdd L)) (fun i => e (i.castAdd L)))
  · have hfield : K<Fintype.card F := by
      by_contra hh
      have hf : Fintype.card F≤K+1 := by omega
      have hc := (actual_PSLn_card_upper_bound F (k+4)).trans
        (bounded_field_rank_card F (k+4) (K+1) T hf (by omega) (by omega))
      omega
    revert beta e
    rw [Nat.add_comm H L]
    intro beta e
    exact scalar_product_append beta e (hlarge F hfield k
      (fun i => beta (i.castAdd H)) (fun i => e (i.castAdd H)))
end NikolovSegal.PartIITypeAUniformProduct
