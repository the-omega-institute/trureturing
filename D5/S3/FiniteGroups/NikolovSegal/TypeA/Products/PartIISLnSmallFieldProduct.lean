/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnSmallFieldProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnSmallFieldProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Products.PartIISLnAllFieldValues
import D5.S3.FiniteGroups.NikolovSegal.TypeA.Products.PartIISLnClassWidth

/-! Actual PartII Section5 small-field scalar PRODUCT input for ALL bare
SLn and intrinsic PSLn automorphisms in every sufficiently large rank.
The finite-outer consumer, genuine full class width, F2/full-group
classification and exact ordered shift are PROVED consumed inputs.
The chosen width and rank cutoff precede every field, rank and beta/e tuple;
one correction tuple precedes every target. Other simple families remain open. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace NikolovSegal.PartIISLnSmallFieldProduct
open Matrix PartIIFixedSLnPower PartIISLnClassWidth
universe u
variable {F : Type u} [Field F] [Fintype F]
private abbrev classLength : ℕ := 25*((80+80*80)*12)

private theorem class_word_values_target {S : Type*} [Group S] {R : ℕ}
    (h target : S) (a : Fin R → S)
    (ha : orderedProduct (fun i => (a i)⁻¹*h*a i)=target*h^R) :
    orderedProduct (fun i => (a i*(h^i.val)⁻¹)⁻¹*h*(a i*(h^i.val)⁻¹)*h⁻¹)=target := by
  calc
    _ = orderedProduct (fun i => (a i)⁻¹*h*a i)*(h^R)⁻¹ :=
      PartIIConjugacyValueConsumption.ordered_conjugacy_commutator_values h R a
    _ = (target*h^R)*(h^R)⁻¹ := congrArg (fun w : S => w*(h^R)⁻¹) ha
    _ = target := by group

/-- Exact full-group SLn coverage in the actual long-cycle rank shape,
including F2 and original prescribed q/e; no shift remains in the target. -/
theorem actual_bare_SLn_bounded_field_product_shape
    (q : ℕ) (hq : 0<q) (r k K : ℕ) (hp : k+2≤q*r)
    (hL : 16≤q*r+1) (hF : Fintype.card F≤K)
    (beta : Fin (classLength*(K^2*(K^K*2))) →
      MulAut (SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F))
    (e : Fin (classLength*(K^2*(K^K*2))) → ℕ)
    (he : ∀ i, 0<e i ∧ e i∣q) :
    ∃ y : Fin (classLength*(K^2*(K^K*2))) → SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
      ∀ target : SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
        ∃ c : Fin (classLength*(K^2*(K^K*2))) → SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
          orderedProduct (fun i => (c i)⁻¹*((beta i*MulAut.conj (y i)⁻¹)^(q/e i)) (c i))=target := by
  obtain ⟨_,y,hy⟩ := PartIISLnAllFieldValues.actual_bare_SLn_all_field_values
    q hq r k K classLength hp hF beta e he
  refine ⟨y,?_⟩
  intro target
  let h := (fixedElement (F:=F) (q*r) k)^q
  obtain ⟨a,ha⟩ := actual_fixed_cycle_full_group_class_word q r k hp hL (target*h^classLength)
  obtain ⟨c,hc⟩ := hy (fun i => a i*(h^i.val)⁻¹)
  refine ⟨c,?_⟩
  change orderedProduct (fun i => (c i)⁻¹*((beta i*MulAut.conj (y i)⁻¹)^(q/e i)) (c i))=
    orderedProduct (fun i => (a i*(h^i.val)⁻¹)⁻¹*h*(a i*(h^i.val)⁻¹)*h⁻¹) at hc
  change orderedProduct (fun i => (a i)⁻¹*h*a i)=target*h^classLength at ha
  exact hc.trans (class_word_values_target h target a ha)

/-- Intrinsic PSLn full scalar PRODUCT. Target lifting is ordinary quotient
surjectivity; the bare automorphisms themselves are NOT lifted. -/
theorem actual_bare_PSLn_bounded_field_product_shape
    (q : ℕ) (hq : 0<q) (r k K : ℕ) (hp : k+2≤q*r)
    (hL : 16≤q*r+1) (hF : Fintype.card F≤K)
    (beta : Fin (classLength*(K^2*(K^K*2))) →
      MulAut (ProjectiveSpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F))
    (e : Fin (classLength*(K^2*(K^K*2))) → ℕ)
    (he : ∀ i, 0<e i ∧ e i∣q) :
    ∃ y : Fin (classLength*(K^2*(K^K*2))) → ProjectiveSpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
      ∀ target : ProjectiveSpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
        ∃ c : Fin (classLength*(K^2*(K^K*2))) → ProjectiveSpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
          orderedProduct (fun i => (c i)⁻¹*((beta i*MulAut.conj (y i)⁻¹)^(q/e i)) (c i))=target := by
  classical
  obtain ⟨_,y,hy⟩ := PartIISLnAllFieldValues.actual_bare_PSLn_all_field_values
    q hq r k K classLength hp hF beta e he
  let pi := QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F))
  let h := (pi (fixedElement (F:=F) (q*r) k))^q
  refine ⟨y,?_⟩
  intro target
  obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective (Subgroup.center _) (target*h^classLength)
  obtain ⟨a,ha⟩ := actual_fixed_cycle_full_group_class_word q r k hp hL g
  have hm := map_list_prod pi
    (List.ofFn (fun i => (a i)⁻¹*(fixedElement (F:=F) (q*r) k)^q*a i))
  change pi (orderedProduct (fun i => (a i)⁻¹*(fixedElement (F:=F) (q*r) k)^q*a i))=_ at hm
  rw [ha,hg] at hm
  have hpword : orderedProduct (fun i => (pi (a i))⁻¹*h*pi (a i))=target*h^classLength := by
    simpa only [orderedProduct,List.map_ofFn,Function.comp_def,map_mul,map_inv,map_pow,h] using hm.symm
  obtain ⟨c,hc⟩ := hy (fun i => pi (a i)*(h^i.val)⁻¹)
  refine ⟨c,?_⟩
  change orderedProduct (fun i => (c i)⁻¹*((beta i*MulAut.conj (y i)⁻¹)^(q/e i)) (c i))=
    orderedProduct (fun i => (pi (a i)*(h^i.val)⁻¹)⁻¹*h*(pi (a i)*(h^i.val)⁻¹)*h⁻¹) at hc
  exact hc.trans (class_word_values_target h target (fun i => pi (a i)) hpword)

/-- Fixed chosen length and explicit rank cutoff BEFORE all groups and
bare automorphism/divisor tuples. Covers EVERY bounded finite field and
EVERY rank above the cutoff, with no congruence/rank-shape premise. -/
theorem actual_uniform_bare_SLn_bounded_field_scalar_product
    (q : ℕ) (hq : 0<q) (K : ℕ) (hK : 0<K) :
    ∃ N rankCutoff : ℕ, 0<N ∧
      ∀ (F : Type u) [Field F] [Fintype F], Fintype.card F≤K →
      ∀ n : ℕ, rankCutoff≤n →
      ∀ (beta : Fin N → MulAut (SpecialLinearGroup (Fin n) F)) (e : Fin N → ℕ),
        (∀ i, 0<e i ∧ e i∣q) →
        ∃ y : Fin N → SpecialLinearGroup (Fin n) F,
          ∀ target : SpecialLinearGroup (Fin n) F,
            ∃ c : Fin N → SpecialLinearGroup (Fin n) F,
              orderedProduct (fun i => (c i)⁻¹*((beta i*MulAut.conj (y i)⁻¹)^(q/e i)) (c i))=target := by
  refine ⟨classLength*(K^2*(K^K*2)),24*q+86,?_,?_⟩
  · exact Nat.mul_pos (by decide) (Nat.mul_pos (Nat.pow_pos hK) (Nat.mul_pos (Nat.pow_pos hK) (by decide)))
  · intro F _ _ hF n hn beta e he
    obtain ⟨r,k,hs,hp⟩ := (cycleClass% rank_decomposition) q hq n (by omega)
    subst n
    have hL : 16≤q*r+1 := by omega
    exact actual_bare_SLn_bounded_field_product_shape q hq r k K hp hL hF beta e he

/-- Same uniform field/rank quantifiers, intrinsic projective targets and
arbitrary bare quotient actions; one global correction before ALL targets. -/
theorem actual_uniform_bare_PSLn_bounded_field_scalar_product
    (q : ℕ) (hq : 0<q) (K : ℕ) (hK : 0<K) :
    ∃ N rankCutoff : ℕ, 0<N ∧
      ∀ (F : Type u) [Field F] [Fintype F], Fintype.card F≤K →
      ∀ n : ℕ, rankCutoff≤n →
      ∀ (beta : Fin N → MulAut (ProjectiveSpecialLinearGroup (Fin n) F)) (e : Fin N → ℕ),
        (∀ i, 0<e i ∧ e i∣q) →
        ∃ y : Fin N → ProjectiveSpecialLinearGroup (Fin n) F,
          ∀ target : ProjectiveSpecialLinearGroup (Fin n) F,
            ∃ c : Fin N → ProjectiveSpecialLinearGroup (Fin n) F,
              orderedProduct (fun i => (c i)⁻¹*((beta i*MulAut.conj (y i)⁻¹)^(q/e i)) (c i))=target := by
  refine ⟨classLength*(K^2*(K^K*2)),24*q+86,?_,?_⟩
  · exact Nat.mul_pos (by decide) (Nat.mul_pos (Nat.pow_pos hK) (Nat.mul_pos (Nat.pow_pos hK) (by decide)))
  · intro F _ _ hF n hn beta e he
    obtain ⟨r,k,hs,hp⟩ := (cycleClass% rank_decomposition) q hq n (by omega)
    subst n
    have hL : 16≤q*r+1 := by omega
    exact actual_bare_PSLn_bounded_field_product_shape q hq r k K hp hL hF beta e he
end NikolovSegal.PartIISLnSmallFieldProduct
