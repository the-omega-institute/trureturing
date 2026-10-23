/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIIConjugacyValueConsumption
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIIConjugacyValueConsumption
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Products.PartIISLnBareSmallFieldValues

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
/-! PartII Section5, (4): exact noncommutative conversion of an ordered
conjugacy-class word to genuine commutator VALUES. The actual finite-outer
consumer is instantiated below. There is no assumed class width or target
surjectivity; the uniform LS2 theorem remains a separate unproved kernel. -/
namespace NikolovSegal.PartIIConjugacyValueConsumption
universe u
private theorem ordered_shift {S : Type u} [Group S] (h : S) : ∀ N : ℕ,
    ∀ a : Fin N → S,
      orderedProduct (fun i => h^i.val*a i*(h^(i.val+1))⁻¹)=
        orderedProduct a*(h^N)⁻¹ := by
  intro N
  induction N with
  | zero => intro a;simp [orderedProduct]
  | succ N ih =>
    intro a
    let b : Fin N → S := fun i => h^i.val*a i.succ*(h^(i.val+1))⁻¹
    have hf : (fun i : Fin N => h^i.succ.val*a i.succ*(h^(i.succ.val+1))⁻¹)=
        fun i => (MulAut.conj h) (b i) := by
      funext i
      simp only [b,Fin.val_succ,MulAut.conj_apply,pow_succ,_root_.mul_inv_rev]
      group
    have hp : orderedProduct (fun i => (MulAut.conj h) (b i))=
        (MulAut.conj h) (orderedProduct b) := by
      simpa only [orderedProduct, List.map_ofFn, Function.comp_def] using
        (map_list_prod (MulAut.conj h) (List.ofFn b)).symm
    simp only [orderedProduct,List.ofFn_succ,List.prod_cons,Fin.val_zero,pow_zero,
      zero_add,pow_one,one_mul]
    change (a 0*h⁻¹)*orderedProduct (fun i : Fin N => h^i.succ.val*a i.succ*(h^(i.succ.val+1))⁻¹)=
      (a 0*orderedProduct (fun i : Fin N => a i.succ))*(h^(N+1))⁻¹
    rw [hf,hp]
    have hb := ih (fun i : Fin N => a i.succ)
    change orderedProduct b=orderedProduct (fun i : Fin N => a i.succ)*(h^N)⁻¹ at hb
    rw [hb]
    simp only [MulAut.conj_apply,pow_succ,_root_.mul_inv_rev]
    group
/-- Every factor remains a genuine h-commutator VALUE. The witness
u_i*h^-i and the final h^-N offset retain increasing, noncommutative order. -/
theorem ordered_conjugacy_commutator_values {S : Type u} [Group S]
    (h : S) (N : ℕ) (a : Fin N → S) :
    orderedProduct (fun i => (a i*(h^i.val)⁻¹)⁻¹*h*(a i*(h^i.val)⁻¹)*h⁻¹)=
      orderedProduct (fun i => (a i)⁻¹*h*a i)*(h^N)⁻¹ := by
  have hf : (fun i => (a i*(h^i.val)⁻¹)⁻¹*h*(a i*(h^i.val)⁻¹)*h⁻¹)=
      fun i => h^i.val*((a i)⁻¹*h*a i)*(h^(i.val+1))⁻¹ := by
    funext i
    rw [pow_succ]
    group
  rw [hf]
  exact ordered_shift h N _

/-- Actual Section5 consumption for arbitrary bare PSLn automorphisms,
now including F3/F4. ONE original right correction precedes every genuine
class-witness tuple; all unused indices and original q/e remain exact.
The proved class-size bound does not supply uniform class PRODUCT width. -/
theorem actual_bare_PSLn_conjugacy_word_values
    {F : Type u} [Field F] [Fintype F]
    (q : ℕ) (hq : 0 < q) (r k K R : ℕ) (hp : k+2≤q*r)
    (h2 : 2<Fintype.card F) (hF : Fintype.card F≤K)
    (beta : Fin (R*(K^2*(K^K*2))) →
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F))
    (e : Fin (R*(K^2*(K^K*2))) → ℕ) (he : ∀ i, 0<e i ∧ e i∣q) :
    let z := QuotientGroup.mk' (Subgroup.center
      (Matrix.SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F))
        (PartIIFixedSLnPower.fixedElement (F:=F) (q*r) k)
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F)≤
      (Nat.card (ConjClasses.mk (z^q)).carrier)^16 ∧
    ∃ y : Fin (R*(K^2*(K^K*2))) → Matrix.ProjectiveSpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
      ∀ a : Fin R → Matrix.ProjectiveSpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
        ∃ c : Fin (R*(K^2*(K^K*2))) → Matrix.ProjectiveSpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
          orderedProduct (fun i => (c i)⁻¹*((beta i*MulAut.conj (y i)⁻¹)^(q/e i)) (c i))=
            orderedProduct (fun i => (a i)⁻¹*z^q*a i)*((z^q)^R)⁻¹ := by
  dsimp only
  obtain ⟨hclass,y,hy⟩ := PartIISLnBareSmallFieldValues.actual_bare_PSLn_small_field_values
    q hq r k K R hp h2 hF beta e he
  refine ⟨by simpa only [map_pow] using hclass,y,?_⟩
  intro a
  let z := QuotientGroup.mk' (Subgroup.center
      (Matrix.SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F))
        (PartIIFixedSLnPower.fixedElement (F:=F) (q*r) k)
  obtain ⟨c,hc⟩ := hy (fun i => a i*((z^q)^i.val)⁻¹)
  refine ⟨c,?_⟩
  exact hc.trans (ordered_conjugacy_commutator_values (z^q) R a)
end NikolovSegal.PartIIConjugacyValueConsumption
