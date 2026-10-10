/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalPrescribedProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalPrescribedProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryRadicalCornerPrescribedProduct
import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryRadicalBoundaryPrescribedProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
/-! PartII Proposition6.7 pp262–263 actual prescribed unitary D Phi branch.
Four ordered batches reconstruct the middle rows, first exceptional
pair, second exceptional pair, then the genuine trace-zero corner.
Every residual is an actual ordered inverse-left-product; no radical
or whole-group coverage premise is used. -/
namespace NikolovSegal.PartIIUnitaryRadicalPrescribedProduct
open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions
open PartIIRadicalCoordinates PartIIUnitaryUpperTorus PartIIFieldMaps UnitaryField
open PartIIUnitaryRadicalMiddleFieldProduct PartIIUnitaryRadicalBoundaryFieldProduct
open PartIIUnitaryRadicalCornerPrescribedProduct
open PartIIUnitaryRadicalBoundaryPrescribedProduct PartIIUnitaryRadicalPrescribedMiddleProduct
universe u
variable {F : Type u} [Field F] [Finite F] {k M : ℕ}
private def values (h : Fin M → SpecialLinearGroup (Fin (k+6)) F)
    (a : Fin M → Fin (k+6) → Fˣ) (phi : Fin M → RingAut F) (s : Fin M → ℕ)
    (x : Fin M → SpecialLinearGroup (Fin (k+6)) F) :=
  orderedProduct (fun j => (x j)⁻¹*((MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false)^(s j)) (x j))
private theorem residual_row (P b : SpecialLinearGroup (Fin (k+6)) F)
    (hP : InRadical P) (hb : InRadical b) (j : Fin (k+6)) (hj0 : j≠first) (hjl : j≠last) :
    (P⁻¹*b) first j= -P first j+b first j := by
  rw [(actual_radical_product_row_column _ _ (actual_radical_inverse_mem _ hP) hb j hj0 hjl).1,
    (actual_radical_inverse_row_column _ hP j hj0 hjl).1]
private theorem zero_rows_corner (ι : RingAut F) (hinv : Function.Involutive ι)
    (g : SpecialLinearGroup (Fin (k+6)) F) (hg : InRadical g) (hgu : steinberg ι g=g)
    (hz : ∀ j, j≠first → j≠last → g first j=0) :
    g=(vCorner% corner) (g first last) ∧ g first last+ι (g first last)=0 := by
  have hc : ∀ j, j≠first → j≠last → g j last=0 := by
    intro j hj0 hjl
    have hr0 : j.rev≠first := by intro he; apply hjl; have hh := congrArg Fin.rev he; simpa [first,last] using hh
    have hrl : j.rev≠last := by intro he; apply hj0; have hh := congrArg Fin.rev he; simpa [first,last] using hh
    have hh := (vMiddle% unitary_reflected_column) ι hinv g hg hgu j.rev hr0 hrl
    simpa only [Fin.rev_rev,hz j.rev hr0 hrl,map_zero,neg_zero] using hh
  let z : F := g first last
  have he : g=(vCorner% corner) z := by
    apply SpecialLinearGroup.ext
    intro i j
    rw [vCorner% corner_entry]
    by_cases hij : i=j
    · subst j
      have hne : ¬(i=first ∧ i=last) := by
        rintro ⟨rfl,hh⟩
        have hval := congrArg Fin.val hh
        simp only [first,last,Fin.val_zero,Fin.val_last] at hval
        omega
      rw [if_neg hne,add_zero]
      exact sub_eq_zero.mp (hg.1 i i (by omega))
    · by_cases hi : i=first
      · subst i
        by_cases hj : j=last
        · subst j
          simp only [Matrix.one_apply,if_neg hij,zero_add,and_self,ite_true]
          rfl
        · rw [hz j (Ne.symm hij) hj]
          simp [Matrix.one_apply,hij,hj]
      · by_cases hj : j=last
        · subst j
          rw [hc i hi hij]
          simp [Matrix.one_apply,hij,hi]
        · rw [hg.2 i j hi hj]
          simp [hi]
  have hu : steinberg ι ((vCorner% corner) z : SpecialLinearGroup (Fin (k+6)) F)=(vCorner% corner) z := by rw [← he]; exact hgu
  have hh := congrArg (fun a : SpecialLinearGroup (Fin (k+6)) F => a first last) hu
  have hrev0 : (first:Fin (k+6)).rev=(last:Fin (k+6)) := by apply Fin.ext; simp [first,last]
  have hrevl : (last:Fin (k+6)).rev=(first:Fin (k+6)) := by apply Fin.ext; simp [first,last]
  have hcoord : ∀ t : F, ((vCorner% corner) t : SpecialLinearGroup (Fin (k+6)) F) first last=t := by
    intro t
    rw [vCorner% corner_entry]
    simp [Matrix.one_apply,first,last,Fin.ext_iff]
  rw [steinberg_entry,hrev0,hrevl,show (((vCorner% corner) z : SpecialLinearGroup (Fin (k+6)) F)⁻¹)=((vCorner% corner) (-z)) from (vCorner% corner_inv) z,hcoord,hcoord,map_neg] at hh
  refine ⟨he,?_⟩
  change z+ι z=0
  linear_combination -hh

/-- Full actual V* prescribed D Phi PRODUCT in four ordered batches. The four
correction tuples (one global tuple) precede EVERY target. Middle,
both exceptional root pairs and the noncommutative corner are truly
reconstructed from actual unitary witnesses. -/
theorem actual_unitary_radical_prescribed_four_batch [Fintype F] [DecidableEq F]
    {q : ℕ} (hq : 0<q) (hM : q*(2*q+1)<M)
    (ι : RingAut F) (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (hK : 2*(2*q+1)^q<Nat.card (fixedField ι))
    (a0 a1 a2 a3 : Fin M → Fin (k+6) → Fˣ)
    (c0 c1 c2 c3 : Fin M → (fixedField ι)ˣ)
    (ha0 : ∀ i j, ι (a0 i j:F)*(a0 i j.rev:F)=((c0 i:fixedField ι):F))
    (ha1 : ∀ i j, ι (a1 i j:F)*(a1 i j.rev:F)=((c1 i:fixedField ι):F))
    (ha2 : ∀ i j, ι (a2 i j:F)*(a2 i j.rev:F)=((c2 i:fixedField ι):F))
    (ha3 : ∀ i j, ι (a3 i j:F)*(a3 i j.rev:F)=((c3 i:fixedField ι):F))
    (phi0 phi1 phi2 phi3 : Fin M → RingAut F) (s0 s1 s2 s3 : Fin M → ℕ)
    (hs0 : ∀ j, 0<s0 j ∧ s0 j∣q) (hs1 : ∀ j, 0<s1 j ∧ s1 j∣q)
    (hs2 : ∀ j, 0<s2 j ∧ s2 j∣q) (hs3 : ∀ j, 0<s3 j ∧ s3 j∣q) :
    ∃ h0 h1 h2 h3 : Fin M → SpecialLinearGroup (Fin (k+6)) F,
      (∀ j i l, i≠l → h0 j i l=0 ∧ h1 j i l=0 ∧ h2 j i l=0 ∧ h3 j i l=0) ∧
      (∀ j, steinberg ι (h0 j)=h0 j ∧ steinberg ι (h1 j)=h1 j ∧
        steinberg ι (h2 j)=h2 j ∧ steinberg ι (h3 j)=h3 j) ∧
      ∀ b : SpecialLinearGroup (Fin (k+6)) F, InRadical b → steinberg ι b=b →
        ∃ x0 x1 x2 x3 : Fin M → SpecialLinearGroup (Fin (k+6)) F,
          (∀ j, (InRadical (x0 j) ∧ steinberg ι (x0 j)=x0 j) ∧
            (InRadical (x1 j) ∧ steinberg ι (x1 j)=x1 j) ∧
            (InRadical (x2 j) ∧ steinberg ι (x2 j)=x2 j) ∧
            (InRadical (x3 j) ∧ steinberg ι (x3 j)=x3 j)) ∧
          values h0 a0 phi0 s0 x0*values h1 a1 phi1 s1 x1*
            values h2 a2 phi2 s2 x2*values h3 a3 phi3 s3 x3=b := by
  classical
  have hc : Nat.card (fixedField ι)≤Fintype.card F := by
    simpa only [Nat.card_eq_fintype_card] using
      Nat.card_le_card_of_injective (fun x : fixedField ι => (x:F)) Subtype.val_injective
  have hF : 2*(2*q+1)^q<Fintype.card F := hK.trans_le hc
  have hFm : (q+1)^q<Fintype.card F := by
    have hp : (q+1)^q≤(2*q+1)^q := Nat.pow_le_pow_left (by omega) q
    have hp' : (2*q+1)^q≤2*(2*q+1)^q := by omega
    exact (hp.trans hp').trans_lt hF
  obtain ⟨h0,hd0,hh0,hcover0⟩ := actual_unitary_radical_prescribed_middle_product (k:=k+2) hq
    (by nlinarith) hFm ι hinv hne a0 c0 ha0 phi0 s0 hs0
  obtain ⟨h1,hd1,hh1,hcover1⟩ := actual_unitary_radical_boundary_prescribed_product (k:=k) hq
    hM hF ι hinv hne false a1 c1 ha1 phi1 s1 hs1
  obtain ⟨h2,hd2,hh2,hcover2⟩ := actual_unitary_radical_boundary_prescribed_product (k:=k) hq
    hM hF ι hinv hne true a2 c2 ha2 phi2 s2 hs2
  obtain ⟨h3,hd3,hh3,hcover3⟩ := actual_unitary_radical_corner_prescribed_product (k:=k+2)
    hq hM ι hinv hne hK a3 c3 ha3 phi3 s3 hs3
  refine ⟨h0,h1,h2,h3,fun j i l hil => ⟨hd0 j i l hil,hd1 j i l hil,hd2 j i l hil,hd3 j i l hil⟩,fun j => ⟨hh0 j,hh1 j,hh2 j,hh3 j⟩,?_⟩
  intro b hb hbu
  obtain ⟨x0,hx0,hP0,hP0u,hmatch0⟩ := hcover0 b hb hbu
  let P0 := values h0 a0 phi0 s0 x0
  let R0 := P0⁻¹*b
  obtain ⟨hR0,hR0u,hzero0⟩ := actual_unitary_middle_residual ι hinv P0 b hP0 hP0u hb hbu hmatch0
  obtain ⟨x1,hx1,hP1,hP1u,hmatch1⟩ := hcover1 R0 hR0 hR0u
  let P1 := values h1 a1 phi1 s1 x1
  let R1 := P1⁻¹*R0
  have hP1u' : steinberg ι P1=P1 := hP1u
  have hmatch1' : ∀ j, j≠first → j≠last → P1 first j=if j=axis false then R0 first j else 0 := hmatch1
  have hR1 : InRadical R1 := actual_radical_product_mem _ _ (actual_radical_inverse_mem _ hP1) hR0
  have hR1u : steinberg ι R1=R1 := by change steinberg ι (P1⁻¹*R0)=_; rw [map_mul,map_inv,hP1u',hR0u]
  obtain ⟨x2,hx2,hP2,hP2u,hmatch2⟩ := hcover2 R1 hR1 hR1u
  let P2 := values h2 a2 phi2 s2 x2
  let R2 := P2⁻¹*R1
  have hP2u' : steinberg ι P2=P2 := hP2u
  have hmatch2' : ∀ j, j≠first → j≠last → P2 first j=if j=axis true then R1 first j else 0 := hmatch2
  have hR2 : InRadical R2 := actual_radical_product_mem _ _ (actual_radical_inverse_mem _ hP2) hR1
  have hR2u : steinberg ι R2=R2 := by change steinberg ι (P2⁻¹*R1)=_; rw [map_mul,map_inv,hP2u',hR1u]
  have hzero : ∀ j : Fin (k+6), j≠first → j≠last → R2 first j=0 := by
    intro j hj0 hjl
    rw [residual_row P2 R1 hP2 hR1 j hj0 hjl,hmatch2' j hj0 hjl]
    by_cases he2 : j=axis true
    · simp only [if_pos he2]; ring
    · simp only [if_neg he2,neg_zero,zero_add]
      rw [residual_row P1 R0 hP1 hR0 j hj0 hjl,hmatch1' j hj0 hjl]
      by_cases he1 : j=axis false
      · simp only [if_pos he1]; ring
      · simp only [if_neg he1,neg_zero,zero_add]
        have hjm : Middle (k:=k+2) j := by
          have hn := j.isLt
          have h0 : j.val≠0 := fun h => hj0 (Fin.ext h)
          have hl : j.val≠k+5 := fun h => hjl (Fin.ext h)
          have h1 : j.val≠1 := fun h => he1 (Fin.ext h)
          have h2 : j.val≠k+4 := fun h => he2 (Fin.ext h)
          constructor <;> omega
        exact (hzero0 j hjm).1
  obtain ⟨heR2,htrace⟩ := zero_rows_corner ι hinv R2 hR2 hR2u hzero
  obtain ⟨x3,hx3,he3⟩ := hcover3 (R2 first last) htrace
  refine ⟨x0,x1,x2,x3,fun j => ⟨hx0 j,hx1 j,hx2 j,hx3 j⟩,?_⟩
  have hh3 : values h3 a3 phi3 s3 x3=R2 := he3.trans heR2.symm
  change P0*P1*P2*values h3 a3 phi3 s3 x3=b
  rw [hh3]
  dsimp only [R2,R1,R0]
  group

/-- Chosen positive length/cutoff BEFORE ALL fields/ranks/diagonal-SIMILITUDE/field tuples.
ONE actual SU inner correction precedes every FULL radical target;
ordered exact-length commutator VALUES, actual V* witnesses and every
original positive divisor power are retained. Whole SU/bare classification are further obligations. -/
theorem actual_uniform_unitary_radical_prescribed_product (q : ℕ) (hq : 0<q) :
    ∃ N C : ℕ, 0<N ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C<Fintype.card F → ∀ (ι : RingAut F), Function.Involutive ι → ι≠RingEquiv.refl F →
      ∀ k : ℕ, ∀ (a : Fin N → Fin (k+6) → Fˣ) (c : Fin N → (fixedField ι)ˣ),
      (∀ i j, ι (a i j:F)*(a i j.rev:F)=((c i:fixedField ι):F)) →
      ∀ (phi : Fin N → RingAut F) (s : Fin N → ℕ),
      (∀ j, 0<s j ∧ s j∣q) →
      ∃ h : Fin N → SpecialLinearGroup (Fin (k+6)) F,
        (∀ j i l, i≠l → h j i l=0) ∧ (∀ j, steinberg ι (h j)=h j) ∧
        ∀ b : SpecialLinearGroup (Fin (k+6)) F, InRadical b → steinberg ι b=b →
          ∃ x : Fin N → SpecialLinearGroup (Fin (k+6)) F,
            (∀ j, InRadical (x j) ∧ steinberg ι (x j)=x j) ∧
            orderedProduct (fun j => (x j)⁻¹*
              ((MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false)^(s j)) (x j))=b := by
  classical
  let M := q*(2*q+1)+1
  let K := 2*(2*q+1)^q
  refine ⟨M+M+M+M,K^2,by dsimp only [M]; omega,?_⟩
  intro F _ _ _ hF ι hinv hne k a c ha phi s hs
  have hK : K<Nat.card (fixedField ι) := by
    have hc := card_field ι hinv hne
    have hl : K^2<Nat.card F := by simpa only [Nat.card_eq_fintype_card] using hF
    rw [hc] at hl
    nlinarith
  let i0 := fun j : Fin M => ((j.castAdd M).castAdd M).castAdd M
  let i1 := fun j : Fin M => ((j.natAdd M).castAdd M).castAdd M
  let i2 := fun j : Fin M => (j.natAdd (M+M)).castAdd M
  let i3 := fun j : Fin M => j.natAdd (M+M+M)
  obtain ⟨h0,h1,h2,h3,hd,hh,hcover⟩ := actual_unitary_radical_prescribed_four_batch (k:=k) hq
    (by dsimp only [M]; omega) ι hinv hne hK
    (fun j => a (i0 j)) (fun j => a (i1 j)) (fun j => a (i2 j)) (fun j => a (i3 j))
    (fun j => c (i0 j)) (fun j => c (i1 j)) (fun j => c (i2 j)) (fun j => c (i3 j))
    (fun i j => ha _ _) (fun i j => ha _ _) (fun i j => ha _ _) (fun i j => ha _ _)
    (fun j => phi (i0 j)) (fun j => phi (i1 j)) (fun j => phi (i2 j)) (fun j => phi (i3 j))
    (fun j => s (i0 j)) (fun j => s (i1 j)) (fun j => s (i2 j)) (fun j => s (i3 j))
    (fun j => hs _) (fun j => hs _) (fun j => hs _) (fun j => hs _)
  let h := Fin.append (Fin.append (Fin.append h0 h1) h2) h3
  have hhu : ∀ j, steinberg ι (h j)=h j := by
    intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simpa only [h,Fin.append_left] using (hh j).1
        · simpa only [h,Fin.append_left,Fin.append_right] using (hh j).2.1
      · simpa only [h,Fin.append_left,Fin.append_right] using (hh j).2.2.1
    · simpa only [h,Fin.append_right] using (hh j).2.2.2
  have hdiagonal : ∀ j i l, i≠l → h j i l=0 := by
    intro j i l hil
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simpa only [h,Fin.append_left] using (hd j i l hil).1
        · simpa only [h,Fin.append_left,Fin.append_right] using (hd j i l hil).2.1
      · simpa only [h,Fin.append_left,Fin.append_right] using (hd j i l hil).2.2.1
    · simpa only [h,Fin.append_right] using (hd j i l hil).2.2.2
  refine ⟨h,hdiagonal,hhu,?_⟩
  intro b hb hbu
  obtain ⟨x0,x1,x2,x3,hx,he⟩ := hcover b hb hbu
  let x := Fin.append (Fin.append (Fin.append x0 x1) x2) x3
  refine ⟨x,?_,?_⟩
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simpa only [x,Fin.append_left] using (hx j).1
        · simpa only [x,Fin.append_left,Fin.append_right] using (hx j).2.1
      · simpa only [x,Fin.append_left,Fin.append_right] using (hx j).2.2.1
    · simpa only [x,Fin.append_right] using (hx j).2.2.2
  · let v0 := fun j => (x0 j)⁻¹*((MulAut.conj (h0 j)*PartIIProposition6_5.diagonalFieldGraph (a (i0 j)) (phi (i0 j)) false)^(s (i0 j))) (x0 j)
    let v1 := fun j => (x1 j)⁻¹*((MulAut.conj (h1 j)*PartIIProposition6_5.diagonalFieldGraph (a (i1 j)) (phi (i1 j)) false)^(s (i1 j))) (x1 j)
    let v2 := fun j => (x2 j)⁻¹*((MulAut.conj (h2 j)*PartIIProposition6_5.diagonalFieldGraph (a (i2 j)) (phi (i2 j)) false)^(s (i2 j))) (x2 j)
    let v3 := fun j => (x3 j)⁻¹*((MulAut.conj (h3 j)*PartIIProposition6_5.diagonalFieldGraph (a (i3 j)) (phi (i3 j)) false)^(s (i3 j))) (x3 j)
    have hv : (fun j => (x j)⁻¹*((MulAut.conj (h j)*PartIIProposition6_5.diagonalFieldGraph (a j) (phi j) false)^(s j)) (x j))=
        Fin.append (Fin.append (Fin.append v0 v1) v2) v3 := by
      funext j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
          · simp only [x,h,Fin.append_left,v0,i0]
          · simp only [x,h,Fin.append_left,Fin.append_right,v1,i1]
        · simp only [x,h,Fin.append_left,Fin.append_right,v2,i2]
      · simp only [x,h,Fin.append_right,v3,i3]
    rw [hv]
    simpa only [values,orderedProduct,List.ofFn_fin_append,List.prod_append] using he
end NikolovSegal.PartIIUnitaryRadicalPrescribedProduct
