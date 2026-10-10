/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnBareSmallFieldValues
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISLnBareSmallFieldValues
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIIPSLnFixedPowerClass
import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnSmallFullGroup
import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIPSLnLargeFieldProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
/-! Original PartII Section5, actual type-A branch with 2<|F|<=K.
Bare FULL-GROUP classifications, determinant-one normalization, fixed
long-cycle qth powers and their class-size counts are proved inputs.
The output is the genuine original q/e VALUE range, with correction
before every witness. Uniform conjugacy-class width remains unproved. -/
namespace NikolovSegal.PartIISLnBareSmallFieldValues
open Matrix PartIIOuterSLnAction PartIIFixedSLnPower
universe u
variable {F : Type u} [Field F] [Fintype F]

/-- The actual finite-outer consumer for arbitrary bare SLn actions in
the stated field/rank branch, with no normal-form/fixed-root premise. -/
theorem actual_bare_SLn_small_field_values
    (q : ℕ) (hq : 0 < q) (r k K R : ℕ) (hp : k+2≤q*r)
    (h2 : 2<Fintype.card F) (hF : Fintype.card F≤K)
    (beta : Fin (R*(K^2*(K^K*2))) → MulAut (SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F))
    (e : Fin (R*(K^2*(K^K*2))) → ℕ) (he : ∀ i, 0<e i ∧ e i∣q) :
    Nat.card (SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F)≤
      (Nat.card (ConjClasses.mk ((fixedElement (F:=F) (q*r) k)^q)).carrier)^8 ∧
    ∃ y : Fin (R*(K^2*(K^K*2))) → SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
      ∀ g : Fin R → SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
        ∃ c : Fin (R*(K^2*(K^K*2))) → SpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
          orderedProduct (fun i => (c i)⁻¹*((beta i*MulAut.conj (y i)⁻¹)^(q/e i)) (c i))=
          orderedProduct (fun i => (g i)⁻¹*(fixedElement (q*r) k)^q*(g i)*((fixedElement (q*r) k)^q)⁻¹) := by
  classical
  letI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  choose c a phi eps hc using fun i =>
    SLnSmallField.sl_bare_full_group_diagonal_field_graph (ringChar F) (by omega) h2 (beta i)
  choose h b hb using fun i => actual_DFG_finite_outer_normalization (a i) (phi i) (eps i)
  have hnormal : ∀ i, beta i=MulAut.conj ((c i)⁻¹*h i)*(b i : MulAut _) := by
    intro i
    have hd : MulAut.conj (c i)*beta i=PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i) :=
      MulEquiv.ext (hc i)
    have hn := hb i
    rw [← hd] at hn
    calc
      _ = (MulAut.conj (c i))⁻¹*(MulAut.conj (c i)*beta i) := by group
      _ = (MulAut.conj (c i))⁻¹*(MulAut.conj (h i)*(b i : MulAut _)) := by rw [hn]
      _ = _ := by rw [map_mul,map_inv,mul_assoc]
  refine ⟨actual_q_power_large_class q r k hp,?_⟩
  apply PartIIOuterBlockConstruction.actual_finite_outer_original_power_values
    (finiteOuter (F:=F) (k+4*(q*r+1))) (fixedElement (q*r) k) _ q hq R
      (K^2*(K^K*2)) (actual_finite_outer_small_field_card _ K hF)
      beta (fun i => (c i)⁻¹*h i) b hnormal e he
  intro t
  obtain ⟨a,phi,eps,ht⟩ := t.prop
  rw [ht]
  exact actual_fixed_element (q*r) k a phi eps

private abbrev proj {n : ℕ} := PartIIPSLnLargeFieldProduct.projectiveAction (F:=F) (n:=n)
private abbrev pi {n : ℕ} : SpecialLinearGroup (Fin n) F →* ProjectiveSpecialLinearGroup (Fin n) F :=
  QuotientGroup.mk' (Subgroup.center _)
private theorem proj_mul {n : ℕ} (a b : MulAut (SpecialLinearGroup (Fin n) F)) : proj (a*b)=proj a*proj b := by
  apply MulEquiv.ext;intro x
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (SpecialLinearGroup (Fin n) F)) x
  rfl
private theorem proj_one {n : ℕ} : proj (1:MulAut (SpecialLinearGroup (Fin n) F))=1 := by
  apply MulEquiv.ext;intro x
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (SpecialLinearGroup (Fin n) F)) x
  rfl
private def projHom {n : ℕ} : MulAut (SpecialLinearGroup (Fin n) F) →* MulAut (ProjectiveSpecialLinearGroup (Fin n) F) where
  toFun := proj
  map_one' := proj_one
  map_mul' := proj_mul
private theorem proj_conj {n : ℕ} (g : SpecialLinearGroup (Fin n) F) : proj (MulAut.conj g)=MulAut.conj (pi g) := by
  apply MulEquiv.ext;intro x
  obtain ⟨t,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (SpecialLinearGroup (Fin n) F)) x
  change pi (g*t*g⁻¹)=pi g*pi t*(pi g)⁻¹
  simp only [map_mul,map_inv]
private def imageOuter (s : ℕ) : Subgroup (MulAut (ProjectiveSpecialLinearGroup (Fin (s+2)) F)) :=
  (finiteOuter (F:=F) s).map projHom
private def outerMap (s : ℕ) : finiteOuter (F:=F) s → imageOuter (F:=F) s :=
  fun b => ⟨proj b.val,Subgroup.mem_map.mpr ⟨b.val,b.prop,rfl⟩⟩
private theorem outerMap_surj (s : ℕ) : Function.Surjective (outerMap (F:=F) s) := by
  intro b
  obtain ⟨a,ha,he⟩ := Subgroup.mem_map.mp b.prop
  exact ⟨⟨a,ha⟩,Subtype.ext he⟩
private noncomputable instance outerImageFintype (s : ℕ) : Fintype (imageOuter (F:=F) s) := by
  classical
  exact Fintype.ofSurjective (outerMap s) (outerMap_surj s)
private theorem outerImage_card (s K : ℕ) (hF : Fintype.card F≤K) :
    Fintype.card (imageOuter (F:=F) s)≤K^2*(K^K*2) :=
  (Fintype.card_le_of_surjective (outerMap s) (outerMap_surj s)).trans (actual_finite_outer_small_field_card s K hF)

/-- Intrinsic PSLn counterpart: the finite outer image is constructed;
the bare automorphisms and their inner corrections are never lifted. -/
theorem actual_bare_PSLn_small_field_values
    (q : ℕ) (hq : 0 < q) (r k K R : ℕ) (hp : k+2≤q*r)
    (h2 : 2<Fintype.card F) (hF : Fintype.card F≤K)
    (beta : Fin (R*(K^2*(K^K*2))) → MulAut (ProjectiveSpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F))
    (e : Fin (R*(K^2*(K^K*2))) → ℕ) (he : ∀ i, 0<e i ∧ e i∣q) :
    Nat.card (ProjectiveSpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F)≤
      (Nat.card (ConjClasses.mk (pi ((fixedElement (F:=F) (q*r) k)^q))).carrier)^16 ∧
    ∃ y : Fin (R*(K^2*(K^K*2))) → ProjectiveSpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
      ∀ g : Fin R → ProjectiveSpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
        ∃ c : Fin (R*(K^2*(K^K*2))) → ProjectiveSpecialLinearGroup (Fin (k+4*(q*r+1)+2)) F,
          orderedProduct (fun i => (c i)⁻¹*((beta i*MulAut.conj (y i)⁻¹)^(q/e i)) (c i))=
          orderedProduct (fun i => (g i)⁻¹*(pi (fixedElement (q*r) k))^q*(g i)*((pi (fixedElement (q*r) k))^q)⁻¹) := by
  classical
  letI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  choose c a phi eps hc using fun i =>
    PSLnSmallField.psl_bare_full_group_diagonal_field_graph (ringChar F) (by omega) h2 (beta i)
  choose h b hb using fun i => actual_DFG_finite_outer_normalization (a i) (phi i) (eps i)
  have hnormal : ∀ i, beta i=MulAut.conj ((c i)⁻¹*pi (h i))*((outerMap _ (b i)) : MulAut _) := by
    intro i
    have hd : MulAut.conj (c i)*beta i=proj (PartIIProposition6_5.diagonalFieldGraph (a i) (phi i) (eps i)) := by
      apply MulEquiv.ext;intro x
      obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center _) x
      exact hc i g
    rw [hb i,proj_mul,proj_conj] at hd
    calc
      _ = (MulAut.conj (c i))⁻¹*(MulAut.conj (c i)*beta i) := by group
      _ = (MulAut.conj (c i))⁻¹*(MulAut.conj (pi (h i))*proj (b i).val) := by rw [hd]
      _ = _ := by rw [map_mul,map_inv,mul_assoc];rfl
  refine ⟨PartIIPSLnFixedPowerClass.actual_projective_q_power_large_class q r k hp,?_⟩
  apply PartIIOuterBlockConstruction.actual_finite_outer_original_power_values
    (imageOuter (F:=F) (k+4*(q*r+1))) (pi (fixedElement (q*r) k)) _ q hq R
      (K^2*(K^K*2)) (outerImage_card _ K hF)
      beta (fun i => (c i)⁻¹*pi (h i)) (fun i => outerMap _ (b i)) hnormal e he
  intro t
  obtain ⟨b,ht⟩ := outerMap_surj _ t
  rw [← ht]
  change pi ((b.val) (fixedElement (q*r) k))=pi (fixedElement (q*r) k)
  obtain ⟨a,phi,eps,hb⟩ := b.prop
  rw [hb,actual_fixed_element]
end NikolovSegal.PartIISLnBareSmallFieldValues
