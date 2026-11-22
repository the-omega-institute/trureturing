/- GID: D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralGenerators
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralGenerators
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quotient algebra and low quadratic generators of the neutral image. -/

import D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2NeutralMonomials
import D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2Projection
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.ActualFixedC2

open LatticeGeneratingFieldLocality LatticeInvolution LatticeAllStateField
open LatticeAllStateReconstruction LatticeActualStateFieldCalculus
open LatticeSugawaraCurrents MvPolynomial
open scoped VertexOperator

open private higher_fixed_product_mem fixed_product_comm_mem even_cons_cons
  fixedWordLength from D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2NeutralMonomials

noncomputable section

local instance neutralGeneratorsFixedCarrierGroup (D : LatticeData) : AddCommGroup (FixedCarrier D) :=
  (fixedSpace D).addCommGroup

/-- The intrinsic C₂ quotient of the actual fixed states. -/
abbrev FixedC2Quotient (D : LatticeData) := FixedCarrier D ⧸ fixedC2 D

private theorem quotient_product_comm (D : LatticeData) (x y : FixedC2Quotient D) :
    fixedQuotientProduct D x y = fixedQuotientProduct D y x := by
  obtain ⟨u, rfl⟩ := (fixedC2 D).mkQ_surjective x
  obtain ⟨v, rfl⟩ := (fixedC2 D).mkQ_surjective y
  simp only [fixed_quotient_product_mk]
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (Submodule.Quotient.mk_eq_zero (fixedC2 D)).mpr (fixed_product_comm_mem D u v)

private theorem quotient_product_assoc (D : LatticeData) (x y z : FixedC2Quotient D) :
    fixedQuotientProduct D (fixedQuotientProduct D x y) z =
      fixedQuotientProduct D x (fixedQuotientProduct D y z) := by
  obtain ⟨u, rfl⟩ := (fixedC2 D).mkQ_surjective x
  obtain ⟨v, rfl⟩ := (fixedC2 D).mkQ_surjective y
  obtain ⟨w, rfl⟩ := (fixedC2 D).mkQ_surjective z
  let left (j : ℕ) := fixedMode D u (-1 - (j : ℤ)) (fixedMode D v (-1 + (j : ℤ)) w)
  let right (j : ℕ) := fixedMode D v (-2 - (j : ℤ)) (fixedMode D u j w)
  have it := stateField_iterate D u.val v.val w.val (-1) (-1)
  dsimp only at it
  simp_rw [show ∀ j : ℕ, (-1 : ℂ)^j * ((Ring.choose (-1) j : ℤ) : ℂ) = 1
    from minus_one_binomial, one_smul, show (-1 : ℤ) + -1 = -2 by norm_num] at it
  change Function.HasFiniteSupport (fun j => (left j).val) ∧
      Function.HasFiniteSupport (fun j => (right j).val) ∧ _ at it
  have support (f : ℕ → FixedCarrier D) (h : Function.HasFiniteSupport (fun j => (f j).val)) :
      Function.HasFiniteSupport f := h.subset (fun j hj hv => hj (Subtype.ext hv))
  have hl := support left it.1
  have hr := support right it.2.1
  have eq : fixedMode D (fixedMode D u (-1) v) (-1) w =
      (∑ᶠ j, left j) - ((-1 : ℂ)^(-1 : ℤ)) • (∑ᶠ j, right j) := by
    apply Subtype.ext
    change _ = (fixedSpace D).subtype
      ((∑ᶠ j, left j) - ((-1 : ℂ)^(-1 : ℤ)) • (∑ᶠ j, right j))
    rw [map_sub, map_smul, map_finsum _ hl, map_finsum _ hr]
    exact it.2.2
  have ql : (fixedC2 D).mkQ (∑ᶠ j, left j) = (fixedC2 D).mkQ (left 0) := by
    rw [map_finsum _ hl, finsum_eq_single _ 0]
    intro j hj
    apply (Submodule.Quotient.mk_eq_zero (fixedC2 D)).mpr
    simpa only [left, show -1 - (j : ℤ) = -(((j - 1 : ℕ) : ℤ) + 2) by omega]
      using higher_fixed_product_mem D (j - 1) u (fixedMode D v (-1 + (j : ℤ)) w)
  have qr : (fixedC2 D).mkQ (∑ᶠ j, right j) = 0 := by
    rw [map_finsum _ hr]
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    apply (Submodule.Quotient.mk_eq_zero (fixedC2 D)).mpr
    simpa only [right, show -2 - (j : ℤ) = -((j : ℤ) + 2) by omega]
      using higher_fixed_product_mem D j v (fixedMode D u j w)
  simp only [fixed_quotient_product_mk, eq, map_sub, map_smul, ql, qr, smul_zero, sub_zero]
  simp [left]

private theorem quotient_vacuum_product (D : LatticeData) (x : FixedC2Quotient D) :
    fixedQuotientProduct D ((fixedC2 D).mkQ (fixedVacuum D)) x = x := by
  obtain ⟨v, rfl⟩ := (fixedC2 D).mkQ_surjective x
  rw [fixed_quotient_product_mk]
  congr 1
  apply Subtype.ext
  change ((Y D (vacuum D))[[-1]]) v.val = v.val
  simp [stateField_vacuum, identity_modes]

/-- The existing quotient with the actual (-1) product and vacuum unit. -/
@[instance_reducible]
def fixedQuotientRing (D : LatticeData) : CommRing (FixedC2Quotient D) where
  __ := (inferInstance : AddCommGroup (FixedC2Quotient D))
  mul := fun x y => fixedQuotientProduct D x y
  one := (fixedC2 D).mkQ (fixedVacuum D)
  mul_assoc := quotient_product_assoc D
  mul_comm := quotient_product_comm D
  one_mul := quotient_vacuum_product D
  mul_one x := (quotient_product_comm D x _).trans (quotient_vacuum_product D x)
  left_distrib x y z := (fixedQuotientProduct D x).map_add y z
  right_distrib x y z := congrArg (fun f : FixedC2Quotient D →ₗ[ℂ] FixedC2Quotient D => f z)
    ((fixedQuotientProduct D).map_add x y)
  zero_mul x := congrArg (fun f : FixedC2Quotient D →ₗ[ℂ] FixedC2Quotient D => f x)
    (map_zero (fixedQuotientProduct D))
  mul_zero x := map_zero (fixedQuotientProduct D x)

/-- The complex algebra structure preserves the quotient's existing scalar action. -/
@[instance_reducible]
def fixedQuotientAlgebra (D : LatticeData) :
    letI := fixedQuotientRing D
    Algebra ℂ (FixedC2Quotient D) := by
  letI := fixedQuotientRing D
  apply Algebra.ofModule
  · intro c x y
    exact congrArg (fun f : FixedC2Quotient D →ₗ[ℂ] FixedC2Quotient D => f y)
      ((fixedQuotientProduct D).map_smul c x)
  · intro c x y
    exact (fixedQuotientProduct D x).map_smul c y

attribute [local instance] fixedQuotientRing fixedQuotientAlgebra

/-- The products of representatives in the actual fixed quotient. -/
theorem fixed_quotient_mul_mk (D : LatticeData) (u v : FixedCarrier D) :
    (fixedC2 D).mkQ u * (fixedC2 D).mkQ v = (fixedC2 D).mkQ (fixedMode D u (-1) v) := rfl

/-- Translation normalizes the first index to zero, leaving seven possible totals. -/
def lowNeutralQuadratic (D : LatticeData) (p : Fin D.rank × Fin D.rank × Fin 7) :
    FixedC2Quotient D :=
  pairClass D p.1 p.2.1 0 p.2.2

/-- The linear image of the even vacuum-charge oscillator words. -/
def neutralImage (D : LatticeData) : Submodule ℂ (FixedC2Quotient D) :=
  Submodule.span ℂ {q | ∃ (w : List (Index D)) (hw : Even w.length),
    q = neutralWordClass D w hw}


/-- Fixed states supported in the vacuum charge alone. -/
def fixedNeutralSpace (D : LatticeData) : Submodule ℂ (FixedCarrier D) :=
  (LinearMap.range (Finsupp.lsingle (R := ℂ) (0 : Charge D) :
    Oscillator D →ₗ[ℂ] Carrier D)).comap (fixedSpace D).subtype

/-- The even words span the image of the literal fixed vacuum-charge sector. -/
theorem neutral_image_eq_fixed_neutral_image (D : LatticeData) :
    neutralImage D = (fixedNeutralSpace D).map (fixedC2 D).mkQ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨fixedNeutralWord D w hw, ⟨neutralPolynomial D w, rfl⟩, rfl⟩
  · rintro q ⟨v, ⟨p, hp⟩, rfl⟩
    rw [← plusProjection_fixed D v]
    change Finsupp.single 0 p = v.val at hp
    rw [← hp]
    clear hp v
    let f : Oscillator D →ₗ[ℂ] FixedC2Quotient D :=
      (fixedC2 D).mkQ.comp ((plusProjection D).comp (Finsupp.lsingle 0))
    change f p ∈ neutralImage D
    induction p using MvPolynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact (neutralImage D).add_mem hp hq
    | monomial e c =>
      have hc : monomial e c = c • (monomial e 1 : Oscillator D) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [hc, map_smul]
      apply (neutralImage D).smul_mem
      rcases Nat.even_or_odd (occurrences D e).length with hw | hw
      · let v := fixedNeutralWord D (occurrences D e) hw
        have he : neutralPolynomial D (occurrences D e) = monomial e 1 :=
          occurrences_product D e
        change (fixedC2 D).mkQ
          (plusProjection D (Finsupp.single 0 (monomial e 1))) ∈ neutralImage D
        rw [← he, show Finsupp.single 0 (neutralPolynomial D (occurrences D e)) =
          v.val from rfl, plusProjection_fixed]
        exact Submodule.subset_span ⟨occurrences D e, hw, rfl⟩
      · have hodd : theta D (Finsupp.single (0 : Charge D) (monomial e 1)) =
            -Finsupp.single (0 : Charge D) (monomial e 1 : Oscillator D) := by
          change thetaLinear D (Finsupp.single 0 (monomial e 1)) = _
          rw [theta_single, neg_zero, sigma_monomial, hw.neg_one_pow, neg_one_smul,
            Finsupp.single_neg]
        change (fixedC2 D).mkQ
          (plusProjection D (Finsupp.single 0 (monomial e 1))) ∈ neutralImage D
        rw [plusProjection_odd D _ hodd, map_zero]
        exact (neutralImage D).zero_mem

private theorem neutral_class_length_le (D : LatticeData) (n : ℕ) (hn : Even n)
    (S : Submodule ℂ (FixedC2Quotient D))
    (h : ∀ (w : List (Index D)) (hw : w.length = n),
      neutralWordClass D w (hw.symm ▸ hn) ∈ S) :
    neutralClassLength D n hn ≤ S := by
  rw [neutralClassLength, fixedWordLength, Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  exact h w hw

private theorem neutral_word_nil (D : LatticeData) :
    neutralWordClass D [] (by simp) = (1 : FixedC2Quotient D) := by
  apply congrArg (fixedC2 D).mkQ
  apply Subtype.ext
  rfl

private theorem pair_mem_adjoin (D : LatticeData) (hD : ∀ i : Fin D.rank, D.G i i ≠ 0)
    (x y : Index D) :
    pairClass D x.1 y.1 x.2 y.2 ∈ Algebra.adjoin ℂ (Set.range (lowNeutralQuadratic D)) := by
  by_cases h : 7 ≤ x.2 + y.2
  · rw [neutral_pair_class_high D _ _ _ _ (hD _) h]
    exact Subalgebra.zero_mem _
  · rw [pair_class_normalize]
    apply Subalgebra.smul_mem
    exact Algebra.subset_adjoin ⟨(x.1, y.1, ⟨x.2 + y.2, by omega⟩), rfl⟩

/-- Strip the first two oscillators. The contraction terms are covered by
the induction hypothesis at the length of the tail. -/
theorem neutral_word_mem_low_adjoin (D : LatticeData) (hD : ∀ i : Fin D.rank, D.G i i ≠ 0)
    (w : List (Index D)) (hw : Even w.length) :
    neutralWordClass D w hw ∈ Algebra.adjoin ℂ (Set.range (lowNeutralQuadratic D)) := by
  let A := Algebra.adjoin ℂ (Set.range (lowNeutralQuadratic D))
  suffices h : ∀ n (w : List (Index D)), w.length = n → ∀ hw : Even w.length,
      neutralWordClass D w hw ∈ A from h w.length w rfl hw
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rintro (_ | ⟨x, _ | ⟨y, w⟩⟩) rfl hw
    · rw [neutral_word_nil]
      exact A.one_mem
    · exact (Nat.not_even_one hw).elim
    · have ht : Even w.length := by
        change Even (w.length + 2) at hw
        exact (Nat.even_add.mp hw).mpr (by decide : Even (2 : ℕ))
      have hp : pairClass D x.1 y.1 x.2 y.2 * neutralWordClass D w ht ∈ A :=
        A.mul_mem (pair_mem_adjoin D hD x y) (ih _ (by simp) w rfl ht)
      have hc : neutralClassLength D w.length ht ≤ A.toSubmodule :=
        neutral_class_length_le D _ ht _ (fun v hv => ih _ (by simp) v hv _)
      have hd := hc (fixed_quadratic_word_length D x y w ht)
      change pairClass D x.1 y.1 x.2 y.2 * neutralWordClass D w ht -
        neutralWordClass D (x :: y :: w) hw ∈ A at hd
      simpa only [sub_sub_cancel] using A.sub_mem hp hd

private theorem pair_mul_neutral_image (D : LatticeData) (x y : Index D)
    (q : FixedC2Quotient D) (hq : q ∈ neutralImage D) :
    pairClass D x.1 y.1 x.2 y.2 * q ∈ neutralImage D := by
  change q ∈ (neutralImage D).comap (fixedQuotientProduct D (pairClass D x.1 y.1 x.2 y.2))
  refine (Submodule.span_le.mpr ?_) hq
  rintro _ ⟨w, hw, rfl⟩
  have hlead : neutralWordClass D (x :: y :: w) (even_cons_cons D x y w hw) ∈ neutralImage D :=
    Submodule.subset_span ⟨x :: y :: w, _, rfl⟩
  have hc : neutralClassLength D w.length hw ≤ neutralImage D :=
    neutral_class_length_le D _ hw _ (fun v hv => Submodule.subset_span ⟨v, hv.symm ▸ hw, rfl⟩)
  change fixedQuotientProduct D (pairClass D x.1 y.1 x.2 y.2)
    (neutralWordClass D w hw) ∈ neutralImage D
  simpa only [sub_add_cancel] using
    (neutralImage D).add_mem (hc (fixed_quadratic_word_length D x y w hw)) hlead

/-- The entire linear image of the even vacuum-charge words is exactly the
subalgebra generated by the low-index quadratic classes. -/
theorem neutral_image_eq_low_adjoin (D : LatticeData) (hD : ∀ i : Fin D.rank, D.G i i ≠ 0) :
    neutralImage D = (Algebra.adjoin ℂ (Set.range (lowNeutralQuadratic D))).toSubmodule := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    exact neutral_word_mem_low_adjoin D hD w hw
  · apply (Algebra.adjoin_toSubmodule_le ℂ).mpr
    intro q hq
    induction hq using Submonoid.closure_induction_left with
    | one =>
      rw [← neutral_word_nil]
      exact Submodule.subset_span ⟨[], by simp, rfl⟩
    | mul_left r hr q _ ih =>
      obtain ⟨⟨i, j, s⟩, rfl⟩ := hr
      exact pair_mul_neutral_image D (i, 0) (j, s) q ih

open ActualLeechHyperbolic (leechData leech_spec)

/-- Finite algebra generation for the neutral image of the actual Leech fixed VOA. -/
theorem leech_neutral_image_eq_low_adjoin :
    (fixedNeutralSpace leechData).map (fixedC2 leechData).mkQ =
      (Algebra.adjoin ℂ (Set.range (lowNeutralQuadratic leechData))).toSubmodule :=
  (neutral_image_eq_fixed_neutral_image leechData).symm.trans
    (neutral_image_eq_low_adjoin leechData (gram_diagonal_ne leechData leech_spec.2.2.1))

end
end D5.S3.VertexAlgebra.Lattice.ActualFixedC2

#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixedQuotientAlgebra
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.neutral_image_eq_low_adjoin
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.leech_neutral_image_eq_low_adjoin
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.neutral_image_eq_fixed_neutral_image
