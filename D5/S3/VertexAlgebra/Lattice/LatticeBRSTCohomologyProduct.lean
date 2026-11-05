/- GID: D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyProduct
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyProduct
   mirror-E: none(waiver:algebraic-original-brst-product)
   anchors: []
   utility: none
   digest: The actual original critical BRST cohomology has constant fields and an associative mixed-parity product. -/

/-
SOURCE-ONLY / UNCOMPILED candidate. No kernel or native acceptance is claimed.

This consumes the fixed original BRST quotient, without changing its carrier,
boundary submodule, charge, fields, translation, vacuum, or parity. The three
cohomology supplier files remain source-only/uncompiled. The separate vacuum
non-exactness supplier is not a hypothesis of any result below and is not
reproved here. Its own acceptance remains pending.

Original suppliers retain their attribution: Bakalov--Kac for the lattice
construction, Scott Carnahan / vertexAlg for the residue and coefficient
calculus, Kalle Kytölä / VirasoroProject for the Sugawara architecture,
and the original ghost and Mathlib authors in their source files.
The unrestricted signed iterate supplier is native-compiled but not frozen.
No full tensor Borcherds or quotient Borcherds candidate is imported.
-/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyLaws
import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateFieldIterate

/-! The actual critical BRST quotient has its original associative -1 product. -/

set_option autoImplicit false

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.LatticeBRSTCohomologyField

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeMatterGhostCoupling (State ghostB matterMode ghostVirasoro)
open FieldNormalProductLocality (delta deltaEnd)

noncomputable section

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

section Ward

variable (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
  (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)

include hHG hGH in
/-- The literal original tensor translation is the actual b(-1) Ward homotopy.
Rank 26 is needed for the quotient, but not for this operator equality. -/
theorem original_translation_eq_charge_b :
    LatticeMatterGhostStateField.translation D =
      LatticeBRST.totalCharge D H *
          TensorProduct.map LinearMap.id
            (D5.S3.Quantum.Fermionic.BcGhostFock.b (-1)) +
        TensorProduct.map LinearMap.id
            (D5.S3.Quantum.Fermionic.BcGhostFock.b (-1)) *
          LatticeBRST.totalCharge D H := by
  change LatticeMatterGhostStateField.translation D =
    LatticeBRST.totalCharge D H * ghostB D (-1) +
      ghostB D (-1) * LatticeBRST.totalCharge D H
  rw [LatticeBRST.total_ward_b]
  change TensorProduct.map (LatticeSugawaraConformal.translation D) LinearMap.id +
      TensorProduct.map LinearMap.id
        (D5.S3.Quantum.Fermionic.BcGhostVirasoro.L (-1)) =
    TensorProduct.map (LatticeSugawaraCurrents.sugawaraMode D H (-1)) LinearMap.id +
      TensorProduct.map LinearMap.id
        (D5.S3.Quantum.Fermionic.BcGhostVirasoro.L (-1))
  rw [LatticeSugawaraConformal.sugawaraMode_minus_one_eq_translation D H hHG hGH]

end Ward

variable (h26 : D.rank = 26)
  (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
  (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)

private theorem cycleTranslation_exact (a : cycles D H) :
    cycleTranslation D H a ∈ boundaries D H h26 hHG hGH := by
  apply (mem_boundaries D H h26 hHG hGH _).mpr
  refine ⟨ghostB D (-1) (a : State D), ?_⟩
  change LatticeBRST.totalCharge D H (ghostB D (-1) (a : State D)) =
    LatticeMatterGhostStateField.translation D (a : State D)
  rw [original_translation_eq_charge_b D H hHG hGH]
  simp only [ghostB, LinearMap.add_apply, Module.End.mul_apply,
    show LatticeBRST.totalCharge D H (a : State D) = 0 from a.property,
    map_zero, add_zero]

/-- Translation vanishes on the supplied actual quotient, because every
translated cycle is the boundary of its original b(-1) image. -/
theorem translation_eq_zero : translation D H h26 hHG hGH = 0 := by
  apply LinearMap.ext
  intro a
  obtain ⟨u, rfl⟩ := classOf_surjective D H h26 hHG hGH a
  rw [translation_classOf]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (cycleTranslation_exact D H h26 hHG hGH u)

/-- Every integer mode except -1 vanishes. Taking covariance at k+1 handles
negative k as well; the complex scalar -(k+1) is explicitly nonzero. -/
theorem mode_eq_zero (a : Cohomology D H h26 hHG hGH) (k : ℤ) (hk : k ≠ -1) :
    mode D H h26 hHG hGH k a = 0 := by
  have hs : -(((k + 1 : ℤ) : ℂ)) ≠ 0 := by
    apply neg_ne_zero.mpr
    exact_mod_cast (show k + 1 ≠ 0 by omega)
  have e := (covariance D H h26 hHG hGH a (k + 1)).symm
  have ez : -(((k + 1 : ℤ) : ℂ)) • mode D H h26 hHG hGH k a = 0 := by
    simpa only [translation_eq_zero D H h26 hHG hGH,
      zero_mul, mul_zero, sub_self, Y_modes,
      show k + 1 - 1 = k by omega] using e
  exact (smul_eq_zero.mp ez).resolve_left hs

/-- The bilinear multiplication IS mode -1 of the supplied quotient field. -/
def product : Cohomology D H h26 hHG hGH →ₗ[ℂ]
    Module.End ℂ (Cohomology D H h26 hHG hGH) :=
  mode D H h26 hHG hGH (-1)

@[simp] theorem product_classOf (a b : cycles D H) :
    product D H h26 hHG hGH (classOf D H h26 hHG hGH a)
      (classOf D H h26 hHG hGH b) =
    classOf D H h26 hHG hGH (cycleMode D H (-1) a b) := rfl

/-- In mode indexing, a constant field has precisely its -1 coefficient. -/
theorem Y_modes_constant (a : Cohomology D H h26 hHG hGH) (n : ℤ) :
    ((Y D H h26 hHG hGH a)[[n]]) =
      if n = -1 then product D H h26 hHG hGH a else 0 := by
  rw [Y_modes]
  split_ifs with hn
  · subst n; rfl
  · exact mode_eq_zero D H h26 hHG hGH a n hn

theorem product_vacuum_left (a : Cohomology D H h26 hHG hGH) :
    product D H h26 hHG hGH (vacuum D H h26 hHG hGH) a = a := by
  exact (vacuum_mode D H h26 hHG hGH (-1) a).trans (if_pos rfl)

theorem product_vacuum_right (a : Cohomology D H h26 hHG hGH) :
    product D H h26 hHG hGH a (vacuum D H h26 hHG hGH) = a := by
  simpa only [product, Y_modes] using creation D H h26 hHG hGH a

/- Preserve the ORIGINAL support, first through the injective cycle subtype,
then through classOf. A quotient map need not preserve infinite-support
finsums, so no unrestricted map_finsum statement is used. -/
private theorem cycle_finite {f : ℕ → cycles D H}
    (hf : Function.HasFiniteSupport (fun i => (f i : State D))) :
    Function.HasFiniteSupport f := by
  apply hf.subset
  intro i hi
  change f i ≠ 0 at hi
  change (f i : State D) ≠ 0
  intro hz
  exact hi (Subtype.ext hz)

/-- Associativity for arbitrary classes, including mixed parity. The actual
native signed iterate is applied to arbitrary cycle representatives at
r=n=-1. Its forward family reduces to i=0 on the quotient. Both reverse
families die by their nonnegative INNER modes, without removing those
families or their support conditions from the original identity. -/
theorem product_assoc (a b c : Cohomology D H h26 hHG hGH) :
    product D H h26 hHG hGH (product D H h26 hHG hGH a b) c =
      product D H h26 hHG hGH a (product D H h26 hHG hGH b c) := by
  classical
  obtain ⟨u, rfl⟩ := classOf_surjective D H h26 hHG hGH a
  obtain ⟨v, rfl⟩ := classOf_surjective D H h26 hHG hGH b
  obtain ⟨w, rfl⟩ := classOf_surjective D H h26 hHG hGH c
  let u0 : cycles D H := (2 : ℂ)⁻¹ • (u + cycleParity D H u)
  let u1 : cycles D H := (2 : ℂ)⁻¹ • (u - cycleParity D H u)
  let weight : ℕ → ℂ := fun i =>
    ((-1 : ℂ)^i) * ((Ring.choose (-1 : ℤ) i : ℤ) : ℂ)
  let left : ℕ → cycles D H := fun i =>
    weight i • cycleMode D H (-1 - (i : ℤ)) u
      (cycleMode D H (-1 + (i : ℤ)) v w)
  let right0 : ℕ → cycles D H := fun i =>
    weight i • cycleMode D H (-1 + -1 - (i : ℤ)) v
      (cycleMode D H (i : ℤ) u0 w)
  let right1 : ℕ → cycles D H := fun i =>
    weight i • cycleMode D H (-1 + -1 - (i : ℤ)) (cycleParity D H v)
      (cycleMode D H (i : ℤ) u1 w)
  have original := LatticeMatterGhostStateFieldIterate.stateField_iterate D
    (u : State D) (v : State D) (w : State D) (-1) (-1)
  dsimp only at original
  obtain ⟨hL, hR0, hR1, hIterate⟩ := original
  have finiteL : Function.HasFiniteSupport left := cycle_finite D H hL
  have finiteR0 : Function.HasFiniteSupport right0 := cycle_finite D H hR0
  have finiteR1 : Function.HasFiniteSupport right1 := cycle_finite D H hR1
  have cycleIdentity :
      cycleMode D H (-1) (cycleMode D H (-1) u v) w =
        (∑ᶠ i : ℕ, left i) - ((-1 : ℂ)^(-1 : ℤ)) •
          ((∑ᶠ i : ℕ, right0 i) + (∑ᶠ i : ℕ, right1 i)) := by
    apply Subtype.ext
    change originalMode D (-1) (originalMode D (-1) u v) w =
      (cycles D H).subtype
        ((∑ᶠ i : ℕ, left i) - ((-1 : ℂ)^(-1 : ℤ)) •
          ((∑ᶠ i : ℕ, right0 i) + (∑ᶠ i : ℕ, right1 i)))
    rw [map_sub, map_smul, map_add, map_finsum _ finiteL,
      map_finsum _ finiteR0, map_finsum _ finiteR1]
    exact hIterate
  have descended := congrArg (classOf D H h26 hHG hGH) cycleIdentity
  rw [map_sub, map_smul, map_add, map_finsum _ finiteL,
    map_finsum _ finiteR0, map_finsum _ finiteR1] at descended
  have leftSum : (∑ᶠ i : ℕ, classOf D H h26 hHG hGH (left i)) =
      product D H h26 hHG hGH (classOf D H h26 hHG hGH u)
        (product D H h26 hHG hGH (classOf D H h26 hHG hGH v)
          (classOf D H h26 hHG hGH w)) := by
    rw [finsum_eq_single _ 0]
    · simp only [left, weight, Nat.cast_zero, sub_zero, add_zero, pow_zero,
        Ring.choose_zero_right, Int.cast_one, mul_one, one_smul,
        product_classOf]
    · intro i hi
      dsimp only [left]
      rw [map_smul, ← mode_classOf, ← mode_classOf,
        mode_eq_zero D H h26 hHG hGH
          (classOf D H h26 hHG hGH v) (-1 + (i : ℤ)) (by omega)]
      simp only [LinearMap.zero_apply, map_zero, smul_zero]
  have rightSum0 : (∑ᶠ i : ℕ, classOf D H h26 hHG hGH (right0 i)) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    dsimp only [right0]
    rw [map_smul, ← mode_classOf, ← mode_classOf,
      mode_eq_zero D H h26 hHG hGH
        (classOf D H h26 hHG hGH u0) (i : ℤ) (by omega)]
    simp only [LinearMap.zero_apply, map_zero, smul_zero]
  have rightSum1 : (∑ᶠ i : ℕ, classOf D H h26 hHG hGH (right1 i)) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    dsimp only [right1]
    rw [map_smul, ← mode_classOf, ← mode_classOf,
      mode_eq_zero D H h26 hHG hGH
        (classOf D H h26 hHG hGH u1) (i : ℤ) (by omega)]
    simp only [LinearMap.zero_apply, map_zero, smul_zero]
  rw [leftSum, rightSum0, rightSum1, add_zero, smul_zero, sub_zero] at descended
  simpa only [product_classOf] using descended

theorem product_parity (a b : Cohomology D H h26 hHG hGH) :
    parity D H h26 hHG hGH (product D H h26 hHG hGH a b) =
      product D H h26 hHG hGH (parity D H h26 hHG hGH a)
        (parity D H h26 hHG hGH b) := by
  have h := LinearMap.congr_fun (field_parity D H h26 hHG hGH a (-1)) b
  simpa only [product, Y_modes, Module.End.mul_apply] using h

/-- Natural parity labels are unrestricted: only the stated eigenvalue
equations are used. Constant-field signed locality is evaluated at
(-1-N,-1); the existing finite binomial expansion leaves its i=0 term. -/
theorem product_supercomm (a b : Cohomology D H h26 hHG hGH) (p q : ℕ)
    (ha : parity D H h26 hHG hGH a = (-1 : ℂ)^p • a)
    (hb : parity D H h26 hHG hGH b = (-1 : ℂ)^q • b) :
    product D H h26 hHG hGH a b =
      (-1 : ℂ)^(p*q) • product D H h26 hHG hGH b a := by
  classical
  obtain ⟨N, hN⟩ := locality D H h26 hHG hGH a b p q ha hb
  simp only [Y_modes] at hN
  let F : ℤ → ℤ → Module.End ℂ (Cohomology D H h26 hHG hGH) := fun r s =>
    mode D H h26 hHG hGH r a * mode D H h26 hHG hGH s b -
      (-1 : ℂ)^(p*q) •
        (mode D H h26 hHG hGH s b * mode D H h26 hHG hGH r a)
  change delta^[N] F = 0 at hN
  have killed : ((deltaEnd ^ N) F) (-1 - (N : ℤ)) (-1) = 0 := by
    rw [Module.End.pow_apply]
    change (delta^[N] F) (-1 - (N : ℤ)) (-1) = 0
    rw [hN]
    rfl
  rw [FieldDeltaBinomial.delta_binomial] at killed
  have isolate :
      (∑ i ∈ Finset.range (N + 1),
        (((-1 : ℂ)^i) * (N.choose i : ℂ)) •
          F (-1 - (N : ℤ) + (N : ℤ) - (i : ℤ)) (-1 + (i : ℤ))) =
      F (-1) (-1) := by
    rw [Finset.sum_eq_single 0]
    · simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
        one_smul, Nat.cast_zero, sub_zero, add_zero,
        show -1 - (N : ℤ) + (N : ℤ) = -1 by omega]
    · intro i hi hne
      have hz := mode_eq_zero D H h26 hHG hGH b (-1 + (i : ℤ)) (by omega)
      simp only [F, hz, mul_zero, zero_mul, smul_zero, sub_self]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (Nat.zero_lt_succ N))).elim
  rw [isolate] at killed
  have commutes :
      mode D H h26 hHG hGH (-1) a * mode D H h26 hHG hGH (-1) b =
        (-1 : ℂ)^(p*q) •
          (mode D H h26 hHG hGH (-1) b * mode D H h26 hHG hGH (-1) a) :=
    sub_eq_zero.mp killed
  have applied := LinearMap.congr_fun commutes (vacuum D H h26 hHG hGH)
  have rightUnit (x : Cohomology D H h26 hHG hGH) :
      mode D H h26 hHG hGH (-1) x (vacuum D H h26 hHG hGH) = x :=
    product_vacuum_right D H h26 hHG hGH x
  simpa only [product, Module.End.mul_apply, LinearMap.smul_apply, rightUnit] using applied

/-- Literal spectral projections of the supplied quotient parity. -/
def evenPart : Module.End ℂ (Cohomology D H h26 hHG hGH) :=
  (2 : ℂ)⁻¹ • (LinearMap.id + parity D H h26 hHG hGH)

def oddPart : Module.End ℂ (Cohomology D H h26 hHG hGH) :=
  (2 : ℂ)⁻¹ • (LinearMap.id - parity D H h26 hHG hGH)

private theorem evenPart_classOf (u : cycles D H) :
    evenPart D H h26 hHG hGH (classOf D H h26 hHG hGH u) =
      classOf D H h26 hHG hGH (cycleProject D H 0 u) := by
  change (2 : ℂ)⁻¹ • (classOf D H h26 hHG hGH u +
      parity D H h26 hHG hGH (classOf D H h26 hHG hGH u)) = _
  simp only [cycleProject, pow_zero, one_smul, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply, map_smul, map_add, parity_classOf]

private theorem oddPart_classOf (u : cycles D H) :
    oddPart D H h26 hHG hGH (classOf D H h26 hHG hGH u) =
      classOf D H h26 hHG hGH (cycleProject D H 1 u) := by
  change (2 : ℂ)⁻¹ • (classOf D H h26 hHG hGH u -
      parity D H h26 hHG hGH (classOf D H h26 hHG hGH u)) = _
  simp only [cycleProject, pow_one, neg_one_smul, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.neg_apply, LinearMap.id_apply,
    map_smul, map_add, map_neg, parity_classOf, sub_eq_add_neg]

theorem evenPart_add_oddPart (a : Cohomology D H h26 hHG hGH) :
    evenPart D H h26 hHG hGH a + oddPart D H h26 hHG hGH a = a := by
  obtain ⟨u, rfl⟩ := classOf_surjective D H h26 hHG hGH a
  rw [evenPart_classOf, oddPart_classOf, ← map_add]
  apply congrArg (classOf D H h26 hHG hGH)
  apply Subtype.ext
  exact project_split D (u : State D)

private theorem evenPart_homogeneous (a : Cohomology D H h26 hHG hGH) :
    parity D H h26 hHG hGH (evenPart D H h26 hHG hGH a) =
      (-1 : ℂ)^0 • evenPart D H h26 hHG hGH a := by
  obtain ⟨u, rfl⟩ := classOf_surjective D H h26 hHG hGH a
  simp only [evenPart_classOf, parity_classOf]
  rw [← map_smul]
  apply congrArg (classOf D H h26 hHG hGH)
  apply Subtype.ext
  exact project_homogeneous D 0 (u : State D)

private theorem oddPart_homogeneous (a : Cohomology D H h26 hHG hGH) :
    parity D H h26 hHG hGH (oddPart D H h26 hHG hGH a) =
      (-1 : ℂ)^1 • oddPart D H h26 hHG hGH a := by
  obtain ⟨u, rfl⟩ := classOf_surjective D H h26 hHG hGH a
  simp only [oddPart_classOf, parity_classOf]
  rw [← map_smul]
  apply congrArg (classOf D H h26 hHG hGH)
  apply Subtype.ext
  exact project_homogeneous D 1 (u : State D)

/-- Actual mixed-parity braiding. No mixed class is asserted to possess a
homogeneous representative: all four terms use the actual even/odd maps. -/
theorem product_mixed_braiding (a b : Cohomology D H h26 hHG hGH) :
    product D H h26 hHG hGH a b =
      product D H h26 hHG hGH (evenPart D H h26 hHG hGH b)
        (evenPart D H h26 hHG hGH a) +
      product D H h26 hHG hGH (oddPart D H h26 hHG hGH b)
        (evenPart D H h26 hHG hGH a) +
      product D H h26 hHG hGH (evenPart D H h26 hHG hGH b)
        (oddPart D H h26 hHG hGH a) -
      product D H h26 hHG hGH (oddPart D H h26 hHG hGH b)
        (oddPart D H h26 hHG hGH a) := by
  have h00 := product_supercomm D H h26 hHG hGH
    (evenPart D H h26 hHG hGH a) (evenPart D H h26 hHG hGH b) 0 0
    (evenPart_homogeneous D H h26 hHG hGH a)
    (evenPart_homogeneous D H h26 hHG hGH b)
  have h01 := product_supercomm D H h26 hHG hGH
    (evenPart D H h26 hHG hGH a) (oddPart D H h26 hHG hGH b) 0 1
    (evenPart_homogeneous D H h26 hHG hGH a)
    (oddPart_homogeneous D H h26 hHG hGH b)
  have h10 := product_supercomm D H h26 hHG hGH
    (oddPart D H h26 hHG hGH a) (evenPart D H h26 hHG hGH b) 1 0
    (oddPart_homogeneous D H h26 hHG hGH a)
    (evenPart_homogeneous D H h26 hHG hGH b)
  have h11 := product_supercomm D H h26 hHG hGH
    (oddPart D H h26 hHG hGH a) (oddPart D H h26 hHG hGH b) 1 1
    (oddPart_homogeneous D H h26 hHG hGH a)
    (oddPart_homogeneous D H h26 hHG hGH b)
  norm_num only [Nat.zero_mul, Nat.mul_zero, Nat.one_mul, pow_zero, pow_one,
    one_smul, neg_one_smul] at h00 h01 h10 h11
  calc
    _ = product D H h26 hHG hGH
        (evenPart D H h26 hHG hGH a + oddPart D H h26 hHG hGH a)
        (evenPart D H h26 hHG hGH b + oddPart D H h26 hHG hGH b) := by
      rw [evenPart_add_oddPart, evenPart_add_oddPart]
    _ = _ := by
      simp only [map_add, LinearMap.add_apply]
      rw [h00, h01, h10, h11]
      abel

end
end D5.S3.VertexAlgebra.LatticeBRSTCohomologyField
