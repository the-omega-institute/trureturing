/- GID: D5/S3/VertexAlgebra/StateField/BorcherdsFromLocality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/StateField/BorcherdsFromLocality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Creation, translation and locality imply the full integer Borcherds identity. -/

import D5.S3.VertexAlgebra.StateField.BorcherdsPermutations
import D5.S3.VertexAlgebra.BinomialKernelDelta
import D5.S3.VertexAlgebra.LatticeActualVertexAlgebra

/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under the Apache 2.0 license. See the repository root LICENSE.
Authors: Scott Carnahan (upstream reconstruction), with native adaptations.
-/

/-!
# The Borcherds identity from locality

The finite coefficient proof generalizes LatticeAllStateJacobi, which adapts
PolynomialFockJacobi at bfd9ff0f15397a4fb933f36d701a60d325d84b08
(SHA-256 4835d521f0adc06d6799a4ef1f72d0936be53abbd3f2bbb666ecf2e6f8aab1fa).
The residue reconstruction traces to ScottCarnahan/vertexAlg at
4453e34ec390e82a0c789c731ada8f9a6e86bdea. See Matsuo–Nagatomo, Theorem 5.4.1.

proof_shape: borcherds: content
admission_basis: escape-witness
escape_witness: The signed Pascal recurrence propagates the iterate identity
at p = 0 and the operator-uniform locality cutoff in r to all integer p.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.StateField.BorcherdsFromLocality

open BorcherdsPermutations (Modes LowerTruncated modesOfStateField
  lowerTruncated_modesOfStateField product iterate defect defect_eq_zero_iff_borcherds)
open StateFieldResidueReconstruction (integerBinomial epsilon
  stateField_iterate_of_creation_translation_locality)
open FieldNormalProductLocality (commutator delta deltaEnd)
open BinomialKernelDelta (chooseSign chooseSign_pascal chooseSign_zero finsum_split)
open scoped BigOperators VertexOperator

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The defect obeys the same shift recurrence in the three binomial parameters. -/
private theorem defect_pascal (μ : Modes V) (trunc : LowerTruncated μ)
    (a b c : V) (p q r : ℤ) :
    defect μ a b c (p + 1) q r =
      defect μ a b c p (q + 1) r + defect μ a b c p q (r + 1) := by
  have offsetFinite (x y : V) (n : ℤ) (f : ℕ → V → V)
      (zero : ∀ i, f i 0 = 0) :
      Function.HasFiniteSupport (fun i : ℕ => f i (μ (n + i) x y)) := by
    obtain ⟨cutoff, vanish⟩ := trunc x y
    refine (Finset.range (cutoff - n).toNat).finite_toSet.subset ?_
    intro i hi
    apply Finset.mem_range.mpr
    by_contra! high
    apply hi
    change f i (μ (n + i) x y) = 0
    rw [vanish _ (by omega), zero]
  have chooseZero (n : ℤ) : integerBinomial n 0 = 1 := by simp [integerBinomial]
  have choosePascal (n : ℤ) (i : ℕ) :
      integerBinomial (n + 1) (i + 1) =
        integerBinomial n i + integerBinomial n (i + 1) := by
    unfold integerBinomial
    rw [Ring.choose_succ_succ, Int.cast_add]
  have sumPascal (n : ℤ) (f : ℕ → V) (finite : Function.HasFiniteSupport f) :
      (∑ᶠ i : ℕ, integerBinomial (n + 1) i • f i) =
        (∑ᶠ i : ℕ, integerBinomial n i • f i) +
          (∑ᶠ i : ℕ, integerBinomial n i • f (i + 1)) := by
    have tail := finite.fun_comp_of_injective (g := fun i : ℕ => i + 1)
      (fun _ _ h => Nat.add_right_cancel h)
    rw [finsum_split (fun i => integerBinomial (n + 1) i • f i)
        (finite.smul_right (integerBinomial (n + 1))),
      finsum_split (fun i => integerBinomial n i • f i)
        (finite.smul_right (integerBinomial n))]
    simp only [chooseZero, one_smul]
    simp_rw [choosePascal, add_smul]
    rw [finsum_add_distrib
      (f := fun i => integerBinomial n i • f (i + 1))
      (g := fun i => integerBinomial n (i + 1) • f (i + 1))
      (tail.smul_right (integerBinomial n))
      (tail.smul_right (fun i => integerBinomial n (i + 1)))]
    abel
  have signedSumPascal (n : ℤ) (f : ℕ → V) (finite : Function.HasFiniteSupport f) :
      (∑ᶠ i : ℕ, chooseSign (n + 1) i • f i) =
        (∑ᶠ i : ℕ, chooseSign n i • f i) -
          (∑ᶠ i : ℕ, chooseSign n i • f (i + 1)) := by
    have tail := finite.fun_comp_of_injective (g := fun i : ℕ => i + 1)
      (fun _ _ h => Nat.add_right_cancel h)
    rw [finsum_split (fun i => chooseSign (n + 1) i • f i)
        (finite.smul_right (chooseSign (n + 1))),
      finsum_split (fun i => chooseSign n i • f i)
        (finite.smul_right (chooseSign n))]
    simp only [chooseSign_zero, one_smul]
    simp_rw [chooseSign_pascal, sub_smul]
    rw [finsum_sub_distrib
      (f := fun i => chooseSign n (i + 1) • f (i + 1))
      (g := fun i => chooseSign n i • f (i + 1))
      (tail.smul_right (fun i => chooseSign n (i + 1)))
      (tail.smul_right (chooseSign n))]
    abel
  have iterateLaw :
      iterate μ a b c (p + 1) q r =
        iterate μ a b c p (q + 1) r + iterate μ a b c p q (r + 1) := by
    let f (i : ℕ) := μ (p + 1 + q - i) (μ (r + i) a b) c
    have law := sumPascal p f
      (offsetFinite a b r (fun i v => μ (p + 1 + q - i) v c) (by simp))
    simpa only [iterate, f, Nat.cast_add, Nat.cast_one,
      show p + (q + 1) = p + 1 + q by omega,
      show ∀ i : ℕ, r + ((i : ℤ) + 1) = r + 1 + i by intro i; omega,
      show ∀ i : ℕ, p + 1 + q - ((i : ℤ) + 1) = p + q - i by intro i; omega]
      using law
  have productLaw (x y : V) (m n : ℤ) :
      product μ x y c m n (r + 1) =
        product μ x y c (m + 1) n r - product μ x y c m (n + 1) r := by
    let f (i : ℕ) := μ (m + (r + 1) - i) x (μ (n + i) y c)
    have law := signedSumPascal r f
      (offsetFinite y c n (fun i v => μ (m + (r + 1) - i) x v) (by simp))
    simpa only [product, chooseSign, integerBinomial, f, Nat.cast_add, Nat.cast_one,
      show m + (r + 1) = m + 1 + r by omega,
      show ∀ i : ℕ, m + 1 + r - ((i : ℤ) + 1) = m + r - i by intro i; omega,
      show ∀ i : ℕ, n + ((i : ℤ) + 1) = n + 1 + i by intro i; omega]
      using law
  have sign : epsilon (r + 1) = -epsilon r := by
    rw [epsilon, epsilon, zpow_add₀ (by norm_num)]
    norm_num
  rw [defect, defect, defect, iterateLaw, productLaw a b p q, productLaw b a q p, sign]
  module

/-- For a nonnegative parameter the signed product difference is a coefficient
of the corresponding power of the locality operator. -/
private theorem product_sub_reverse_nat (Y : V →ₗ[ℂ] VertexOperator ℂ V)
    (a b c : V) (p q : ℤ) (r : ℕ) :
    product (modesOfStateField Y) a b c p q r -
        epsilon r • product (modesOfStateField Y) b a c q p r =
      ((deltaEnd ^ r) (commutator (Y a) (Y b))) p q c := by
  classical
  have productNat (x y : V) (m n : ℤ) :
      product (modesOfStateField Y) x y c m n r =
        ∑ i ∈ Finset.range (r + 1),
          ((-1 : ℂ)^i * (r.choose i : ℂ)) •
            ((Y x)[[m + r - i]]) (((Y y)[[n + i]]) c) := by
    unfold product
    simp only [integerBinomial, Ring.choose_natCast, Int.cast_natCast]
    apply finsum_eq_sum_of_support_subset
    intro i hi
    apply Finset.mem_range.mpr
    by_contra! outside
    exact hi (by simp [Nat.choose_eq_zero_of_lt (show r < i by omega)])
  rw [productNat, productNat, FieldDeltaBinomial.delta_binomial, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, FieldNormalProductLocality.commutator,
    Module.End.mul_apply, LinearMap.sub_apply, smul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.smul_sum, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro i hi
  have within : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp only [Nat.add_sub_cancel, Nat.choose_symm within, smul_smul, epsilon, zpow_natCast]
  have signs : (-1 : ℂ)^r * ((-1 : ℂ)^(r - i) * (r.choose i : ℂ)) =
      (-1 : ℂ)^i * (r.choose i : ℂ) := by
    have split : (-1 : ℂ)^r = (-1 : ℂ)^i * (-1 : ℂ)^(r - i) := by
      rw [← pow_add, Nat.add_sub_of_le within]
    have square : (-1 : ℂ)^(r - i) * (-1 : ℂ)^(r - i) = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      _ = (-1 : ℂ)^i * ((-1 : ℂ)^(r - i) * (-1 : ℂ)^(r - i)) *
          (r.choose i : ℂ) := by rw [split]; ring
      _ = _ := by rw [square, mul_one]
  rw [signs]
  push_cast [Int.natCast_sub within]
  rw [show q + (r : ℤ) - ((r : ℤ) - i) = q + i by omega,
    show p + ((r : ℤ) - i) = p + r - i by omega]

/-- The full Borcherds identity for a local, creative and translation-covariant
state-field map. The vertex-operator type supplies lower truncation. -/
theorem borcherds (Y : V →ₗ[ℂ] VertexOperator ℂ V)
    (vacuum : V) (T : Module.End ℂ V) (translation_vacuum : T vacuum = 0)
    (creation : ∀ a : V, ((Y a)[[-1]]) vacuum = a)
    (creativity : ∀ (a : V) (n : ℤ), 0 ≤ n → ((Y a)[[n]]) vacuum = 0)
    (covariance : ∀ (a : V) (n : ℤ),
      T * ((Y a)[[n]]) - ((Y a)[[n]]) * T = -(n : ℂ) • ((Y a)[[n - 1]]))
    (locality : ∀ a b : V, ∃ N : ℕ, delta^[N] (commutator (Y a) (Y b)) = 0)
    (a b c : V) (p q r : ℤ) :
    let μ : V → ℤ → V → V := fun x n y => ((Y x)[[n]]) y
    let left : ℕ → V := fun i => integerBinomial p i • μ (μ a (r + i) b) (p + q - i) c
    let first : ℕ → V := fun i =>
      ((-1 : ℂ)^i * integerBinomial r i) • μ a (p + r - i) (μ b (q + i) c)
    let second : ℕ → V := fun i =>
      ((-1 : ℂ)^i * integerBinomial r i) • (epsilon r • μ b (q + r - i) (μ a (p + i) c))
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport first ∧
      Function.HasFiniteSupport second ∧
        (∑ᶠ i : ℕ, left i) = ∑ᶠ i : ℕ, ((-1 : ℂ)^i * integerBinomial r i) •
          (μ a (p + r - i) (μ b (q + i) c) - epsilon r • μ b (q + r - i) (μ a (p + i) c)) := by
  let μ := modesOfStateField Y
  have trunc : LowerTruncated μ := lowerTruncated_modesOfStateField Y
  apply (defect_eq_zero_iff_borcherds μ trunc a b c p q r).mp
  have base (n s : ℤ) (v : V) :
      product μ a b v 0 n s - epsilon s • product μ b a v n 0 s =
        μ n (μ s a b) v := by
    have law := (stateField_iterate_of_creation_translation_locality Y vacuum T
      translation_vacuum creation creativity covariance locality a b v s n).2.2
    simpa only [product, zero_add, add_comm n s, μ, modesOfStateField, LinearMap.comp_apply,
      LinearMap.proj_apply, integerBinomial, epsilon] using law.symm
  have zeroSeed (n s : ℤ) : defect μ a b c 0 n s = 0 := by
    rw [defect, base, iterate, finsum_eq_single _ 0]
    · simp [integerBinomial]
    · intro i hi
      simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]
  obtain ⟨cutoff, killed⟩ := locality a b
  have highProduct (m n : ℤ) (s : ℕ) (hs : cutoff ≤ s) (v : V) :
      product μ a b v m n s - epsilon s • product μ b a v n m s = 0 := by
    have killed' : (deltaEnd ^ cutoff) (commutator (Y a) (Y b)) = 0 := by
      rw [Module.End.pow_apply]
      exact killed
    have vanish : (deltaEnd ^ s) (commutator (Y a) (Y b)) = 0 := by
      obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hs
      rw [Nat.add_comm cutoff extra, pow_add, Module.End.mul_apply, killed', map_zero]
    rw [product_sub_reverse_nat Y a b v m n s, vanish]
    rfl
  have highMode (s : ℤ) (hs : (cutoff : ℤ) ≤ s) : μ s a b = 0 := by
    obtain ⟨s, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ s by omega)
    have h := base (-1) s vacuum
    rw [highProduct _ _ s (by omega), show μ (-1) (μ (s : ℤ) a b) vacuum =
      μ (s : ℤ) a b from creation _] at h
    exact h.symm
  have highSeed (m n s : ℤ) (hs : (cutoff : ℤ) ≤ s) : defect μ a b c m n s = 0 := by
    have iterateZero : iterate μ a b c m n s = 0 := by
      unfold iterate
      apply finsum_eq_zero_of_forall_eq_zero
      intro i
      rw [highMode (s + i) (by omega), map_zero, LinearMap.zero_apply, smul_zero]
    obtain ⟨s, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ s by omega)
    rw [defect, highProduct _ _ s (by omega), iterateZero, sub_zero]
  have positive (m : ℕ) : ∀ n s : ℤ, defect μ a b c m n s = 0 := by
    induction m with
    | zero => exact zeroSeed
    | succ m ih =>
      intro n s
      rw [Nat.cast_succ, defect_pascal μ trunc, ih, ih, add_zero]
  -- Descend in the third index from the uniform cutoff, then in the first
  -- index from zero at each fixed value of the third index.
  have negative (d : ℕ) : ∀ (m : ℕ) (n : ℤ),
      defect μ a b c (-(m : ℤ)) n ((cutoff : ℤ) - d) = 0 := by
    induction d with
    | zero => intro m n; exact highSeed _ _ _ (by omega)
    | succ d outer =>
      intro m
      induction m with
      | zero => intro n; exact zeroSeed _ _
      | succ m inner =>
        intro n
        have step := defect_pascal μ trunc a b c (-((m + 1 : ℕ) : ℤ)) (n - 1)
          ((cutoff : ℤ) - (d + 1 : ℕ))
        rw [show -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) by omega,
          show n - 1 + 1 = n by omega,
          show (cutoff : ℤ) - (d + 1 : ℕ) + 1 = (cutoff : ℤ) - d by omega,
          inner, outer, add_zero] at step
        exact step.symm
  by_cases hp : 0 ≤ p
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    exact positive m q r
  by_cases hr : (cutoff : ℤ) ≤ r
  · exact highSeed p q r hr
  rw [show p = -((-p).toNat : ℤ) by omega,
    show r = (cutoff : ℤ) - (((cutoff : ℤ) - r).toNat : ℤ) by omega]
  exact negative _ _ _

/-- Bundle an actual local state-field map, deriving its Borcherds field. -/
def ofLocality (Y : V →ₗ[ℂ] VertexOperator ℂ V)
    (vacuum : V) (T : Module.End ℂ V)
    (vacuum_field : Y vacuum = FieldNormalProduct.identityField)
    (translation_vacuum : T vacuum = 0)
    (creation : ∀ a : V, ((Y a)[[-1]]) vacuum = a)
    (creativity : ∀ (a : V) (n : ℤ), 0 ≤ n → ((Y a)[[n]]) vacuum = 0)
    (covariance : ∀ (a : V) (n : ℤ),
      T * ((Y a)[[n]]) - ((Y a)[[n]]) * T = -(n : ℂ) • ((Y a)[[n - 1]]))
    (locality : ∀ a b : V, ∃ N : ℕ, delta^[N] (commutator (Y a) (Y b)) = 0) :
    LatticeActualVertexAlgebra.StateFieldVertexAlgebra V where
  stateField := Y
  vacuum := vacuum
  translation := T
  vacuum_field := vacuum_field
  creation := creation
  creativity := creativity
  translation_vacuum := translation_vacuum
  covariance := covariance
  locality := locality
  borcherds := borcherds Y vacuum T translation_vacuum creation creativity covariance locality

end
end D5.S3.VertexAlgebra.StateField.BorcherdsFromLocality
