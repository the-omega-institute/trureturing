/- GID: D5/S3/VertexAlgebra/LatticeSugawaraConformal
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeSugawaraConformal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual all-charge matrix Sugawara modes satisfy Virasoro and translate the lattice generators.
-/

/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
Authors of the upstream Sugawara architecture: Kalle Kytölä
Modified source: the statewise normal-ordering and commutator architecture of
VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4 is adapted
here to the actual matrix lattice currents and every integral charge sector.
The charged-ground cancellation, inverse-Gram trace and actual translation
identification concern the existing lattice carrier, without a Fock transfer.
Classical source: Bakalov--Kac, Twisted Modules over Lattice Vertex Algebras,
arXiv math/0402315v1, section 4.1, equations (4.12)--(4.16).

proof_shape: sugawaraMode_virasoro: content
proof_shape: actual_conformal_generators: content
admission_basis: escape-witness
escape_witness: The live all-charge central-defect calculation cancels both
charged boundary terms and computes the rank cubic on every sector; the
actual normal-product coefficient L(-1) is identified with charge-sensitive
translation on every oscillator polynomial.
proof_shape: translation_single: bind-only; consumed by rawCoeff_translation,
neutral_translation_covariance and actual_translation_generators
proof_shape: translation_vacuum: bind-only; consumed by actual_translation_generators
proof_shape: rawCoeff_translation: bind-only; consumed by actual_lattice_translation_covariance
proof_shape: actual_lattice_translation_covariance: bind-only; consumed by actual_translation_generators
proof_shape: neutral_translation_covariance: bind-only; consumed by
sugawaraMode_minus_one_eq_translation and actual_translation_generators
proof_shape: actual_translation_generators: bind-only; consumed by actual_conformal_generators
The translation auxiliaries are proof organization within this substantive
host and supply no separate admission basis. No all-state vertex algebra,
Jacobi, positivity or finite-dimensional weight-space conclusion is assumed.
-/

import D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
import D5.S3.VertexAlgebra.FieldNormalProduct
import D5.S3.Quantum.Algebra.ConditionalPolynomialRigidity
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeSugawaraConformal

open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open D5.S3.VertexAlgebra.FieldNormalProduct
open MvPolynomial
open scoped BigOperators VertexOperator

noncomputable section

/-- The complex Gram matrix associated with the integral lattice form. -/
abbrev gramComplex (D : LatticeData) : Matrix (Fin D.rank) (Fin D.rank) ℂ :=
  D.G.map (Int.cast : ℤ → ℂ)

/-- The actual normal-ordered quadratic summand. -/
def quadraticSummand (D : LatticeData) (i j : Fin D.rank) :
    VertexOperator ℂ (Carrier D) :=
  (normalMinusOne (neutralField D i) (neutralField D j)).1

/-- The actual matrix-weighted quadratic field. -/
def sugawaraField (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    VertexOperator ℂ (Carrier D) :=
  (2 : ℂ)⁻¹ • ∑ i : Fin D.rank, ∑ j : Fin D.rank,
    H i j • quadraticSummand D i j

/-- Its normalized coefficient at `m+1`. -/
def sugawaraMode (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) :
    Module.End ℂ (Carrier D) :=
  (sugawaraField D H)[[m + 1]]

/-- Gram-weighted differentiation at one positive oscillator frequency. -/
def weightedPartial (D : LatticeData) (i : Fin D.rank) (r : ℕ) :
    Module.End ℂ (Oscillator D) :=
  ∑ j : Fin D.rank, (D.G i j : ℂ) • (pderiv (j,r)).toLinearMap

private theorem weightedPartial_commute (D : LatticeData) (i j : Fin D.rank)
    (a b : ℕ) (p : Oscillator D) :
    weightedPartial D i a (weightedPartial D j b p) =
      weightedPartial D j b (weightedPartial D i a p) := by
  classical
  simp only [weightedPartial, LinearMap.sum_apply, LinearMap.smul_apply,
    Derivation.coeFn_coe, map_sum, map_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro u hu
  run_tac
    let supplier := (Lean.Name.num
      `_private.D5.S3.Quantum.Algebra.ConditionalPolynomialRigidity 0).append
      `D5.S3.Quantum.Algebra.ConditionalPolynomialRigidity.partials_commute
    Lean.Elab.Tactic.evalTactic (← `(tactic| rw [($(Lean.mkIdent supplier))]))
  exact smul_comm _ _ _

private theorem weightedPartial_X_mul (D : LatticeData) (i j : Fin D.rank)
    (a b : ℕ) (p : Oscillator D) :
    weightedPartial D i a (X (j,b) * p) =
      (if a = b then (D.G i j : ℂ) • p else 0) +
        X (j,b) * weightedPartial D i a p := by
  classical
  simp only [weightedPartial, LinearMap.sum_apply, LinearMap.smul_apply,
    Derivation.coeFn_coe]
  simp_rw [pderiv_mul, smul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · by_cases hab : a = b
    · subst b
      simp [pderiv_X, Pi.single_apply, Prod.mk.injEq]
    · simp [pderiv_X, Pi.single_apply, Prod.mk.injEq, hab, Ne.symm hab]
  · simp [Finset.mul_sum, mul_smul_comm]

private theorem neutralPolynomialMode_positive (D : LatticeData) (i : Fin D.rank)
    (β : Charge D) (a : ℕ) :
    neutralPolynomialMode D i β ((a : ℤ) + 1) = (a + 1 : ℂ) • weightedPartial D i a := by
  simp [neutralPolynomialMode, weightedPartial,
    show ¬ (a : ℤ) + 1 < 0 by omega, show (a : ℤ) + 1 ≠ 0 by omega,
    Int.cast_add, Int.cast_natCast]

private theorem neutralPolynomialMode_negative (D : LatticeData) (i : Fin D.rank)
    (β : Charge D) (a : ℕ) :
    neutralPolynomialMode D i β (-(a : ℤ) - 1) = LinearMap.mulLeft ℂ (X (i,a)) := by
  simp [neutralPolynomialMode, show -(a : ℤ) - 1 < 0 by omega,
    show -(-(a : ℤ) - 1) - 1 = (a : ℤ) by omega]

/-- The current law on the actual oscillator polynomial in every integral charge sector. -/
theorem neutralPolynomialMode_heisenberg (D : LatticeData) (i j : Fin D.rank)
    (β : Charge D) (m n : ℤ) :
    neutralPolynomialMode D i β m * neutralPolynomialMode D j β n -
      neutralPolynomialMode D j β n * neutralPolynomialMode D i β m =
      (if m + n = 0 then (m : ℂ) * (D.G i j : ℂ) else 0) •
        (1 : Module.End ℂ (Oscillator D)) := by
  classical
  have zeroLeft (n : ℤ) :
      neutralPolynomialMode D i β 0 * neutralPolynomialMode D j β n -
        neutralPolynomialMode D j β n * neutralPolynomialMode D i β 0 = 0 := by
    have hz : neutralPolynomialMode D i β 0 =
        (bilinear D (unitCharge D i) β : ℂ) • LinearMap.id := by
      simp [neutralPolynomialMode]
    rw [hz]
    apply LinearMap.ext
    intro p
    simp [map_smul]
  have zeroRight (m : ℤ) :
      neutralPolynomialMode D i β m * neutralPolynomialMode D j β 0 -
        neutralPolynomialMode D j β 0 * neutralPolynomialMode D i β m = 0 := by
    have hz : neutralPolynomialMode D j β 0 =
        (bilinear D (unitCharge D j) β : ℂ) • LinearMap.id := by
      simp [neutralPolynomialMode]
    rw [hz]
    apply LinearMap.ext
    intro p
    simp [map_smul]
  have positiveNegative (i j : Fin D.rank) (a b : ℕ) :
      neutralPolynomialMode D i β ((a : ℤ) + 1) *
          neutralPolynomialMode D j β (-(b : ℤ) - 1) -
        neutralPolynomialMode D j β (-(b : ℤ) - 1) *
          neutralPolynomialMode D i β ((a : ℤ) + 1) =
      (if a = b then (a + 1 : ℂ) * (D.G i j : ℂ) else 0) •
        (1 : Module.End ℂ (Oscillator D)) := by
    rw [neutralPolynomialMode_positive, neutralPolynomialMode_negative]
    apply LinearMap.ext
    intro p
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      LinearMap.mulLeft_apply, Module.End.one_apply]
    rw [weightedPartial_X_mul]
    by_cases h : a = b
    · simp [h, smul_add, mul_smul_comm, smul_smul]
    · simp [h, mul_smul_comm]
  cases m with
  | ofNat a =>
    cases a with
    | zero => simpa using zeroLeft n
    | succ a =>
      rw [show Int.ofNat (a+1) = (a : ℤ)+1 by simp]
      cases n with
      | ofNat b =>
        cases b with
        | zero => simpa [show (a : ℤ)+1 ≠ 0 by omega] using zeroRight ((a : ℤ)+1)
        | succ b =>
          rw [show Int.ofNat (b+1) = (b : ℤ)+1 by simp]
          have hn : (a : ℤ)+1+((b : ℤ)+1) ≠ 0 := by omega
          rw [if_neg hn, zero_smul, neutralPolynomialMode_positive,
            neutralPolynomialMode_positive]
          apply LinearMap.ext
          intro p
          simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
            map_smul, LinearMap.zero_apply]
          rw [weightedPartial_commute]
          exact sub_eq_zero.mpr (smul_comm _ _ _)
      | negSucc b =>
        rw [show Int.negSucc b = -(b : ℤ)-1 by omega]
        have h : (a : ℤ)+1+(-(b : ℤ)-1) = 0 ↔ a = b := by omega
        simp only [h]
        simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one]
          using positiveNegative i j a b
  | negSucc a =>
    rw [show Int.negSucc a = -(a : ℤ)-1 by omega]
    cases n with
    | ofNat b =>
      cases b with
      | zero =>
        have hn : -(a : ℤ)-1+Int.ofNat 0 ≠ 0 := by change -(a : ℤ)-1+0 ≠ 0; omega
        rw [if_neg hn, zero_smul]
        exact zeroRight (-(a : ℤ)-1)
      | succ b =>
        rw [show Int.ofNat (b+1) = (b : ℤ)+1 by simp]
        have h : -(a : ℤ)-1+((b : ℤ)+1) = 0 ↔ b = a := by omega
        simp only [h]
        have hc := positiveNegative j i b a
        have hg : D.G j i = D.G i j := D.symmetric j i
        calc
          _ = -(neutralPolynomialMode D j β ((b : ℤ)+1) *
              neutralPolynomialMode D i β (-(a : ℤ)-1) -
            neutralPolynomialMode D i β (-(a : ℤ)-1) *
              neutralPolynomialMode D j β ((b : ℤ)+1)) := by abel
          _ = _ := by
            rw [hc, hg]
            by_cases hab : b = a
            · subst b
              rw [if_pos rfl, if_pos rfl, ← neg_smul]
              congr 1
              simp only [Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one]
              ring
            · rw [if_neg hab, if_neg hab]
              simp
    | negSucc b =>
      rw [show Int.negSucc b = -(b : ℤ)-1 by omega]
      have hn : -(a : ℤ)-1+(-(b : ℤ)-1) ≠ 0 := by omega
      rw [if_neg hn, zero_smul, neutralPolynomialMode_negative,
        neutralPolynomialMode_negative]
      apply LinearMap.ext
      intro p
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.mulLeft_apply,
        LinearMap.zero_apply]
      exact sub_eq_zero.mpr (by ac_rfl)

@[simp] theorem neutralMode_single (D : LatticeData) (i : Fin D.rank) (m : ℤ)
    (β : Charge D) (p : Oscillator D) :
    neutralMode D i m (Finsupp.single β p) =
      Finsupp.single β (neutralPolynomialMode D i β m p) := by
  simp [neutralMode]

/-- The faithful Heisenberg law on the actual finite-charge carrier. -/
theorem neutralMode_heisenberg (D : LatticeData) (i j : Fin D.rank) (m n : ℤ) :
    neutralMode D i m * neutralMode D j n - neutralMode D j n * neutralMode D i m =
      (if m + n = 0 then (m : ℂ) * (D.G i j : ℂ) else 0) •
        (1 : Module.End ℂ (Carrier D)) := by
  classical
  apply Finsupp.lhom_ext'
  intro β
  apply LinearMap.ext
  intro p
  have h := congrArg (fun f : Module.End ℂ (Oscillator D) => f p)
    (neutralPolynomialMode_heisenberg D i j β m n)
  simpa only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.sub_apply,
    Module.End.mul_apply, neutralMode_single, LinearMap.smul_apply, Module.End.one_apply,
    ← Finsupp.single_sub, Finsupp.smul_single] using congrArg (Finsupp.single β) h

/-- Largest actual oscillator frequency appearing in a polynomial, or zero. -/
def polynomialFrequencyBound (D : LatticeData) (p : Oscillator D) : ℕ :=
  p.vars.sup (fun x : Index D => x.2 + 1)

/-- Finite maximum over the charge sectors of the actual input. -/
def vectorFrequencyBound (D : LatticeData) (v : Carrier D) : ℕ :=
  v.support.sup (fun β => polynomialFrequencyBound D (v β))

/-- Positive currents beyond the polynomial's actual frequency bound vanish. -/
theorem neutralPolynomialMode_vanish (D : LatticeData) (i : Fin D.rank)
    (β : Charge D) (p : Oscillator D) (n : ℤ)
    (hn : (polynomialFrequencyBound D p : ℤ) < n) :
    neutralPolynomialMode D i β n p = 0 := by
  classical
  have hnpos : 0 < n := lt_of_le_of_lt (Int.natCast_nonneg _) hn
  have hderiv (j : Fin D.rank) : pderiv (j, (n-1).toNat) p = 0 := by
    apply pderiv_eq_zero_of_notMem_vars
    intro hmem
    have hb := Finset.le_sup (f := fun x : Index D => x.2 + 1) hmem
    have hc : ((n-1).toNat : ℤ) = n-1 := Int.toNat_of_nonneg (by omega)
    change (n-1).toNat + 1 ≤ polynomialFrequencyBound D p at hb
    omega
  have hderiv' (j : Fin D.rank) : pderiv (j, n.toNat-1) p = 0 := by
    simpa using hderiv j
  simp [neutralPolynomialMode, not_lt.mpr hnpos.le, ne_of_gt hnpos, hderiv']

/-- The bound is attached to each finite-charge vector, not to the endomorphism. -/
theorem neutralMode_vanish (D : LatticeData) (i : Fin D.rank) (v : Carrier D)
    (n : ℤ) (hn : (vectorFrequencyBound D v : ℤ) < n) : neutralMode D i n v = 0 := by
  classical
  rw [neutralMode, Finsupp.lsum_apply]
  change (∑ β ∈ v.support, _) = 0
  apply Finset.sum_eq_zero
  intro β hβ
  have hb := Finset.le_sup (f := fun β => polynomialFrequencyBound D (v β)) hβ
  have hv := neutralPolynomialMode_vanish D i β (v β) n (by
    change polynomialFrequencyBound D (v β) ≤ vectorFrequencyBound D v at hb
    omega)
  simp [hv]

/-- Usual creation-left normal order, including the charge-sensitive zero mode. -/
def normalSummand (D : LatticeData) (i j : Fin D.rank) (k l : ℤ) :
    Module.End ℂ (Carrier D) :=
  if k < 0 then neutralMode D i k * neutralMode D j l
    else neutralMode D j l * neutralMode D i k

/-- Any common positive-mode bound of this input bounds its quadratic summands. -/
theorem normalSummand_support_of_bound (D : LatticeData) (i j : Fin D.rank)
    (m : ℤ) (v : Carrier D) (R : ℕ)
    (hR : ∀ a : Fin D.rank, ∀ n : ℤ, (R : ℤ) < n → neutralMode D a n v = 0) :
    Function.support (fun k : ℤ => normalSummand D i j k (m-k) v) ⊆
      Set.Icc (min 0 (m - R)) (R : ℤ) := by
  intro k hk
  by_contra h
  have hout : k < min 0 (m-R) ∨ (R : ℤ) < k := by
    simp only [Set.mem_Icc, not_and_or, not_le] at h
    exact h
  rcases hout with hlo | hhi
  · have hkneg : k < 0 := lt_of_lt_of_le hlo (min_le_left _ _)
    have hmk : (R : ℤ) < m-k := by
      have := lt_of_lt_of_le hlo (min_le_right _ _)
      omega
    exact hk (by simp [normalSummand, hkneg, Module.End.mul_apply, hR j (m-k) hmk])
  · have hkpos : ¬ k < 0 := by omega
    exact hk (by simp [normalSummand, hkpos, Module.End.mul_apply, hR i k hhi])

/-- Exact state-dependent closed interval; arbitrary modes and finite ranks. -/
theorem normalSummand_support_interval (D : LatticeData) (i j : Fin D.rank)
    (m : ℤ) (v : Carrier D) :
    Function.support (fun k : ℤ => normalSummand D i j k (m-k) v) ⊆
      Set.Icc (min 0 (m - vectorFrequencyBound D v)) (vectorFrequencyBound D v : ℤ) :=
  normalSummand_support_of_bound D i j m v (vectorFrequencyBound D v)
    (fun a n hn => neutralMode_vanish D a v n hn)

private theorem normalSummand_finite (D : LatticeData) (i j : Fin D.rank)
    (m : ℤ) (v : Carrier D) :
    Function.HasFiniteSupport (fun k : ℤ => normalSummand D i j k (m-k) v) :=
  (Set.finite_Icc _ _).subset (normalSummand_support_interval D i j m v)

private theorem neutralField_ncoeff (D : LatticeData) (i : Fin D.rank) (k : ℤ) :
    (neutralField D i)[[k]] = neutralMode D i k := by
  rw [neutralField, VertexOperator.ncoeff_of_coeff]
  rw [show -(-k-1)-1 = k by omega]

/-- The actual normal-minus-one subtype supplies precisely the two normal-mode halves. -/
theorem quadraticSummand_coefficient (D : LatticeData) (i j : Fin D.rank)
    (m : ℤ) (v : Carrier D) :
    ((quadraticSummand D i j)[[m+1]]) v =
      ∑ᶠ k : ℤ, normalSummand D i j k (m-k) v := by
  classical
  rw [quadraticSummand, (normalMinusOne (neutralField D i) (neutralField D j)).2]
  simp_rw [neutralField_ncoeff]
  let term (k : ℤ) := normalSummand D i j k (m-k) v
  have finite : Function.HasFiniteSupport term := normalSummand_finite D i j m v
  have union : Set.range Int.ofNat ∪ Set.range Int.negSucc = Set.univ := by
    ext k
    constructor
    · intro h; trivial
    · intro h
      cases k with
      | ofNat t => exact Or.inl ⟨t,rfl⟩
      | negSucc t => exact Or.inr ⟨t,rfl⟩
  have disjoint : Disjoint (Set.range Int.ofNat) (Set.range Int.negSucc) := by
    apply Set.disjoint_left.mpr
    rintro k ⟨a,rfl⟩ ⟨b,he⟩
    simp only [Int.negSucc_eq, Int.ofNat_eq_natCast] at he
    omega
  have split : (∑ᶠ k : ℤ, term k) =
      (∑ᶠ t : ℕ, term (Int.ofNat t)) + (∑ᶠ t : ℕ, term (Int.negSucc t)) := by
    rw [← finsum_mem_univ, ← union,
      finsum_mem_union' disjoint (finite.subset Set.inter_subset_right)
        (finite.subset Set.inter_subset_right),
      finsum_mem_range (fun a b h => Int.ofNat.inj h),
      finsum_mem_range (fun a b h => Int.negSucc.inj h)]
  change _ = ∑ᶠ k, term k
  rw [split]
  conv_rhs => rw [add_comm]
  congr 1
  · apply finsum_congr
    intro t
    rw [show Int.negSucc t = -(t : ℤ)-1 by omega]
    dsimp only [term, normalSummand]
    rw [if_pos (show -(t : ℤ)-1 < 0 by omega), Module.End.mul_apply,
      show m-(-(t : ℤ)-1) = m+1+t by omega]
  · apply finsum_congr
    intro t
    simp only [term, normalSummand, Int.ofNat_eq_natCast]
    rw [if_neg (show ¬ (t : ℤ) < 0 by omega), Module.End.mul_apply,
      show m+1-(t : ℤ)-1 = m-t by omega]

/-- Coefficient identification of the actual matrix-weighted field, on each actual input. -/
theorem sugawaraMode_finsum (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) (v : Carrier D) :
    sugawaraMode D H m v = (2 : ℂ)⁻¹ •
      ∑ i : Fin D.rank, ∑ j : Fin D.rank, H i j •
        ∑ᶠ k : ℤ, normalSummand D i j k (m-k) v := by
  simp only [sugawaraMode, sugawaraField, map_smul, map_sum, Pi.smul_apply,
    Finset.sum_apply, LinearMap.smul_apply, LinearMap.sum_apply, quadraticSummand_coefficient]

/-- An honest finite interval computes the same actual mode on the specified vector. -/
theorem sugawaraMode_interval_sum (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) (v : Carrier D) :
    sugawaraMode D H m v = (2 : ℂ)⁻¹ •
      ∑ i : Fin D.rank, ∑ j : Fin D.rank, H i j •
        ∑ k ∈ Finset.Icc (min 0 (m-vectorFrequencyBound D v))
          (vectorFrequencyBound D v : ℤ), normalSummand D i j k (m-k) v := by
  classical
  rw [sugawaraMode_finsum]
  apply congrArg (fun w : Carrier D => (2 : ℂ)⁻¹ • w)
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply congrArg (fun w : Carrier D => H i j • w)
  apply finsum_eq_sum_of_support_subset
  intro k hk
  simpa only [Finset.mem_coe, Finset.mem_Icc, Set.mem_Icc] using
    normalSummand_support_interval D i j m v hk

private theorem current_product_commutator (D : LatticeData) (i j a : Fin D.rank)
    (k l q : ℤ) :
    (neutralMode D i k * neutralMode D j l) * neutralMode D a q -
      neutralMode D a q * (neutralMode D i k * neutralMode D j l) =
      (if l+q = 0 then ((l : ℂ)*(D.G j a : ℂ)) • neutralMode D i k else 0) +
      (if k+q = 0 then ((k : ℂ)*(D.G i a : ℂ)) • neutralMode D j l else 0) := by
  calc
    _ = neutralMode D i k *
        (neutralMode D j l * neutralMode D a q - neutralMode D a q * neutralMode D j l) +
      (neutralMode D i k * neutralMode D a q - neutralMode D a q * neutralMode D i k) *
        neutralMode D j l := by noncomm_ring
    _ = _ := by
      rw [neutralMode_heisenberg, neutralMode_heisenberg]
      split_ifs <;> simp [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

private theorem normalSummand_current_commutator (D : LatticeData)
    (i j a : Fin D.rank) (k l q : ℤ) :
    normalSummand D i j k l * neutralMode D a q -
      neutralMode D a q * normalSummand D i j k l =
      (if l+q = 0 then ((l : ℂ)*(D.G j a : ℂ)) • neutralMode D i k else 0) +
      (if k+q = 0 then ((k : ℂ)*(D.G i a : ℂ)) • neutralMode D j l else 0) := by
  by_cases hk : k < 0
  · rw [normalSummand, if_pos hk]
    exact current_product_commutator D i j a k l q
  · rw [normalSummand, if_neg hk]
    simpa only [add_comm] using current_product_commutator D j i a l k q

/-- Each actual quadratic field coefficient contracts at both exceptional integer indices. -/
theorem quadraticSummand_current_commutator (D : LatticeData)
    (i j a : Fin D.rank) (m q : ℤ) :
    (quadraticSummand D i j)[[m+1]] * neutralMode D a q -
      neutralMode D a q * (quadraticSummand D i j)[[m+1]] =
      -(q : ℂ) • ((D.G j a : ℂ) • neutralMode D i (m+q) +
        (D.G i a : ℂ) • neutralMode D j (m+q)) := by
  classical
  apply LinearMap.ext
  intro v
  have hv := normalSummand_finite D i j m v
  have hw := normalSummand_finite D i j m (neutralMode D a q v)
  have hmap := hv.fun_comp (map_zero (neutralMode D a q))
  let x : Carrier D := (-(q : ℂ)*(D.G j a : ℂ)) • neutralMode D i (m+q) v
  let y : Carrier D := (-(q : ℂ)*(D.G i a : ℂ)) • neutralMode D j (m+q) v
  have hx : Function.HasFiniteSupport (fun k : ℤ => if m-k+q = 0 then x else 0) := by
    apply (Set.finite_singleton (m+q)).subset
    intro k hk
    have he : m-k+q = 0 := by
      by_contra h
      exact hk (by simp [h])
    simp only [Set.mem_singleton_iff]
    omega
  have hy : Function.HasFiniteSupport (fun k : ℤ => if k+q = 0 then y else 0) := by
    apply (Set.finite_singleton (-q)).subset
    intro k hk
    have he : k+q = 0 := by
      by_contra h
      exact hk (by simp [h])
    simp only [Set.mem_singleton_iff]
    omega
  change ((quadraticSummand D i j)[[m+1]]) (neutralMode D a q v) -
    neutralMode D a q (((quadraticSummand D i j)[[m+1]]) v) = _
  rw [quadraticSummand_coefficient, quadraticSummand_coefficient,
    map_finsum (neutralMode D a q) hv, ← finsum_sub_distrib hw hmap]
  calc
    _ = ∑ᶠ k : ℤ, ((if m-k+q = 0 then x else 0) + (if k+q = 0 then y else 0)) := by
      apply finsum_congr
      intro k
      change (normalSummand D i j k (m-k) * neutralMode D a q -
        neutralMode D a q * normalSummand D i j k (m-k)) v = _
      rw [normalSummand_current_commutator]
      simp only [LinearMap.add_apply, DFunLike.ite_apply, LinearMap.smul_apply,
        LinearMap.zero_apply]
      congr 1
      · by_cases hk : m-k+q = 0
        · have hmk : m-k = -q := by omega
          have hkm : k = m+q := by omega
          simp [hk, hmk, hkm, x]
        · simp [hk]
      · by_cases hk : k+q = 0
        · have hkq : k = -q := by omega
          have hmq : m-k = m+q := by omega
          simp [hk, hkq, hmq, y]
        · simp [hk]
    _ = x+y := by
      rw [finsum_add_distrib hx hy,
        finsum_eq_single _ (m+q) (fun k hk => by simp [show m-k+q ≠ 0 by omega]),
        finsum_eq_single _ (-q) (fun k hk => by simp [show k+q ≠ 0 by omega])]
      simp
    _ = _ := by simp [x, y, smul_add, smul_smul]

private theorem sugawaraMode_coefficient_sum (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) :
    sugawaraMode D H m = (2 : ℂ)⁻¹ •
      ∑ i : Fin D.rank, ∑ j : Fin D.rank, H i j • (quadraticSummand D i j)[[m+1]] := by
  simp only [sugawaraMode, sugawaraField, map_smul, map_sum, Pi.smul_apply, Finset.sum_apply]

/-- The matrix current law on the actual carrier for unrestricted integer modes. -/
theorem sugawaraMode_current_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Fin D.rank) (m q : ℤ) :
    sugawaraMode D H m * neutralMode D a q -
      neutralMode D a q * sugawaraMode D H m =
      -(q : ℂ) • neutralMode D a (m+q) := by
  classical
  have left (i : Fin D.rank) : ∑ j, H i j * (D.G j a : ℂ) = if i = a then 1 else 0 := by
    simpa [Matrix.mul_apply, gramComplex, Matrix.one_apply] using
      congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℂ => M i a) hHG
  have right (j : Fin D.rank) : ∑ i, H i j * (D.G i a : ℂ) = if j = a then 1 else 0 := by
    have h := congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℂ => M a j) hGH
    simpa [Matrix.mul_apply, gramComplex, Matrix.one_apply, D.symmetric a,
      mul_comm, eq_comm] using h
  have first : (∑ i : Fin D.rank, ∑ j : Fin D.rank,
      (H i j * (D.G j a : ℂ)) • neutralMode D i (m+q)) = neutralMode D a (m+q) := by
    simp_rw [← Finset.sum_smul, left]
    simp
  have second : (∑ i : Fin D.rank, ∑ j : Fin D.rank,
      (H i j * (D.G i a : ℂ)) • neutralMode D j (m+q)) = neutralMode D a (m+q) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, right]
    simp
  rw [sugawaraMode_coefficient_sum]
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← smul_sub,
    Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← smul_sub, quadraticSummand_current_commutator]
  have coefficients (i j : Fin D.rank) :
      H i j • (-(q : ℂ) • ((D.G j a : ℂ) • neutralMode D i (m+q) +
        (D.G i a : ℂ) • neutralMode D j (m+q))) =
      -(q : ℂ) • ((H i j*(D.G j a : ℂ)) • neutralMode D i (m+q) +
        (H i j*(D.G i a : ℂ)) • neutralMode D j (m+q)) := by
    simp only [smul_add, smul_smul]
    congr 1 <;> congr 1 <;> ring
  simp_rw [coefficients, ← Finset.smul_sum, Finset.sum_add_distrib]
  rw [first, second, ← two_smul ℂ, smul_smul]
  have hc : (2 : ℂ)⁻¹ * (-(q : ℂ) * 2) = -(q : ℂ) := by ring
  rw [smul_smul, mul_assoc, hc]

/-- The unsimplified Virasoro defect of the actual modes. -/
def centralDefect (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m n : ℤ) : Module.End ℂ (Carrier D) :=
  sugawaraMode D H m * sugawaraMode D H n - sugawaraMode D H n * sugawaraMode D H m -
    ((m-n : ℤ) : ℂ) • sugawaraMode D H (m+n)

/-- The actual central defect commutes with every current, in every charge sector. -/
theorem centralDefect_current_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Fin D.rank) (m n q : ℤ) :
    centralDefect D H m n * neutralMode D a q -
      neutralMode D a q * centralDefect D H m n = 0 := by
  have h := sugawaraMode_current_commutator D H hHG hGH
  have jacobi :
      (sugawaraMode D H m * sugawaraMode D H n - sugawaraMode D H n * sugawaraMode D H m) *
          neutralMode D a q - neutralMode D a q *
        (sugawaraMode D H m * sugawaraMode D H n - sugawaraMode D H n * sugawaraMode D H m) =
      sugawaraMode D H m * (sugawaraMode D H n * neutralMode D a q -
          neutralMode D a q * sugawaraMode D H n) -
        (sugawaraMode D H n * neutralMode D a q - neutralMode D a q * sugawaraMode D H n) *
          sugawaraMode D H m -
      (sugawaraMode D H n * (sugawaraMode D H m * neutralMode D a q -
          neutralMode D a q * sugawaraMode D H m) -
        (sugawaraMode D H m * neutralMode D a q - neutralMode D a q * sugawaraMode D H m) *
          sugawaraMode D H n) := by noncomm_ring
  have hexp :
      (sugawaraMode D H m * sugawaraMode D H n - sugawaraMode D H n * sugawaraMode D H m -
        ((m-n : ℤ) : ℂ) • sugawaraMode D H (m+n)) * neutralMode D a q -
        neutralMode D a q * (sugawaraMode D H m * sugawaraMode D H n -
          sugawaraMode D H n * sugawaraMode D H m - ((m-n : ℤ) : ℂ) • sugawaraMode D H (m+n)) =
      -(q : ℂ) • (sugawaraMode D H m * neutralMode D a (n+q) -
          neutralMode D a (n+q) * sugawaraMode D H m) -
        -(q : ℂ) • (sugawaraMode D H n * neutralMode D a (m+q) -
          neutralMode D a (m+q) * sugawaraMode D H n) -
        ((m-n : ℤ) : ℂ) • (sugawaraMode D H (m+n) * neutralMode D a q -
          neutralMode D a q * sugawaraMode D H (m+n)) := by
    rw [show ∀ x y z t : Module.End ℂ (Carrier D), (x-y-z)*t-t*(x-y-z) =
      ((x-y)*t-t*(x-y))- (z*t-t*z) by intros; noncomm_ring]
    rw [jacobi, h a n q, h a m q]
    simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]
  change (sugawaraMode D H m * sugawaraMode D H n -
    sugawaraMode D H n * sugawaraMode D H m -
    ((m-n : ℤ) : ℂ) • sugawaraMode D H (m+n)) * neutralMode D a q -
    neutralMode D a q * (sugawaraMode D H m * sugawaraMode D H n -
      sugawaraMode D H n * sugawaraMode D H m -
      ((m-n : ℤ) : ℂ) • sugawaraMode D H (m+n)) = 0
  rw [hexp, h a m (n+q), h a n (m+q), h a (m+n) q]
  rw [show m+(n+q) = m+n+q by omega, show n+(m+q) = m+n+q by omega]
  simp only [smul_smul, ← sub_smul]
  have hc : -(q : ℂ) * -((n+q : ℤ) : ℂ) - -(q : ℂ) * -((m+q : ℤ) : ℂ) -
      ((m-n : ℤ) : ℂ) * -(q : ℂ) = 0 := by push_cast; ring
  rw [hc, zero_smul]

/-- Restriction of the actual Sugawara mode to one actual charge sector. -/
def sectorSugawaraMode (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (β : Charge D) (m : ℤ) :
    Module.End ℂ (Oscillator D) :=
  (Finsupp.lapply β).comp ((sugawaraMode D H m).comp (Finsupp.lsingle β))

/-- The actual field coefficients preserve each charge; restriction loses no action. -/
theorem sugawaraMode_single_sector (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (β : Charge D) (m : ℤ) (p : Oscillator D) :
    sugawaraMode D H m (Finsupp.single β p) =
      Finsupp.single β (sectorSugawaraMode D H β m p) := by
  classical
  let P : Module.End ℂ (Carrier D) := (Finsupp.lsingle β).comp (Finsupp.lapply β)
  have term (i j : Fin D.rank) (k : ℤ) :
      P (normalSummand D i j k (m-k) (Finsupp.single β p)) =
        normalSummand D i j k (m-k) (Finsupp.single β p) := by
    unfold normalSummand
    split_ifs <;> simp [P, Module.End.mul_apply]
  have hP : P (sugawaraMode D H m (Finsupp.single β p)) =
      sugawaraMode D H m (Finsupp.single β p) := by
    rw [sugawaraMode_finsum]
    simp only [map_smul, map_sum]
    apply congrArg (fun v : Carrier D => (2 : ℂ)⁻¹ • v)
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply congrArg (fun v : Carrier D => H i j • v)
    rw [map_finsum P (normalSummand_finite D i j m (Finsupp.single β p))]
    exact finsum_congr (term i j)
  simpa only [P, sectorSugawaraMode, LinearMap.comp_apply, Finsupp.lapply_apply,
    Finsupp.lsingle_apply] using hP.symm

/-- The sector defect is the faithful restriction of the actual central defect. -/
def sectorCentralDefect (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (β : Charge D) (m n : ℤ) :
    Module.End ℂ (Oscillator D) :=
  sectorSugawaraMode D H β m * sectorSugawaraMode D H β n -
    sectorSugawaraMode D H β n * sectorSugawaraMode D H β m -
    ((m-n : ℤ) : ℂ) • sectorSugawaraMode D H β (m+n)

private theorem centralDefect_single_sector (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (β : Charge D) (m n : ℤ) (p : Oscillator D) :
    centralDefect D H m n (Finsupp.single β p) =
      Finsupp.single β (sectorCentralDefect D H β m n p) := by
  simp only [centralDefect, sectorCentralDefect, LinearMap.sub_apply, Module.End.mul_apply,
    sugawaraMode_single_sector, LinearMap.smul_apply, ← Finsupp.single_sub, Finsupp.smul_single]

private theorem sectorCentralDefect_current_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (β : Charge D) (a : Fin D.rank) (m n q : ℤ) :
    sectorCentralDefect D H β m n * neutralPolynomialMode D a β q -
      neutralPolynomialMode D a β q * sectorCentralDefect D H β m n = 0 := by
  apply LinearMap.ext
  intro p
  have h := congrArg (fun F : Module.End ℂ (Carrier D) => F (Finsupp.single β p))
    (centralDefect_current_commutator D H hHG hGH a m n q)
  have hx := congrArg (fun v : Carrier D => v β) h
  simpa only [LinearMap.sub_apply, Module.End.mul_apply, neutralMode_single,
    centralDefect_single_sector, Finsupp.sub_apply, Finsupp.single_eq_same,
    LinearMap.zero_apply, Finsupp.zero_apply] using hx

private theorem polynomial_current_commutant_scalar (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1)
    (β : Charge D) (A : Module.End ℂ (Oscillator D))
    (hA : ∀ (a : Fin D.rank) (q : ℤ),
      A * neutralPolynomialMode D a β q - neutralPolynomialMode D a β q * A = 0) :
    A = constantCoeff (A 1) • (1 : Module.End ℂ (Oscillator D)) := by
  classical
  have hweighted (i : Fin D.rank) (r : ℕ) : weightedPartial D i r (A 1) = 0 := by
    have h := congrArg (fun F : Module.End ℂ (Oscillator D) => F 1)
      (hA i ((r : ℤ)+1))
    rw [neutralPolynomialMode_positive] at h
    have hone : weightedPartial D i r (1 : Oscillator D) = 0 := by
      simp [weightedPartial, pderiv_one]
    have hs : (r+1 : ℂ) • weightedPartial D i r (A 1) = 0 := by
      simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
        hone, smul_zero, map_zero, zero_sub, neg_eq_zero, LinearMap.zero_apply] using h
    have hc : (r+1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero r)
    exact (smul_eq_zero.mp hs).resolve_left hc
  have hpartial (x : Index D) : pderiv x (A 1) = 0 := by
    have reconstruct : (∑ i : Fin D.rank, H x.1 i • weightedPartial D i x.2 (A 1)) =
        pderiv x (A 1) := by
      simp only [weightedPartial, LinearMap.sum_apply, LinearMap.smul_apply,
        Derivation.coeFn_coe, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      have row (j : Fin D.rank) : ∑ i, H x.1 i * (D.G i j : ℂ) =
          if x.1 = j then 1 else 0 := by
        simpa [Matrix.mul_apply, gramComplex, Matrix.one_apply] using
          congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℂ => M x.1 j) hHG
      simp_rw [row]
      simp
    rw [← reconstruct]
    simp [hweighted]
  have hconstant : A 1 = C (constantCoeff (A 1)) := by
    run_tac
      let supplier := (Lean.Name.num
        `_private.D5.S3.Quantum.Algebra.ConditionalPolynomialRigidity 0).append
        `D5.S3.Quantum.Algebra.ConditionalPolynomialRigidity.eq_constant_of_partials_zero
      Lean.Elab.Tactic.evalTactic
        (← `(tactic| exact ($(Lean.mkIdent supplier)) _ $(Lean.mkIdent `hpartial)))
  apply LinearMap.ext
  intro p
  change A p = constantCoeff (A 1) • p
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [show (C c : Oscillator D) = c • 1 by simp [smul_eq_C_mul], map_smul, hconstant]
    simp [smul_eq_C_mul, mul_comm]
  | add p q hp hq => simp [map_add, hp, hq, smul_add]
  | mul_X p x hp =>
    have h := congrArg (fun F : Module.End ℂ (Oscillator D) => F p)
      (hA x.1 (-(x.2 : ℤ)-1))
    rw [neutralPolynomialMode_negative] at h
    change A (X x * p) - X x * A p = 0 at h
    rw [mul_comm p (X x), sub_eq_zero.mp h, hp]
    simp [mul_smul_comm]

/-- Scalarity is proved independently on every integral charge sector. -/
theorem centralDefect_sector_scalar (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (β : Charge D) (m n : ℤ) :
    sectorCentralDefect D H β m n =
      constantCoeff (sectorCentralDefect D H β m n 1) •
        (1 : Module.End ℂ (Oscillator D)) :=
  polynomial_current_commutant_scalar D H hHG β (sectorCentralDefect D H β m n)
    (fun a q => sectorCentralDefect_current_commutator D H hHG hGH β a m n q)

/-- Weighted Euler derivation on the actual oscillator variables. -/
def oscillatorEuler (D : LatticeData) : Derivation ℂ (Oscillator D) (Oscillator D) :=
  mkDerivation ℂ (fun x : Index D => (x.2+1 : ℂ) • X x)

/-- The charge-preserving weighted Euler operator on the actual carrier. -/
def eulerMode (D : LatticeData) : Module.End ℂ (Carrier D) :=
  Finsupp.lsum ℂ (fun β => (Finsupp.lsingle β).comp (oscillatorEuler D).toLinearMap)

@[simp] private theorem eulerMode_single (D : LatticeData) (β : Charge D) (p : Oscillator D) :
    eulerMode D (Finsupp.single β p) = Finsupp.single β (oscillatorEuler D p) := by
  simp [eulerMode]

private theorem oscillatorEuler_partial (D : LatticeData) (j : Fin D.rank) (r : ℕ) :
    (oscillatorEuler D).toLinearMap * (pderiv (j,r)).toLinearMap -
      (pderiv (j,r)).toLinearMap * (oscillatorEuler D).toLinearMap =
      -(r+1 : ℂ) • (pderiv (j,r)).toLinearMap := by
  classical
  have h : ⁅oscillatorEuler D, pderiv (j,r)⁆ =
      -(r+1 : ℂ) • (pderiv (j,r) : Derivation ℂ (Oscillator D) (Oscillator D)) := by
    apply MvPolynomial.derivation_ext
    intro x
    by_cases hx : x = (j,r)
    · subst x
      simp [Derivation.commutator_apply, oscillatorEuler, Pi.single_apply]
      rw [← neg_smul]
      congr 1
      ring
    · simp [Derivation.commutator_apply, oscillatorEuler, Pi.single_apply, hx]
  apply LinearMap.ext
  intro p
  exact congrArg (fun δ : Derivation ℂ (Oscillator D) (Oscillator D) => δ p) h

private theorem oscillatorEuler_weightedPartial (D : LatticeData) (i : Fin D.rank) (r : ℕ) :
    (oscillatorEuler D).toLinearMap * weightedPartial D i r -
      weightedPartial D i r * (oscillatorEuler D).toLinearMap =
      -(r+1 : ℂ) • weightedPartial D i r := by
  classical
  simp only [weightedPartial, Finset.mul_sum, Finset.sum_mul,
    Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← smul_sub, oscillatorEuler_partial, smul_comm (D.G i _ : ℂ) (-(r+1 : ℂ))]
  rw [← Finset.smul_sum]

private theorem oscillatorEuler_current (D : LatticeData) (i : Fin D.rank)
    (β : Charge D) (q : ℤ) :
    (oscillatorEuler D).toLinearMap * neutralPolynomialMode D i β q -
      neutralPolynomialMode D i β q * (oscillatorEuler D).toLinearMap =
      -(q : ℂ) • neutralPolynomialMode D i β q := by
  cases q with
  | ofNat a =>
    cases a with
    | zero =>
      have hz : neutralPolynomialMode D i β 0 =
          (bilinear D (unitCharge D i) β : ℂ) • (1 : Module.End ℂ (Oscillator D)) := by
        simp [neutralPolynomialMode, Module.End.one_eq_id]
      simp only [Int.ofNat_eq_natCast, Nat.cast_zero, Int.cast_zero, neg_zero, zero_smul]
      rw [hz]
      simp [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    | succ r =>
      rw [show Int.ofNat (r+1) = (r : ℤ)+1 by simp, neutralPolynomialMode_positive]
      rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← smul_sub,
        oscillatorEuler_weightedPartial]
      simp only [Int.cast_add, Int.cast_natCast, Int.cast_one]
      exact smul_comm _ _ _
  | negSucc r =>
    rw [show Int.negSucc r = -(r : ℤ)-1 by omega, neutralPolynomialMode_negative]
    apply LinearMap.ext
    intro p
    change oscillatorEuler D (X (i,r) * p) - X (i,r) * oscillatorEuler D p =
      -((-(r : ℤ)-1 : ℤ) : ℂ) • (X (i,r)*p)
    rw [(oscillatorEuler D).leibniz]
    simp [oscillatorEuler, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, add_comm,
      Int.cast_sub, Int.cast_neg, Int.cast_natCast, smul_eq_C_mul]

/-- Weighted Euler gives the current its actual frequency, including all zero modes. -/
theorem eulerMode_current_commutator (D : LatticeData) (i : Fin D.rank) (q : ℤ) :
    eulerMode D * neutralMode D i q - neutralMode D i q * eulerMode D =
      -(q : ℂ) • neutralMode D i q := by
  apply Finsupp.lhom_ext'
  intro β
  apply LinearMap.ext
  intro p
  have h := congrArg (fun F : Module.End ℂ (Oscillator D) => F p)
    (oscillatorEuler_current D i β q)
  simpa only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.sub_apply,
    Module.End.mul_apply, neutralMode_single, eulerMode_single, LinearMap.smul_apply,
    ← Finsupp.single_sub, Finsupp.smul_single, Derivation.coeFn_coe] using
      congrArg (Finsupp.single β) h

private theorem normalSummand_euler_commutator (D : LatticeData)
    (i j : Fin D.rank) (k l : ℤ) :
    eulerMode D * normalSummand D i j k l - normalSummand D i j k l * eulerMode D =
      -((k+l : ℤ) : ℂ) • normalSummand D i j k l := by
  have product (i j : Fin D.rank) (k l : ℤ) :
      eulerMode D * (neutralMode D i k * neutralMode D j l) -
        (neutralMode D i k * neutralMode D j l) * eulerMode D =
        -((k+l : ℤ) : ℂ) • (neutralMode D i k * neutralMode D j l) := by
    calc
      _ = (eulerMode D * neutralMode D i k - neutralMode D i k * eulerMode D) *
          neutralMode D j l + neutralMode D i k *
        (eulerMode D * neutralMode D j l - neutralMode D j l * eulerMode D) := by
        noncomm_ring
      _ = _ := by
        rw [eulerMode_current_commutator, eulerMode_current_commutator]
        simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← add_smul]
        congr 1
        push_cast
        ring
  by_cases hk : k < 0
  · rw [normalSummand, if_pos hk]
    exact product i j k l
  · rw [normalSummand, if_neg hk]
    simpa only [add_comm] using product j i l k

private theorem quadraticSummand_euler_commutator (D : LatticeData)
    (i j : Fin D.rank) (m : ℤ) :
    eulerMode D * (quadraticSummand D i j)[[m+1]] -
      (quadraticSummand D i j)[[m+1]] * eulerMode D =
      -(m : ℂ) • (quadraticSummand D i j)[[m+1]] := by
  apply LinearMap.ext
  intro v
  have hv := normalSummand_finite D i j m v
  have hw := normalSummand_finite D i j m (eulerMode D v)
  have hmap := hv.fun_comp (map_zero (eulerMode D))
  change eulerMode D (((quadraticSummand D i j)[[m+1]]) v) -
    ((quadraticSummand D i j)[[m+1]]) (eulerMode D v) =
    -(m : ℂ) • ((quadraticSummand D i j)[[m+1]]) v
  rw [quadraticSummand_coefficient, quadraticSummand_coefficient,
    map_finsum (eulerMode D) hv,
    ← finsum_sub_distrib hmap hw]
  calc
    _ = ∑ᶠ k : ℤ, -(m : ℂ) • normalSummand D i j k (m-k) v := by
      apply finsum_congr
      intro k
      have h := congrArg (fun A : Module.End ℂ (Carrier D) => A v)
        (normalSummand_euler_commutator D i j k (m-k))
      simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
        show k+(m-k) = m by omega] using h
    _ = _ := (smul_finsum' _ hv).symm

/-- Euler measures the degree of the actual Sugawara modes on every vector. -/
theorem eulerMode_sugawara_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) :
    eulerMode D * sugawaraMode D H m - sugawaraMode D H m * eulerMode D =
      -(m : ℂ) • sugawaraMode D H m := by
  classical
  rw [sugawaraMode_coefficient_sum]
  simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
    Finset.mul_sum, Finset.sum_mul, ← smul_sub]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← smul_sub, quadraticSummand_euler_commutator,
    smul_comm (H _ _) (-(m : ℂ)), ← Finset.smul_sum]
  exact smul_comm _ _ _

private theorem eulerMode_defect_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m n : ℤ) :
    eulerMode D * centralDefect D H m n - centralDefect D H m n * eulerMode D =
      -((m+n : ℤ) : ℂ) • centralDefect D H m n := by
  have product (m n : ℤ) :
      eulerMode D * (sugawaraMode D H m * sugawaraMode D H n) -
        (sugawaraMode D H m * sugawaraMode D H n) * eulerMode D =
        -((m+n : ℤ) : ℂ) • (sugawaraMode D H m * sugawaraMode D H n) := by
    calc
      _ = (eulerMode D * sugawaraMode D H m - sugawaraMode D H m * eulerMode D) *
          sugawaraMode D H n + sugawaraMode D H m *
        (eulerMode D * sugawaraMode D H n - sugawaraMode D H n * eulerMode D) := by
        noncomm_ring
      _ = _ := by
        rw [eulerMode_sugawara_commutator, eulerMode_sugawara_commutator]
        simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← add_smul]
        congr 1
        push_cast
        ring
  unfold centralDefect
  calc
    _ = (eulerMode D * (sugawaraMode D H m * sugawaraMode D H n) -
          (sugawaraMode D H m * sugawaraMode D H n) * eulerMode D) -
        (eulerMode D * (sugawaraMode D H n * sugawaraMode D H m) -
          (sugawaraMode D H n * sugawaraMode D H m) * eulerMode D) -
        ((m-n : ℤ) : ℂ) • (eulerMode D * sugawaraMode D H (m+n) -
          sugawaraMode D H (m+n) * eulerMode D) := by
      simp only [mul_sub, sub_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]
      abel
    _ = _ := by
      rw [product, product, eulerMode_sugawara_commutator, add_comm n m]
      simp only [smul_sub, smul_comm ((m-n : ℤ) : ℂ) (-((m+n : ℤ) : ℂ))]

/-- Off the contraction diagonal the actual central defect vanishes on all charges. -/
theorem centralDefect_off_diagonal (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (m n : ℤ) (hmn : m + n ≠ 0) : centralDefect D H m n = 0 := by
  apply Finsupp.lhom_ext'
  intro β
  apply LinearMap.ext
  intro p
  let c := constantCoeff (sectorCentralDefect D H β m n 1)
  have hs (p : Oscillator D) : centralDefect D H m n (Finsupp.single β p) =
      c • Finsupp.single β p := by
    rw [centralDefect_single_sector, centralDefect_sector_scalar D H hHG hGH]
    simp [c, Finsupp.smul_single]
  have h := congrArg (fun A : Module.End ℂ (Carrier D) => A (Finsupp.single β p))
    (eulerMode_defect_commutator D H m n)
  have hc : -((m+n : ℤ) : ℂ) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast hmn)
  have hz : -((m+n : ℤ) : ℂ) • centralDefect D H m n (Finsupp.single β p) = 0 := by
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      eulerMode_single, hs, map_smul, sub_self] using h.symm
  have hout := (smul_eq_zero.mp hz).resolve_left hc
  simpa only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_apply] using hout

/-- The charge scalar carried by the actual zero current. -/
abbrev chargeScalar (D : LatticeData) (β : Charge D) (i : Fin D.rank) : ℂ :=
  (bilinear D (unitCharge D i) β : ℂ)

/-- The matrix quadratic zero-mode charge contribution. -/
def chargeQuadratic (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (β : Charge D) : ℂ :=
  (2 : ℂ)⁻¹ * ∑ i : Fin D.rank, ∑ j : Fin D.rank,
    H i j * chargeScalar D β i * chargeScalar D β j

private theorem ground_frequency_bound (D : LatticeData) (β : Charge D) :
    vectorFrequencyBound D (Finsupp.single β (1 : Oscillator D)) = 0 := by
  classical
  simp [vectorFrequencyBound, polynomialFrequencyBound]

private theorem neutralMode_zero_single (D : LatticeData) (i : Fin D.rank)
    (β : Charge D) (p : Oscillator D) :
    neutralMode D i 0 (Finsupp.single β p) = chargeScalar D β i • Finsupp.single β p := by
  simp [neutralPolynomialMode, chargeScalar, Finsupp.smul_single]

private theorem neutralMode_ground_positive (D : LatticeData) (i : Fin D.rank)
    (β : Charge D) (q : ℤ) (hq : 0 < q) :
    neutralMode D i q (Finsupp.single β (1 : Oscillator D)) = 0 := by
  apply neutralMode_vanish
  simpa only [ground_frequency_bound, Nat.cast_zero] using hq

/-- Every positive actual Sugawara mode kills every charged ground state. -/
theorem sugawaraMode_ground_positive (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (β : Charge D) (m : ℤ) (hm : 0 < m) :
    sugawaraMode D H m (Finsupp.single β (1 : Oscillator D)) = 0 := by
  classical
  rw [sugawaraMode_interval_sum, ground_frequency_bound]
  simp only [Nat.cast_zero, sub_zero, min_eq_left hm.le, Finset.Icc_self,
    Finset.sum_singleton]
  have term (i j : Fin D.rank) :
      normalSummand D i j 0 m (Finsupp.single β (1 : Oscillator D)) = 0 := by
    rw [normalSummand, if_neg (by omega), Module.End.mul_apply, neutralMode_zero_single,
      map_smul, neutralMode_ground_positive D j β m hm, smul_zero]
  simp [term]

/-- The charged ground contribution is present on every sector. -/
theorem sugawaraMode_ground_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (β : Charge D) :
    sugawaraMode D H 0 (Finsupp.single β (1 : Oscillator D)) =
      chargeQuadratic D H β • Finsupp.single β (1 : Oscillator D) := by
  classical
  rw [sugawaraMode_interval_sum, ground_frequency_bound]
  simp only [Nat.cast_zero, sub_zero, min_self, Finset.Icc_self, Finset.sum_singleton]
  have term (i j : Fin D.rank) :
      normalSummand D i j 0 0 (Finsupp.single β (1 : Oscillator D)) =
        (chargeScalar D β i * chargeScalar D β j) • Finsupp.single β (1 : Oscillator D) := by
    rw [normalSummand, if_neg (by omega), Module.End.mul_apply, neutralMode_zero_single,
      map_smul, neutralMode_zero_single, smul_smul]
  simp_rw [term, smul_smul]
  simp_rw [← Finset.sum_smul]
  simp only [chargeQuadratic, smul_smul, mul_assoc]

private theorem sugawara_current_product (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (i j : Fin D.rank) (a k l : ℤ) :
    sugawaraMode D H a * (neutralMode D i k * neutralMode D j l) -
      (neutralMode D i k * neutralMode D j l) * sugawaraMode D H a =
      -(k : ℂ) • (neutralMode D i (a+k) * neutralMode D j l) +
        -(l : ℂ) • (neutralMode D i k * neutralMode D j (a+l)) := by
  calc
    _ = (sugawaraMode D H a * neutralMode D i k - neutralMode D i k * sugawaraMode D H a) *
        neutralMode D j l + neutralMode D i k *
      (sugawaraMode D H a * neutralMode D j l - neutralMode D j l * sugawaraMode D H a) := by
      noncomm_ring
    _ = _ := by
      rw [sugawaraMode_current_commutator D H hHG hGH,
        sugawaraMode_current_commutator D H hHG hGH]
      simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]

private theorem sugawara_normal_ground (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (β : Charge D) (i j : Fin D.rank) (a k : ℤ) (ha : 0 < a)
    (hk : k ∈ Finset.Icc (-a) 0) :
    sugawaraMode D H a (normalSummand D i j k (-a-k) (Finsupp.single β 1)) =
      ((if k = -a then (a : ℂ) * chargeScalar D β i * chargeScalar D β j else 0) +
        (if k = 0 then (a : ℂ) * chargeScalar D β i * chargeScalar D β j else 0) +
        (-(k : ℂ) * ((a+k : ℤ) : ℂ) * (D.G i j : ℂ))) • Finsupp.single β 1 := by
  classical
  have hkb : -a ≤ k ∧ k ≤ 0 := Finset.mem_Icc.mp hk
  have product (i j : Fin D.rank) (k l : ℤ) :
      sugawaraMode D H a (neutralMode D i k (neutralMode D j l (Finsupp.single β 1))) =
      -(k : ℂ) • neutralMode D i (a+k) (neutralMode D j l (Finsupp.single β 1)) +
        -(l : ℂ) • neutralMode D i k (neutralMode D j (a+l) (Finsupp.single β 1)) := by
    have h := congrArg (fun A : Module.End ℂ (Carrier D) => A (Finsupp.single β 1))
      (sugawara_current_product D H hHG hGH i j a k l)
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply, sugawaraMode_ground_positive D H β a ha, map_zero, sub_zero] using h
  by_cases hk0 : k = 0
  · subst k
    have hna : (0 : ℤ) ≠ -a := by omega
    rw [normalSummand, if_neg (by omega), Module.End.mul_apply, sub_zero, product j i (-a) 0]
    simp only [Int.cast_zero, Int.cast_neg, neg_zero, neg_neg, zero_smul, add_zero,
      add_neg_cancel, if_neg hna, if_true, zero_add, mul_zero, zero_mul]
    simp only [neutralMode_zero_single, map_smul, smul_smul]
    rw [mul_assoc]
  · have hkneg : k < 0 := by omega
    rw [normalSummand, if_pos hkneg, Module.End.mul_apply, product i j k (-a-k)]
    have hz : neutralMode D j (a+(-a-k)) (Finsupp.single β (1 : Oscillator D)) = 0 :=
      neutralMode_ground_positive D j β _ (by omega)
    rw [hz, map_zero, smul_zero, add_zero]
    by_cases hka : k = -a
    · subst k
      simp only [add_neg_cancel, sub_self, Int.cast_neg, neg_neg, Int.cast_zero,
        mul_zero, add_zero, if_true, if_neg hk0, zero_add]
      simp only [neutralMode_zero_single, map_smul, smul_smul]
      congr 1
      ring
    · have hpositive : 0 < a+k := by omega
      have hcomm := congrArg (fun A : Module.End ℂ (Carrier D) => A (Finsupp.single β 1))
        (neutralMode_heisenberg D i j (a+k) (-a-k))
      rw [if_pos (by omega)] at hcomm
      have hcontract : neutralMode D i (a+k) (neutralMode D j (-a-k) (Finsupp.single β 1)) =
          (((a+k : ℤ) : ℂ)*(D.G i j : ℂ)) • Finsupp.single β 1 := by
        simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
          Module.End.one_apply, neutralMode_ground_positive D i β (a+k) hpositive,
          map_zero, sub_zero] using hcomm
      rw [hcontract, smul_smul, if_neg hka, if_neg hk0, zero_add, zero_add]
      rw [mul_assoc]

private theorem contraction_sum (a : ℕ) :
    ∑ k ∈ Finset.Icc (-(a : ℤ)) 0,
      -(k : ℂ) * (((a : ℤ)+k : ℤ) : ℂ) = ((a : ℂ)^3-a)/6 := by
  classical
  have reindex : (∑ k ∈ Finset.Icc (-(a : ℤ)) 0,
      -(k : ℂ) * (((a : ℤ)+k : ℤ) : ℂ)) =
      ∑ s ∈ Finset.range (a+1), (s : ℂ)*((a : ℂ)-s) := by
    apply Finset.sum_bij (fun k hk => (-k).toNat)
    · intro k hk
      have hb := Finset.mem_Icc.mp hk
      have hc : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      simp only [Finset.mem_range]
      omega
    · intro k hk l hl he
      have hb := Finset.mem_Icc.mp hk
      have hc := Finset.mem_Icc.mp hl
      have hkcast : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      have hlcast : ((-l).toNat : ℤ) = -l := Int.toNat_of_nonneg (by omega)
      omega
    · intro s hs
      have hsle : s ≤ a := by have hb := Finset.mem_range.mp hs; omega
      refine ⟨-(s : ℤ), Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      simp
    · intro k hk
      have hb := Finset.mem_Icc.mp hk
      have hcast : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      have hc : ((-k).toNat : ℂ) = -(k : ℂ) := by exact_mod_cast hcast
      rw [hc]
      push_cast
      ring
  rw [reindex]
  let F (s : ℕ) : ℂ := (a : ℂ)*(s : ℂ)*((s : ℂ)-1)/2 -
    ((s : ℂ)-1)*(s : ℂ)*(2*(s : ℂ)-1)/6
  have hterm (s : ℕ) : (s : ℂ)*((a : ℂ)-s) = F (s+1)-F s := by
    simp only [F, Nat.cast_add, Nat.cast_one]
    ring
  simp_rw [hterm]
  rw [Finset.sum_range_sub]
  simp only [F, Nat.cast_zero, Nat.cast_add, Nat.cast_one]
  ring

private theorem inverse_gram_trace (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1) :
    ∑ i : Fin D.rank, ∑ j : Fin D.rank, H i j * (D.G i j : ℂ) = (D.rank : ℂ) := by
  classical
  have diag (i : Fin D.rank) : ∑ j, H i j * (D.G i j : ℂ) = 1 := by
    simpa [Matrix.mul_apply, gramComplex, Matrix.one_apply, D.symmetric i] using
      congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℂ => M i i) hHG
  simp_rw [diag]
  simp

/-- Diagonal charged-ground cancellation leaves only the cubic inverse-Gram trace. -/
theorem centralDefect_ground_diagonal (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (β : Charge D) (a : ℕ) (ha : 0 < a) :
    centralDefect D H (a : ℤ) (-(a : ℤ)) (Finsupp.single β (1 : Oscillator D)) =
      ((D.rank : ℂ)/12*((a : ℂ)^3-a)) • Finsupp.single β (1 : Oscillator D) := by
  classical
  let v : Carrier D := Finsupp.single β 1
  have hapos : (0 : ℤ) < a := by exact_mod_cast ha
  have inner (i j : Fin D.rank) :
      ∑ k ∈ Finset.Icc (-(a : ℤ)) 0,
        sugawaraMode D H (a : ℤ) (normalSummand D i j k (-(a : ℤ)-k) v) =
      ((2*(a : ℂ)*chargeScalar D β i*chargeScalar D β j) +
        (((a : ℂ)^3-a)/6)*(D.G i j : ℂ)) • v := by
    have term (k : ℤ) (hk : k ∈ Finset.Icc (-(a : ℤ)) 0) :=
      sugawara_normal_ground D H hHG hGH β i j (a : ℤ) k hapos hk
    change (∑ k ∈ Finset.Icc (-(a : ℤ)) 0,
      sugawaraMode D H (a : ℤ) (normalSummand D i j k (-(a : ℤ)-k) (Finsupp.single β 1))) = _
    rw [Finset.sum_congr rfl term]
    simp only [← Finset.sum_smul, Finset.sum_add_distrib]
    have hsum : (∑ k ∈ Finset.Icc (-(a : ℤ)) 0,
        -(k : ℂ) * (((a : ℤ)+k : ℤ) : ℂ) * (D.G i j : ℂ)) =
        (((a : ℂ)^3-a)/6) * (D.G i j : ℂ) := by
      rw [← Finset.sum_mul, contraction_sum]
    rw [hsum]
    simp only [Finset.sum_ite_eq', Finset.mem_Icc, le_refl, Int.natCast_nonneg,
      neg_nonpos.mpr (Int.natCast_nonneg a), and_self, if_true]
    apply congrArg (fun c : ℂ => c • v)
    simp only [Int.cast_natCast]
    ring
  have hLL : sugawaraMode D H (a : ℤ) (sugawaraMode D H (-(a : ℤ)) v) =
      (2*(a : ℂ)*chargeQuadratic D H β +
        ((D.rank : ℂ)/12*((a : ℂ)^3-a))) • v := by
    rw [sugawaraMode_interval_sum D H (-(a : ℤ)) v,
      show vectorFrequencyBound D v = 0 from ground_frequency_bound D β]
    simp only [Nat.cast_zero, sub_zero, min_eq_right (by omega : -(a : ℤ) ≤ 0)]
    simp only [map_smul, map_sum]
    simp_rw [inner, smul_smul]
    simp_rw [← Finset.sum_smul]
    rw [smul_smul]
    apply congrArg (fun c : ℂ => c • v)
    simp only [mul_add, Finset.sum_add_distrib]
    have charge : ∑ i : Fin D.rank, ∑ j : Fin D.rank,
        H i j * (2*(a : ℂ)*chargeScalar D β i*chargeScalar D β j) =
        (2*(a : ℂ)) * ∑ i : Fin D.rank, ∑ j : Fin D.rank,
          H i j*chargeScalar D β i*chargeScalar D β j := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have central : ∑ i : Fin D.rank, ∑ j : Fin D.rank,
        H i j * ((((a : ℂ)^3-a)/6)*(D.G i j : ℂ)) =
        (((a : ℂ)^3-a)/6)*(D.rank : ℂ) := by
      rw [← inverse_gram_trace D H hHG]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [charge, central]
    simp only [chargeQuadratic]
    ring
  simp only [centralDefect, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    sugawaraMode_ground_positive D H β (a : ℤ) hapos, map_zero, sub_zero,
    add_neg_cancel, sub_neg_eq_add]
  change sugawaraMode D H (a : ℤ) (sugawaraMode D H (-(a : ℤ)) v) -
    (((a : ℤ)+(a : ℤ) : ℤ) : ℂ) • sugawaraMode D H 0 v = _
  rw [hLL, sugawaraMode_ground_zero]
  simp only [v, smul_smul, ← sub_smul, Int.cast_add, Int.cast_natCast]
  apply congrArg (fun c : ℂ => c • Finsupp.single β (1 : Oscillator D))
  ring


/-- The charged-ground value propagates to every oscillator in every charge sector. -/
theorem centralDefect_diagonal_positive (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : ℕ) (ha : 0 < a) :
    centralDefect D H (a : ℤ) (-(a : ℤ)) =
      ((D.rank : ℂ)/12*((a : ℂ)^3-a)) • (1 : Module.End ℂ (Carrier D)) := by
  apply Finsupp.lhom_ext'
  intro β
  have hc := congrArg (fun v : Carrier D => constantCoeff (v β))
    (centralDefect_ground_diagonal D H hHG hGH β a ha)
  simp [centralDefect_single_sector, Finsupp.smul_single] at hc
  apply LinearMap.ext
  intro p
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.smul_apply,
    Module.End.one_apply, centralDefect_single_sector]
  rw [centralDefect_sector_scalar D H hHG hGH, hc]
  simp [Finsupp.smul_single]

private theorem centralDefect_skew (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m n : ℤ) :
    centralDefect D H m n = -centralDefect D H n m := by
  have hc : ((n-m : ℤ) : ℂ) = -((m-n : ℤ) : ℂ) := by push_cast; ring
  simp only [centralDefect, hc, add_comm n m, neg_smul]
  abel

/-- The all-integer diagonal defect has the rank cubic, including zero and negative modes. -/
theorem centralDefect_diagonal (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (m : ℤ) :
    centralDefect D H m (-m) =
      ((D.rank : ℂ)/12*((m : ℂ)^3-m)) • (1 : Module.End ℂ (Carrier D)) := by
  rcases lt_trichotomy m 0 with hm | hm | hm
  · let a := (-m).toNat
    have hcast : (a : ℤ) = -m := Int.toNat_of_nonneg (by omega)
    have ha : 0 < a := by omega
    have hp := centralDefect_diagonal_positive D H hHG hGH a ha
    rw [hcast] at hp
    simp only [neg_neg] at hp
    rw [centralDefect_skew, hp, ← neg_smul]
    have hc : (a : ℂ) = -(m : ℂ) := by exact_mod_cast hcast
    rw [hc]
    congr 1
    ring
  · subst m
    simp [centralDefect]
  · let a := m.toNat
    have hcast : (a : ℤ) = m := Int.toNat_of_nonneg hm.le
    have ha : 0 < a := by omega
    have hp := centralDefect_diagonal_positive D H hHG hGH a ha
    rw [hcast] at hp
    have hc : (a : ℂ) = (m : ℂ) := by exact_mod_cast hcast
    simpa only [hc] using hp

/-- The actual central defect is scalar, uniformly over all integral charges. -/
theorem centralDefect_formula (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (m n : ℤ) :
    centralDefect D H m n =
      (if m+n = 0 then (D.rank : ℂ)/12*((m : ℂ)^3-m) else 0) •
        (1 : Module.End ℂ (Carrier D)) := by
  by_cases hmn : m+n = 0
  · have hn : n = -m := by omega
    subst n
    simpa only [add_neg_cancel, if_true] using centralDefect_diagonal D H hHG hGH m
  · rw [if_neg hmn, zero_smul, centralDefect_off_diagonal D H hHG hGH m n hmn]

/-- Virasoro on the actual finite-charge lattice carrier, with central charge equal to rank. -/
theorem sugawaraMode_virasoro (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (m n : ℤ) :
    sugawaraMode D H m * sugawaraMode D H n - sugawaraMode D H n * sugawaraMode D H m =
      ((m-n : ℤ) : ℂ) • sugawaraMode D H (m+n) +
        (if m+n = 0 then (D.rank : ℂ)/12*((m : ℂ)^3-m) else 0) •
          (1 : Module.End ℂ (Carrier D)) := by
  have h := centralDefect_formula D H hHG hGH m n
  unfold centralDefect at h
  simpa only [add_comm] using sub_eq_iff_eq_add.mp h


attribute [-instance] PowerSeries.algebraPolynomial

/-- Translation of the actual oscillator variables, without divided powers. -/
def oscillatorDerivation (D : LatticeData) :
    Derivation ℂ (Oscillator D) (Oscillator D) :=
  MvPolynomial.mkDerivation ℂ (fun x : Index D =>
    (x.2 + 1 : ℂ) • (X (x.1, x.2 + 1) : Oscillator D))

/-- The charge contribution on a sector. -/
def chargePolynomial (D : LatticeData) (β : Charge D) : Oscillator D :=
  ∑ i : Fin D.rank, (β i : ℂ) • X (i, 0)

def sectorTranslation (D : LatticeData) (β : Charge D) :
    Module.End ℂ (Oscillator D) :=
  (oscillatorDerivation D).toLinearMap + LinearMap.mulLeft ℂ (chargePolynomial D β)

/-- The operator preserves each charge and extends over finite charge support. -/
def translation (D : LatticeData) : Module.End ℂ (Carrier D) :=
  Finsupp.lsum ℂ (fun β => (Finsupp.lsingle β).comp (sectorTranslation D β))

@[simp] theorem translation_single (D : LatticeData) (β : Charge D)
    (p : Oscillator D) :
    translation D (Finsupp.single β p) =
      Finsupp.single β (oscillatorDerivation D p + chargePolynomial D β * p) := by
  simp [translation, sectorTranslation]

@[simp] theorem translation_vacuum (D : LatticeData) :
    translation D (Finsupp.single (0 : Charge D) (1 : Oscillator D)) = 0 := by
  simp [chargePolynomial]

private theorem charge_add (D : LatticeData) (α β : Charge D) :
    chargePolynomial D (α + β) = chargePolynomial D α + chargePolynomial D β := by
  simp [chargePolynomial, Int.cast_add, add_smul, Finset.sum_add_distrib]

/-- Coefficientwise oscillator derivation, fixing the polynomial variable. -/
private def polynomialDerivation (D : LatticeData) :
    Derivation ℂ (Polynomial (Oscillator D)) (Polynomial (Oscillator D)) :=
  PolynomialModule.equivPolynomialSelf.toLinearMap.compDer
    (oscillatorDerivation D).mapCoeffs

private theorem polynomialDerivation_coeff (D : LatticeData)
    (q : Polynomial (Oscillator D)) (d : ℕ) :
    (polynomialDerivation D q).coeff d = oscillatorDerivation D (q.coeff d) := rfl

private theorem polynomialDerivation_monomial (D : LatticeData) (d : ℕ)
    (p : Oscillator D) :
    polynomialDerivation D (Polynomial.monomial d p) =
      Polynomial.monomial d (oscillatorDerivation D p) := by
  ext j
  rw [polynomialDerivation_coeff]
  by_cases h : d = j <;> simp [Polynomial.coeff_monomial, h]

private theorem partial_translation_zero (D : LatticeData) (j : Fin D.rank)
    (p : Oscillator D) :
    oscillatorDerivation D (pderiv (j, 0) p) -
      pderiv (j, 0) (oscillatorDerivation D p) = 0 := by
  have h : ⁅oscillatorDerivation D, pderiv (j, 0)⁆ =
      (0 : Derivation ℂ (Oscillator D) (Oscillator D)) := by
    apply MvPolynomial.derivation_ext
    intro x
    simp [Derivation.commutator_apply, oscillatorDerivation, pderiv_X,
      Pi.single_apply, apply_ite]
  exact congrArg (fun d : Derivation ℂ (Oscillator D) (Oscillator D) => d p) h

private theorem partial_translation_succ (D : LatticeData) (j : Fin D.rank)
    (r : ℕ) (p : Oscillator D) :
    oscillatorDerivation D (pderiv (j, r + 1) p) -
      pderiv (j, r + 1) (oscillatorDerivation D p) =
        -(r + 1 : ℂ) • pderiv (j, r) p := by
  have h : ⁅oscillatorDerivation D, pderiv (j, r + 1)⁆ =
      (-(r + 1 : ℂ) • pderiv (j, r) : Derivation ℂ (Oscillator D) (Oscillator D)) := by
    apply MvPolynomial.derivation_ext
    intro x
    simp only [Derivation.commutator_apply, pderiv_X, Pi.single_apply,
      oscillatorDerivation, MvPolynomial.mkDerivation_X,
      Derivation.smul_apply]
    rw [show (MvPolynomial.mkDerivation ℂ
      (fun x : Index D => (x.2 + 1 : ℂ) • (X (x.1, x.2 + 1) : Oscillator D)))
      (if x = (j, r + 1) then 1 else 0) = 0 by split_ifs <;> simp]
    have hx : (x.1, x.2 + 1) = (j, r + 1) ↔ x = (j, r) := by
      simp only [Nat.add_right_cancel_iff, Prod.ext_iff]
    rw [Derivation.map_smul, pderiv_X]
    simp only [Pi.single_apply]
    simp only [hx]
    by_cases h : x = (j, r)
    · subst x; simp [smul_eq_C_mul]
    · simp [h]
  exact congrArg (fun d : Derivation ℂ (Oscillator D) (Oscillator D) => d p) h

private theorem partial_charge (D : LatticeData) (β : Charge D)
    (j : Fin D.rank) (r : ℕ) :
    pderiv (j, r) (chargePolynomial D β) =
      if r = 0 then C (β j : ℂ) else 0 := by
  classical
  by_cases hr : r = 0
  · subst r
    simp [chargePolynomial, pderiv_X, Pi.single_apply, Prod.mk.injEq,
      smul_eq_C_mul]
  · simp [chargePolynomial, pderiv_X, Prod.mk.injEq,
      smul_eq_C_mul, hr, Ne.symm hr]

/-- Coefficientwise oscillator derivation on a formal power series. -/
private def seriesDerivation (D : LatticeData) :
    Derivation ℂ (PowerSeries (Oscillator D)) (PowerSeries (Oscillator D)) where
  toFun f := PowerSeries.mk (fun n => oscillatorDerivation D (PowerSeries.coeff n f))
  map_add' f g := by apply PowerSeries.ext; intro n; simp
  map_smul' c f := by apply PowerSeries.ext; intro n; simp
  map_one_eq_zero' := by
    apply PowerSeries.ext
    intro n
    simp [PowerSeries.coeff_one, apply_ite]
  leibniz' f g := by
    apply PowerSeries.ext
    intro n
    change PowerSeries.coeff n (PowerSeries.mk (fun n =>
      oscillatorDerivation D (PowerSeries.coeff n (f * g)))) =
      PowerSeries.coeff n (f * PowerSeries.mk (fun n =>
        oscillatorDerivation D (PowerSeries.coeff n g)) +
        g * PowerSeries.mk (fun n => oscillatorDerivation D (PowerSeries.coeff n f)))
    rw [mul_comm g (PowerSeries.mk (fun n => oscillatorDerivation D (PowerSeries.coeff n f)))]
    simp only [PowerSeries.coeff_mk, map_add, PowerSeries.coeff_mul, map_sum,
      Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    ring

private theorem seriesDerivation_coeff (D : LatticeData)
    (f : PowerSeries (Oscillator D)) (n : ℕ) :
    PowerSeries.coeff n (seriesDerivation D f) =
      oscillatorDerivation D (PowerSeries.coeff n f) := by
  change PowerSeries.coeff n (PowerSeries.mk
    (fun n => oscillatorDerivation D (PowerSeries.coeff n f))) = _
  rw [PowerSeries.coeff_mk]

private theorem seriesDerivation_derivative (D : LatticeData)
    (f : PowerSeries (Oscillator D)) :
    seriesDerivation D (PowerSeries.derivative (Oscillator D) f) =
      PowerSeries.derivative (Oscillator D) (seriesDerivation D f) := by
  apply PowerSeries.ext
  intro n
  simp only [seriesDerivation_coeff, PowerSeries.coeff_derivative,
    Derivation.leibniz, Derivation.map_add, Derivation.map_natCast, Derivation.map_one_eq_zero,
    add_zero, smul_eq_mul]
  ring

private theorem logarithm_derivative_coeff (D : LatticeData) (α : Charge D)
    (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.derivative (Oscillator D) (creationSeries D α)) =
      ∑ i : Fin D.rank, (α i : ℂ) • (X (i,n) : Oscillator D) := by
  rw [PowerSeries.coeff_derivative]
  simp only [creationSeries, PowerSeries.coeff_mk, Nat.succ_ne_zero, ↓reduceDIte,
    Nat.add_sub_cancel]
  rw [mul_comm, show (n + 1 : Oscillator D) =
    algebraMap ℂ (Oscillator D) (n + 1 : ℂ) by simp,
    ← Algebra.smul_def, smul_smul]
  rw [Nat.cast_add, Nat.cast_one,
    mul_inv_cancel₀ (by exact_mod_cast Nat.succ_ne_zero n), one_smul]

private theorem exponential_constant (D : LatticeData) (α : Charge D) :
    PowerSeries.coeff 0 (creationExponential D α) = 1 := by
  have hA : PowerSeries.constantCoeff (creationSeries D α) = 0 := by
    simp [creationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [creationExponential, PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero' hA), finsum_eq_single _ 0]
  · simp
  · intro j hj
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, hA]
    simp [hj]

private theorem exponential_derivative (D : LatticeData) (α : Charge D) :
    PowerSeries.derivative (Oscillator D) (creationExponential D α) =
      creationExponential D α *
        PowerSeries.derivative (Oscillator D) (creationSeries D α) := by
  have hA : PowerSeries.constantCoeff (creationSeries D α) = 0 := by
    simp [creationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [creationExponential,
    PowerSeries.derivative_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hA),
    PowerSeries.derivative_exp]

/-- The oscillator derivative of the actual exponential, proved from its ODE. -/
private theorem creation_derivation_series (D : LatticeData) (α : Charge D) :
    seriesDerivation D (creationExponential D α) =
      PowerSeries.derivative (Oscillator D) (creationExponential D α) -
        PowerSeries.C (chargePolynomial D α) * creationExponential D α := by
  let E := creationExponential D α
  let A := PowerSeries.derivative (Oscillator D) (creationSeries D α)
  let H := seriesDerivation D E - PowerSeries.derivative (Oscillator D) E +
    PowerSeries.C (chargePolynomial D α) * E
  have hE : PowerSeries.derivative (Oscillator D) E = E * A :=
    exponential_derivative D α
  have hA : seriesDerivation D A = PowerSeries.derivative (Oscillator D) A := by
    apply PowerSeries.ext
    intro n
    rw [seriesDerivation_coeff]
    conv_rhs => rw [PowerSeries.coeff_derivative]
    rw [show PowerSeries.coeff n A =
      ∑ i : Fin D.rank, (α i : ℂ) • (X (i,n) : Oscillator D) from
      logarithm_derivative_coeff D α n]
    rw [show PowerSeries.coeff (n+1) A =
      ∑ i : Fin D.rank, (α i : ℂ) • (X (i,n+1) : Oscillator D) from
      logarithm_derivative_coeff D α (n+1)]
    simp only [map_sum, Derivation.map_smul,
      oscillatorDerivation, MvPolynomial.mkDerivation_X]
    simp only [Finset.sum_mul, smul_eq_C_mul, C_add, C_1]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [map_natCast]
    ring
  have hH : PowerSeries.derivative (Oscillator D) H = H * A := by
    dsimp only [H]
    rw [map_add, map_sub, ← seriesDerivation_derivative, hE,
      (seriesDerivation D).leibniz, (PowerSeries.derivative (Oscillator D)).leibniz,
      (PowerSeries.derivative (Oscillator D)).leibniz,
      PowerSeries.derivative_C, hA, hE]
    simp only [smul_eq_mul, mul_zero, add_zero]
    ring
  have h0 : PowerSeries.coeff 0 H = 0 := by
    dsimp only [H]
    rw [map_add, map_sub, seriesDerivation_coeff, exponential_constant,
      Derivation.map_one_eq_zero, hE]
    simp [PowerSeries.coeff_mul, E, A, exponential_constant,
      logarithm_derivative_coeff, chargePolynomial]
  have hzero : H = 0 := by
    apply PowerSeries.ext
    intro n
    rw [map_zero]
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => exact h0
      | succ n =>
        have hr := congrArg (PowerSeries.coeff n) hH
        rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at hr
        have hz : (∑ x ∈ Finset.HasAntidiagonal.antidiagonal n,
            PowerSeries.coeff x.1 H * PowerSeries.coeff x.2 A) = 0 := by
          apply Finset.sum_eq_zero
          intro x hx
          rw [ih x.1 (by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx; omega),
            zero_mul]
        rw [hz] at hr
        have hr' : (n + 1) • PowerSeries.coeff (n + 1) H =
            (n + 1) • (0 : Oscillator D) := by
          simpa only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_comm,
            mul_zero, zero_mul] using hr
        exact (smul_right_inj (Nat.succ_ne_zero n)).mp hr'
  dsimp only [H] at hzero
  change seriesDerivation D E = PowerSeries.derivative (Oscillator D) E -
    PowerSeries.C (chargePolynomial D α) * E
  linear_combination hzero

private theorem creation_derivation (D : LatticeData) (α : Charge D) (t : ℤ) :
    oscillatorDerivation D (creationCoeff D α t) =
      (t + 1 : ℂ) • creationCoeff D α (t + 1) -
        chargePolynomial D α * creationCoeff D α t := by
  by_cases ht : t < 0
  · by_cases h : t = -1
    · subst t; simp [creationCoeff]
    · simp [creationCoeff, ht, show t + 1 < 0 by omega]
  · have ht0 : 0 ≤ t := by omega
    have hn : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg ht0
    have hs : (t + 1).toNat = t.toNat + 1 := by omega
    have h := congrArg (PowerSeries.coeff t.toNat) (creation_derivation_series D α)
    rw [map_sub, seriesDerivation_coeff, PowerSeries.coeff_derivative,
      PowerSeries.coeff_C_mul] at h
    have hscale : (t.toNat + 1 : Oscillator D) =
        algebraMap ℂ (Oscillator D) (t + 1 : ℂ) := by
      simp only [map_add, map_one, map_intCast]
      have htP : (t.toNat : Oscillator D) = (t : Oscillator D) := by exact_mod_cast hn
      rw [htP]
    rw [hscale] at h
    rw [creationCoeff, dif_neg ht, creationCoeff, dif_neg (by omega), hs]
    simpa only [creationCoeff, dif_neg ht, Algebra.smul_def, mul_comm] using h

private theorem translated_sum (D : LatticeData) (α : Charge D)
    {ι : Type*} (s : Finset ι) (p : ι → Oscillator D) :
    translatedPolynomial D α (∑ i ∈ s, p i) =
      ∑ i ∈ s, translatedPolynomial D α (p i) := by
  simp [translatedPolynomial]

private theorem translated_add (D : LatticeData) (α : Charge D)
    (p q : Oscillator D) :
    translatedPolynomial D α (p + q) =
      translatedPolynomial D α p + translatedPolynomial D α q := by
  simp [translatedPolynomial]

private theorem translated_mul (D : LatticeData) (α : Charge D)
    (p q : Oscillator D) :
    translatedPolynomial D α (p * q) =
      translatedPolynomial D α p * translatedPolynomial D α q := by
  simp [translatedPolynomial]

private theorem translated_X (D : LatticeData) (α : Charge D) (x : Index D) :
    translatedPolynomial D α (X x) = translationVariable D α x.1 x.2 := by
  simp [translatedPolynomial]

private theorem translated_smul (D : LatticeData) (α : Charge D) (c : ℂ)
    (p : Oscillator D) :
    translatedPolynomial D α (c • p) = c • translatedPolynomial D α p := by
  have h : translatedPolynomial D α (C c) =
      algebraMap ℂ (Polynomial (Oscillator D)) c := by simp [translatedPolynomial]
  rw [smul_eq_C_mul, translated_mul, h, ← Algebra.smul_def]


private theorem polynomialDerivation_C (D : LatticeData) (p : Oscillator D) :
    polynomialDerivation D (Polynomial.C p) =
      Polynomial.C (oscillatorDerivation D p) :=
  polynomialDerivation_monomial D 0 p

private theorem polynomialDerivation_X (D : LatticeData) :
    polynomialDerivation D (Polynomial.X : Polynomial (Oscillator D)) = 0 := by
  rw [← Polynomial.monomial_one_one_eq_X, polynomialDerivation_monomial]
  simp

/-- All-polynomial annihilation transport; the indeterminate is the inverse field variable. -/
private theorem annihilation_transport (D : LatticeData) (α : Charge D)
    (p : Oscillator D) :
    translatedPolynomial D α (oscillatorDerivation D p) =
      polynomialDerivation D (translatedPolynomial D α p) +
        Polynomial.X ^ 2 * (translatedPolynomial D α p).derivative := by
  classical
  have hgen (x : Index D) :
      translatedPolynomial D α (oscillatorDerivation D (X x)) =
        polynomialDerivation D (translatedPolynomial D α (X x)) +
          Polynomial.X ^ 2 * (translatedPolynomial D α (X x)).derivative := by
    rw [show oscillatorDerivation D (X x) =
      (x.2 + 1 : ℂ) • (X (x.1, x.2 + 1) : Oscillator D) from
        MvPolynomial.mkDerivation_X ℂ _ x]
    rw [translated_smul]
    simp only [translated_X]
    simp only [translationVariable, map_sub, Derivation.leibniz,
      polynomialDerivation_C, polynomialDerivation_X, Derivation.leibniz_pow,
      smul_zero, zero_add, mul_zero, smul_eq_mul,
      oscillatorDerivation, MvPolynomial.mkDerivation_X,
      Derivation.map_smul, Derivation.map_one_eq_zero,
      Polynomial.derivative_C,
      Polynomial.derivative_mul, Polynomial.derivative_pow,
      Polynomial.derivative_X, mul_one, zero_mul]
    simp only [Nat.add_sub_cancel, smul_eq_C_mul, map_mul, map_add, map_natCast, map_one]
    rw [show x.2 + 1 + 1 = x.2 + 2 by omega]
    simp only [Algebra.smul_def, map_add, map_natCast, map_one, map_zero,
      Nat.cast_add, Nat.cast_one]
    ring
  induction p using MvPolynomial.induction_on with
  | C c =>
    simp [translatedPolynomial, polynomialDerivation_C]
  | add p q hp hq =>
    simp only [map_add, translated_add, hp, hq, mul_add]
    abel
  | mul_X p x hp =>
    rw [(oscillatorDerivation D).leibniz]
    simp only [smul_eq_mul, translated_add, translated_mul]
    rw [hp, hgen, (polynomialDerivation D).leibniz, Polynomial.derivative_mul]
    simp only [smul_eq_mul]
    ring

private theorem charge_pairing (D : LatticeData) (α β : Charge D) :
    (∑ i, β i * bilinear D α (unitCharge D i)) = bilinear D α β := by
  classical
  simp only [bilinear, unitCharge, Finset.mul_sum]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The actual input charge supplies precisely the missing inverse-variable term. -/
private theorem charge_transport (D : LatticeData) (α β : Charge D) :
    translatedPolynomial D α (chargePolynomial D β) =
      Polynomial.C (chargePolynomial D β) -
        Polynomial.C ((bilinear D α β : ℂ) • (1 : Oscillator D)) * Polynomial.X := by
  classical
  rw [chargePolynomial, translated_sum]
  simp only [translated_smul, translated_X, translationVariable,
    Nat.zero_add, pow_one, smul_sub, Finset.sum_sub_distrib]
  have hb : (∑ i : Fin D.rank, (β i : ℂ) *
      (bilinear D α (unitCharge D i) : ℂ)) = (bilinear D α β : ℂ) := by
    exact_mod_cast charge_pairing D α β
  simp only [← smul_mul_assoc, Polynomial.smul_C, smul_smul,
    ← Finset.sum_mul, ← map_sum]
  rw [show (∑ i : Fin D.rank,
      ((β i : ℂ) * (bilinear D α (unitCharge D i) : ℂ)) • (1 : Oscillator D)) =
      (bilinear D α β : ℂ) • (1 : Oscillator D) by
        rw [← Finset.sum_smul, hb] ]

/-- A finite coefficient convolution. Its linearity includes the full support of each input. -/
private def convolution (D : LatticeData) (α : Charge D) (b k : ℤ) :
    Polynomial (Oscillator D) →ₗ[Oscillator D] Oscillator D :=
  (Finsupp.lsum (Oscillator D) (fun d : ℕ =>
    LinearMap.mulRight (Oscillator D) (creationCoeff D α (k - b + d)))).comp
      ((AddMonoidAlgebra.coeffLinearEquiv (Oscillator D)).toLinearMap.comp
        (Polynomial.toFinsuppIsoLinear (Oscillator D)).toLinearMap)

private theorem convolution_monomial (D : LatticeData) (α : Charge D) (b k : ℤ)
    (d : ℕ) (a : Oscillator D) :
    convolution D α b k (Polynomial.monomial d a) =
      a * creationCoeff D α (k - b + d) := by
  simp [convolution, Polynomial.toFinsupp_monomial]

private theorem convolution_C_mul (D : LatticeData) (α : Charge D) (b k : ℤ)
    (a : Oscillator D) (q : Polynomial (Oscillator D)) :
    convolution D α b k (Polynomial.C a * q) = a * convolution D α b k q := by
  rw [← Polynomial.smul_eq_C_mul]
  exact map_smul _ _ _

/-- The escaping cancellation combines creation, annihilation and the changed charge. -/
private theorem convolution_cancellation (D : LatticeData) (α : Charge D)
    (b k : ℤ) (q : Polynomial (Oscillator D)) :
    oscillatorDerivation D (convolution D α b k q) -
        convolution D α b k (polynomialDerivation D q) +
        chargePolynomial D α * convolution D α b k q +
        (b : ℂ) • convolution D α b k (Polynomial.X * q) -
        convolution D α b k (Polynomial.X ^ 2 * q.derivative) =
      (k + 1 : ℂ) • convolution D α b (k + 1) q := by
  classical
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
    simp only [map_add, mul_add, smul_add]
    linear_combination hq + hr
  | monomial d a =>
    rw [convolution_monomial, (oscillatorDerivation D).leibniz,
      polynomialDerivation_monomial, convolution_monomial, creation_derivation]
    have hx : (Polynomial.X : Polynomial (Oscillator D)) * Polynomial.monomial d a =
        Polynomial.monomial (d + 1) a := by
      simp [← Polynomial.monomial_one_one_eq_X, Polynomial.monomial_mul_monomial,
        Nat.add_comm]
    have hd : (Polynomial.X : Polynomial (Oscillator D)) ^ 2 *
        (Polynomial.monomial d a).derivative =
        Polynomial.monomial (d + 1) ((d : Oscillator D) * a) := by
      cases d with
      | zero => simp
      | succ d =>
        simp [← Polynomial.monomial_one_one_eq_X,
          Polynomial.monomial_mul_monomial, Polynomial.monomial_pow, mul_comm,
          Nat.add_comm, Nat.add_left_comm]
    rw [hx, hd, convolution_monomial, convolution_monomial, convolution_monomial]
    rw [show k - b + (d + 1 : ℕ) = k - b + d + 1 by omega,
      show k + 1 - b + d = k - b + d + 1 by omega]
    simp only [smul_eq_mul, smul_eq_C_mul, C_add, C_sub, C_1,
      Int.cast_add, Int.cast_sub, Int.cast_natCast,
      map_natCast, map_intCast]
    ring

private theorem sector_apply (D : LatticeData) (β : Charge D) (p : Oscillator D) :
    sectorTranslation D β p = oscillatorDerivation D p + chargePolynomial D β * p := rfl

private theorem sector_convolution (D : LatticeData) (α β : Charge D)
    (k : ℤ) (p : Oscillator D) :
    sectorTranslation D (α + β)
        (convolution D α (bilinear D α β) k (translatedPolynomial D α p)) -
      convolution D α (bilinear D α β) k
        (translatedPolynomial D α (sectorTranslation D β p)) =
      (k + 1 : ℂ) • convolution D α (bilinear D α β) (k + 1)
        (translatedPolynomial D α p) := by
  have hQ : translatedPolynomial D α (sectorTranslation D β p) =
      polynomialDerivation D (translatedPolynomial D α p) +
        Polynomial.X ^ 2 * (translatedPolynomial D α p).derivative +
        Polynomial.C (chargePolynomial D β) * translatedPolynomial D α p -
        Polynomial.C ((bilinear D α β : ℂ) • (1 : Oscillator D)) *
          (Polynomial.X * translatedPolynomial D α p) := by
    rw [sector_apply, translated_add, translated_mul, annihilation_transport, charge_transport]
    ring
  rw [sector_apply, charge_add, hQ, map_sub, map_add, map_add,
    convolution_C_mul, convolution_C_mul]
  have h := convolution_cancellation D α (bilinear D α β) k
    (translatedPolynomial D α p)
  simp only [smul_eq_C_mul, mul_one] at h ⊢
  linear_combination h

/-- Exponent coefficient covariance on the full, finitely supported charge direct sum. -/
theorem rawCoeff_translation (D : LatticeData) (α : Charge D) (k : ℤ) :
    translation D * rawCoeff D α k - rawCoeff D α k * translation D =
      (k + 1 : ℂ) • rawCoeff D α (k + 1) := by
  apply Finsupp.lhom_ext
  intro β p
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    translation_single]
  rw [(actual_creation_coefficient_transport D α α).2.2.1,
    (actual_creation_coefficient_transport D α α).2.2.1,
    (actual_creation_coefficient_transport D α α).2.2.1]
  simp only [rawSingle, map_smul, translation_single]
  change epsilon D α β • Finsupp.single (α + β)
      (sectorTranslation D (α + β)
        (convolution D α (bilinear D α β) k (translatedPolynomial D α p))) -
    epsilon D α β • Finsupp.single (α + β)
      (convolution D α (bilinear D α β) k
        (translatedPolynomial D α (sectorTranslation D β p))) = _
  rw [← smul_sub, ← Finsupp.single_sub, sector_convolution, ← Finsupp.smul_single,
    smul_comm]
  rfl

/-- Ordinary lattice modes, with the mode shift obtained from the actual field constructor. -/
theorem actual_lattice_translation_covariance (D : LatticeData) (α : Charge D)
    (n : ℤ) :
    translation D * ((actualField D α)[[n]]) -
        ((actualField D α)[[n]]) * translation D =
      -(n : ℂ) • ((actualField D α)[[n - 1]]) := by
  rw [actualField, VertexOperator.ncoeff_of_coeff, VertexOperator.ncoeff_of_coeff]
  have h := rawCoeff_translation D α (-n - 1)
  rw [show -n - 1 + 1 = -(n - 1) - 1 by omega] at h
  simpa only [Int.cast_sub, Int.cast_neg, Int.cast_one, sub_add_cancel] using h

private theorem sector_partial (D : LatticeData) (β : Charge D)
    (j : Fin D.rank) (r : ℕ) (p : Oscillator D) :
    sectorTranslation D β (pderiv (j,r) p) -
      pderiv (j,r) (sectorTranslation D β p) =
        (oscillatorDerivation D (pderiv (j,r) p) -
          pderiv (j,r) (oscillatorDerivation D p)) -
        pderiv (j,r) (chargePolynomial D β) * p := by
  simp only [sector_apply, map_add, Derivation.leibniz, smul_eq_mul]
  ring

private theorem positive_current_commutator (D : LatticeData) (β : Charge D)
    (i : Fin D.rank) (m : ℤ) (p : Oscillator D) :
    sectorTranslation D β
        ((m : ℂ) • ∑ j : Fin D.rank, (D.G i j : ℂ) • pderiv (j,(m-1).toNat) p) -
      (m : ℂ) • ∑ j : Fin D.rank, (D.G i j : ℂ) •
        pderiv (j,(m-1).toNat) (sectorTranslation D β p) =
      (m : ℂ) • ∑ j : Fin D.rank, (D.G i j : ℂ) •
        (sectorTranslation D β (pderiv (j,(m-1).toNat) p) -
          pderiv (j,(m-1).toNat) (sectorTranslation D β p)) := by
  simp only [map_smul, map_sum, smul_sub, Finset.sum_sub_distrib]

private theorem neutral_sector_translation (D : LatticeData) (β : Charge D)
    (i : Fin D.rank) (m : ℤ) (p : Oscillator D) :
    sectorTranslation D β (neutralPolynomialMode D i β m p) -
      neutralPolynomialMode D i β m (sectorTranslation D β p) =
        -(m : ℂ) • neutralPolynomialMode D i β (m - 1) p := by
  classical
  by_cases hm : m < 0
  · have hm1 : m - 1 < 0 := by omega
    have hn : ((-m-1).toNat : ℤ) = -m-1 := Int.toNat_of_nonneg (by omega)
    have hs : (-(m-1)-1).toNat = (-m-1).toNat + 1 := by omega
    simp only [neutralPolynomialMode, if_pos hm, if_pos hm1,
      LinearMap.mulLeft_apply, sector_apply, Derivation.leibniz,
      oscillatorDerivation, MvPolynomial.mkDerivation_X, hs, smul_eq_mul]
    rw [show ((-m-1).toNat + 1 : ℂ) = -(m : ℂ) by
      have h : ((-m-1).toNat : ℂ) = - (m : ℂ) - 1 := by exact_mod_cast hn
      linear_combination h]
    simp only [smul_eq_C_mul]
    ring
  · by_cases hz : m = 0
    · subst m
      simp [neutralPolynomialMode, map_smul]
    · have hp : 0 < m := by omega
      simp only [neutralPolynomialMode, if_neg hm, if_neg hz,
        LinearMap.smul_apply, LinearMap.sum_apply, Derivation.coeFn_coe]
      rw [positive_current_commutator]
      by_cases h1 : m = 1
      · subst m
        simp only [Int.reduceSub, Int.toNat_zero, Int.cast_one,
          one_smul, sector_partial, partial_translation_zero, partial_charge,
          if_true, zero_sub]
        have hb : bilinear D (unitCharge D i) β = ∑ j, D.G i j * β j := by
          simp [bilinear, unitCharge]
        simp only [lt_self_iff_false, if_false,
          LinearMap.smul_apply, LinearMap.id_apply]
        rw [hb]
        simp only [smul_eq_C_mul, C_mul,
          Int.cast_sum, Int.cast_mul, map_sum, Finset.sum_mul]
        simp [mul_comm, mul_assoc]
      · have hm1 : 0 < m - 1 := by omega
        let r := (m - 2).toNat
        have hr : (r : ℤ) = m - 2 := Int.toNat_of_nonneg (by omega)
        have hs : (m - 1).toNat = r + 1 := by omega
        have hrC : (r + 1 : ℂ) = (m - 1 : ℂ) := by
          have h : (r : ℂ) = (m : ℂ) - 2 := by exact_mod_cast hr
          linear_combination h
        simp only [hs, sector_partial, partial_translation_succ, partial_charge,
          Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false,
          zero_mul, sub_zero, hrC]
        simp only [if_neg (by omega : ¬ m - 1 < 0),
          if_neg (by omega : m - 1 ≠ 0), LinearMap.smul_apply,
          LinearMap.sum_apply, Derivation.coeFn_coe, Int.cast_sub, Int.cast_one,
          Finset.smul_sum, smul_smul]
        apply Finset.sum_congr rfl
        intro j hj
        dsimp only [r]
        rw [show m - 1 - 1 = m - 2 by omega]
        congr 1
        ring

/-- All neutral current modes, including the separate positive-mode-one boundary. -/
theorem neutral_translation_covariance (D : LatticeData) (i : Fin D.rank)
    (m : ℤ) :
    translation D * neutralMode D i m - neutralMode D i m * translation D =
      -(m : ℂ) • neutralMode D i (m - 1) := by
  apply Finsupp.lhom_ext
  intro β p
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    neutralMode, Finsupp.lsum_single, LinearMap.comp_apply, Finsupp.lsingle_apply,
    translation_single]
  change Finsupp.single β (sectorTranslation D β (neutralPolynomialMode D i β m p)) -
    Finsupp.single β (neutralPolynomialMode D i β m (sectorTranslation D β p)) = _
  rw [← Finsupp.single_sub, neutral_sector_translation, ← Finsupp.smul_single]

/-- The constructed operator, vacuum and both actual generating families in one contract. -/
theorem actual_translation_generators (D : LatticeData) :
    (∀ (β : Charge D) (p : Oscillator D),
      translation D (Finsupp.single β p) =
        Finsupp.single β (oscillatorDerivation D p + chargePolynomial D β * p)) ∧
    translation D (Finsupp.single (0 : Charge D) (1 : Oscillator D)) = 0 ∧
    (∀ (α : Charge D) (n : ℤ),
      translation D * ((actualField D α)[[n]]) -
          ((actualField D α)[[n]]) * translation D =
        -(n : ℂ) • ((actualField D α)[[n - 1]])) ∧
    (∀ (i : Fin D.rank) (m : ℤ),
      translation D * neutralMode D i m - neutralMode D i m * translation D =
        -(m : ℂ) • neutralMode D i (m - 1)) := by
  exact ⟨translation_single D, translation_vacuum D,
    actual_lattice_translation_covariance D, neutral_translation_covariance D⟩


private theorem inverse_charge_contractions (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (β : Charge D) :
    (∀ i, ∑ j : Fin D.rank, H i j * chargeScalar D β j = (β i : ℂ)) ∧
    (∀ j, ∑ i : Fin D.rank, H i j * chargeScalar D β i = (β j : ℂ)) := by
  classical
  have hcharge (i : Fin D.rank) : chargeScalar D β i =
      ∑ a : Fin D.rank, (D.G i a : ℂ) * (β a : ℂ) := by
    simp [chargeScalar, bilinear, unitCharge, Int.cast_sum]
  have row (i a : Fin D.rank) : ∑ j, H i j * (D.G j a : ℂ) = if i = a then 1 else 0 := by
    simpa [Matrix.mul_apply, gramComplex, Matrix.one_apply] using
      congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℂ => M i a) hHG
  have col (j a : Fin D.rank) : ∑ i, H i j * (D.G i a : ℂ) = if j = a then 1 else 0 := by
    simpa [Matrix.mul_apply, gramComplex, Matrix.one_apply, D.symmetric a,
      mul_comm, eq_comm] using
      congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℂ => M a j) hGH
  constructor
  · intro i
    calc
      _ = ∑ a : Fin D.rank, (∑ j, H i j * (D.G j a : ℂ)) * (β a : ℂ) := by
        simp only [hcharge, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by simp [row]
  · intro j
    calc
      _ = ∑ a : Fin D.rank, (∑ i, H i j * (D.G i a : ℂ)) * (β a : ℂ) := by
        simp only [hcharge, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by simp [col]

/-- The actual minus-one coefficient has precisely the charged ground translation term. -/
theorem sugawaraMode_ground_minus_one (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (β : Charge D) :
    sugawaraMode D H (-1) (Finsupp.single β (1 : Oscillator D)) =
      Finsupp.single β (chargePolynomial D β) := by
  classical
  have inv := inverse_charge_contractions D H hHG hGH β
  have negative (i : Fin D.rank) (p : Oscillator D) :
      neutralMode D i (-1) (Finsupp.single β p) = Finsupp.single β (X (i,0)*p) := by
    simp [neutralPolynomialMode]
  have term (i j : Fin D.rank) :
      normalSummand D i j (-1) 0 (Finsupp.single β 1) +
        normalSummand D i j 0 (-1) (Finsupp.single β 1) =
      chargeScalar D β j • Finsupp.single β (X (i,0)) +
        chargeScalar D β i • Finsupp.single β (X (j,0)) := by
    simp only [normalSummand, show (-1 : ℤ) < 0 by omega, if_true,
      show ¬(0 : ℤ) < 0 by omega, if_false, Module.End.mul_apply,
      neutralMode_zero_single, map_smul, negative, mul_one]
  rw [sugawaraMode_interval_sum, ground_frequency_bound]
  have hI : Finset.Icc (-1 : ℤ) 0 = {-1,0} := by decide
  simp only [Nat.cast_zero, sub_zero, min_eq_right (by omega : (-1 : ℤ) ≤ 0), hI,
    Finset.sum_insert (by decide : (-1 : ℤ) ∉ ({0} : Finset ℤ)), Finset.sum_singleton,
    show (-1 : ℤ)-(-1) = 0 by omega, sub_zero]
  simp_rw [term, smul_add, smul_smul]
  simp only [Finset.sum_add_distrib]
  have first : (∑ i : Fin D.rank, ∑ j : Fin D.rank,
      (H i j * chargeScalar D β j) • Finsupp.single β (X (i,0))) =
      Finsupp.single β (chargePolynomial D β) := by
    simp_rw [← Finset.sum_smul, inv.1]
    simp [chargePolynomial, Finsupp.smul_single, Finsupp.single_finsetSum]
  have second : (∑ i : Fin D.rank, ∑ j : Fin D.rank,
      (H i j * chargeScalar D β i) • Finsupp.single β (X (j,0))) =
      Finsupp.single β (chargePolynomial D β) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, inv.2]
    simp [chargePolynomial, Finsupp.smul_single, Finsupp.single_finsetSum]
  rw [first, second, ← two_smul ℂ, smul_smul]
  norm_num

/-- The actual normal-product coefficient L(-1) is the constructed charge-sensitive translation. -/
theorem sugawaraMode_minus_one_eq_translation (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    sugawaraMode D H (-1) = translation D := by
  apply Finsupp.lhom_ext'
  intro β
  let A : Module.End ℂ (Oscillator D) := sectorSugawaraMode D H β (-1) - sectorTranslation D β
  have hA (i : Fin D.rank) (q : ℤ) :
      A * neutralPolynomialMode D i β q - neutralPolynomialMode D i β q * A = 0 := by
    apply LinearMap.ext
    intro p
    have hL := congrArg (fun F : Module.End ℂ (Carrier D) => (F (Finsupp.single β p)) β)
      (sugawaraMode_current_commutator D H hHG hGH i (-1) q)
    have hT := congrArg (fun F : Module.End ℂ (Carrier D) => (F (Finsupp.single β p)) β)
      (neutral_translation_covariance D i q)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, neutralMode_single,
      sugawaraMode_single_sector, translation_single, Finsupp.sub_apply,
      Finsupp.single_eq_same, LinearMap.smul_apply, Finsupp.smul_apply] at hL hT
    calc
      _ = (sectorSugawaraMode D H β (-1) (neutralPolynomialMode D i β q p) -
      neutralPolynomialMode D i β q (sectorSugawaraMode D H β (-1) p)) -
      (sectorTranslation D β (neutralPolynomialMode D i β q p) -
      neutralPolynomialMode D i β q (sectorTranslation D β p)) := by
        simp only [A, LinearMap.sub_apply, Module.End.mul_apply, map_sub,
          LinearMap.zero_apply]
        abel
      _ = 0 := by
        change _ - (oscillatorDerivation D (neutralPolynomialMode D i β q p) +
          chargePolynomial D β * neutralPolynomialMode D i β q p -
          neutralPolynomialMode D i β q
            (oscillatorDerivation D p + chargePolynomial D β * p)) = 0
        rw [hL, hT, show (-1 : ℤ)+q = q-1 by omega, sub_self]
  have hs := polynomial_current_commutant_scalar D H hHG β A hA
  have hg := congrArg (fun v : Carrier D => v β)
    (sugawaraMode_ground_minus_one D H hHG hGH β)
  simp only [sugawaraMode_single_sector, Finsupp.single_eq_same] at hg
  have hz : A 1 = 0 := by simp [A, hg, sectorTranslation]
  rw [hz, map_zero, zero_smul] at hs
  apply LinearMap.ext
  intro p
  have hp := congrArg (fun F : Module.End ℂ (Oscillator D) => F p) hs
  have he : sectorSugawaraMode D H β (-1) p = sectorTranslation D β p := by
    exact sub_eq_zero.mp hp
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, sugawaraMode_single_sector,
    translation_single, he]
  rfl


/-- The inverse-Gram charge quadratic is the original lattice norm divided by two. -/
theorem chargeQuadratic_eq (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (β : Charge D) :
    chargeQuadratic D H β = (bilinear D β β : ℂ)/2 := by
  classical
  have inv := (inverse_charge_contractions D H hHG hGH β).1
  have hcharge (i : Fin D.rank) : chargeScalar D β i =
      ∑ a : Fin D.rank, (D.G i a : ℂ) * (β a : ℂ) := by
    simp [chargeScalar, bilinear, unitCharge, Int.cast_sum]
  have hsum : (∑ i : Fin D.rank, ∑ j : Fin D.rank,
      H i j * chargeScalar D β i * chargeScalar D β j) = (bilinear D β β : ℂ) := by
    calc
      _ = ∑ i : Fin D.rank, chargeScalar D β i * (∑ j, H i j * chargeScalar D β j) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ∑ i : Fin D.rank, chargeScalar D β i * (β i : ℂ) := by simp_rw [inv]
      _ = _ := by
        simp only [hcharge, bilinear, Int.cast_sum, Int.cast_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
  rw [chargeQuadratic, hsum]
  ring

/-- The actual zero mode is frequency Euler plus the charged lattice norm. -/
theorem sugawaraMode_zero_single (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (β : Charge D) (p : Oscillator D) :
    sugawaraMode D H 0 (Finsupp.single β p) =
      Finsupp.single β
        (oscillatorEuler D p + ((bilinear D β β : ℂ)/2) • p) := by
  let A : Module.End ℂ (Oscillator D) := sectorSugawaraMode D H β 0 - (oscillatorEuler D).toLinearMap
  have hA (i : Fin D.rank) (q : ℤ) :
      A * neutralPolynomialMode D i β q - neutralPolynomialMode D i β q * A = 0 := by
    have hL : sectorSugawaraMode D H β 0 * neutralPolynomialMode D i β q -
        neutralPolynomialMode D i β q * sectorSugawaraMode D H β 0 =
          -(q : ℂ) • neutralPolynomialMode D i β q := by
      apply LinearMap.ext
      intro p
      have h := congrArg (fun F : Module.End ℂ (Carrier D) => (F (Finsupp.single β p)) β)
        (sugawaraMode_current_commutator D H hHG hGH i 0 q)
      simpa only [LinearMap.sub_apply, Module.End.mul_apply, neutralMode_single,
        sugawaraMode_single_sector, Finsupp.sub_apply, Finsupp.single_eq_same,
        LinearMap.smul_apply, Finsupp.smul_apply, zero_add] using h
    calc
      _ = (sectorSugawaraMode D H β 0 * neutralPolynomialMode D i β q -
          neutralPolynomialMode D i β q * sectorSugawaraMode D H β 0) -
        ((oscillatorEuler D).toLinearMap * neutralPolynomialMode D i β q -
          neutralPolynomialMode D i β q * (oscillatorEuler D).toLinearMap) := by
        dsimp only [A]
        noncomm_ring
      _ = 0 := by rw [hL, oscillatorEuler_current, sub_self]
  have hs := polynomial_current_commutant_scalar D H hHG β A hA
  have hg := congrArg (fun v : Carrier D => v β) (sugawaraMode_ground_zero D H β)
  simp only [sugawaraMode_single_sector, Finsupp.smul_single, Finsupp.single_eq_same] at hg
  have hz : constantCoeff (A 1) = chargeQuadratic D H β := by simp [A, hg]
  rw [hz, chargeQuadratic_eq D H hHG hGH] at hs
  have hp := congrArg (fun F : Module.End ℂ (Oscillator D) => F p) hs
  have he : sectorSugawaraMode D H β 0 p =
      oscillatorEuler D p + ((bilinear D β β : ℂ)/2) • p := by
    simpa only [LinearMap.smul_apply, Module.End.one_apply, Derivation.coeFn_coe] using
      sub_eq_iff_eq_add'.mp hp
  rw [sugawaraMode_single_sector, he]


private theorem oscillatorEuler_monomial (D : LatticeData) (d : Index D →₀ ℕ) (c : ℂ) :
    oscillatorEuler D (monomial d c) =
      ((Finsupp.weight (fun x : Index D => x.2+1) d : ℕ) : ℂ) • monomial d c := by
  classical
  rw [oscillatorEuler, mkDerivation_monomial]
  have term (x : Index D) :
      monomial (d-Finsupp.single x 1) (d x : ℂ) • ((x.2+1 : ℂ) • X x) =
        ((x.2+1 : ℂ)*(d x : ℂ)) • (monomial d (1 : ℂ) : Oscillator D) := by
    have h := X_mul_pderiv_monomial (i := x) (m := d) (r := (1 : ℂ))
    simp only [pderiv_monomial, one_mul] at h
    change monomial (d-Finsupp.single x 1) (d x : ℂ) * ((x.2+1 : ℂ) • X x) = _
    rw [mul_smul_comm, mul_comm _ (X x), h]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  simp_rw [Finsupp.sum, term, ← Finset.sum_smul]
  have weight : (∑ x ∈ d.support, (x.2+1 : ℂ)*(d x : ℂ)) =
      ((Finsupp.weight (fun x : Index D => x.2+1) d : ℕ) : ℂ) := by
    simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Nat.cast_sum,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [weight, smul_comm c]
  simp [smul_monomial]

/-- Weighted homogeneous oscillators have the frequency degree plus their charged norm. -/
theorem sugawaraMode_weighted_homogeneous (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (β : Charge D) (p : Oscillator D) (r : ℕ)
    (hp : IsWeightedHomogeneous (fun x : Index D => x.2+1) p r) :
    sugawaraMode D H 0 (Finsupp.single β p) =
      ((r : ℂ)+(bilinear D β β : ℂ)/2) • Finsupp.single β p := by
  classical
  have hEuler : oscillatorEuler D p = (r : ℂ) • p := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
    calc
      _ = ∑ d ∈ p.support, (r : ℂ) • monomial d (coeff d p) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [oscillatorEuler_monomial, hp (mem_support_iff.mp hd)]
      _ = _ := by rw [← Finset.smul_sum, ← p.as_sum]
  rw [sugawaraMode_zero_single D H hHG hGH, hEuler, ← add_smul, Finsupp.smul_single]

/-- The actual Virasoro modes act as conformal translation on both genuine generating families. -/
theorem actual_conformal_generators (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    (∀ m n : ℤ, sugawaraMode D H m * sugawaraMode D H n -
      sugawaraMode D H n * sugawaraMode D H m =
      ((m-n : ℤ) : ℂ) • sugawaraMode D H (m+n) +
        (if m+n = 0 then (D.rank : ℂ)/12*((m : ℂ)^3-m) else 0) •
          (1 : Module.End ℂ (Carrier D))) ∧
    (∀ (β : Charge D) (p : Oscillator D),
      sugawaraMode D H 0 (Finsupp.single β p) =
        Finsupp.single β
        (oscillatorEuler D p + ((bilinear D β β : ℂ)/2) • p)) ∧
    (∀ (β : Charge D) (p : Oscillator D),
      sugawaraMode D H (-1) (Finsupp.single β p) =
        Finsupp.single β (oscillatorDerivation D p + chargePolynomial D β * p)) ∧
    sugawaraMode D H (-1) (Finsupp.single (0 : Charge D) (1 : Oscillator D)) = 0 ∧
    (∀ (α : Charge D) (n : ℤ),
      sugawaraMode D H (-1) * ((actualField D α)[[n]]) -
        ((actualField D α)[[n]]) * sugawaraMode D H (-1) =
        -(n : ℂ) • ((actualField D α)[[n-1]])) ∧
    (∀ (i : Fin D.rank) (q : ℤ),
      sugawaraMode D H (-1) * neutralMode D i q -
        neutralMode D i q * sugawaraMode D H (-1) =
        -(q : ℂ) • neutralMode D i (q-1)) ∧
    (∀ (β : Charge D) (p : Oscillator D) (r : ℕ),
      IsWeightedHomogeneous (fun x : Index D => x.2+1) p r →
      sugawaraMode D H 0 (Finsupp.single β p) =
        ((r : ℂ)+(bilinear D β β : ℂ)/2) • Finsupp.single β p) := by
  constructor
  · exact sugawaraMode_virasoro D H hHG hGH
  · constructor
    · exact sugawaraMode_zero_single D H hHG hGH
    · rw [sugawaraMode_minus_one_eq_translation D H hHG hGH]
      have g := actual_translation_generators D
      exact ⟨g.1, g.2.1, g.2.2.1, g.2.2.2,
        sugawaraMode_weighted_homogeneous D H hHG hGH⟩

end
end D5.S3.VertexAlgebra.LatticeSugawaraConformal
