/- GID: D5/S3/VertexAlgebra/LatticeSugawaraCurrents
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeSugawaraCurrents
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual lattice current laws and statewise finite coefficients of the matrix Sugawara field. -/

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

proof_shape: sugawaraMode_interval_sum: content
proof_shape: sugawaraMode_current_commutator: content
admission_basis: escape-witness
escape_witness: The normal-minus-one coefficient is identified with the
statewise finite integer-indexed normal sum; its current commutator contracts
both exceptional indices on the actual all-charge carrier.
proof_shape: neutralPolynomialMode_positive: bind-only; consumed by
neutralPolynomialMode_heisenberg and polynomial_current_commutant_scalar
proof_shape: neutralPolynomialMode_negative: bind-only; consumed by
neutralPolynomialMode_heisenberg and polynomial_current_commutant_scalar
proof_shape: normalSummand_finite: bind-only; consumed by
quadraticSummand_coefficient and sugawaraMode_single_sector
proof_shape: sugawaraMode_coefficient_sum: bind-only; consumed by
sugawaraMode_current_commutator and eulerMode_sugawara_commutator
The cross-module consumers belong to this same conformal construction.
The frozen private partials_commute is applied directly, without reproof.
Utility is none: these are general operator and finite-support identities,
not bounded enumeration, a checker, numerical reduction or a certified instance.
-/

import D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
import D5.S3.VertexAlgebra.FieldNormalProduct
import D5.S3.Quantum.Algebra.ConditionalPolynomialRigidity
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeSugawaraCurrents

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

theorem neutralPolynomialMode_positive (D : LatticeData) (i : Fin D.rank)
    (β : Charge D) (a : ℕ) :
    neutralPolynomialMode D i β ((a : ℤ) + 1) = (a + 1 : ℂ) • weightedPartial D i a := by
  simp [neutralPolynomialMode, weightedPartial,
    show ¬ (a : ℤ) + 1 < 0 by omega, show (a : ℤ) + 1 ≠ 0 by omega,
    Int.cast_add, Int.cast_natCast]

theorem neutralPolynomialMode_negative (D : LatticeData) (i : Fin D.rank)
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

theorem normalSummand_finite (D : LatticeData) (i j : Fin D.rank)
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

theorem sugawaraMode_coefficient_sum (D : LatticeData)
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

end
end D5.S3.VertexAlgebra.LatticeSugawaraCurrents
