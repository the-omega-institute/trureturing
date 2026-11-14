/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalNormalRowSource
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original three-slot normal Gaussian Laurent coefficients and charged correction convolution. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
import D5.S3.VertexAlgebra.TwistedGround.OriginalChargedRowSource
import D5.S3.VertexAlgebra.TwistedGround.ElementaryGaussianContraction
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
Original signed normal-current coefficients equal finite three-slot affine
Gaussian Laurent coefficients. The charged-Corr convolution uses the original
operators and detector, with occupation bounds rather than frequency cutoffs.
Attribution: the imported lattice/half-Fock suppliers retain their FLM,
Dong--Nagatomo and Bakalov--Kac sources. Finite Gaussian and factorial Fock
calculus are classical; their composition here is repository-derived.
-/

/-
Proposed content witnesses: seedEntry_gaussian and entry_gaussian compare actual
charged-seed and signed-current coefficients with Gaussian moments by occupation
induction. Bind-only helpers have actual proof consumers; proposed admission
basis is escape-witness, pending independent review. Utility none: general
identities with unbounded occupations and integer modes, not enumeration,
checkers, numerical reductions or certified instances. No novelty is asserted.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource

open MvPolynomial LatticeGeneratingFieldLocality
open LatticeHalfFock LatticeActualAnnihilation
open LatticeHalfFockChargedCoefficients LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField SignedOscillatorWick OriginalFourMChargeCoset
open NativeGaussianMoment (nativeMoment nativeMoment_step sub_single_degree occupation_nonzero)
open FactorialFockQuadraticEstimate (gaussianCoefficient gaussianCoefficient_zero)
open FactorialFockMetric (weight)
open ElementaryGaussianContraction (leftKernel step_left left_symm left_vanish)
open OriginalChargedRowSource
open D5.S3.VertexAlgebra.SignedOscillatorWick (wick_constant_left creation_constant)
open D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField (wordField_perm)

universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

/-- An honest finite Laurent coefficient: every occupation has its forced
sum of variable weights. No original row is used in this definition. -/
def affineLaurent (A : Matrix I I ℂ) (mu : I → ℂ) (w : I → ℤ)
    (d : I →₀ ℕ) : ℤ →₀ ℂ :=
  Finsupp.single (Finsupp.weight w d) (affineCoefficient A mu d)

private def gradedMoment (A : Matrix I I ℂ) (mu : I → ℂ) (w : I → ℤ)
    (d : I →₀ ℕ) (n : ℤ) : ℂ :=
  if n = Finsupp.weight w d then affineMoment A mu d else 0

private theorem gradedMoment_coefficient (A : Matrix I I ℂ) (mu : I → ℂ)
    (w : I → ℤ) (d : I →₀ ℕ) (n : ℤ) :
    gradedMoment A mu w d n = (weight d : ℂ) * affineLaurent A mu w d n := by
  classical
  simp only [gradedMoment, affineLaurent, Finsupp.single_apply]
  by_cases h : n = Finsupp.weight w d
  · simp only [h, ite_true, affineMoment_coefficient]
  · simp only [h, Ne.symm h, ite_false, mul_zero]

private theorem weight_sub (w : I → ℤ) (d : I →₀ ℕ) (j : I) (hj : d j ≠ 0) :
    Finsupp.weight w (d - Finsupp.single j 1) + w j = Finsupp.weight w d := by
  classical
  have h := congrArg (Finsupp.weight w) (Finsupp.sub_add_single_one_cancel hj)
  simpa only [map_add, Finsupp.weight_single, one_smul] using h

/-- The Laurent shifts are derived from the weight of each inserted singleton
or pair. Terms with zero multiplicity are removed before truncated subtraction. -/
private theorem gradedMoment_step (A : Matrix I I ℂ) (mu : I → ℂ)
    (hs : ∀ i j, A i j = A j i) (w : I → ℤ) (d : I →₀ ℕ) (i : I) (n : ℤ) :
    gradedMoment A mu w (d + Finsupp.single i 1) n =
      mu i * gradedMoment A mu w d (n - w i) +
      ∑ j, (d j : ℂ) * A i j *
        gradedMoment A mu w (d - Finsupp.single j 1) (n - w i - w j) := by
  classical
  have ht : Finsupp.weight w (d + Finsupp.single i 1) =
      Finsupp.weight w d + w i := by simp only [map_add, Finsupp.weight_single, one_smul]
  by_cases hn : n = Finsupp.weight w d + w i
  · have hm : n - w i = Finsupp.weight w d := by omega
    rw [gradedMoment, ht, if_pos hn, affineMoment_step A mu hs]
    rw [gradedMoment, if_pos hm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hz : d j = 0
    · simp only [hz, Nat.cast_zero, zero_mul]
    · have hw := weight_sub w d j hz
      have hp : n - w i - w j = Finsupp.weight w (d - Finsupp.single j 1) := by omega
      rw [gradedMoment, if_pos hp]
  · have hm : n - w i ≠ Finsupp.weight w d := by omega
    rw [gradedMoment, ht, if_neg hn, gradedMoment, if_neg hm, mul_zero, zero_add]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hz : d j = 0
    · simp only [hz, Nat.cast_zero, zero_mul]
    · have hw := weight_sub w d j hz
      have hp : n - w i - w j ≠ Finsupp.weight w (d - Finsupp.single j 1) := by omega
      rw [gradedMoment, if_neg hp, mul_zero]

private theorem annihilate_monomial (D : LatticeData) (i : Fin D.rank) (n : ℕ)
    (d : Index D →₀ ℕ) :
    annihilate D i n (monomial d 1) =
      ∑ j : Fin D.rank, ((d (j,n) : ℂ) * (D.G i j : ℂ)) •
        (monomial (d - Finsupp.single (j,n) 1) 1 : Oscillator D) := by
  classical
  simp only [annihilate, LatticeSugawaraCurrents.weightedPartial,
    LinearMap.sum_apply, LinearMap.smul_apply, Derivation.coeFn_coe,
    pderiv_monomial, one_mul, smul_monomial, smul_eq_mul, mul_one]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  ring

/-- Product reindexing is justified by the actual statewise support BEFORE
curry or current simplification. There is no finsum in Module.End. -/
private theorem wick_word_head (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (b : Index D) (w : List (Index D)) (e : ℤ)
    (p x : Oscillator D) :
    wick D p (oscillatorWord D hu a (b :: w) e x) =
      ∑ᶠ m : ℤ, frequency m * jetScalar b.2 m *
        if m < 0 then
          wick D (annihilate D b.1 (-m-1).toNat p)
            (oscillatorWord D hu a w (e+2*m+2*b.2+3) x)
        else
          wick D p (oscillatorWord D hu a w (e+2*m+2*b.2+3)
            (annihilate D b.1 m.toNat x)) := by
  classical
  have hs := oscillatorFlat_finite D hu a (b :: w) e x
  have hp : Function.HasFiniteSupport (fun modes : ℤ × ModeTuple D w =>
      wick D p (oscillatorFlat D a (b :: w) modes e x)) :=
    hs.subset (by intro modes hm hz; exact hm (by simpa [hz]))
  change wick D p (∑ᶠ modes : ℤ × ModeTuple D w,
    oscillatorFlat D a (b :: w) modes e x) = _
  rw [map_finsum _ hs, finsum_curry _ hp]
  apply finsum_congr
  intro m
  simp_rw [wick_flat_cons, ← jet_mixed]
  by_cases hm : m < 0
  · simp only [if_pos hm]
    change _ = frequency m * jetScalar b.2 m *
      wick D (annihilate D b.1 (-m-1).toNat p)
        (∑ᶠ modes : ModeTuple D w, oscillatorFlat D a w modes (e+2*m+2*b.2+3) x)
    rw [map_finsum _ (oscillatorFlat_finite D hu a w _ x), mul_finsum]
  · simp only [if_neg hm]
    change _ = frequency m * jetScalar b.2 m * wick D p
      (∑ᶠ modes : ModeTuple D w, oscillatorFlat D a w modes (e+2*m+2*b.2+3)
        (annihilate D b.1 m.toNat x))
    rw [map_finsum _ (oscillatorFlat_finite D hu a w _ _), mul_finsum]

/-- Positive modes and colours are reindexed together; coefficients which
vanish do not create spurious inverse-image requirements. -/
private theorem positive_reindex (D : LatticeData) (d : Index D →₀ ℕ)
    (B : Finset ℤ) (hB : d.support.image (fun j => (j.2 : ℤ)) ⊆ B)
    (F : ℤ → Fin D.rank → ℂ) :
    (∑ m ∈ B, ∑ c : Fin D.rank, if m < 0 then 0 else
      (d (c,m.toNat) : ℂ) * F m c) =
      ∑ j ∈ d.support, (d j : ℂ) * F (j.2 : ℤ) j.1 := by
  classical
  rw [← Finset.sum_product' B (Finset.univ : Finset (Fin D.rank))]
  refine Finset.sum_bij_ne_zero (fun mc _ _ => (mc.2,mc.1.toNat)) ?_ ?_ ?_ ?_
  · intro mc hmc hn
    have hm : ¬ mc.1 < 0 := by intro hh; simp [hh] at hn
    apply Finsupp.mem_support_iff.mpr
    intro hz
    simp [hz, hm] at hn
  · intro mc hmc hn nd hnd hn' he
    have hm : ¬ mc.1 < 0 := by intro hh; simp [hh] at hn
    have hnd' : ¬ nd.1 < 0 := by intro hh; simp [hh] at hn'
    have hc := congrArg Prod.fst he
    have hk := congrArg Prod.snd he
    have h₁ := Int.toNat_of_nonneg (by omega : 0 ≤ mc.1)
    have h₂ := Int.toNat_of_nonneg (by omega : 0 ≤ nd.1)
    exact Prod.ext (by omega) hc
  · intro j hj hn
    refine ⟨((j.2 : ℤ),j.1), Finset.mem_product.mpr
      ⟨hB (Finset.mem_image.mpr ⟨j,hj,rfl⟩), Finset.mem_univ _⟩, ?_, ?_⟩
    · simpa only [if_neg (show ¬ (j.2 : ℤ) < 0 by omega), Int.toNat_natCast] using hn
    · simp
  · intro mc hmc hn
    have hm : ¬ mc.1 < 0 := by intro hh; simp [hh] at hn
    have he := Int.toNat_of_nonneg (by omega : 0 ≤ mc.1)
    simp only [if_neg hm, he]

private theorem negative_reindex (D : LatticeData) (d : Index D →₀ ℕ)
    (B : Finset ℤ) (hB : d.support.image (fun j => -(j.2 : ℤ)-1) ⊆ B)
    (F : ℤ → Fin D.rank → ℂ) :
    (∑ m ∈ B, ∑ c : Fin D.rank, if m < 0 then
      (d (c,(-m-1).toNat) : ℂ) * F m c else 0) =
      ∑ j ∈ d.support, (d j : ℂ) * F (-(j.2 : ℤ)-1) j.1 := by
  classical
  rw [← Finset.sum_product' B (Finset.univ : Finset (Fin D.rank))]
  refine Finset.sum_bij_ne_zero (fun mc _ _ => (mc.2,(-mc.1-1).toNat)) ?_ ?_ ?_ ?_
  · intro mc hmc hn
    have hm : mc.1 < 0 := by by_contra hh; simp [hh] at hn
    have hidx : (-mc.1-1).toNat = (-mc.1).toNat - 1 := by omega
    apply Finsupp.mem_support_iff.mpr
    intro hz
    have hz' : d (mc.2, (-mc.1).toNat - 1) = 0 := by simpa [hidx] using hz
    have hprod : (d (mc.2, (-mc.1).toNat - 1) : ℂ) * F mc.1 mc.2 ≠ 0 := by
      simpa [hm, hidx] using hn
    have hcast : (d (mc.2, (-mc.1).toNat - 1) : ℂ) ≠ 0 := by
      intro hzero
      exact hprod (by rw [hzero, zero_mul])
    have hnat : d (mc.2, (-mc.1).toNat - 1) ≠ 0 := by exact_mod_cast hcast
    exact hnat hz'
  · intro mc hmc hn nd hnd hn' he
    have hm : mc.1 < 0 := by by_contra hh; simp [hh] at hn
    have hnd' : nd.1 < 0 := by by_contra hh; simp [hh] at hn'
    have hc := congrArg Prod.fst he
    have hk := congrArg Prod.snd he
    have h₁ := Int.toNat_of_nonneg (by omega : 0 ≤ -mc.1-1)
    have h₂ := Int.toNat_of_nonneg (by omega : 0 ≤ -nd.1-1)
    exact Prod.ext (by omega) hc
  · intro j hj hn
    refine ⟨(-(j.2 : ℤ)-1,j.1), Finset.mem_product.mpr
      ⟨hB (Finset.mem_image.mpr ⟨j,hj,rfl⟩), Finset.mem_univ _⟩, ?_, ?_⟩
    · simpa only [show -(j.2 : ℤ)-1 < 0 by omega, ite_true,
        show (-(-(j.2 : ℤ)-1)-1).toNat = j.2 by omega] using hn
    · simp
  · intro mc hmc hn
    have hm : mc.1 < 0 := by by_contra hh; simp [hh] at hn
    have he : -(((-mc.1-1).toNat : ℕ) : ℤ)-1 = mc.1 := by omega
    simp only [if_pos hm, he]

/-- Actual finite normal-current insertion, including every negative label,
all Gram colours, and the literal exponent shifts. This is consumed below. -/
private theorem wick_word_finite_step (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (b : Index D) (w : List (Index D)) (e : ℤ)
    (beta gamma : Index D →₀ ℕ) :
    wick D (monomial gamma 1)
        (oscillatorWord D hu a (b :: w) e (monomial beta 1)) =
      (∑ j ∈ gamma.support, (gamma j : ℂ) *
        (-frequency (j.2 : ℤ) * jetScalar b.2 (-(j.2 : ℤ)-1) * (D.G b.1 j.1 : ℂ)) *
        wick D (monomial (gamma - Finsupp.single j 1) 1)
          (oscillatorWord D hu a w (e-2*j.2+2*b.2+1) (monomial beta 1))) +
      ∑ j ∈ beta.support, (beta j : ℂ) *
        (frequency (j.2 : ℤ) * jetScalar b.2 (j.2 : ℤ) * (D.G b.1 j.1 : ℂ)) *
        wick D (monomial gamma 1) (oscillatorWord D hu a w (e+2*j.2+2*b.2+3)
          (monomial (beta - Finsupp.single j 1) 1)) := by
  classical
  let B := gamma.support.image (fun j => -(j.2 : ℤ)-1) ∪
    beta.support.image (fun j => (j.2 : ℤ))
  let Fneg := fun m c => frequency m * jetScalar b.2 m * (D.G b.1 c : ℂ) *
    wick D (monomial (gamma - Finsupp.single (c,(-m-1).toNat) 1) 1)
      (oscillatorWord D hu a w (e+2*m+2*b.2+3) (monomial beta 1))
  let Fpos := fun m c => frequency m * jetScalar b.2 m * (D.G b.1 c : ℂ) *
    wick D (monomial gamma 1) (oscillatorWord D hu a w (e+2*m+2*b.2+3)
      (monomial (beta - Finsupp.single (c,m.toNat) 1) 1))
  let f := fun m =>
    (∑ c : Fin D.rank, if m < 0 then (gamma (c,(-m-1).toNat) : ℂ) * Fneg m c else 0) +
    ∑ c : Fin D.rank, if m < 0 then 0 else (beta (c,m.toNat) : ℂ) * Fpos m c
  rw [wick_word_head]
  have hf : (fun m : ℤ => frequency m * jetScalar b.2 m *
      if m < 0 then wick D (annihilate D b.1 (-m-1).toNat (monomial gamma 1))
        (oscillatorWord D hu a w (e+2*m+2*b.2+3) (monomial beta 1))
      else wick D (monomial gamma 1) (oscillatorWord D hu a w (e+2*m+2*b.2+3)
        (annihilate D b.1 m.toNat (monomial beta 1)))) = f := by
    funext m
    by_cases hm : m < 0
    · simp only [f, if_pos hm, Finset.sum_const_zero, add_zero, annihilate_monomial,
        map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
        Finset.mul_sum, Fneg]
      apply Finset.sum_congr rfl
      intro c hc
      ring
    · simp only [f, if_neg hm, Finset.sum_const_zero, zero_add, annihilate_monomial,
        map_sum, map_smul, smul_eq_mul, Finset.mul_sum, Fpos]
      apply Finset.sum_congr rfl
      intro c hc
      ring
  rw [hf]
  have hs : Function.support f ⊆ B := by
    intro m hm
    by_contra hout
    have hneg (hn : m < 0) : ∀ c : Fin D.rank, gamma (c,(-m-1).toNat) = 0 := by
      intro c
      by_contra hz
      apply hout
      apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨(c,(-m-1).toNat), Finsupp.mem_support_iff.mpr hz, ?_⟩
      dsimp
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ -m-1)]
      omega
    have hpos : ∀ c : Fin D.rank, m < 0 ∨ beta (c,m.toNat) = 0 := by
      intro c
      by_cases hn : m < 0
      · exact Or.inl hn
      · right
        by_contra hz
        apply hout
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨(c,m.toNat), Finsupp.mem_support_iff.mpr hz,
          Int.toNat_of_nonneg (by omega)⟩
    apply hm
    dsimp [f]
    by_cases hn : m < 0
    · simp only [if_pos hn, hneg hn, Nat.cast_zero, zero_mul,
        Finset.sum_const_zero, add_zero]
    · have hz : ∀ c, beta (c,m.toNat) = 0 := fun c => (hpos c).resolve_left hn
      simp only [if_neg hn, hz, Nat.cast_zero, zero_mul,
        Finset.sum_const_zero, zero_add]
  rw [finsum_eq_sum_of_support_subset _ hs]
  change (∑ m ∈ B, (_ + _)) = _
  rw [Finset.sum_add_distrib,
    negative_reindex D gamma B Finset.subset_union_left Fneg,
    positive_reindex D beta B Finset.subset_union_right Fpos]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    dsimp [Fneg]
    rw [frequency_opposite]
    have he : e+2*(-(j.2 : ℤ)-1)+2*b.2+3 = e-2*j.2+2*b.2+1 := by omega
    rw [he]
    simp only [show (-(-(j.2 : ℤ)-1)-1).toNat = j.2 by omega]
    ring
  · apply Finset.sum_congr rfl
    intro j hj
    simp only [Fpos, Int.toNat_natCast]
    ring
private theorem oscillatorWord_perm (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (w v : List (Index D)) (h : w.Perm v) (e : ℤ)
    (x : Oscillator D) : oscillatorWord D hu a w e x = oscillatorWord D hu a v e x := by
  classical
  let oneGround : ActualGround D hu := fun _ => 1
  let g := groundRepresentation D hu (groundLift D a)⁻¹ oneGround
  have hg : groundAction D hu a g = oneGround :=
    (groundRepresentation D hu).self_inv_apply (groundLift D a) oneGround
  have hf := wordField_perm D hu (chargedField D hu a) w v h
  have he := congrArg (fun F : NativeField D hu =>
    oscillatorCoordinate D hu (F.coeff e (x ⊗ₜ[ℂ] g))) hf
  rw [word_tmul, word_tmul, map_smul, map_smul, hg,
    oscillatorCoordinate_tmul, oscillatorCoordinate_tmul] at he
  have hc : chargeScalar D a ≠ 0 := zpow_ne_zero _ (by norm_num)
  apply smul_right_injective (Oscillator D) hc
  simpa only [oneGround, one_smul] using he

private theorem normal_monomial (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (d : Index D →₀ ℕ) (e : ℤ) :
    oscillatorNormal D hu a e (monomial d 1) =
      oscillatorWord D hu a (occurrences D d) e :=
  (basisMonomials (Index D) ℂ).constr_basis ℂ _ d

private theorem normal_insert (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (d : Index D →₀ ℕ) (b : Index D) (e : ℤ)
    (x : Oscillator D) :
    oscillatorNormal D hu a e (monomial (d + Finsupp.single b 1) 1) x =
      oscillatorWord D hu a (b :: occurrences D d) e x := by
  classical
  have hp : (b :: occurrences D d).Perm (occurrences D (d + Finsupp.single b 1)) := by
    apply Multiset.coe_eq_coe.mp
    simp [occurrences, Finsupp.toMultiset_add, Finsupp.toMultiset_single,
      ← Multiset.cons_coe, Multiset.coe_toList, add_comm]
  rw [normal_monomial]
  exact (oscillatorWord_perm D hu a _ _ hp e x).symm

private theorem normal_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (e : ℤ) (x : Oscillator D) :
    oscillatorNormal D hu a e (monomial 0 1) x = oscillatorCoefficient D a e x := by
  classical
  rw [normal_monomial]
  have hempty : occurrences D (0 : Index D →₀ ℕ) = [] := by
    simp only [occurrences, Finsupp.toMultiset_zero, Multiset.toList_zero]
  rw [hempty]
  change (∑ᶠ _ : Unit, oscillatorCoefficient D a e x) = oscillatorCoefficient D a e x
  exact finsum_unique _

private theorem wick_normal_step (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (d beta gamma : Index D →₀ ℕ) (b : Index D) (e : ℤ) :
    wick D (monomial gamma 1)
        (oscillatorNormal D hu a e (monomial (d + Finsupp.single b 1) 1) (monomial beta 1)) =
      (∑ j ∈ gamma.support, (gamma j : ℂ) *
        (-frequency (j.2 : ℤ) * jetScalar b.2 (-(j.2 : ℤ)-1) * (D.G b.1 j.1 : ℂ)) *
        wick D (monomial (gamma - Finsupp.single j 1) 1)
          (oscillatorNormal D hu a (e-2*j.2+2*b.2+1) (monomial d 1) (monomial beta 1))) +
      ∑ j ∈ beta.support, (beta j : ℂ) *
        (frequency (j.2 : ℤ) * jetScalar b.2 (j.2 : ℤ) * (D.G b.1 j.1 : ℂ)) *
        wick D (monomial gamma 1) (oscillatorNormal D hu a (e+2*j.2+2*b.2+3)
          (monomial d 1) (monomial (beta - Finsupp.single j 1) 1)) := by
  classical
  rw [normal_insert, wick_word_finite_step]
  simp only [normal_monomial]

/-- The direct IO block in the ORIGINAL colour coordinates. -/
def IO (D : LatticeData) (b c : Index D) : ℂ :=
  if b.2 = c.2 then -frequency (b.2 : ℤ) * (D.G b.1 c.1 : ℂ) else 0

private theorem annihilate_supported (D : LatticeData) (b : Index D)
    (d : Index D →₀ ℕ) :
    -frequency (b.2 : ℤ) • annihilate D b.1 b.2 (monomial d 1) =
      ∑ j ∈ d.support, ((d j : ℂ) * IO D b j) •
        (monomial (d - Finsupp.single j 1) 1 : Oscillator D) := by
  classical
  let f := fun j : Index D => (if b.2 = j.2 then (D.G b.1 j.1 : ℂ) else 0) •
    (1 : Oscillator D)
  have hd : annihilationDerivation D b.1 b.2 = mkDerivation ℂ f := by
    apply derivation_ext
    intro j
    rw [annihilation_apply, annihilate_X, mkDerivation_X]
    simp only [f, smul_ite, zero_smul]
    split_ifs <;> simp
  rw [← annihilation_apply, hd, mkDerivation_monomial]
  simp only [one_smul, Finsupp.sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : b.2 = j.2
  · simp only [f, if_pos h, IO, if_pos h]
    rw [smul_comm (monomial (d - Finsupp.single j 1) (d j : ℂ) : Oscillator D)
      (D.G b.1 j.1 : ℂ)]
    simp only [smul_eq_mul, mul_one, smul_smul, smul_monomial]
    congr 1
    ring
  · simp only [f, if_neg h, zero_smul, smul_zero, IO, if_neg h, mul_zero]

private theorem wick_creator_right (D : LatticeData) (b : Index D)
    (gamma : Index D →₀ ℕ) (x : Oscillator D) :
    wick D (monomial gamma 1) (X b * x) =
      ∑ j ∈ gamma.support, (gamma j : ℂ) * IO D b j *
        wick D (monomial (gamma - Finsupp.single j 1) 1) x := by
  classical
  rw [← wick_lowering, annihilate_supported]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]

private theorem seed_input_step (D : LatticeData) (a : Charge D)
    (beta gamma : Index D →₀ ℕ) (b : Index D) (e : ℤ) :
    wick D (monomial gamma 1) (oscillatorCoefficient D a e
        (monomial (beta + Finsupp.single b 1) 1)) =
      -(bilinear D a (unitCharge D b.1) : ℂ) *
        wick D (monomial gamma 1)
          (oscillatorCoefficient D a (e + omega D b) (monomial beta 1)) +
      ∑ j ∈ gamma.support, (gamma j : ℂ) * IO D b j *
        wick D (monomial (gamma - Finsupp.single j 1) 1)
          (oscillatorCoefficient D a e (monomial beta 1)) := by
  classical
  have hm : (monomial (beta + Finsupp.single b 1) 1 : Oscillator D) =
      X b * monomial beta 1 := by simp only [X, monomial_mul_monomial, one_mul, add_comm]
  rw [hm, oscillator_coefficient_X_mul]
  simp only [map_sub, map_smul, smul_eq_mul, wick_creator_right]
  ring

private theorem oscillator_vacuum (D : LatticeData) (a : Charge D) (e : ℤ) :
    oscillatorCoefficient D a e (1 : Oscillator D) = halfCreationCoeff D a (e+chargeNorm D a) := by
  classical
  change (∑ᶠ r : ℕ, oscillatorTerm D a e 1 r) = _
  rw [finsum_eq_sum_of_support_subset _ (term_support D a e 1)]
  have hp : halfTranslatedPolynomial D a (1 : Oscillator D) =
      (1 : Polynomial (Oscillator D)) := by simp [halfTranslatedPolynomial]
  rw [hp]
  have hsupp : (1 : Polynomial (Oscillator D)).support = {0} := by
    rw [show (1 : Polynomial (Oscillator D)) = Polynomial.C 1 by simp,
      Polynomial.support_C one_ne_zero]
  rw [hsupp]
  simp [halfTranslatedPolynomial, oscillatorTerm]

/-- The output mean is derived from the real creation series and Wick sign:
(-frequency n) * 2/(2n+1) = -1. No coherent-source mean is a premise. -/
private theorem seed_output_only_step (D : LatticeData) (a : Charge D)
    (gamma : Index D →₀ ℕ) (b : Index D) (e : ℤ) :
    wick D (monomial (gamma + Finsupp.single b 1) 1)
        (oscillatorCoefficient D a e 1) =
      -(bilinear D a (unitCharge D b.1) : ℂ) *
        wick D (monomial gamma 1) (oscillatorCoefficient D a (e-omega D b) 1) := by
  classical
  have hm : (monomial (gamma + Finsupp.single b 1) 1 : Oscillator D) =
      X b * monomial gamma 1 := by simp only [X, monomial_mul_monomial, one_mul, add_comm]
  have hs : -frequency (b.2 : ℤ) * (2 / (2*b.2+1 : ℂ)) = -1 := by
    have hn : (2*b.2+1 : ℂ) ≠ 0 := by exact_mod_cast (show 2*b.2+1 ≠ 0 by omega)
    rw [← mul_div_assoc, div_eq_iff hn]
    simp only [frequency, Int.cast_natCast]
    ring
  rw [hm, oscillator_vacuum, wick_creation, half_annihilation_creation]
  rw [LatticeFiniteNegativeGeneration.bilinear_symmetric D (unitCharge D b.1) a]
  simp only [map_smul, smul_smul, smul_eq_mul, mul_assoc]
  rw [← mul_assoc, hs]
  rw [oscillator_vacuum]
  have he : e+chargeNorm D a-(2*b.2+1 : ℕ) = e-omega D b+chargeNorm D a := by
    simp only [omega, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    omega
  rw [he]
  ring

private theorem seed_zero (D : LatticeData) (a : Charge D) (e : ℤ) :
    wick D (monomial 0 1) (oscillatorCoefficient D a e (monomial 0 1)) =
      if e+chargeNorm D a = 0 then 1 else 0 := by
  classical
  change wick D (C 1) (oscillatorCoefficient D a e 1) = _
  rw [oscillator_vacuum, wick_constant_left, one_mul, creation_constant]
/-- Mixed Gaussian blocks, with their binomial coefficients derived from
all signed jets; the equalities below are consumed by the original row proof. -/
def SI (D : LatticeData) (b c : Index D) : ℂ :=
  (-(b.2+1 : ℂ) * Ring.choose (-((c.2 : ℤ) : ℂ)-1/2) (b.2+1)) * (D.G b.1 c.1 : ℂ)

def SO (D : LatticeData) (b c : Index D) : ℂ :=
  (-(b.2+1 : ℂ) * Ring.choose (-((-(c.2 : ℤ)-1 : ℤ) : ℂ)-1/2) (b.2+1)) *
    (D.G b.1 c.1 : ℂ)

private theorem SI_jet (D : LatticeData) (b c : Index D) :
    SI D b c = frequency (c.2 : ℤ) * jetScalar b.2 (c.2 : ℤ) * (D.G b.1 c.1 : ℂ) := by
  rw [SI, ← jet_mixed]

private theorem SO_jet (D : LatticeData) (b c : Index D) :
    SO D b c = -frequency (c.2 : ℤ) * jetScalar b.2 (-(c.2 : ℤ)-1) * (D.G b.1 c.1 : ℂ) := by
  rw [SO, ← jet_mixed, frequency_opposite]

/-- Source, input, output. The source/source block is zero for oscillatorNormal. -/
def normalMatrix (D : LatticeData) (label : I ↪ Index D) :
    Matrix (I ⊕ (I ⊕ I)) (I ⊕ (I ⊕ I)) ℂ := fun
  | .inl b, .inr (.inl c) => SI D (label b) (label c)
  | .inr (.inl c), .inl b => SI D (label b) (label c)
  | .inl b, .inr (.inr c) => SO D (label b) (label c)
  | .inr (.inr c), .inl b => SO D (label b) (label c)
  | .inr (.inl b), .inr (.inr c) => IO D (label b) (label c)
  | .inr (.inr c), .inr (.inl b) => IO D (label b) (label c)
  | _, _ => 0

def normalMean (D : LatticeData) (a : Charge D) (label : I ↪ Index D) :
    I ⊕ (I ⊕ I) → ℂ
  | .inl _ => 0
  | .inr (.inl b) => -(bilinear D a (unitCharge D (label b).1) : ℂ)
  | .inr (.inr b) => -(bilinear D a (unitCharge D (label b).1) : ℂ)

/-- These weights are derived from the actual shift e+2m+2k+3:
m=n gives -omega_n-2r, m=-n-1 gives omega_n-2r. -/
def normalWeight (D : LatticeData) (label : I ↪ Index D) : I ⊕ (I ⊕ I) → ℤ
  | .inl b => -2*((label b).2 : ℤ)-2
  | .inr (.inl b) => -(omega D (label b) : ℤ)
  | .inr (.inr b) => (omega D (label b) : ℤ)

def threeOccupation (d h l : I →₀ ℕ) : (I ⊕ (I ⊕ I)) →₀ ℕ :=
  d.sumElim (h.sumElim l)

private theorem three_add_S (d h l : I →₀ ℕ) (i : I) :
    threeOccupation (d + Finsupp.single i 1) h l =
      threeOccupation d h l + Finsupp.single (.inl i) 1 := by
  classical
  ext (j | (j | j)) <;> simp [threeOccupation, Finsupp.sumElim_apply, Finsupp.single_apply]
private theorem three_add_I (d h l : I →₀ ℕ) (i : I) :
    threeOccupation d (h + Finsupp.single i 1) l =
      threeOccupation d h l + Finsupp.single (.inr (.inl i)) 1 := by
  classical
  ext (j | (j | j)) <;> simp [threeOccupation, Finsupp.sumElim_apply, Finsupp.single_apply]
private theorem three_add_O (d h l : I →₀ ℕ) (i : I) :
    threeOccupation d h (l + Finsupp.single i 1) =
      threeOccupation d h l + Finsupp.single (.inr (.inr i)) 1 := by
  classical
  ext (j | (j | j)) <;> simp [threeOccupation, Finsupp.sumElim_apply, Finsupp.single_apply]
private theorem three_sub_I (d h l : I →₀ ℕ) (i : I) :
    threeOccupation d h l - Finsupp.single (.inr (.inl i)) 1 =
      threeOccupation d (h - Finsupp.single i 1) l := by
  classical
  ext (j | (j | j)) <;> simp [threeOccupation, Finsupp.sumElim_apply, Finsupp.single_apply]
private theorem three_sub_O (d h l : I →₀ ℕ) (i : I) :
    threeOccupation d h l - Finsupp.single (.inr (.inr i)) 1 =
      threeOccupation d h (l - Finsupp.single i 1) := by
  classical
  ext (j | (j | j)) <;> simp [threeOccupation, Finsupp.sumElim_apply, Finsupp.single_apply]
private theorem three_at_S (d h l : I →₀ ℕ) (i : I) : threeOccupation d h l (.inl i) = d i := rfl
private theorem three_at_I (d h l : I →₀ ℕ) (i : I) : threeOccupation d h l (.inr (.inl i)) = h i := rfl
private theorem three_at_O (d h l : I →₀ ℕ) (i : I) : threeOccupation d h l (.inr (.inr i)) = l i := rfl

theorem normalMatrix_symm (D : LatticeData) (label : I ↪ Index D) :
    ∀ i j, normalMatrix D label i j = normalMatrix D label j i := by
  classical
  rintro (i | (i | i)) (j | (j | j)) <;> rfl

private def normalMoment (D : LatticeData) (a : Charge D) (label : I ↪ Index D)
    (d h l : I →₀ ℕ) (n : ℤ) : ℂ :=
  gradedMoment (normalMatrix D label) (normalMean D a label) (normalWeight D label)
    (threeOccupation d h l) n

private theorem normalMoment_S (D : LatticeData) (a : Charge D) (label : I ↪ Index D)
    (d h l : I →₀ ℕ) (i : I) (n : ℤ) :
    normalMoment D a label (d + Finsupp.single i 1) h l n =
      (∑ j, (l j : ℂ) * SO D (label i) (label j) *
        normalMoment D a label d h (l - Finsupp.single j 1)
          (n-2*(label j).2+2*(label i).2+1)) +
      ∑ j, (h j : ℂ) * SI D (label i) (label j) *
        normalMoment D a label d (h - Finsupp.single j 1) l
          (n+2*(label j).2+2*(label i).2+3) := by
  classical
  have hs := gradedMoment_step (normalMatrix D label) (normalMean D a label)
    (normalMatrix_symm D label) (normalWeight D label) (threeOccupation d h l) (.inl i) n
  rw [← three_add_S] at hs
  simp only [Fintype.sum_sum_type, normalMean, normalMatrix, three_at_S,
    three_at_I, three_at_O, zero_mul, mul_zero, Finset.sum_const_zero, zero_add,
    three_sub_I, three_sub_O, normalWeight] at hs
  have hp (j : I) : n-(-2*((label i).2 : ℤ)-2)-(-(omega D (label j) : ℤ)) =
      n+2*(label j).2+2*(label i).2+3 := by simp only [omega]; push_cast; omega
  have hn (j : I) : n-(-2*((label i).2 : ℤ)-2)-(omega D (label j) : ℤ) =
      n-2*(label j).2+2*(label i).2+1 := by simp only [omega]; push_cast; omega
  simp_rw [hp, hn] at hs
  exact hs.trans (add_comm _ _)

private theorem normalMoment_I (D : LatticeData) (a : Charge D) (label : I ↪ Index D)
    (h l : I →₀ ℕ) (i : I) (n : ℤ) :
    normalMoment D a label 0 (h + Finsupp.single i 1) l n =
      -(bilinear D a (unitCharge D (label i).1) : ℂ) *
        normalMoment D a label 0 h l (n+omega D (label i)) +
      ∑ j, (l j : ℂ) * IO D (label i) (label j) *
        normalMoment D a label 0 h (l - Finsupp.single j 1) n := by
  classical
  have hs := gradedMoment_step (normalMatrix D label) (normalMean D a label)
    (normalMatrix_symm D label) (normalWeight D label) (threeOccupation 0 h l) (.inr (.inl i)) n
  rw [← three_add_I] at hs
  simp only [Fintype.sum_sum_type, normalMean, normalMatrix, three_at_S,
    three_at_I, three_at_O, Finsupp.zero_apply, Nat.cast_zero,
    zero_mul, mul_zero, Finset.sum_const_zero, zero_add, three_sub_O, normalWeight,
    sub_neg_eq_add] at hs
  change normalMoment D a label 0 (h + Finsupp.single i 1) l n = _ at hs
  rw [hs]
  simp only [normalMoment]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  by_cases he : (label i).2 = (label j).2
  · have hw : omega D (label i) = omega D (label j) := by simp only [omega, he]
    rw [hw, add_sub_cancel_right]
  · simp only [IO, if_neg he, mul_zero, zero_mul]

private theorem normalMoment_O (D : LatticeData) (a : Charge D) (label : I ↪ Index D)
    (l : I →₀ ℕ) (i : I) (n : ℤ) :
    normalMoment D a label 0 0 (l + Finsupp.single i 1) n =
      -(bilinear D a (unitCharge D (label i).1) : ℂ) *
        normalMoment D a label 0 0 l (n-omega D (label i)) := by
  classical
  have hs := gradedMoment_step (normalMatrix D label) (normalMean D a label)
    (normalMatrix_symm D label) (normalWeight D label) (threeOccupation 0 0 l) (.inr (.inr i)) n
  rw [← three_add_O] at hs
  simpa only [Fintype.sum_sum_type, normalMean, normalMatrix, three_at_S,
    three_at_I, three_at_O, Finsupp.zero_apply, Nat.cast_zero,
    zero_mul, mul_zero, Finset.sum_const_zero, zero_add, add_zero, normalWeight,
    normalMoment] using hs

private theorem normalMoment_zero (D : LatticeData) (a : Charge D) (label : I ↪ Index D)
    (n : ℤ) : normalMoment D a label 0 0 0 n = if n = 0 then 1 else 0 := by
  classical
  simp only [normalMoment, threeOccupation, Finsupp.sumElim_zero_zero,
    gradedMoment, map_zero, affineMoment_zero]

private def M (D : LatticeData) (label : I ↪ Index D) (d : I →₀ ℕ) : Oscillator D :=
  monomial (d.embDomain label) 1

/-- A shorthand for the original seed, not a recurrence-defined carrier. -/
private def seedEntry (D : LatticeData) (a : Charge D) (label : I ↪ Index D)
    (h l : I →₀ ℕ) (e : ℤ) : ℂ :=
  wick D (M D label l) (oscillatorCoefficient D a e (M D label h))

private theorem support_sum (d : I →₀ ℕ) (F : I → ℂ) :
    (∑ j ∈ d.support, (d j : ℂ) * F j) = ∑ j, (d j : ℂ) * F j := by
  classical
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j hj hout
  simp only [Finsupp.notMem_support_iff.mp hout, Nat.cast_zero, zero_mul]

private theorem seedEntry_I (D : LatticeData) (a : Charge D) (label : I ↪ Index D)
    (h l : I →₀ ℕ) (i : I) (e : ℤ) :
    seedEntry D a label (h + Finsupp.single i 1) l e =
      -(bilinear D a (unitCharge D (label i).1) : ℂ) *
        seedEntry D a label h l (e+omega D (label i)) +
      ∑ j, (l j : ℂ) * IO D (label i) (label j) *
        seedEntry D a label h (l - Finsupp.single j 1) e := by
  classical
  simp only [seedEntry, M, Finsupp.embDomain_add, Finsupp.embDomain_single]
  rw [seed_input_step]
  simp only [Finsupp.support_embDomain, Finset.sum_map, Finsupp.embDomain_apply_self,
    ← Finsupp.embDomain_single label, ← Finsupp.embDomain_tsub, mul_assoc]
  rw [support_sum]

private theorem seedEntry_O (D : LatticeData) (a : Charge D) (label : I ↪ Index D)
    (l : I →₀ ℕ) (i : I) (e : ℤ) :
    seedEntry D a label 0 (l + Finsupp.single i 1) e =
      -(bilinear D a (unitCharge D (label i).1) : ℂ) *
        seedEntry D a label 0 l (e-omega D (label i)) := by
  classical
  simpa only [seedEntry, M, Finsupp.embDomain_zero, monomial_zero', map_one,
    Finsupp.embDomain_add, Finsupp.embDomain_single] using
    seed_output_only_step D a (l.embDomain label) (label i) e

/-- The charged seed is identified with its native finite noncentral Gaussian,
including the e+Q(a) selector. The original seed recurrences discharge all
mean and IO coefficients; no row equality is assumed. -/
private theorem seedEntry_gaussian (D : LatticeData) (a : Charge D)
    (label : I ↪ Index D) (h l : I →₀ ℕ) (e : ℤ) :
    seedEntry D a label h l e = normalMoment D a label 0 h l (e+chargeNorm D a) := by
  classical
  have output_only : ∀ n (l : I →₀ ℕ), l.degree = n → ∀ e,
      seedEntry D a label 0 l e = normalMoment D a label 0 0 l (e+chargeNorm D a) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro l hl e
      by_cases hz : l = 0
      · subst l
        simpa only [seedEntry, M, Finsupp.embDomain_zero, normalMoment_zero] using seed_zero D a e
      · obtain ⟨i,hi⟩ := occupation_nonzero l hz
        let r := l - Finsupp.single i 1
        have hr : r + Finsupp.single i 1 = l := Finsupp.sub_add_single_one_cancel hi
        have hd : r.degree < n := by have := sub_single_degree l i hi; dsimp [r]; omega
        rw [← hr, seedEntry_O, normalMoment_O, ih _ hd r rfl]
        congr 2
        omega
  have go : ∀ n (h : I →₀ ℕ), h.degree = n → ∀ l e,
      seedEntry D a label h l e = normalMoment D a label 0 h l (e+chargeNorm D a) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro h hh l e
      by_cases hz : h = 0
      · subst h
        exact output_only _ l rfl e
      · obtain ⟨i,hi⟩ := occupation_nonzero h hz
        let r := h - Finsupp.single i 1
        have hr : r + Finsupp.single i 1 = h := Finsupp.sub_add_single_one_cancel hi
        have hd : r.degree < n := by have := sub_single_degree h i hi; dsimp [r]; omega
        rw [← hr, seedEntry_I, normalMoment_I]
        simp_rw [ih _ hd r rfl]
        congr 1
        congr 2
        omega
  exact go _ h rfl l e

/-- Actual finite source/input/detector row in arbitrary finite support
coordinates. The definition does not invoke the Gaussian right-hand side. -/
private def entry (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (label : I ↪ Index D) (d h l : I →₀ ℕ) (e : ℤ) : ℂ :=
  wick D (M D label l) (oscillatorNormal D hu a e (M D label d) (M D label h))

private theorem entry_S (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (label : I ↪ Index D) (d h l : I →₀ ℕ) (i : I) (e : ℤ) :
    entry D hu a label (d + Finsupp.single i 1) h l e =
      (∑ j, (l j : ℂ) * SO D (label i) (label j) *
        entry D hu a label d h (l - Finsupp.single j 1)
          (e-2*(label j).2+2*(label i).2+1)) +
      ∑ j, (h j : ℂ) * SI D (label i) (label j) *
        entry D hu a label d (h - Finsupp.single j 1) l
          (e+2*(label j).2+2*(label i).2+3) := by
  classical
  simp only [entry, M, Finsupp.embDomain_add, Finsupp.embDomain_single]
  rw [wick_normal_step]
  simp only [Finsupp.support_embDomain, Finset.sum_map, Finsupp.embDomain_apply_self,
    ← Finsupp.embDomain_single label, ← Finsupp.embDomain_tsub, SI_jet, SO_jet, mul_assoc]
  rw [support_sum, support_sum]

/-- Substantive source induction: actual charged normal order equals the
finite native affine moment in every degree. The finite reindexing theorem
is on this proof path, as are both charged seed means and the original IO. -/
private theorem entry_gaussian (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (label : I ↪ Index D) (d h l : I →₀ ℕ) (e : ℤ) :
    entry D hu a label d h l e = normalMoment D a label d h l (e+chargeNorm D a) := by
  classical
  have go : ∀ n (d : I →₀ ℕ), d.degree = n → ∀ h l e,
      entry D hu a label d h l e = normalMoment D a label d h l (e+chargeNorm D a) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro d hd h l e
      by_cases hz : d = 0
      · subst d
        change wick D (M D label l)
          (oscillatorNormal D hu a e (monomial 0 1) (M D label h)) = _
        rw [normal_zero]
        exact seedEntry_gaussian D a label h l e
      · obtain ⟨i,hi⟩ := occupation_nonzero d hz
        let r := d - Finsupp.single i 1
        have hr : r + Finsupp.single i 1 = d := Finsupp.sub_add_single_one_cancel hi
        have hdeg : r.degree < n := by have := sub_single_degree d i hi; dsimp [r]; omega
        rw [← hr, entry_S, normalMoment_S]
        simp_rw [ih _ hdeg r rfl]
        congr 1
        · apply Finset.sum_congr rfl
          intro j hj
          congr 2
          omega
        · apply Finset.sum_congr rfl
          intro j hj
          congr 2
          omega
  exact go _ d rfl h l e

private theorem three_weight (d h l : I →₀ ℕ) :
    weight (threeOccupation d h l) = weight d * weight h * weight l := by
  classical
  simp only [threeOccupation, weight, Finsupp.prod_sumElim, Function.comp_def]
  ring

/-- Original normal row with all three factorials and exponent e+chargeNorm(a).
The independent native Gaussian coefficient uses auxiliary degrees bounded
by total occupation degree. Repository admission and identityK remain separate. -/
theorem original_normal_row_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (label : I ↪ Index D) (d h l : I →₀ ℕ) (e : ℤ) :
    wick D (monomial (l.embDomain label) 1)
        (oscillatorNormal D hu a e (monomial (d.embDomain label) 1)
          (monomial (h.embDomain label) 1)) =
      (weight d : ℂ) * (weight h : ℂ) * (weight l : ℂ) *
        affineLaurent (normalMatrix D label) (normalMean D a label) (normalWeight D label)
          (threeOccupation d h l) (e+chargeNorm D a) := by
  classical
  have he := entry_gaussian D hu a label d h l e
  rw [normalMoment, gradedMoment_coefficient, three_weight] at he
  push_cast at he
  simpa only [entry, M, mul_assoc] using he
/-- Ordinary finite exponential in homogeneous auxiliary coordinates, with
all powers 0 through N. This definition contains no Wick/current recurrence. -/
def finiteGaussianExponential (A : Matrix I I ℂ) (N : ℕ) : MvPolynomial I ℂ :=
  ∑ n ∈ Finset.range (N+1), FactorialFockQuadraticEstimate.gaussianPiece A n

open D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate (gaussianPiece_homogeneous)

private theorem gaussianCoefficient_finite (A : Matrix I I ℂ) (d : I →₀ ℕ)
    (N : ℕ) (hd : d.degree ≤ 2*N) :
    gaussianCoefficient A d = (finiteGaussianExponential A N).coeff d := by
  classical
  rw [gaussianCoefficient, finiteGaussianExponential, coeff_sum]
  symm
  apply Finset.sum_eq_single (d.degree / 2)
  · intro n hn hne
    apply (gaussianPiece_homogeneous A n).coeff_eq_zero
    omega
  · intro hout
    have hn : d.degree / 2 ∈ Finset.range (N+1) := Finset.mem_range.mpr (by omega)
    exact (hout hn).elim

/-- Cancelling the auxiliary variable by finite coefficient summation really
uses the ordinary truncated exponential through total external degree.
This identifies the native coefficient definition with the allowed finite
exponential interpretation, not with a recurrence-defined moment proxy. -/
private theorem affineCoefficient_finite (A : Matrix I I ℂ) (mu : I → ℂ)
    (d : I →₀ ℕ) :
    affineCoefficient A mu d =
      ∑ k ∈ Finset.range (d.degree+1),
        (finiteGaussianExponential (affineKernel A mu) d.degree).coeff
          (d.sumElim (Finsupp.single () k)) := by
  classical
  unfold affineCoefficient
  apply Finset.sum_congr rfl
  intro k hk
  apply gaussianCoefficient_finite
  have hdeg : (d.sumElim (Finsupp.single () k)).degree = d.degree+k := by
    simp only [Finsupp.degree_eq_sum, Fintype.sum_sum_type,
      Finsupp.sumElim_inl, Finsupp.sumElim_inr, Fintype.sum_unique, Finsupp.single_eq_same]
  rw [hdeg]
  have h := Finset.mem_range.mp hk
  omega

/-- Literal finite support, not a hardcoded rank or frequency box. -/
def rowSupport (D : LatticeData) (alpha beta gamma : Index D →₀ ℕ) : Finset (Index D) :=
  alpha.support ∪ beta.support ∪ gamma.support

def supportLabel (D : LatticeData) (K : Finset (Index D)) : {b // b ∈ K} ↪ Index D :=
  Function.Embedding.subtype (fun b => b ∈ K)

def restricted (D : LatticeData) (K : Finset (Index D)) (d : Index D →₀ ℕ) :
    {b // b ∈ K} →₀ ℕ :=
  d.comapDomain (supportLabel D K) (supportLabel D K).injective.injOn

theorem restricted_reconstruct (D : LatticeData) (K : Finset (Index D))
    (d : Index D →₀ ℕ) (hd : d.support ⊆ K) :
    (restricted D K d).embDomain (supportLabel D K) = d := by
  classical
  apply Finsupp.embDomain_comapDomain
  intro b hb
  exact ⟨⟨b,hd hb⟩,rfl⟩

theorem embedded_weight (D : LatticeData) (label : I ↪ Index D) (d : I →₀ ℕ) :
    weight (d.embDomain label) = weight d := by
  classical
  exact Finsupp.prod_embDomain

/-- The finite three-slot Gaussian Laurent coefficient, interpreted as follows.
Let N be the total occupation degree. The auxiliary Y has zero Y^2 block.
Use sum_{n=0}^N Q_hom^n/n!, sum auxiliary degrees k=0..N (Y=1),
and retain the Laurent weight of the original three-slot occupation.
Thus every coefficient is ordinary; no analytic exponential is evaluated.

Here Q_hom = SI + SO + IO + Y*(mu_I*I + mu_O*O).
Scaling S_(i,k) by t^(-2(k+1)), I_(j,n) by t^(-omega_n),
and O_(j,n) by t^(omega_n) gives exactly the stated Laurent blocks.
All coefficients of one occupation have the same Laurent weight; this is
why its Laurent polynomial is a single `Finsupp.single` below. -/
def normalLaurentRow (D : LatticeData) (a : Charge D)
    (alpha beta gamma : Index D →₀ ℕ) : ℤ →₀ ℂ :=
  let K := rowSupport D alpha beta gamma
  let label := supportLabel D K
  let d := threeOccupation (restricted D K alpha) (restricted D K beta) (restricted D K gamma)
  Finsupp.single (Finsupp.weight (normalWeight D label) d)
    (∑ k ∈ Finset.range (d.degree+1),
      (finiteGaussianExponential (affineKernel (normalMatrix D label)
        (normalMean D a label)) d.degree).coeff (d.sumElim (Finsupp.single () k)))

theorem normalLaurentRow_native (D : LatticeData) (a : Charge D)
    (alpha beta gamma : Index D →₀ ℕ) :
    normalLaurentRow D a alpha beta gamma =
      affineLaurent (normalMatrix D (supportLabel D (rowSupport D alpha beta gamma)))
        (normalMean D a (supportLabel D (rowSupport D alpha beta gamma)))
        (normalWeight D (supportLabel D (rowSupport D alpha beta gamma)))
        (threeOccupation (restricted D (rowSupport D alpha beta gamma) alpha)
          (restricted D (rowSupport D alpha beta gamma) beta)
          (restricted D (rowSupport D alpha beta gamma) gamma)) := by
  classical
  unfold normalLaurentRow affineLaurent
  rw [affineCoefficient_finite]

/-- The original arbitrary-charge normal-row identity on EVERY original
source/input/detector occupation, including all zero and rank-zero cases.
The RHS is an ordinary finite Gaussian exponential coefficient, with three
factorials, original Gram colours, and extraction at e+Q(a). -/
theorem original_normal_row (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (alpha beta gamma : Index D →₀ ℕ) (e : ℤ) :
    wick D (monomial gamma 1)
        (oscillatorNormal D hu a e (monomial alpha 1) (monomial beta 1)) =
      (weight alpha : ℂ) * (weight beta : ℂ) * (weight gamma : ℂ) *
        normalLaurentRow D a alpha beta gamma (e+chargeNorm D a) := by
  classical
  let K := rowSupport D alpha beta gamma
  have ha : alpha.support ⊆ K := Finset.subset_union_left.trans Finset.subset_union_left
  have hb : beta.support ⊆ K := Finset.subset_union_right.trans Finset.subset_union_left
  have hc : gamma.support ⊆ K := Finset.subset_union_right
  have hra := restricted_reconstruct D K alpha ha
  have hrb := restricted_reconstruct D K beta hb
  have hrc := restricted_reconstruct D K gamma hc
  have hwa : weight (restricted D K alpha) = weight alpha := by
    calc
      _ = weight ((restricted D K alpha).embDomain (supportLabel D K)) :=
        (embedded_weight D (supportLabel D K) _).symm
      _ = _ := congrArg weight hra
  have hwb : weight (restricted D K beta) = weight beta := by
    calc
      _ = weight ((restricted D K beta).embDomain (supportLabel D K)) :=
        (embedded_weight D (supportLabel D K) _).symm
      _ = _ := congrArg weight hrb
  have hwc : weight (restricted D K gamma) = weight gamma := by
    calc
      _ = weight ((restricted D K gamma).embDomain (supportLabel D K)) :=
        (embedded_weight D (supportLabel D K) _).symm
      _ = _ := congrArg weight hrc
  have he := original_normal_row_finite D hu a (supportLabel D K)
    (restricted D K alpha) (restricted D K beta) (restricted D K gamma) e
  rw [hra, hrb, hrc, hwa, hwb, hwc] at he
  rw [normalLaurentRow_native]
  exact he

/-- Literal charged Corr convolution using the original normal-row identity.
No centered Corr theorem is used. Every residual occupation delta contributes
its own delta!, and both original external factorials remain. This theorem
does NOT claim that this double finite sum is the SS/source-mean extension. -/
theorem original_corrected_normal_convolution (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (alpha beta gamma : Index D →₀ ℕ) (e : ℤ) :
    wick D (monomial gamma 1)
        (oscillatorCorrected D hu a e (monomial alpha 1) (monomial beta 1)) =
      (weight beta : ℂ) * (weight gamma : ℂ) *
        ∑ s ∈ (LatticeHalfFockFiniteCorrection.Corr D a (monomial alpha 1)).support,
          ∑ delta ∈ (LatticeHalfFockFiniteCorrection.Corr D a (monomial alpha 1) s).support,
            (LatticeHalfFockFiniteCorrection.Corr D a (monomial alpha 1) s).coeff delta *
              (weight delta : ℂ) * normalLaurentRow D a delta beta gamma
                (e+2*(s : ℤ)+chargeNorm D a) := by
  classical
  let c := LatticeHalfFockFiniteCorrection.Corr D a (monomial alpha 1)
  change wick D (monomial gamma 1)
    ((∑ s ∈ c.support, oscillatorNormal D hu a (e+2*(s : ℤ)) (c s))
      (monomial beta 1)) = _
  simp only [LinearMap.sum_apply, map_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  conv_lhs => rw [(c s).as_sum]
  simp only [map_sum, LinearMap.sum_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro delta hd
  rw [show (monomial delta ((c s).coeff delta) : Oscillator D) =
    (c s).coeff delta • monomial delta 1 by simp only [smul_monomial, smul_eq_mul, mul_one],
    map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, original_normal_row]
  ring

/-!
Arbitrary charge, integer exponents and empty support are included.
OriginalCorrectedRowRecompositionSource derives support and shift selection;
OriginalAffineRecompositionSource proves the complete corrected Gaussian row
with all three factorials and e+chargeNorm D a. IdentityK and two-row sewing
remain open, retaining four external factorials, both chargeScalar factors,
one left average and -Ginv/(k+1). No physical or VOA completion is asserted.
-/

end D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource
