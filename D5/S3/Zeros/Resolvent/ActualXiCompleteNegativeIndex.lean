/- GID: D5/S3/Zeros/Resolvent/ActualXiCompleteNegativeIndex
   generality: I
   mirror-B: D5/B/S3/Zeros/Resolvent/ActualXiCompleteNegativeIndex
   mirror-E: none(waiver:actual-analytic-zero-source)
   anchors: []
   utility: none
   digest: The complete actual xi negative index counts distinct off-line quartets. -/

import D5.S3.Weil.ZetaLinear.ExactStickyReduction
import D5.S3.Constants.Moments.CountableHankelIntegerFamily
import D5.S3.Constants.Moments.CountableHankelNegativeIndex
import D5.S3.Zeros.Resolvent.ActualXiDictionary
import D5.S3.Zeros.Resolvent.ActualXiIntegerCriterion
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.LinearAlgebra.Pi
import Mathlib.SetTheory.Cardinal.Embedding

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Polynomial
open scoped BigOperators ComplexConjugate

namespace D5.S3.Zeros.Resolvent.ActualXiCompleteNegativeIndex

open D5.S3.Weil.ZetaLinear.ExactStickyReduction
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Constants.Moments.CountableHankelNegativeWitness
open D5.S3.Zeros.Resolvent.ActualXiFoldedSpectrum
open D5.S3.Zeros.Resolvent.ActualXiHankelDictionary

/-- Every linear map from a finite real coordinate space has one polynomial
coefficient support, independently of any energy or injectivity assumption. -/
theorem common_support_of_linear_map {k : ℕ}
    (T : (Fin k → ℝ) →ₗ[ℝ] ℝ[X]) :
    ∃ N : ℕ, ∃ A : (Fin k → ℝ) →ₗ[ℝ] (Fin (N + 1) → ℝ),
      ∀ x, Polynomial.ofFn (N + 1) (A x) = T x := by
  classical
  let p : Fin k → ℝ[X] := fun j => T (Pi.single j 1)
  let N : ℕ := Finset.univ.sup (fun j => (p j).natDegree)
  let A : (Fin k → ℝ) →ₗ[ℝ] (Fin (N + 1) → ℝ) :=
    (Polynomial.toFn (N + 1)).comp T
  have hpdeg (j : Fin k) : (p j).natDegree < N + 1 := by
    exact Nat.lt_succ_of_le
      (Finset.le_sup (f := fun j => (p j).natDegree) (Finset.mem_univ j))
  have hrow (j : Fin k) :
      Polynomial.ofFn (N + 1) (A (Pi.single j 1)) = T (Pi.single j 1) := by
    change Polynomial.ofFn (N + 1) (Polynomial.toFn (N + 1) (p j)) = p j
    exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (hpdeg j)
  have hcomp : (Polynomial.ofFn (N + 1)).comp A = T := by
    apply LinearMap.pi_ext
    intro j r
    have hsingle : (Pi.single j r : Fin k → ℝ) = r • Pi.single j 1 := by
      funext i
      by_cases hij : i = j <;> simp [Pi.single_apply, hij]
    rw [hsingle]
    simp only [LinearMap.comp_apply, map_smul, hrow]
  exact ⟨N, A, fun x => congrArg
    (fun L : (Fin k → ℝ) →ₗ[ℝ] ℝ[X] => L x) hcomp⟩

/-- Reconstruction is unconditional in `x`; strict negativity requires `x ≠ 0`.
This statement includes `k = 0`, with no condition at all on `E 0`. -/
theorem common_support_of_negative_span (E : ℝ[X] → ℝ) {k : ℕ}
    (T : (Fin k → ℝ) →ₗ[ℝ] ℝ[X])
    (hT : Function.Injective T)
    (hneg : ∀ x, x ≠ 0 → E (T x) < 0) :
    ∃ N : ℕ, ∃ A : (Fin k → ℝ) →ₗ[ℝ] (Fin (N + 1) → ℝ),
      Function.Injective A ∧
      (∀ x, Polynomial.ofFn (N + 1) (A x) = T x) ∧
      (∀ x, x ≠ 0 → E (Polynomial.ofFn (N + 1) (A x)) < 0) := by
  obtain ⟨N, A, hrepr⟩ := common_support_of_linear_map T
  have hA : Function.Injective A := by
    intro x y hxy
    apply hT
    rw [← hrepr x, ← hrepr y, hxy]
  refine ⟨N, A, hA, hrepr, ?_⟩
  intro x hx
  rw [hrepr x]
  exact hneg x hx

/-- Negative ranks of arbitrary-energy finite coefficient restrictions. -/
def finiteCoefficientNegativeRanks (E : ℝ[X] → ℝ) : Set ℕ :=
  ⋃ N : ℕ, {k | ∃ A : (Fin k → ℝ) →ₗ[ℝ] (Fin (N + 1) → ℝ),
    Function.Injective A ∧
      ∀ x, x ≠ 0 → E (Polynomial.ofFn (N + 1) (A x)) < 0}

def finiteCoefficientNegativeIndex (E : ℝ[X] → ℝ) : WithTop ℕ :=
  sSup ((fun k : ℕ => (k : WithTop ℕ)) '' finiteCoefficientNegativeRanks E)

/-- The finite-support argument needs no quadratic, continuity, or sign
assumption on the energy. In the reverse direction use Mathlib's injection. -/
theorem negativeRanks_eq_finiteCoefficientNegativeRanks (E : ℝ[X] → ℝ) :
    negativeRanks E = finiteCoefficientNegativeRanks E := by
  ext k
  constructor
  · rintro ⟨T, hT, hneg⟩
    obtain ⟨N, A, hA, _hrepr, hnegA⟩ := common_support_of_negative_span E T hT hneg
    exact Set.mem_iUnion.mpr ⟨N, A, hA, hnegA⟩
  · intro hk
    obtain ⟨N, A, hA, hneg⟩ := Set.mem_iUnion.mp hk
    exact ⟨(Polynomial.ofFn (N + 1)).comp A,
      (Polynomial.injective_ofFn (N + 1)).comp hA, hneg⟩

theorem negativeIndex_eq_finiteCoefficientNegativeIndex (E : ℝ[X] → ℝ) :
    negativeIndex E = finiteCoefficientNegativeIndex E := by
  unfold negativeIndex finiteCoefficientNegativeIndex
  rw [negativeRanks_eq_finiteCoefficientNegativeRanks E]

/-- The full actual positive-height energy, with ordinary complex squares. -/
def actualEnergy (p : ℝ[X]) : ℝ :=
  (∑' n : PositiveZero,
    weight n * (p.eval₂ Complex.ofRealHom (node n)) ^ 2).re

/-- This is the original derivative Hankel matrix, with even shift `m = 0`. -/
def actualCoefficientEnergy (N : ℕ) (u : Fin (N + 1) → ℝ) : ℝ :=
  ∑ a : Fin (N + 1), ∑ b : Fin (N + 1),
    u a * u b * xiCoefficient ((a : ℕ) + (b : ℕ))

private lemma ofFn_eval_complex (N : ℕ) (u : Fin (N + 1) → ℝ) (z : ℂ) :
    (Polynomial.ofFn (N + 1) u).eval₂ Complex.ofRealHom z =
      ∑ a : Fin (N + 1), (u a : ℂ) * z ^ (a : ℕ) := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial,
    Complex.ofRealHom_eq_coe]

lemma actual_coefficient_energy_identity (N : ℕ) (u : Fin (N + 1) → ℝ) :
    actualCoefficientEnergy N u = actualEnergy (Polynomial.ofFn (N + 1) u) := by
  unfold actualCoefficientEnergy actualEnergy
  simp_rw [ofFn_eval_complex]
  simpa only [Nat.mul_zero, zero_add, pow_zero, one_mul] using
    (actual_xi_hankel_identity N 0 u)

/-- The supremum of the negative indices of all finite actual derivative
Hankel matrices; the index of each matrix is defined on its real vectors. -/
def actualMatrixNegativeIndex : WithTop ℕ :=
  ⨆ N : ℕ, negativeIndex (actualCoefficientEnergy N)

/-- Both inclusions explicitly transport energy through the actual dictionary. -/
theorem actual_negativeIndex_eq_matrix_sup :
    negativeIndex actualEnergy = actualMatrixNegativeIndex := by
  rw [negativeIndex_eq_finiteCoefficientNegativeIndex actualEnergy]
  unfold finiteCoefficientNegativeIndex actualMatrixNegativeIndex
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨N, A, hA, hneg⟩ := Set.mem_iUnion.mp hk
    apply le_iSup_of_le N
    unfold negativeIndex
    apply le_sSup
    refine ⟨k, ⟨A, hA, ?_⟩, rfl⟩
    intro x hx
    rw [actual_coefficient_energy_identity]
    exact hneg x hx
  · apply iSup_le
    intro N
    unfold negativeIndex
    apply sSup_le
    rintro _ ⟨k, ⟨A, hA, hneg⟩, rfl⟩
    apply le_sSup
    refine ⟨k, Set.mem_iUnion.mpr ⟨N, A, hA, ?_⟩, rfl⟩
    intro x hx
    rw [← actual_coefficient_energy_identity]
    exact hneg x hx

/-- Upper positive-height zeros to the right of the critical line select one
representative of each distinct off-line quartet, independently of multiplicity. -/
abbrev QuartetRepresentative :=
  {n : PositiveZero // (1 / 2 : ℝ) < (actualData.zero n).re}

def actualQuartetCount : ENat := ENat.card QuartetRepresentative

private lemma zero_conjugation_re (n : PositiveZero) :
    (actualData.zero (conjugation n)).re = 1 - (actualData.zero n).re := by
  change (actualData.zero (actualData.reflection (actualData.conjugation n))).re = _
  rw [actualData.zero_reflection, actualData.zero_conjugation]
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]

lemma actual_quartet_rep_ne_conjugate
    (r s : QuartetRepresentative) : r.1 ≠ conjugation s.1 := by
  intro hrs
  have hz := congrArg (fun n : PositiveZero => (actualData.zero n).re) hrs
  rw [zero_conjugation_re] at hz
  linarith [r.property, s.property]

lemma actual_quartet_cover (n : PositiveZero)
    (hnonreal : conj (node n) ≠ node n) :
    ∃ r : QuartetRepresentative, n = r.1 ∨ n = conjugation r.1 := by
  have hline : (actualData.zero n).re ≠ 1 / 2 := by
    intro h
    apply hnonreal
    have him : (node n).im = 0 := (node_real_iff n).mpr h
    apply Complex.ext <;> simp [him]
  rcases lt_or_gt_of_ne hline with hlt | hgt
  · have hr : (1 / 2 : ℝ) < (actualData.zero (conjugation n)).re := by
      rw [zero_conjugation_re]
      linarith
    refine ⟨⟨conjugation n, hr⟩, Or.inr ?_⟩
    change n = tau (tau n)
    exact (tau_involutive n).symm
  · exact ⟨⟨n, hgt⟩, Or.inl rfl⟩

/-- Exhaust all pairs when the representative type is finite, including empty. -/
theorem actual_upper_of_finite_representatives [Finite QuartetRepresentative] :
    negativeIndex actualEnergy ≤ actualQuartetCount := by
  classical
  letI : Fintype QuartetRepresentative := Fintype.ofFinite QuartetRepresentative
  change negativeIndex actualEnergy ≤ ENat.card QuartetRepresentative
  rw [ENat.card_eq_coe_fintype_card]
  let e : Fin (Fintype.card QuartetRepresentative) ↪ QuartetRepresentative :=
    (Fintype.equivFin QuartetRepresentative).symm.toEmbedding
  let s : Fin (Fintype.card QuartetRepresentative) → PositiveZero :=
    fun j => (e j).1
  apply D5.S3.Constants.Moments.CountableHankelNegativeIndex.negativeIndex_le
    node weight conjugation (fun n => (node_norm_lt_one n).le)
    node_conjugation weight_conjugation weight_norm_summable
    (Fintype.card QuartetRepresentative) s
  · intro i hni _hwi
    obtain ⟨r, hir | hir⟩ := actual_quartet_cover i hni
    · refine ⟨(Fintype.equivFin QuartetRepresentative) r, Or.inl ?_⟩
      simpa [s, e] using hir
    · refine ⟨(Fintype.equivFin QuartetRepresentative) r, Or.inr ?_⟩
      simpa [s, e] using hir
  · intro n hn
    have him : (node n).im = 0 := by
      have hi := congrArg Complex.im hn
      simp only [Complex.conj_im] at hi
      linarith
    exact (node_real_positive n him).2.1.le

/-- An embedded family of distinct off-line quartets supplies the same number
of negative polynomial directions, using the original owner-local suppliers. -/
theorem actual_lower_of_rep_embedding {k : ℕ}
    (e : Fin k ↪ QuartetRepresentative) :
    (k : WithTop ℕ) ≤ negativeIndex actualEnergy := by
  classical
  let s : Fin k → PositiveZero := fun j => (e j).1
  obtain ⟨N, U, hUneg, hUinj⟩ :=
    exists_integer_negative_family node weight conjugation
      (fun n => (node_norm_lt_one n).le) node_injective node_conjugation
      weight_conjugation weight_norm_summable
      ActualXiIntegerCriterion.node_large_finite s
      (Subtype.val_injective.comp e.injective)
      (fun a b => actual_quartet_rep_ne_conjugate (e a) (e b))
      (fun j => ActualXiIntegerCriterion.weight_ne_zero (s j))
  let A : (Fin k → ℝ) →ₗ[ℝ] (Fin (N + 1) → ℝ) :=
    { toFun := fun t a => ∑ j, t j * (U j a : ℝ)
      map_add' := by
        intro t v
        funext a
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro r t
        funext a
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
          Finset.mul_sum, mul_assoc] }
  have hA : Function.Injective A := hUinj
  have hcombine (t : Fin k → ℝ) (z : ℂ) :
      (∑ a : Fin (N + 1), (A t a : ℂ) * z ^ (a : ℕ)) =
        ∑ j, (t j : ℂ) * ∑ a : Fin (N + 1), (U j a : ℂ) * z ^ (a : ℕ) := by
    change (∑ a : Fin (N + 1), ((∑ j, t j * (U j a : ℝ) : ℝ) : ℂ) *
      z ^ (a : ℕ)) = _
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hmatrix (t : Fin k → ℝ) (ht : t ≠ 0) :
      actualCoefficientEnergy N (A t) < 0 := by
    rw [actual_coefficient_energy_identity]
    unfold actualEnergy
    simp_rw [ofFn_eval_complex, hcombine t]
    exact hUneg t ht
  have hrank : k ∈ negativeRanks actualEnergy := by
    refine ⟨(Polynomial.ofFn (N + 1)).comp A,
      (Polynomial.injective_ofFn (N + 1)).comp hA, ?_⟩
    intro t ht
    change actualEnergy (Polynomial.ofFn (N + 1) (A t)) < 0
    rw [← actual_coefficient_energy_identity]
    exact hmatrix t ht
  unfold negativeIndex
  exact le_sSup ⟨k, hrank, rfl⟩

/-- Complete count for zero, finite, and infinite off-line quartet families.
No RH premise, analytic-multiplicity count, or truncation is introduced. -/
theorem actual_complete_negative_index :
    negativeIndex actualEnergy = actualQuartetCount := by
  classical
  by_cases hfinite : Finite QuartetRepresentative
  · letI : Finite QuartetRepresentative := hfinite
    letI : Fintype QuartetRepresentative := Fintype.ofFinite QuartetRepresentative
    apply le_antisymm
    · exact actual_upper_of_finite_representatives
    · have h := actual_lower_of_rep_embedding
        (Fintype.equivFin QuartetRepresentative).symm.toEmbedding
      simpa only [actualQuartetCount, ENat.card_eq_coe_fintype_card] using h
  · letI : Infinite QuartetRepresentative := not_finite_iff_infinite.mp hfinite
    have htop : actualQuartetCount = ⊤ := ENat.card_eq_top_of_infinite
    rw [htop]
    apply ENat.eq_top_iff_forall_ge.mpr
    intro k
    obtain ⟨e, _⟩ :=
      Fin.Embedding.exists_embedding_disjoint_range_of_add_le_ENat_card
        (α := QuartetRepresentative) (n := k)
        (s := (∅ : Set QuartetRepresentative)) (by simp)
    exact actual_lower_of_rep_embedding e

/-- The supremum of finite original-derivative Hankel indices is the same
complete quartet count. This consumes the support and energy transfer. -/
theorem actual_complete_derivative_hankel_index :
    (⨆ N : ℕ, negativeIndex (actualCoefficientEnergy N)) = actualQuartetCount := by
  change actualMatrixNegativeIndex = actualQuartetCount
  rw [← actual_negativeIndex_eq_matrix_sup, actual_complete_negative_index]

end D5.S3.Zeros.Resolvent.ActualXiCompleteNegativeIndex
