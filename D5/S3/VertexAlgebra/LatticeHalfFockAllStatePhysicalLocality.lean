/- GID: D5/S3/VertexAlgebra/LatticeHalfFockAllStatePhysicalLocality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockAllStatePhysicalLocality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual correctedField has unrestricted all-state physical two-sheet locality. -/

/- Canonical direct-slice all-source locality on the unchanged correctedField.
   The proof uses one uniform signed-shift order and pointwise finite source
   expansion; no parity reconstruction or auxiliary field constructor occurs.
   Inherited notices: Copyright (c) 2025 Kalle Kytölä; additional half-integer
   implementation (c) 2026; Apache 2.0. Normal-product architecture: Scott
   Carnahan (c) 2025, Apache 2.0, vertexAlg
   4453e34ec390e82a0c789c731ada8f9a6e86bdea via FieldNormalProduct.
   Finite support/contraction architecture: VirasoroProject
   5ff4245383b2cdd4eea7a0524bc1274c32041eb4 via PolynomialFock
   bfd9ff0f15397a4fb933f36d701a60d325d84b08.
   Context: Dong--Nagatomo math/9808088v1 §3.2 pp.12–14;
   Bakalov--Kac math/0402315v1 (4.4), (4.23)–(4.38); FLM (1988).
   Inherited attribution is not new retrieval or acceptance evidence. -/

import D5.S3.VertexAlgebra.LatticeHalfFockPhysicalWordLocality
import D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/- proof_shape: chargedWordField_cover_locality: private content; correctedField_physical_locality: content
   admission_basis: escape-witness
   escape_witness: Uniform signed-slice Dong locality converts to the original
   doubled-shift commutator. Genuine finite maxima propagate through actual
   charge, Corr-shift and monomial supports. Every
   signed original coefficient and arbitrary target vector remains in scope.
   No all-state locality, Jacobi, rank or positivity premise is introduced.
   Literature status: classical twisted lattice locality; zero novelty. -/

namespace D5.S3.VertexAlgebra.LatticeHalfFockAllStatePhysicalLocality

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockCorrectedField
open LatticeHalfFockFiniteCorrection
open LatticeHalfFockPhysicalRescaling LatticeHalfFockPhysicalWordLocality
open FieldNormalProductLocality FiniteFieldLocality
open scoped BigOperators VertexOperator

noncomputable section

private theorem delta_power {State : Type*} [AddCommGroup State] [Module ℂ State]
    (distribution : ℤ → ℤ → Module.End ℂ State) (order : ℕ) :
    (deltaEnd ^ order) distribution = delta^[order] distribution :=
  Module.End.pow_apply deltaEnd order distribution

private def coverGrid (D : LatticeData) (hu : IsUnit D.G.det)
    (first second : NativeField D hu) (firstExponent secondExponent : ℤ) :
    ℤ → ℤ → Module.End ℂ (ActualTensor D hu) :=
  fun left right => first.coeff (firstExponent - 2 * left) *
      second.coeff (secondExponent - 2 * right) -
    second.coeff (secondExponent - 2 * right) * first.coeff (firstExponent - 2 * left)

private def CoverLocal (D : LatticeData) (hu : IsUnit D.G.det)
    (first second : NativeField D hu) : Prop :=
  ∃ order : ℕ, ∀ firstExponent secondExponent : ℤ,
    delta^[order] (coverGrid D hu first second firstExponent secondExponent) = 0

private def translated {State : Type*} (distribution : ℤ → ℤ → State) (left right : ℤ) :
    ℤ → ℤ → State := fun first second => distribution (left + first) (right + second)

private theorem delta_translated {State : Type*} [AddCommGroup State]
    (distribution : ℤ → ℤ → State) (left right : ℤ) (order : ℕ) :
    delta^[order] (translated distribution left right) =
      translated (delta^[order] distribution) left right := by
  induction order with
  | zero => rfl
  | succ order inductionProof =>
    rw [Function.iterate_succ_apply', inductionProof, Function.iterate_succ_apply']
    funext first second
    simp only [delta, translated, add_assoc]

private theorem coverLocal_add (D : LatticeData) (hu : IsUnit D.G.det)
    (first second third : NativeField D hu)
    (firstLocal : CoverLocal D hu first third) (secondLocal : CoverLocal D hu second third) :
    CoverLocal D hu (first + second) third := by
  obtain ⟨firstOrder, firstKilled⟩ := firstLocal
  obtain ⟨secondOrder, secondKilled⟩ := secondLocal
  refine ⟨max firstOrder secondOrder, ?_⟩
  intro firstExponent secondExponent
  have grid : coverGrid D hu (first + second) third firstExponent secondExponent =
      coverGrid D hu first third firstExponent secondExponent +
        coverGrid D hu second third firstExponent secondExponent := by
    funext left right
    simp only [coverGrid, map_add, Pi.add_apply, add_mul, mul_add]
    abel
  rw [grid, ← delta_power]
  rw [map_add, delta_power, delta_power,
    monotone _ _ _ (le_max_left _ _) (firstKilled firstExponent secondExponent),
    monotone _ _ _ (le_max_right _ _) (secondKilled firstExponent secondExponent), add_zero]

private theorem delta_flip {State : Type*} [AddCommGroup State] [Module ℂ State]
    (value : ℤ → ℤ → Module.End ℂ State) (order : ℕ) :
    delta^[order] (flipDistribution value) =
      ((-1 : ℂ) ^ order) • flipDistribution (delta^[order] value) := by
  induction order with
  | zero => simp
  | succ count inductionProof =>
    rw [Function.iterate_succ_apply', inductionProof, Function.iterate_succ_apply']
    funext left right
    simp only [delta, flipDistribution, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.smul_apply, pow_succ]
    module

private theorem coverLocal_symm (D : LatticeData) (hu : IsUnit D.G.det)
    (first second : NativeField D hu) (locality : CoverLocal D hu first second) :
    CoverLocal D hu second first := by
  obtain ⟨order, killed⟩ := locality
  refine ⟨order, ?_⟩
  intro firstExponent secondExponent
  have grid : coverGrid D hu second first firstExponent secondExponent =
      -flipDistribution (coverGrid D hu first second secondExponent firstExponent) := by
    funext left right
    simp only [coverGrid, flipDistribution, LinearMap.coe_mk, AddHom.coe_mk, Pi.neg_apply]
    abel
  rw [grid, ← delta_power]
  rw [map_neg, delta_power, delta_flip, killed, map_zero, smul_zero, neg_zero]

private theorem coverLocal_smul (D : LatticeData) (hu : IsUnit D.G.det)
    (scalar : ℂ) (first second : NativeField D hu) (locality : CoverLocal D hu first second) :
    CoverLocal D hu (scalar • first) second := by
  obtain ⟨order, killed⟩ := locality
  refine ⟨order, ?_⟩
  intro firstExponent secondExponent
  have grid : coverGrid D hu (scalar • first) second firstExponent secondExponent =
      scalar • coverGrid D hu first second firstExponent secondExponent := by
    funext left right
    simp only [coverGrid, map_smul, Pi.smul_apply,
      Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_sub]
  rw [grid, ← delta_power]
  rw [map_smul, delta_power, killed, smul_zero]

private theorem coverLocal_sum (D : LatticeData) (hu : IsUnit D.G.det)
    {IndexType : Type*} (indices : Finset IndexType) (fields : IndexType → NativeField D hu)
    (other : NativeField D hu) (locality : ∀ index ∈ indices, CoverLocal D hu (fields index) other) :
    CoverLocal D hu (∑ index ∈ indices, fields index) other := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_⟩
    intros
    simp only [Finset.sum_empty, Function.iterate_zero_apply]
    funext left right
    simp [coverGrid]
  | @insert head tail absent inductionProof =>
    rw [Finset.sum_insert absent]
    exact coverLocal_add D hu _ _ _ (locality head (Finset.mem_insert_self _ _))
      (inductionProof (fun index member => locality index (Finset.mem_insert_of_mem member)))

private theorem coverLocal_shift (D : LatticeData) (hu : IsUnit D.G.det)
    (shift : ℕ) (first second : NativeField D hu) (locality : CoverLocal D hu first second) :
    CoverLocal D hu (shiftField D hu shift first) second := by
  obtain ⟨order, killed⟩ := locality
  refine ⟨order, ?_⟩
  intro firstExponent secondExponent
  have grid : coverGrid D hu (shiftField D hu shift first) second firstExponent secondExponent =
      coverGrid D hu first second (firstExponent + 2 * shift) secondExponent := by
    funext left right
    simp only [coverGrid, shiftField_coeff]
    rw [show firstExponent - 2 * left + 2 * shift = firstExponent + 2 * shift - 2 * left by omega]
  rw [grid, killed]


private theorem chargedWordField_cover_locality (D : LatticeData) (hu : IsUnit D.G.det)
    (first second : Charge D) (firstWord secondWord : List (Index D)) :
    CoverLocal D hu (chargedWordField D hu first firstWord)
      (chargedWordField D hu second secondWord) := by
  obtain ⟨order, killed⟩ := physicalWord_locality D hu first second firstWord secondWord
  refine ⟨order, ?_⟩
  intro firstExponent secondExponent
  let distribution : ℤ → ℤ → Module.End ℂ (ActualTensor D hu) :=
    commutator (physicalSlice D hu (chargedWordField D hu first firstWord)
      (-firstExponent - 2))
      (physicalSlice D hu (chargedWordField D hu second secondWord)
        (-secondExponent - 2))
  have grid : coverGrid D hu (chargedWordField D hu first firstWord)
      (chargedWordField D hu second secondWord) firstExponent secondExponent =
      distribution := by
    funext left right
    simp only [coverGrid, distribution,
      FieldNormalProductLocality.commutator, physicalSlice_mode]
    congr 1 <;> ring_nf
  rw [grid]
  exact killed _ _

private theorem polynomialField_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (polynomial : Oscillator D) :
    polynomialField D hu charge polynomial =
      ∑ monomial ∈ polynomial.support,
        polynomial.coeff monomial • chargedWordField D hu charge (occurrences D monomial) := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum polynomial]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro monomial member
  have term : MvPolynomial.monomial monomial (polynomial.coeff monomial) =
      polynomial.coeff monomial • MvPolynomial.monomial monomial (1 : ℂ) := by
    simp [MvPolynomial.smul_monomial]
  rw [term, map_smul]
  have basis := (MvPolynomial.basisMonomials (Index D) ℂ).constr_basis ℂ
    (fun exponent => chargedWordField D hu charge (occurrences D exponent)) monomial
  exact congrArg (fun value => polynomial.coeff monomial • value) basis

private theorem correctedField_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    (state : Carrier D) :
    correctedField D hu state = ∑ charge ∈ state.support,
      ∑ shift ∈ (Corr D charge (state charge)).support,
        ∑ monomial ∈ (Corr D charge (state charge) shift).support,
          (Corr D charge (state charge) shift).coeff monomial •
            shiftField D hu shift
              (chargedWordField D hu charge (occurrences D monomial)) := by
  classical
  simp only [correctedField, correctedPolynomial, correctedSum, Finsupp.lsum_apply,
    Finsupp.sum, Finset.sum_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    Corr, shiftCoefficients]
  apply Finset.sum_congr rfl
  intro charge chargeMember
  apply Finset.sum_congr rfl
  intro shift shiftMember
  rw [polynomialField_expansion, map_sum]
  simp only [map_smul]

private theorem correctedField_word_locality (D : LatticeData) (hu : IsUnit D.G.det)
    (state : Carrier D) (charge : Charge D) (word : List (Index D)) :
    CoverLocal D hu (correctedField D hu state) (chargedWordField D hu charge word) := by
  rw [correctedField_expansion D hu state]
  apply coverLocal_sum
  intro sourceCharge _
  apply coverLocal_sum
  intro shift _
  apply coverLocal_sum
  intro monomial _
  apply coverLocal_smul
  apply coverLocal_shift
  exact chargedWordField_cover_locality D hu sourceCharge charge
    (occurrences D monomial) word

/-- Exact all-source physical locality on the canonical corrected field. -/
theorem correctedField_physical_locality (D : LatticeData) (hu : IsUnit D.G.det)
    (first second : Carrier D) :
    ∃ order : ℕ, ∀ firstExponent secondExponent : ℤ, ∀ vector : ActualTensor D hu,
      ∑ offset ∈ Finset.range (order + 1),
        (((-1 : ℂ) ^ offset) * (order.choose offset : ℂ)) •
          ((correctedField D hu first).coeff
              (firstExponent - 2 * ((order - offset : ℕ) : ℤ))
              ((correctedField D hu second).coeff
                (secondExponent - 2 * (offset : ℤ)) vector) -
            (correctedField D hu second).coeff
              (secondExponent - 2 * (offset : ℤ))
              ((correctedField D hu first).coeff
                (firstExponent - 2 * ((order - offset : ℕ) : ℤ)) vector)) = 0 := by
  have locality : CoverLocal D hu (correctedField D hu first)
      (correctedField D hu second) := by
    apply coverLocal_symm
    rw [correctedField_expansion D hu second]
    apply coverLocal_sum
    intro charge _
    apply coverLocal_sum
    intro shift _
    apply coverLocal_sum
    intro monomial _
    apply coverLocal_smul
    apply coverLocal_shift
    exact coverLocal_symm D hu _ _
      (correctedField_word_locality D hu first charge (occurrences D monomial))
  obtain ⟨order, killed⟩ := locality
  refine ⟨order, ?_⟩
  intro firstExponent secondExponent vector
  have zero : ((deltaEnd ^ order)
      (coverGrid D hu (correctedField D hu first) (correctedField D hu second)
        firstExponent secondExponent)) 0 0 vector = 0 := by
    rw [Module.End.pow_apply]
    exact congrArg (fun distribution : ℤ → ℤ → Module.End ℂ (ActualTensor D hu) =>
      distribution 0 0 vector) (killed firstExponent secondExponent)
  rw [FieldDeltaBinomial.delta_binomial] at zero
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, coverGrid, zero_add,
    LinearMap.sub_apply, Module.End.mul_apply, Pi.zero_apply, LinearMap.zero_apply] at zero
  convert zero using 1
  apply Finset.sum_congr rfl
  intro offset member
  have bound : offset ≤ order := Nat.le_of_lt_succ (Finset.mem_range.mp member)
  rw [Int.natCast_sub bound]

end
end D5.S3.VertexAlgebra.LatticeHalfFockAllStatePhysicalLocality
