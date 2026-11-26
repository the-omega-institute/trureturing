import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFirstOscillatorMultilinearity
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qSignedNormalWord
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedFieldEnergy
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedStateEnergy
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg

/-!
Conformal zero-mode covariance for the order-three P48q field on finite
products of first oscillator directions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qWickEnergyCovariance

open LatticeGeneratingFieldLocality (Charge bilinear)
open P48qTwistedChargeAction (lattice Momentum)
open P48qThirdTwistedField (Cartan Mode Fock State frequency fieldCoeff fixedDualBases)
open P48qTwistedStateEnergy (Occupation occupationFrequency oscillator oscillator_monomial
  totalLZero totalLZero_apply totalLZero_fieldCoeff_commutator)
open P48qTwistedHeisenberg (mode mode_zero_apply create annihilate scale annCoordinates
  creCoordinates)
open P48qSignedNormalWord (insertMode insertMode_apply wordTerm wordTerm_finite
  normalOrderedCoeff wickCoeff)
open P48qArbitraryWickRecursion (normalWick normalWickWord normalWick_nil normalWick_step)
open P48qCurrentChargedIterate (contraction)
open P48qQuadraticStateField (correction)
open P48qFirstOscillatorField (directionPolynomial sourceEquiv subspaceField
  subspaceField_direction_word wordField_coeff)
open MvPolynomial
open scoped BigOperators VertexOperator

open private oscillator_X_mul from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedFieldEnergy
open private mode_at_pos mode_at_neg onState_apply from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg
open private wordTerm_cons from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qSignedNormalWord

private theorem frequency_sub_single_add (d : Occupation) (j : Mode) (h : d j ≠ 0) :
    occupationFrequency (d - Finsupp.single j 1) + frequency j = occupationFrequency d := by
  simpa only [occupationFrequency, Finsupp.weight_apply, Nat.nsmul_eq_mul, Nat.mul_comm]
    using (Finsupp.weight_sub_single_add (w := frequency) h)

/-- Differentiation lowers the weighted polynomial degree by the variable's frequency. -/
private theorem oscillator_pderiv (j : Mode) (P : Fock) :
    oscillator (pderiv j P) = pderiv j (oscillator P) +
      (-(frequency j : ℂ) / 3) • pderiv j P := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    by_cases h : d j = 0
    · simp [oscillator_monomial, pderiv_monomial, h]
    · have hweight := congrArg (fun n : ℕ => (n : ℂ)) (frequency_sub_single_add d j h)
      simp only [Nat.cast_add] at hweight
      rw [oscillator_monomial, Derivation.map_smul, pderiv_monomial, oscillator_monomial,
        ← add_smul]
      congr 1
      rw [← hweight]
      ring
  | add P Q hP hQ =>
    simp only [map_add, hP, hQ, smul_add]
    abel

private theorem oscillator_sum_degree (As : Fin 16 → Module.End ℂ Fock)
    (c : Fin 16 → ℂ) (r : ℂ)
    (h : ∀ i P, oscillator (As i P) = As i (oscillator P) + r • As i P)
    (P : Fock) :
    oscillator ((∑ i, c i • As i) P) =
      (∑ i, c i • As i) (oscillator P) + r • (∑ i, c i • As i) P := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h, smul_add,
    Finset.sum_add_distrib, Finset.smul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => smul_comm (c i) r (As i P)

private theorem mode_degree_of_sector (T : Module.End ℂ State) (A : Module.End ℂ Fock)
    (r : ℂ) (hT : ∀ w p, T w p = A (w p))
    (hA : ∀ P, oscillator (A P) = A (oscillator P) + r • A P) :
    ⁅totalLZero, T⁆ = r • T := by
  apply LinearMap.ext
  intro w
  apply Finsupp.ext
  intro p
  simp only [Ring.lie_def, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
    Finsupp.sub_apply, Finsupp.smul_apply, hT, totalLZero_apply, hA, map_add, map_smul]
  abel

/-- At signed cover index m the concrete current has physical energy degree -m/3. -/
theorem totalLZero_mode_commutator (u : Cartan) (m : ℤ) :
    ⁅totalLZero, mode u m⁆ = (-(m : ℂ) / 3) • mode u m := by
  cases m with
  | ofNat m =>
    cases m with
    | zero =>
      change ⁅totalLZero, mode u 0⁆ = (-((0 : ℤ) : ℂ) / 3) • mode u 0
      apply LinearMap.ext
      intro w
      apply Finsupp.ext
      intro p
      simp only [Ring.lie_def, Module.End.mul_apply, LinearMap.sub_apply, Finsupp.sub_apply,
        Int.cast_zero, neg_zero, zero_div, zero_smul, LinearMap.zero_apply, Finsupp.zero_apply,
        totalLZero_apply, mode_zero_apply, map_smul, smul_add]
      module
    | succ n =>
      rw [mode_at_pos]
      apply mode_degree_of_sector _ _ _ (onState_apply _)
      change ∀ P, oscillator (annihilate n (annCoordinates u n) P) =
        annihilate n (annCoordinates u n) (oscillator P) +
          (-((((n + 1 : ℕ) : ℤ) : ℂ)) / 3) • annihilate n (annCoordinates u n) P
      rw [Int.cast_natCast]
      exact
        oscillator_sum_degree (fun i => (pderiv (i, n)).toLinearMap)
          (fun i => scale n * annCoordinates u n i) (-((n + 1 : ℕ) : ℂ) / 3)
          (fun i P => oscillator_pderiv (i, n) P)
  | negSucc n =>
    rw [mode_at_neg]
    apply mode_degree_of_sector _ _ _ (onState_apply _)
    simpa only [create, frequency, Int.cast_negSucc, neg_neg, Nat.cast_add, Nat.cast_one] using
      oscillator_sum_degree (fun i => LinearMap.mulLeft ℂ (X (i, n)))
        (creCoordinates u n) (((n + 1 : ℕ) : ℂ) / 3)
        (fun i P => oscillator_X_mul (i, n) P)

private theorem end_mul_degree (A B : Module.End ℂ State) (r s : ℂ)
    (hA : ⁅totalLZero, A⁆ = r • A) (hB : ⁅totalLZero, B⁆ = s • B) :
    ⁅totalLZero, A * B⁆ = (r + s) • (A * B) := by
  calc
    ⁅totalLZero, A * B⁆ = ⁅totalLZero, A⁆ * B + A * ⁅totalLZero, B⁆ := by
      simp only [Ring.lie_def, sub_mul, mul_sub, mul_assoc]
      abel
    _ = _ := by rw [hA, hB, smul_mul_assoc, mul_smul_comm, add_smul]

private theorem insertMode_degree (u : Cartan) (m : ℤ) (B : Module.End ℂ State) (r : ℂ)
    (hB : ⁅totalLZero, B⁆ = r • B) :
    ⁅totalLZero, insertMode (u, m) B⁆ = (r - (m : ℂ) / 3) • insertMode (u, m) B := by
  rw [insertMode_apply]
  have hm := totalLZero_mode_commutator u m
  by_cases h : m < 0
  · rw [ite_eq_left h, end_mul_degree _ _ _ _ hm hB]
    congr 1
    ring
  · rw [ite_eq_right h, end_mul_degree _ _ _ _ hB hm]
    congr 1
    ring

private theorem wordTerm_degree (a : Charge lattice) (k : ℤ) (directions : List Cartan)
    (indices : P48qSignedNormalWord.Indices directions.length) :
    ⁅totalLZero, wordTerm a k directions indices⁆ =
      ((k : ℂ) / 3 + (bilinear lattice a a : ℂ) / 2 + (directions.length : ℂ)) •
        wordTerm a k directions indices := by
  induction directions generalizing k with
  | nil =>
    have hnil : wordTerm a k [] indices = fieldCoeff fixedDualBases a k :=
      P48qSignedNormalWord.signedWordCoeff_nil a k
    rw [hnil]
    simpa only [Ring.lie_def, Module.End.mul_eq_comp, List.length_nil, Nat.cast_zero, add_zero]
      using totalLZero_fieldCoeff_commutator fixedDualBases a k
  | cons u tail ih =>
    obtain ⟨m, rest⟩ := indices
    rw [wordTerm_cons, insertMode_degree _ _ _ _ (ih (k + 3 + m) rest)]
    congr 1
    simp only [Int.cast_add, Int.cast_ofNat, List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

/-- The pointwise finite normal-order sum has the common degree of its signed summands. -/
theorem totalLZero_normalOrderedCoeff_commutator (a : Charge lattice) (k : ℤ)
    (directions : List Cartan) :
    ⁅totalLZero, normalOrderedCoeff a k directions⁆ =
      ((k : ℂ) / 3 + (bilinear lattice a a : ℂ) / 2 + (directions.length : ℂ)) •
        normalOrderedCoeff a k directions := by
  apply LinearMap.ext
  intro w
  let r : ℂ := (k : ℂ) / 3 + (bilinear lattice a a : ℂ) / 2 + (directions.length : ℂ)
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply]
  change totalLZero (∑ᶠ indices, wordTerm a k directions indices w) -
    (∑ᶠ indices, wordTerm a k directions indices (totalLZero w)) =
      r • (∑ᶠ indices, wordTerm a k directions indices w)
  have h := wordTerm_finite a k directions w
  have hL : Function.HasFiniteSupport (fun i => totalLZero (wordTerm a k directions i w)) :=
    h.subset fun i hi => by
      change totalLZero (wordTerm a k directions i w) ≠ 0 at hi
      change wordTerm a k directions i w ≠ 0
      exact fun hz => hi (by rw [hz, map_zero])
  rw [map_finsum _ h, ← finsum_sub_distrib hL
    (wordTerm_finite a k directions (totalLZero w)), smul_finsum' _ h]
  apply finsum_congr
  intro indices
  exact DFunLike.congr_fun (wordTerm_degree a k directions indices) w

attribute [local instance 100] LieRing.ofAssociativeRing in
private theorem normalWick_degree
    (A : Matrix Cartan Cartan ℂ) (μ : Cartan → ℂ) (normal : List Cartan → Module.End ℂ State)
    (r : ℂ) (h : ∀ kept, ⁅totalLZero, normal kept⁆ = r • normal kept)
    (pending kept : List Cartan) :
    ⁅totalLZero, normalWick A μ normal pending kept⁆ =
      r • normalWick A μ normal pending kept := by
  cases pending with
  | nil => simpa only [normalWick_nil] using h kept
  | cons u tail =>
    rw [normalWick_step]
    simp only [lie_add, lie_smul, lie_sum,
      normalWick_degree A μ normal r h tail (kept ++ [u]),
      normalWick_degree A μ normal r h tail kept,
      smul_add, Finset.smul_sum]
    rw [smul_comm (μ u) r]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [normalWick_degree A μ normal r h (tail.eraseIdx j) kept, smul_comm (A u (tail.get j)) r]
termination_by pending.length
decreasing_by
  all_goals simp only [List.length_cons]
  all_goals first | exact Nat.lt_succ_self _ | exact Nat.lt_succ_of_le (List.length_eraseIdx_le ..)

/-- The actual Wick coefficient at cover exponent k has the charged weight plus
the first-oscillator length and k/3 as its conformal commutator degree. -/
theorem totalLZero_wickCoeff_commutator (a : Charge lattice) (k : ℤ)
    (directions : List Cartan) :
    ⁅totalLZero, wickCoeff a k directions⁆ =
      ((k : ℂ) / 3 + (bilinear lattice a a : ℂ) / 2 + (directions.length : ℂ)) •
        wickCoeff a k directions := by
  unfold wickCoeff normalWickWord
  apply normalWick_degree
  intro kept
  rw [totalLZero_normalOrderedCoeff_commutator]
  congr 1
  push_cast
  ring

/-- Covariance for the actual field attached to a directional first-oscillator source monomial. -/
theorem totalLZero_subspaceField_direction_word_commutator (a : Charge lattice) (k : ℤ)
    (directions : List Cartan) :
    ⁅totalLZero, HVertexOperator.coeff
      (subspaceField (sourceEquiv (Finsupp.single a (directions.map directionPolynomial).prod)))
      k⁆ =
      ((k : ℂ) / 3 + (bilinear lattice a a : ℂ) / 2 + (directions.length : ℂ)) •
        HVertexOperator.coeff
          (subspaceField (sourceEquiv (Finsupp.single a (directions.map directionPolynomial).prod)))
          k := by
  rw [subspaceField_direction_word, wordField_coeff]
  exact totalLZero_wickCoeff_commutator a k directions

#print axioms totalLZero_mode_commutator
#print axioms totalLZero_normalOrderedCoeff_commutator
#print axioms totalLZero_wickCoeff_commutator
#print axioms totalLZero_subspaceField_direction_word_commutator

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qWickEnergyCovariance
